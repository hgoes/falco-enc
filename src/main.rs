#[macro_use]
extern crate clap;
extern crate llvm_ir;
extern crate symbolic_llvm;
extern crate smtrs;
extern crate serde;
#[macro_use]
extern crate serde_json;
#[macro_use]
extern crate serde_derive;
extern crate num_bigint;
extern crate nom;
#[cfg(feature="cpuprofiling")]
extern crate cpuprofiler;

mod fun_spec;
mod falco;

use llvm_ir::{Module,Instruction,Metadata,parse_module};
use symbolic_llvm::symbolic::llvm::*;
use symbolic_llvm::symbolic::llvm::program::*;
use symbolic_llvm::symbolic::llvm::pointer::*;
use symbolic_llvm::symbolic::llvm::mem::*;
use symbolic_llvm::symbolic::llvm::thread::CallId;
use symbolic_llvm::symbolic::llvm::library::{Library,StdLib};
use llvm_ir::datalayout::DataLayout;
use smtrs::types::Value;
use smtrs::composite::*;
use smtrs::embed::{Embed,DeriveConst,DeriveValues};
use smtrs::backend::{Backend,Pipe};
use smtrs::domain::*;
use smtrs::unique::Uniquer;
use smtrs::expr as expr;
use smtrs::types as types;
use std::fmt::{Debug,Display,format};
use std::fmt;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fs::File;
use std::io;
use std::iter::Peekable;
use num_bigint::{BigInt,BigUint};
use std::mem::{swap,replace};
#[cfg(feature="cpuprofiling")]
use cpuprofiler::PROFILER;

type Val<'a> = CompValue<ByteWidth<BasePointer<'a>>,BitVecValue>;

struct SepDomain<DomA,DomB> {
    offset1: usize,
    dom1: DomA,
    dom2: DomB
}

impl<A : Composite+Clone,B : Composite+Clone,DomA : Domain<A>,DomB : Domain<B>> Domain<(A,B)> for SepDomain<DomA,DomB> {
    type ValueIterator = OptIntersection2<Value,DomA::ValueIterator,DomB::ValueIterator>;
    fn full(obj: &(A,B)) -> Self {
        SepDomain { offset1: obj.0.num_elem(),
                    dom1: DomA::full(&obj.0),
                    dom2: DomB::full(&obj.1) }
    }
    fn is_full(&self) -> bool {
        self.dom1.is_full() && self.dom2.is_full()
    }
    fn union(&mut self,oth: &Self) -> () {
        self.dom1.union(&oth.dom1);
        self.dom2.union(&oth.dom2);
    }
    fn intersection(&mut self,oth: &Self) -> bool {
        if !self.dom1.intersection(&oth.dom1) {
            return false;
        }
        self.dom2.intersection(&oth.dom2)
    }
    fn derive<Em : Embed,F>(&self,exprs: &[Em::Expr],em: &mut Em,f: &F)
                            -> Result<Self,Em::Error>
        where F : Fn(&Em::Var) -> Option<usize> {
        unimplemented!()
    }
    fn refine<Em : Embed,F : Fn(&Em::Var) -> Option<usize>>(&mut self,e: &Em::Expr,em: &mut Em,f: &F)
                                                            -> Result<bool,Em::Error> {
        let off = self.offset1;
        let dom1_valid = self.dom1.refine(e,em,&|v| match f(v) {
            None => None,
            Some(rv) => if rv >= off {
                None
            } else {
                Some(rv)
            }
        })?;
        if !dom1_valid {
            return Ok(false)
        }
        self.dom2.refine(e,em,&|v| match f(v) {
            None => None,
            Some(rv) => if rv < off {
                None
            } else {
                Some(rv-off)
            }
        })
    }
    fn is_const<Em : Embed,F : Fn(&Em::Var) -> Option<usize>>(&self,e: &Em::Expr,em: &mut Em,f: &F)
                                                              -> Result<Option<Value>,Em::Error> {
        let off = self.offset1;
        let const1 = self.dom1.is_const(e,em,&|v| match f(v) {
            None => None,
            Some(rv) => if rv >= off {
                None
            } else {
                Some(rv)
            }
        })?;
        match const1 {
            Some(v) => return Ok(Some(v)),
            None => {}
        }
        self.dom2.is_const(e,em,&|v| match f(v) {
            None => None,
            Some(rv) => if rv < off {
                None
            } else {
                Some(rv-off)
            }
        })
    }
    fn values<Em : Embed,F : Fn(&Em::Var) -> Option<usize>>(&self,e: &Em::Expr,em: &mut Em,f: &F)
                                                            -> Result<Option<Self::ValueIterator>,Em::Error> {
        let off = self.offset1;
        let vals1 = self.dom1.values(e,em,&|v| match f(v) {
            None => None,
            Some(rv) => if rv >= off {
                None
            } else {
                Some(rv)
            }
        })?;
        let vals2 = self.dom2.values(e,em,&|v| match f(v) {
            None => None,
            Some(rv) => if rv < off {
                None
            } else {
                Some(rv-off)
            }
        })?;
        match vals1 {
            None => match vals2 {
                None => Ok(None),
                Some(it2) => Ok(Some(OptIntersection2::Only2(it2)))
            },
            Some(it1) => match vals2 {
                None => Ok(Some(OptIntersection2::Only1(it1))),
                Some(it2) => Ok(Some(OptIntersection2::Both(Intersection2::new(it1,it2))))
            }
        }
    }
    fn forget_var(&mut self,n: usize) -> () {
        if n<self.offset1 {
            self.dom1.forget_var(n)
        } else {
            self.dom2.forget_var(n-self.offset1)
        }
    }
}

struct CompProgram<'a,'b : 'a,V : 'b+Bytes+FromConst<'b>,
                   DomProg : 'a+Domain<Program<'b,V>>,
                   DomInp : 'a+Domain<ProgramInput<'b,V>>> {
    prog: &'a Program<'b,V>,
    inp: &'a ProgramInput<'b,V>,
    dom_prog: &'a DomProg,
    dom_inp: &'a DomInp,
}

impl<'a,'b,V,DomProg,DomInp> Embed for CompProgram<'a,'b,V,DomProg,DomInp>
    where V : Bytes+FromConst<'b>+Debug,
          DomProg : 'a+Domain<Program<'b,V>>,
          DomInp : 'a+Domain<ProgramInput<'b,V>> {
    
    type Sort = types::Sort;
    type Var = CompVar;
    type Expr = CompExpr<(Program<'b,V>,ProgramInput<'b,V>)>;
    type Fun = expr::NoVar;
    type Error = ();
    fn embed_sort(&mut self,tp: types::SortKind<types::Sort>)
                  -> Result<types::Sort,()> {
        Ok(types::Sort::from_kind(tp))
    }
    fn unbed_sort(&mut self,tp: &types::Sort)
                  -> Result<types::SortKind<types::Sort>,()> {
        Ok(tp.kind())
    }
    fn embed(&mut self,e: expr::Expr<Self::Sort,Self::Var,Self::Expr,Self::Fun>)
             -> Result<Self::Expr,()> {
        Ok(CompExpr::new(e))
    }
    fn unbed(&mut self,e: &Self::Expr)
             -> Result<expr::Expr<Self::Sort,Self::Var,Self::Expr,Self::Fun>,()> {
        Ok((*e.0).clone())
    }
    fn type_of_var(&mut self,var: &Self::Var) -> Result<Self::Sort,Self::Error> {
        let prog_sz = self.prog.num_elem();
        if var.0 < prog_sz {
            self.prog.elem_sort(var.0,self)
        } else {
            self.inp.elem_sort(var.0-prog_sz,self)
        }
    }
    fn type_of_fun(&mut self,fun:&Self::Fun) -> Result<Self::Sort,Self::Error> {
        unreachable!()
    }
    fn arity(&mut self,fun:&Self::Fun) -> Result<usize,Self::Error> {
        unreachable!()
    }
    fn type_of_arg(&mut self,fun:&Self::Fun,p:usize) -> Result<Self::Sort,Self::Error> {
        unreachable!()
    }
}

impl<'a,'b,V,DomProg,DomInp> DeriveConst for CompProgram<'a,'b,V,DomProg,DomInp>
    where V : Bytes+FromConst<'b>+Debug,
          DomProg : 'a+Domain<Program<'b,V>>,
          DomInp : 'a+Domain<ProgramInput<'b,V>> {
    fn derive_const(&mut self,e: &Self::Expr)
                    -> Result<Option<Value>,Self::Error> {
        let prog_sz = self.prog.num_elem();
        let const1 = self.dom_prog.is_const(e,self,&|v| if v.0 < prog_sz {
            Some(v.0)
        } else {
            None
        })?;
        if let Some(v) = const1 {
            return Ok(Some(v))
        }
        self.dom_inp.is_const(e,self,&|v| if v.0 >= prog_sz {
            Some(v.0-prog_sz)
        } else {
            None
        })
    }
}

impl<'a,'b,V,DomProg,DomInp> DeriveValues for CompProgram<'a,'b,V,DomProg,DomInp>
    where V : Bytes+FromConst<'b>+Debug,
          DomProg : 'a+Domain<Program<'b,V>>,
          DomInp : 'a+Domain<ProgramInput<'b,V>> {
    type ValueIterator = OptIntersection2<Value,DomProg::ValueIterator,DomInp::ValueIterator>;
    fn derive_values(
        &mut self, 
        e: &Self::Expr
    ) -> Result<Option<Self::ValueIterator>, Self::Error> {
        let prog_sz = self.prog.num_elem();
        let vals_prog = self.dom_prog.values(e,self,&|v| if v.0<prog_sz {
            Some(v.0)
        } else {
            None
        })?;
        let vals_inp = self.dom_inp.values(e,self,&|v| if v.0>=prog_sz {
            Some(v.0-prog_sz)
        } else {
            None
        })?;
        Ok(match vals_prog {
            None => match vals_inp {
                None => None,
                Some(vals_inp_) => Some(OptIntersection2::Only2(vals_inp_))
            },
            Some(vals_prog_) => match vals_inp {
                None => Some(OptIntersection2::Only1(vals_prog_)),
                Some(vals_inp_) => Some(OptIntersection2::Both(
                    Intersection2::new(vals_prog_,vals_inp_)))
            }
        })
    }
}

struct FalcoCfg<Em : Embed> {
    paths: Option<Vec<Transf<Em>>>,
    current_path: Vec<Transf<Em>>
}

impl<Em : Embed> FalcoCfg<Em> {
    pub fn new() -> Self {
        FalcoCfg { paths: Some(Vec::new()),
                   current_path: Vec::new() }
    }
    pub fn condition(mut self,em: &mut Em)
                     -> Result<Option<Transf<Em>>,Em::Error> {
        match self.paths {
            None => Ok(None),
            Some(mut paths) => match paths.len() {
                0 => Ok(Some(Transformation::const_bool(false,em)?)),
                1 => Ok(Some(paths.remove(0))),
                _ => Ok(Some(Transformation::or(paths)))
            }
        }
    }
}

impl<Em : Embed> TranslationCfg<Em> for FalcoCfg<Em> {
    fn change_thread_activation(
        &mut self,
        conds:&mut Vec<Transf<Em>>,pos:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        self.current_path.extend(conds.drain(pos..));
        Ok(())
    }
    fn change_context_activation(
        &mut self,
        conds:&mut Vec<Transf<Em>>,pos:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        self.current_path.extend(conds.drain(pos..));
        Ok(())
    }
    fn change_call_frame_activation(
        &mut self,
        conds:&mut Vec<Transf<Em>>,pos:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        self.current_path.extend(conds.drain(pos..));
        Ok(())
    }
    fn change_instr_activation(
        &mut self,
        conds:&mut Vec<Transf<Em>>,pos:usize,em:&mut Em)
        -> Result<(),Em::Error> {
        self.current_path.extend(conds.drain(pos..));
        let mut path = replace(&mut self.current_path,Vec::new());
        match path.len() {
            0 => {
                self.paths = None;
            },
            1 => match self.paths {
                None => {},
                Some(ref mut paths) => {
                    paths.push(path.remove(0))
                }
            },
            _ => match self.paths {
                None => {},
                Some(ref mut paths) => {
                    paths.push(Transformation::and(path))
                }
            }
        }
        Ok(())
    }
}

fn translate_init_<'a,'b,Em>(module: &'a Module,
                             entry_fun: &'a String,
                             args: Vec<Val<'a>>,
                             inp_args: Transf<Em>,
                             aux: Vec<Vec<u8>>,
                             em: &mut Em)
                             -> Result<(OptRef<'b,Program<'a,Val<'a>>>,Transf<Em>),Em::Error>
    where Em : Embed {
    translate_init(module,entry_fun,args,inp_args,aux,em)
}

fn step<'a,Lib,V,Dom>(m: &'a Module,
                      lib: &Lib,
                      st: &Program<'a,V>,
                      domainUse: &Dom,
                      domainDerive1: &Dom,
                      domainDerive2: &Dom,
                      thread_id: ThreadId<'a>,
                      cf_id: CallId<'a>,
                      instr_id: InstructionRef<'a>,
                      debugging: u64)
                      -> (Program<'a,V>,ProgramInput<'a,V>,
                          Vec<CompExpr<(Program<'a,V>,ProgramInput<'a,V>)>>,
                          Option<CompExpr<(Program<'a,V>,ProgramInput<'a,V>)>>,
                          Dom,
                          Dom)
    where V : 'a+Bytes+FromConst<'a>+Pointer<'a>+IntValue+Vector+Semantic+Debug,
          Dom : Domain<Program<'a,V>>,
          Lib : Library<'a,V> {

    let instr = instr_id.resolve(m);
    let next_instr_id = instr_id.next();
    let prog_size = st.num_elem();

    let mut inp = ProgramInput::new();
    let dom_inp = ();
    let mut exprs = Vec::with_capacity(prog_size);
    {
        let mut comp = CompProgram { prog: st,
                                     inp: &inp,
                                     dom_prog: domainUse,
                                     dom_inp: &dom_inp };
        for i in 0..prog_size {
            exprs.push(comp.var(CompVar(i)).unwrap());
        }
    }

    loop {

        let ninp = {
            let mut comp = CompProgram { prog: st,
                                         inp: &inp,
                                         dom_prog: domainUse,
                                         dom_inp: &dom_inp };
            let inp_size = inp.num_elem();
            
            if prog_size+inp_size>exprs.len() {
                for i in exprs.len()..prog_size+inp_size {
                    exprs.push(comp.var(CompVar(i)).unwrap());
                }
            }
            let mut cfg = FalcoCfg::new();
            debug_assert_eq!(prog_size+inp_size,exprs.len());
            match translate_instr(&m,
                                  &mut cfg,
                                  lib,
                                  thread_id,
                                  cf_id,
                                  instr_id,
                                  instr,
                                  &st,
                                  &inp,
                                  Transformation::id(prog_size),
                                  Transformation::view(prog_size,inp_size,Transformation::id(prog_size+inp_size)),
                                  &exprs[..],
                                  &mut comp) {
                Ok((nprog,trans)) => {
                    debug_assert_eq!(nprog.num_elem(),trans.size());
                    //println!("TR: {:#?}",trans);
                    let nexprs = trans.get_all(&exprs[..],&mut comp).unwrap();
                    if cfg!(debug_assertions) {
                        for (i,e) in nexprs.iter().enumerate() {
                            let expected = nprog.elem_sort(i,&mut comp).unwrap();
                            let got = comp.type_of(e).unwrap();
                            if expected!=got {
                                println!("Warning: At expression {}({:?}), expected: {}, got: {} ({})",
                                         i,nprog.meaning(i),expected,got,e);
                            }
                        }
                    }
                    let (ndom1,ndom2) = {
                        let d1 = domainDerive1.derive(&nexprs[..],&mut comp,
                                                      &|v| if v.0 < prog_size {
                                                          Some(v.0)
                                                      } else {
                                                          panic!("Input vars?")//None
                                                      }).unwrap();
                        let d2 = domainDerive2.derive(&nexprs[..],&mut comp,
                                                      &|v| if v.0 < prog_size {
                                                          Some(v.0)
                                                      } else {
                                                          panic!("Input vars?")//None
                                                      }).unwrap();
                        (d1,d2)
                    };
                    if cfg!(debug_assertions) {
                        for i in 0..nexprs.len() {
                            match ndom2.is_const(&comp.var(CompVar(i)).unwrap(),&mut comp,
                                                 &|v| Some(v.0)).unwrap() {
                                None => panic!("Expression {} ({:?}) is not const in full domain",i,nexprs[i]),
                                Some(_) => {}
                            }
                        }
                    }
                    let cond = match cfg.condition(&mut comp).unwrap() {
                        None => None,
                        Some(c) => Some(c.get(&exprs[..],0,&mut comp).unwrap())
                    };
                    return (nprog,inp.clone(),nexprs,cond,ndom1,ndom2)
                },
                Err(TrErr::InputNeeded(ninp)) => ninp,
                _ => panic!("AAA")
            }
        };
        inp = ninp;
    }
}

type Selectors<Em : Embed> = HashMap<(u64,u64),Em::Var>;

fn get_dbg_loc(instr: &Instruction,m: &Module) -> Option<(u64,u64)> {
    match instr.metadata.get("dbg") {
        None => None,
        Some(n) => match m.md.get(n) {
            Some(&llvm_ir::Metadata::Location(ln,col,_)) => Some((ln,col)),
            _ => None
        }
    }
}

fn make_selectors<B : Backend>(m: &Module,b: &mut B) -> Result<Selectors<B>,B::Error> {
    let mut selectors = HashMap::new();
    for (fun_name,fun) in m.functions.iter() {
        if let Some(ref bdy) = fun.body {
            for blk in bdy.iter() {
                for instr in blk.instrs.iter() {
                    match get_dbg_loc(instr,m) {
                        None => {},
                        Some(loc) => match selectors.entry(loc) {
                            Entry::Occupied(_) => {},
                            Entry::Vacant(vac) => {
                                b.comment(format!("Selector for line: {}, column: {}",loc.0,loc.1).as_str())?;
                                let tp = b.tp_bool()?;
                                let v = b.declare_var(tp)?;
                                vac.insert(v);
                            }
                        }
                    }
                }
            }
        }
    }
    Ok(selectors)
}

macro_rules! debug {
    ($self:expr,$lvl:expr,$str:expr, $( $arg:expr ),* ) => {
        if $lvl <= $self.debugging {
            $self.backend.comment(format!($str, $( $arg ),*).as_ref())
                .expect("Failed to add comment")
        }
    }
}

struct TraceUnwinding<'a,R : io::Read,Em : Embed,V : Semantic+Bytes+FromConst<'a>,Dom>
    where Em : 'a,Em::Var : 'a {
    reader: falco::StepReader<'a,R>,
    step_buffer: Option<falco::Step<'a>>,
    selectors: &'a Selectors<Em>,
    backend: &'a mut Em,
    module: &'a Module,
    main: &'a String,
    program: Program<'a,V>,
    program_input: Vec<Em::Expr>,
    program_meaning: Vec<<Program<'a,V> as Semantic>::Meaning>,
    domain: Dom,
    domain_full: Dom,
    path: Vec<Em::Expr>,
    debugging: u64
}

struct FalcoLib<'a : 'b,'b> {
    ext: &'b falco::External<'a>
}

impl<'a,'b,V : 'a+Bytes+FromConst<'a>+IntValue> Library<'a,V> for FalcoLib<'a,'b> {
    fn call<RetV,Em : DeriveValues>(&self,
                                    fname: &'a String,
                                    args: &Vec<V>,
                                    args_inp: Transf<Em>,
                                    ret_view: Option<RetV>,
                                    dl: &'a DataLayout,
                                    instr_id: InstructionRef<'a>,
                                    conds: &mut Vec<Transf<Em>>,
                                    prog: &Program<'a,V>,
                                    prog_inp: Transf<Em>,
                                    nprog: &mut Program<'a,V>,
                                    updates: &mut Updates<Em>,
                                    exprs: &[Em::Expr],
                                    em: &mut Em)
                                    -> Result<bool,Em::Error>
        where RetV : ViewInsert<Viewed=Program<'a,V>,Element=V>+ViewMut {
        if *fname!=*self.ext.function {
            return Ok(false)
        }
        assert!(self.ext.args.iter().all(Option::is_none));
        match self.ext.ret {
            None => {}
            Some(ref rval) => match rval {
                &falco::Val::Int { bw,ref val } => {
                    let (i,i_inp) = V::const_int(bw,val.clone(),em)?;
                    match ret_view {
                        None => panic!("Trace has a return value but the function doesn't..."),
                        Some(ret_view_) => {
                            ret_view_.insert_cond(nprog,i,Transformation::constant(i_inp),
                                                  conds,updates,prog_inp,em)?
                        }
                    }
                },
                _ => unimplemented!()
            }
        }
        Ok(true)
    }
}

impl<'a,R : io::Read,Em : Backend,V,Dom : Domain<Program<'a,V>>+Clone> TraceUnwinding<'a,R,Em,V,Dom>
    where V : 'a+Bytes+FromConst<'a>+Pointer<'a>+IntValue+Vector+Debug+Semantic, Em::Expr : Display {
    pub fn new(inp: R,
               sel: &'a Selectors<Em>,
               m: &'a Module,
               spec: &'a fun_spec::FunSpecs,
               b: &'a mut Em,
               debug: u64) -> Result<Self,Em::Error> {
        let (args,mut reader) = falco::StepReader::new(m,spec,inp);
        let step0 = match reader.next() {
            None => panic!("Trace must have at least one element"),
            Some(step) => step
        };
        let fun = step0.fun;
        let argc_bw = match m.functions.get(fun) {
            None => panic!("Function {} not found in module",fun),
            Some(rfun) => if rfun.arguments.len()==2 {
                let argc_tp = &rfun.arguments[0].1;
                let argv_tp = &rfun.arguments[1].1;
                match argc_tp {
                    &llvm_ir::types::Type::Int(w) => w,
                    _ => panic!("First parameter of {} function should be an int, but is {:?}",
                                fun,argc_tp)
                }
            } else {
                panic!("Function {} should have two arguments, found {}.",
                       fun,rfun.arguments.len())
            }
        };
        let (ptr_bw,_,_) = m.datalayout.pointer_alignment(0);
        let (argc,argc_inp) = V::const_int(argc_bw,BigUint::from(args.len()),b)?;
        let (argv0,argv0_inp) = choice_empty();
        let (argv1,argv1_inp) = choice_insert(OptRef::Owned(argv0),argv0_inp,
                                              Transformation::const_bool(true,b)?,
                                              OptRef::Owned((PointerTrg::AuxArray,
                                                             (Data((0,(ptr_bw/8) as usize)),None))),
                                              Transformation::id(0))?;
        let (argv,argv_inp) = V::from_pointer((ptr_bw/8) as usize,argv1,argv1_inp);
        let (prog,prog_inp) = translate_init(m,fun,
                                             vec![argc,argv.as_obj()],
                                             Transformation::concat(&[Transformation::constant(argc_inp),argv_inp]),
                                             args,
                                             b)?;
        let init_exprs = prog_inp.get_all(&[][..],b)?;
        // FIXME: This should reference (), but that is not possible in Rust
        let dom_none : Dom = Dom::full(prog.as_ref());
        let dom_init = <Dom as Domain<Program<V>>>::derive(&dom_none,&init_exprs,b,
                                                           &|_| { unreachable!() })?;
        let mut meaning = Vec::with_capacity(init_exprs.len());
        for m in Semantics::new(prog.as_ref()) {
            meaning.push(m);
        }
        //println!("Program: {:#?}",prog.as_ref());
        Ok(TraceUnwinding { reader: reader,
                            step_buffer: Some(step0),
                            selectors: sel,
                            backend: b,
                            module: m,
                            main: fun,
                            program: prog.as_obj(),
                            program_input: init_exprs,
                            program_meaning: meaning,
                            domain: dom_init.clone(),
                            domain_full: dom_init,
                            path: Vec::new(),
                            debugging: debug })
    }
    fn debug<F>(&mut self,level: u64,outp: F) -> ()
        where F : FnOnce() -> String {
        if level >= self.debugging {
            self.backend.comment(outp().as_ref()).expect("Failed to add comment")
        }
    }
    fn step<'b>(&'b mut self) -> bool {
        let entr = match self.step_buffer.take() {
            Some(s) => s,
            None => match self.reader.next() {
                None => return false,
                Some(s) => s
            }
        };
        //println!("Next step: {:#?}",entr);
        let thr_id = (None,self.main);
        let fun = self.module.functions.get(entr.fun).expect("Function not found");
        let (instr,instr_ref) = match fun.body {
            None => panic!("Function has no body"),
            Some(ref blks) => {
                let blk = &blks[entr.blk];
                (&blk.instrs[entr.instr],
                 InstructionRef { function: &fun.name,
                                  basic_block: &blk.name,
                                  instruction: entr.instr })
            }
        };
        debug!(self,1,"Instruction {}.{}.{}",
               instr_ref.function,
               instr_ref.basic_block,
               instr_ref.instruction);
        debug!(self,3,"Content: {:?}",instr);
        let use_full = match instr.content {
            llvm_ir::InstructionC::Call(_,_,_,ref called,_,_) => match called {
                &llvm_ir::Value::Constant(ref c) => match c {
                    &llvm_ir::Constant::Global(ref g) => match g.as_ref() {
                        "malloc" => true,
                        "realloc" => true,
                        _ => false
                    },
                    _ => false
                },
                _ => false
            },
            llvm_ir::InstructionC::Unary(_,_,llvm_ir::UnaryInst::Load(_,_)) => true,
            llvm_ir::InstructionC::Store(_,_,_,_) => true,
            llvm_ir::InstructionC::GEP(_,_) => true,
            _ => false
        };
        let (mut nprog,ninp,nprog_inp,act,mut ndom,ndomFull)
            = match entr.ext {
                None => {
                    let lib = StdLib {};
                    step(self.module,&lib,&self.program,
                         if use_full {
                             &self.domain_full
                         } else {
                             &self.domain
                         },
                         &self.domain,
                         &self.domain_full,
                         thr_id,entr.call_id,instr_ref,
                         self.debugging)
                },
                Some(ref ext) => if ext.function=="realloc" || ext.function=="malloc" {
                    let lib = StdLib {};
                    step(self.module,&lib,&self.program,
                         if use_full {
                             &self.domain_full
                         } else {
                             &self.domain
                         },
                         &self.domain,
                         &self.domain_full,
                         thr_id,entr.call_id,instr_ref,
                         self.debugging)
                } else {
                    let lib = FalcoLib { ext: ext };
                    step(self.module,&lib,&self.program,
                         if use_full {
                             &self.domain_full
                         } else {
                             &self.domain
                         },
                         &self.domain,
                         &self.domain_full,
                         thr_id,entr.call_id,instr_ref,
                         self.debugging)
                }
            };
        let num_inp = ninp.num_elem();
        let mut cinp = Vec::with_capacity(num_inp);
        for i in 0..num_inp {
            let tp = ninp.elem_sort(i,self.backend).unwrap();
            let var = self.backend.declare(tp).unwrap();
            cinp.push(var);
        }
        let prog_sz = self.program.num_elem();
        let mut nprogram_input = Vec::with_capacity(nprog_inp.len());
        for e in nprog_inp.iter() {
            let prev = &self.program_input;
            let ne = e.translate(&mut |n,_| if n<prog_sz {
                Ok(prev[n].clone())
            } else {
                Ok(cinp[n-prog_sz].clone())
            },self.backend).unwrap();
            nprogram_input.push(ne);
        }
        let sel_var = match get_dbg_loc(instr,self.module) {
            None => None,
            Some(l) => Some(self.selectors.get(&l).expect("Selector not found"))
        };
        swap(&mut self.program,&mut nprog);
        let old_program = nprog;
        let mut old_semantics = Vec::with_capacity(nprogram_input.len());
        swap(&mut self.program_meaning,&mut old_semantics);
        match self.program.first_meaning() {
            None => {},
            Some((mut ctx,mut m)) => {
                self.program_meaning.push(m.clone());
                while self.program.next_meaning(&mut ctx,&mut m) {
                    self.program_meaning.push(m.clone());
                }
            }
        }
        /*for m in self.program.meanings() {
            self.program_meaning.push(m);
        }*/
        match sel_var {
            None => {},
            Some(sel) => {
                let sel_expr = self.backend.embed(expr::Expr::Var(sel.clone())).unwrap();
                for (idx,m) in self.program_meaning.iter().enumerate() {
                    // Is this a data variable?
                    if !m.is_pc() {
                        // Has the data variable changed?
                        match *nprog_inp[idx].0 {
                            expr::Expr::Var(ref old_idx)
                                if old_semantics[old_idx.0]==*m => {},
                            _ => {
                                debug!(self,2,"Meaning: {}",MeaningOf::new(&self.program,m));
                                // Variable has changed
                                let tp = self.program.elem_sort(idx,self.backend).unwrap();
                                let nondet = self.backend.declare(tp).unwrap();
                                let ne = self.backend.ite(sel_expr.clone(),nprogram_input[idx].clone(),nondet).unwrap();
                                let nne = self.backend.define(ne).unwrap();
                                nprogram_input[idx] = nne;
                                ndom.forget_var(idx);
                            }
                        }
                    } else if self.debugging>=2 {
                        match *nprog_inp[idx].0 {
                            expr::Expr::Var(ref old_idx)
                                if old_semantics[old_idx.0]==*m => {},
                            _ => {
                                debug!(self,2,"New PC: {} = {}",MeaningOf::new(&self.program,m),nprogram_input[idx]);
                            }
                        }
                    }
                }
            }
        }
        match act {
            None => {},
            Some(act_) => {
                let prev = &self.program_input;
                let nact = act_.translate(&mut |n,_| if n<prog_sz {
                    Ok(prev[n].clone())
                } else {
                    Ok(cinp[n-prog_sz].clone())
                },self.backend).unwrap();
                debug!(self,2,"Activation: {}",nact);
                self.path.push(nact);
            }
        }
        self.program_input = nprogram_input;
        self.domain = ndom;
        self.domain_full = ndomFull;
        true
    }
}

fn main() {
    #[cfg(feature="cpuprofiling")]
    PROFILER.lock().unwrap().start("./falco-enc.profile").unwrap();
    let opts = clap_app!(("falco-enc") =>
                         (version: "0.1")
                         (author: "Henning Günther <guenther@forsyte.at>")
                         (about: "Encodes a falco trace into an SMT instance")
                         (@arg fun_spec: -f --fun_spec <FILE> !required +takes_value "Use a tracing specification file")
                         (@arg entry: -e --entry <FUN> !required +takes_value "Use a function other than main as entry point")
                         (@arg debug: -d --debug !required +multiple "Add extra debugging information to the trace")
                         (@arg llvm_file: +required "The LLVM file")
                         (@arg trace: +required +multiple "The trace file")
    );

    let args = opts.get_matches();

    let llvm_file = args.value_of("llvm_file").unwrap();
    let m = parse_module(llvm_file).expect("Cannot parse llvm module");
    //println!("Module: {:#?}",m);
    let entry = args.value_of("entry").unwrap_or("main").to_string();
    let entry_fun = m.functions.get(&entry).expect("Cannot find entry function");
    let debugging = args.occurrences_of("debug");
    let fun_spec = match args.value_of("fun_spec") {
        None => HashMap::new(),
        Some(file) => fun_spec::read_funspecs(file)
    };
    let mut p = Pipe::new(io::empty(),io::stdout());
    let selectors = make_selectors(&m,&mut p).unwrap();
    for (nr,tr) in args.values_of("trace").unwrap().enumerate() {
        //let (_,reader) = falco::StepReader::new(&m,&fun_spec,File::open(tr).unwrap());
        //println!("Steps: {}",reader.count());
        p.comment(format!("Trace {}",nr).as_ref()).unwrap();
        let path = {
            let mut unw : TraceUnwinding<_,_,Val,AttributeDomain<Const>>
                = TraceUnwinding::new(File::open(tr).unwrap(),&selectors,&m,&fun_spec,&mut p,debugging).unwrap();
            while unw.step() {
            }
            unw.path
        };
        let path_cond = p.and(path).unwrap();
        let neg_path_cond = p.not(path_cond).unwrap();
        p.assert(neg_path_cond).unwrap();
    }
    #[cfg(feature="cpuprofiling")]
    PROFILER.lock().unwrap().stop().unwrap();
    /*let (prog,prog_dom) = {
        let prev = ();
        let mut uniq = Uniquer::new();
        let mut comp = Comp { referenced: &prev,
                              exprs: &mut uniq };
        let (ref_prog,init) = translate_init_(&m,&entry,vec![],Transformation::id(0),&mut comp).unwrap();
        let init_exprs = init.get_all(&[][..],&mut comp).unwrap();
        // FIXME: This should reference (), but that is not possible in Rust
        let dom_none : AttributeDomain<Const> = AttributeDomain::full(ref_prog.as_ref());
        let dom_init = <AttributeDomain<Const> as Domain<Program<Val>>>::derive(&dom_none,&init_exprs,&mut comp,
                                       &|_| { unreachable!() }).unwrap();
        (ref_prog.as_obj(),dom_init)
    };

    println!("Initial domain: {:#?}",prog_dom);
    
    let thread_id = (None,&entry);
    let cf_id = (None,&entry);
    let start = InstructionRef::entry(entry_fun);
    let (nprog,ninp,exprs,ndom) = step(&m,&prog,&prog_dom,thread_id,cf_id,start);
    println!("Program: {:#?}",nprog);
    for (n,e) in exprs.iter().enumerate() {
        println!("Expr {}: {}",n,e);
    }
    println!("Domain: {:#?}",ndom);
    for v in nprog.data_vars() {
        println!("Data var: {}",v)
    }*/
}