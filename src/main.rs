#[macro_use]
extern crate clap;
extern crate llvm_ir;
extern crate symbolic_llvm;
extern crate smtrs;
extern crate serde;
extern crate serde_json;
#[macro_use]
extern crate serde_derive;
extern crate num_bigint;
extern crate nom;
#[cfg(feature="cpuprofiling")]
extern crate cpuprofiler;
extern crate petgraph;

mod fun_spec;
mod falco;
mod graph;

use llvm_ir::{Module,Instruction,parse_module};
use symbolic_llvm::symbolic::llvm::*;
use symbolic_llvm::symbolic::llvm::program::*;
use symbolic_llvm::symbolic::llvm::pointer::{Pointer,PointerTrg,BasePointer};
use symbolic_llvm::symbolic::llvm::mem::*;
use symbolic_llvm::symbolic::llvm::thread::CallId;
use symbolic_llvm::symbolic::llvm::library::{Library,StdLib};
use llvm_ir::datalayout::DataLayout;
use smtrs::types::Value;
use smtrs::composite::*;
use smtrs::composite::expr::*;
use smtrs::composite::vec::*;
use smtrs::composite::map::*;
use smtrs::composite::choice::*;
use smtrs::composite::singleton::*;
use smtrs::embed::{Embed,DeriveConst,DeriveValues};
use smtrs::backend::{Backend,Pipe};
use smtrs::domain::*;
use smtrs::expr as expr;
use smtrs::types as types;
use smtrs::simplify::Simplify;
use std::fmt::{Debug,Display};
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use std::fs::File;
use std::io;
use num_bigint::BigUint;
use std::mem::{swap,replace};
#[cfg(feature="cpuprofiling")]
use cpuprofiler::PROFILER;
use graph::{GraphBuilder,FalcoGraph,MultiCallKind,debug_graph};
use petgraph::Direction;
use petgraph::graph::{Graph,NodeIndex};
use petgraph::algo::toposort;
use std::vec::IntoIter;

type Val<'a> = CompValue<ByteWidth<BasePointer<'a>>,BitVecValue>;

struct CompProgram<'a,'b: 'a,V: 'b+Bytes<'b>+FromConst<'b>,
                   DomProg: 'a+Domain<Program<'b,V>>,
                   DomInp: 'a+Domain<ProgramInput<'b,V>>> {
    prog: &'a Program<'b,V>,
    selectors: usize,
    inp: &'a ProgramInput<'b,V>,
    dom_prog: &'a DomProg,
    dom_inp: &'a DomInp,
}

impl<'a,'b,V,DomProg,DomInp> CompProgram<'a,'b,V,DomProg,DomInp>
where V: Bytes<'b>+FromConst<'b>+Debug,
      DomProg: 'a+Domain<Program<'b,V>>,
      DomInp: 'a+Domain<ProgramInput<'b,V>> {
    pub fn selector(&mut self,nr: usize) -> Result<CompExpr<(Program<'b,V>,ProgramInput<'b,V>)>,()> {
        let prog_sz = self.prog.num_elem();
        self.var(CompVar(prog_sz+nr))
    }
}

impl<'a,'b,V,DomProg,DomInp> Embed for CompProgram<'a,'b,V,DomProg,DomInp>
    where V: Bytes<'b>+FromConst<'b>+Debug,
          DomProg: 'a+Domain<Program<'b,V>>,
          DomInp: 'a+Domain<ProgramInput<'b,V>> {
    
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
        } else if var.0 < prog_sz + self.selectors {
            self.tp_bool()
        } else {
            self.inp.elem_sort(var.0-prog_sz-self.selectors,self)
        }
    }
    fn type_of_fun(&mut self,_:&Self::Fun) -> Result<Self::Sort,Self::Error> {
        unreachable!()
    }
    fn arity(&mut self,_:&Self::Fun) -> Result<usize,Self::Error> {
        unreachable!()
    }
    fn type_of_arg(&mut self,_:&Self::Fun,_:usize) -> Result<Self::Sort,Self::Error> {
        unreachable!()
    }
}

impl<'a,'b,V,DomProg,DomInp> DeriveConst for CompProgram<'a,'b,V,DomProg,DomInp>
    where V: Bytes<'b>+FromConst<'b>+Debug,
          DomProg: 'a+Domain<Program<'b,V>>,
          DomInp: 'a+Domain<ProgramInput<'b,V>> {
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
        let nsels = self.selectors;
        self.dom_inp.is_const(e,self,&|v| if v.0 >= prog_sz+nsels {
            Some(v.0-prog_sz-nsels)
        } else {
            None
        })
    }
}

impl<'a,'b,V,DomProg,DomInp> DeriveValues for CompProgram<'a,'b,V,DomProg,DomInp>
    where V: Bytes<'b>+FromConst<'b>+Debug,
          DomProg: 'a+Domain<Program<'b,V>>,
          DomInp: 'a+Domain<ProgramInput<'b,V>> {
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
        let nsels = self.selectors;
        let vals_inp = self.dom_inp.values(e,self,&|v| if v.0>=prog_sz+nsels {
            Some(v.0-prog_sz-nsels)
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

struct FalcoCfg<Em: Embed> {
    paths: Option<Vec<Em::Expr>>,
    current_path: Vec<Em::Expr>,
    extra_sel: Vec<Em::Expr>
}

impl<Em: Embed> FalcoCfg<Em> {
    pub fn new() -> Self {
        FalcoCfg { paths: Some(Vec::new()),
                   current_path: Vec::new(),
                   extra_sel: Vec::new() }
    }
    pub fn condition(self,em: &mut Em)
                     -> Result<(Option<Em::Expr>,Vec<Em::Expr>),Em::Error> {
        let cond = match self.paths {
            None => None,
            Some(mut paths) => match paths.len() {
                0 => Some(em.const_bool(false)?),
                1 => Some(paths.remove(0)),
                _ => Some(em.or(paths)?)
            }
        };
        Ok((cond,self.extra_sel))
    }
}

impl<Em: Embed> TranslationCfg<Em> for FalcoCfg<Em> {
    fn change_thread_activation(
        &mut self,
        conds:&mut Vec<Em::Expr>,pos:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        self.current_path.extend(conds.drain(pos..));
        Ok(())
    }
    fn change_context_activation(
        &mut self,
        conds:&mut Vec<Em::Expr>,pos:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        self.current_path.extend(conds.drain(pos..));
        Ok(())
    }
    fn change_call_frame_activation(
        &mut self,
        conds:&mut Vec<Em::Expr>,pos:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        self.current_path.extend(conds.drain(pos..));
        Ok(())
    }
    fn change_instr_activation(
        &mut self,
        conds:&mut Vec<Em::Expr>,pos:usize,em:&mut Em)
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
                    paths.push(em.and(path)?)
                }
            }
        }
        Ok(())
    }
    fn change_instr_not_blocking(
        &mut self,
        conds:&mut Vec<Em::Expr>,pos:usize,_:&mut Em)
        -> Result<(),Em::Error> {
        self.extra_sel.extend(conds.drain(pos..));
        Ok(())
    }
}

fn step<'a,Lib,V,Dom>(m: &'a Module,
                      lib: &Lib,
                      st: &mut Program<'a,V>,
                      selectors: usize,
                      domain_use: &Dom,
                      domain_derive1: &Dom,
                      domain_derive2: &Dom,
                      thread_id: ThreadId<'a>,
                      cf_id: CallId<'a>,
                      instr_id: InstructionRef<'a>)
                      -> (ProgramInput<'a,V>,
                          Vec<CompExpr<(Program<'a,V>,ProgramInput<'a,V>)>>,
                          Option<CompExpr<(Program<'a,V>,ProgramInput<'a,V>)>>,
                          Dom,
                          Dom,
                          Vec<CompExpr<(Program<'a,V>,ProgramInput<'a,V>)>>)
    where V: 'a+Bytes<'a>+FromConst<'a>+Pointer<'a>+IntValue<'a>+Vector<'a>+Semantic+FromMD<'a>+Debug,
          Dom: Domain<Program<'a,V>>,
          Lib: for<'b> Library<'a,V,CompProgram<'b,'a,V,Dom,()>> {

    let instr = instr_id.resolve(m);
    let prog_size = st.num_elem();

    let mut inp = ProgramInput::new_sig();
    let inp_size = inp.num_elem();
    let dom_inp = ();
    let mut exprs = Vec::with_capacity(prog_size);
    let mut exprs_inp = Vec::with_capacity(inp.num_elem());
    {
        let mut comp = CompProgram { prog: st,
                                     selectors: selectors,
                                     inp: &inp,
                                     dom_prog: domain_use,
                                     dom_inp: &dom_inp };
        for i in 0..prog_size+selectors {
            exprs.push(comp.var(CompVar(i)).unwrap());
        }
        for i in prog_size+selectors..prog_size+selectors+inp_size {
            exprs_inp.push(comp.var(CompVar(i)).unwrap());
        }
    }
    let old_prog = st.clone();
    loop {

        let ninp = {
            let mut comp = CompProgram { prog: &old_prog,
                                         selectors: selectors,
                                         inp: &inp,
                                         dom_prog: domain_use,
                                         dom_inp: &dom_inp };
            let inp_size = inp.num_elem();
            
            if inp_size>exprs_inp.len() {
                for i in exprs.len()+exprs_inp.len()..exprs.len()+inp_size {
                    exprs_inp.push(comp.var(CompVar(i)).unwrap());
                }
            }
            let mut cfg = FalcoCfg::new();
            match translate_instr(&m,
                                  &mut cfg,
                                  lib,
                                  thread_id,
                                  cf_id,
                                  instr_id,
                                  instr,
                                  st,
                                  &inp,
                                  &mut exprs,&exprs_inp[..],
                                  &mut comp) {
                Ok(()) => {
                    debug_assert_eq!(st.num_elem(),exprs.len());
                    //println!("TR: {:#?}",trans);
                    if cfg!(debug_assertions) {
                        for (i,e) in exprs.iter().enumerate() {
                            let expected = st.elem_sort(i,&mut comp).unwrap();
                            let got = comp.type_of(e).unwrap();
                            if expected!=got {
                                println!("Warning: At expression {}({:?}), expected: {}, got: {} ({})",
                                         i,st.meaning(i),expected,got,e);
                            }
                        }
                    }
                    let (ndom1,ndom2) = {
                        let d1 = domain_derive1.derive(&exprs[..],&mut comp,
                                                       &|v| if v.0 < prog_size {
                                                           Some(v.0)
                                                       } else {
                                                           None
                                                       }).unwrap();
                        let d2 = domain_derive2.derive(&exprs[..],&mut comp,
                                                       &|v| if v.0 < prog_size {
                                                           Some(v.0)
                                                       } else {
                                                           None
                                                       }).unwrap();
                        (d1,d2)
                    };
                    if cfg!(debug_assertions) {
                        for i in 0..exprs.len() {
                            match ndom2.is_const(&comp.var(CompVar(i)).unwrap(),&mut comp,
                                                 &|v| Some(v.0)).unwrap() {
                                None => panic!("Expression {} ({:?}) is not const in full domain",i,exprs[i]),
                                Some(_) => {}
                            }
                        }
                    }
                    let (cond,extra) = cfg.condition(&mut comp).unwrap();
                    return (inp.clone(),exprs,cond,ndom1,ndom2,extra)
                },
                Err(TrErr::InputNeeded(ninp)) => ninp,
                _ => panic!("AAA")
            }
        };
        inp = ninp;
    }
}

type Selectors<Em: Embed> = HashMap<(u64,u64),Em::Var>;

fn get_dbg_loc(instr: &Instruction,m: &Module) -> Option<(u64,u64)> {
    match instr.metadata.get("dbg") {
        None => None,
        Some(n) => match m.md.get(n) {
            Some(&llvm_ir::Metadata::Location(ln,col,_)) => Some((ln,col)),
            _ => None
        }
    }
}

fn make_selectors<B: Backend>(m: &Module,b: &mut B)
                              -> Result<Selectors<B>,B::Error> {
    let mut selectors = HashMap::new();
    for fun in m.functions.values() {
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
                                let v = b.declare_var(tp,Some(format!("sel.{}.{}",loc.0,loc.1)))?;
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

struct TraceUnwinding<'a,R: io::Read,Em: Embed,V: Semantic+Bytes<'a>+FromConst<'a>,Dom>
    where Em: 'a,Em::Var: 'a {
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

/// A translated graph node
#[derive(Clone)]
struct TNode<'a,V: Bytes<'a>+FromConst<'a>+Semantic,Em: Embed,Dom> {
    prog: Program<'a,V>,
    prog_inp: Vec<Em::Expr>,
    domain: Dom,
    domain_full: Dom,
    path_cond: Vec<Em::Expr>
}

#[derive(Clone)]
enum TStatus<'a,V: Bytes<'a>+FromConst<'a>+Semantic,Em : Embed,Dom> {
    Untranslated,
    Translated(Box<TNode<'a,V,Em,Dom>>),
    Finished
}

struct GraphUnwinding<'a,Em: 'a+Embed,V: Semantic+Bytes<'a>+FromConst<'a>,Dom>
    where Em::Var: 'a {
    module: &'a Module,
    backend: &'a mut Em,
    selectors: &'a Selectors<Em>,
    graph: FalcoGraph<'a>,
    queue: IntoIter<NodeIndex>,
    translation: Vec<TStatus<'a,V,Em,Dom>>,
    trace_selector: Vec<Em::Var>,
    trace_args: Vec<Vec<Vec<u8>>>,
    debugging: u64
}

struct FalcoLib<'a: 'b,'b> {
    ext: &'b falco::External<'a>
}

impl<'a,'b,V: 'a+Bytes<'a>+FromConst<'a>+IntValue<'a>,Em: DeriveValues> Library<'a,V,Em> for FalcoLib<'a,'b> {
    fn call<FromArg,Arg: Path<'a,Em,FromArg,To=CompVec<V>>,
            Ret: Path<'a,Em,Program<'a,V>,To=Assoc<&'a String,V>>
            >(&self,
              fname: &'a String,
              args: &Arg,
              args_from: &FromArg,
              args_inp: &[Em::Expr],
              ret: Option<(Ret,&'a String)>,
              _: &'a DataLayout,
              _: InstructionRef<'a>,
              prog: &mut Program<'a,V>,
              prog_inp: &mut Vec<Em::Expr>,
              conds: &mut Vec<Em::Expr>,
              em: &mut Em)
              -> Result<bool,Em::Error> {
        if *fname!=*self.ext.function {
            return Ok(false)
        }
        for (ext,arg) in self.ext.args.iter().zip(
            CompVec::elements(args.clone(),args_from)
        ) {
            match ext {
                &None => {},
                &Some(falco::Val::Int { bw, ref val }) => {
                    let mut eval_inp = Vec::new();
                    let eval = V::const_int(bw,val.clone(),&mut eval_inp,em)?;
                    let eq = comp_eq(&Id,&eval,&eval_inp[..],
                                     &arg,args_from,args_inp,em)?.unwrap();
                    conds.push(eq);
                },
                _ => {}
            }
        }
        //assert!(self.ext.args.iter().all(Option::is_none));
        match self.ext.ret {
            None => {}
            Some(ref rval) => match rval {
                &falco::Val::Int { bw,ref val } => {
                    let mut i_inp = Vec::new();
                    let i = V::const_int(bw,val.clone(),&mut i_inp,em)?;
                    match ret {
                        None => panic!("Trace has a return value but the function doesn't."),
                        Some((ref ret_,name)) => {
                            if conds.len()==0 {
                                Assoc::insert(ret_,prog,prog_inp,
                                              name,i,&mut i_inp,em)?;
                            } else {
                                let rcond = em.and(conds.clone())?;
                                Assoc::insert_cond(ret_.clone(),
                                                   prog,prog_inp,
                                                   name,i,&mut i_inp,
                                                   &rcond,em)?;
                            }
                        }
                    }
                },
                _ => unimplemented!()
            }
        }
        Ok(true)
    }
}

struct FalcoMultiLib<'a: 'b,'b> {
    exts: &'b Vec<(usize,falco::External<'a>)>,
    sel_offset: usize
}

impl<'a,'b,V: 'a+Bytes<'a>+FromConst<'a>+IntValue<'a>,Em> Library<'a,V,Em> for FalcoMultiLib<'a,'b>
    where Em : DeriveValues<Var=CompVar> {
    fn call<FromArg,Arg: Path<'a,Em,FromArg,To=CompVec<V>>,
            Ret: Path<'a,Em,Program<'a,V>,To=Assoc<&'a String,V>>
            >(&self,
              fname: &'a String,
              args: &Arg,
              args_from: &FromArg,
              args_arr: &[Em::Expr],
              ret: Option<(Ret,&'a String)>,
              _: &'a DataLayout,
              _: InstructionRef<'a>,
              prog: &mut Program<'a,V>,
              prog_arr: &mut Vec<Em::Expr>,
              conds: &mut Vec<Em::Expr>,
              em: &mut Em)
              -> Result<bool,Em::Error> {
        let mut act_conds = Vec::new();
        let cpos = conds.len();
        for &(tr_nr,ref ext) in self.exts.iter() {
            let sel_e = em.embed(expr::Expr::Var(CompVar(self.sel_offset+tr_nr)))?;
            conds.push(sel_e.clone());
            if *fname!=*ext.function {
                panic!("External function doesn't match code")
            }
            let mut eq_conds = vec![sel_e];
            for (ext_arg,arg) in ext.args.iter().zip(
                CompVec::elements(args.clone(),args_from)
            ) {
                match ext_arg {
                    &None => {},
                    &Some(falco::Val::Int { bw, ref val }) => {
                        let mut eval_inp = Vec::new();
                        let eval = V::const_int(bw,val.clone(),&mut eval_inp,em)?;
                        let eq = comp_eq(&Id,&eval,&eval_inp[..],
                                         &arg,args_from,args_arr,em)?.unwrap();
                        eq_conds.push(eq);
                    },
                    _ => {}
                }
            }
            let eq_cond = em.and(eq_conds)?;
            act_conds.push(eq_cond);
            //assert!(self.ext.args.iter().all(Option::is_none));
            match ext.ret {
                None => {}
                Some(ref rval) => match rval {
                    &falco::Val::Int { bw,ref val } => {
                        let mut i_inp = Vec::new();
                        let i = V::const_int(bw,val.clone(),&mut i_inp,em)?;
                        match ret {
                            None => panic!("Trace has a return value but the function doesn't..."),
                            Some((ref ret_,name)) => {
                                if conds.len()==0 {
                                    Assoc::insert(ret_,prog,prog_arr,
                                                  name,i,&mut i_inp,em)?;
                                } else {
                                    let rcond = em.and(conds.clone())?;
                                    Assoc::insert_cond(ret_.clone(),
                                                       prog,prog_arr,
                                                       name,i,&mut i_inp,
                                                       &rcond,em)?;
                                }
                            }
                        }
                    },
                    _ => unimplemented!()
                }
            }
            conds.truncate(cpos);
        }
        let act_cond = em.or(act_conds)?;
        conds.push(act_cond);
        Ok(true)
    }
}


/// Decide if the full domain information should be used when encoding
/// the instruction.
fn use_full_domain(instr: &llvm_ir::Instruction) -> bool {
    match instr.content {
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
    }
}


impl<'a,R: io::Read,Em: Backend,V,Dom: Domain<Program<'a,V>>+Clone> TraceUnwinding<'a,R,Em,V,Dom>
    where V: 'a+Bytes<'a>+FromConst<'a>+Pointer<'a>+IntValue<'a>+Vector<'a>+FromMD<'a>+Debug+Semantic,
          Em::Expr: Display {
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
        let fun = step0.id.fun;
        let argc_bw = match m.functions.get(fun) {
            None => panic!("Function {} not found in module",fun),
            Some(rfun) => if rfun.arguments.len()==2 {
                let argc_tp = &rfun.arguments[0].1;
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

        let mut prog_inp = Vec::new();
        let args_len = args.len();
        let prog = translate_init(
            m,fun,
            |res,em| CompVec::construct(
                0..1,
                |n,res,em| {
                    match n {
                        0 => V::const_int(argc_bw,BigUint::from(args_len),res,em),
                        1 => {
                            let mut argv_inp = Vec::new();
                            let argv = Choice::singleton(
                                |res,em| Ok((PointerTrg::AuxArray,(Data((0,(ptr_bw/8) as usize)),None))),
                                &mut argv_inp,em)?;
                            V::from_pointer((ptr_bw/8) as usize,&Id,&argv,&argv_inp[..],res,em)
                        },
                        _ => unreachable!()
                    }
                },res,em),
            |res,em| Choice::singleton(
                |_,_| Ok(Data(args)),
                res,em),
            &mut prog_inp,b)?;
        // FIXME: This should reference (), but that is not possible in Rust
        let dom_none : Dom = Dom::full(&prog);
        let dom_init = <Dom as Domain<Program<V>>>::derive(&dom_none,&prog_inp[..],b,
                                                           &|_| { unreachable!() })?;
        let mut meaning = Vec::with_capacity(prog_inp.len());
        for m in Semantics::new(&prog) {
            meaning.push(m);
        }
        //println!("Program: {:#?}",prog.as_ref());
        Ok(TraceUnwinding { reader: reader,
                            step_buffer: Some(step0),
                            selectors: sel,
                            backend: b,
                            module: m,
                            main: fun,
                            program: prog,
                            program_input: prog_inp,
                            program_meaning: meaning,
                            domain: dom_init.clone(),
                            domain_full: dom_init,
                            path: Vec::new(),
                            debugging: debug })
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
        debug!(self,4,"Step: {:#?}",entr);
        let thr_id = (None,self.main);
        let fun = self.module.functions.get(entr.id.fun)
            .expect("Function not found");
        let (instr,instr_ref) = match fun.body {
            None => panic!("Function has no body"),
            Some(ref blks) => {
                let blk = &blks[entr.id.blk];
                (&blk.instrs[entr.id.instr],
                 InstructionRef { function: &fun.name,
                                  basic_block: &blk.name,
                                  instruction: entr.id.instr })
            }
        };
        debug!(self,1,"Instruction {}.{}.{}",
               instr_ref.function,
               instr_ref.basic_block,
               instr_ref.instruction);
        debug!(self,3,"Content: {:?}",instr);
        let use_full = use_full_domain(instr);
        let mut nprog = self.program.clone();
        let (ninp,nprog_inp,act,mut ndom,ndom_full,extra_sel)
            = match entr.ext {
                falco::CallKind::Internal => {
                    let lib = StdLib {};
                    step(self.module,&lib,&mut nprog,0,
                         if use_full {
                             &self.domain_full
                         } else {
                             &self.domain
                         },
                         &self.domain,
                         &self.domain_full,
                         thr_id,entr.id.call_id,instr_ref)
                },
                falco::CallKind::External(ref ext) => if ext.function=="realloc" || ext.function=="malloc" {
                    let lib = StdLib {};
                    step(self.module,&lib,&mut nprog,0,
                         if use_full {
                             &self.domain_full
                         } else {
                             &self.domain
                         },
                         &self.domain,
                         &self.domain_full,
                         thr_id,entr.id.call_id,instr_ref)
                } else {
                    let lib = FalcoLib { ext: ext };
                    step(self.module,&lib,&mut nprog,0,
                         if use_full {
                             &self.domain_full
                         } else {
                             &self.domain
                         },
                         &self.domain,
                         &self.domain_full,
                         thr_id,entr.id.call_id,instr_ref)
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
                let sel_exprs = if extra_sel.len()==0 {
                    sel_expr
                } else {
                    let mut sels = Vec::with_capacity(extra_sel.len()+1);
                    sels.push(sel_expr);
                    let prev = &self.program_input;
                    for extr in extra_sel.iter() {
                        let ne = extr.translate(&mut |n,_| if n<prog_sz {
                            Ok(prev[n].clone())
                        } else {
                            Ok(cinp[n-prog_sz].clone())
                        },self.backend).unwrap();
                        sels.push(ne);
                    }
                    self.backend.and(sels).unwrap()
                };
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
                                let ne = self.backend.ite(sel_exprs.clone(),nprogram_input[idx].clone(),nondet).unwrap();
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
        self.domain_full = ndom_full;
        true
    }
}

impl<'a,Em: 'a+Backend,V,Dom> GraphUnwinding<'a,Em,V,Dom>
    where V: 'a+Semantic+Bytes<'a>+FromConst<'a>+IntValue<'a>+Pointer<'a>+FromMD<'a>+Vector<'a>+Debug,
          Dom: Domain<Program<'a,V>>+Clone,
          Em::Expr: Display {
    pub fn new(m: &'a Module,
               b: &'a mut Em,
               selectors: &'a Selectors<Em>,
               gr: FalcoGraph<'a>,
               args: Vec<Vec<Vec<u8>>>,
               debugging: u64) -> Result<Self,Em::Error> {
        let qs = match toposort(&gr,None) {
            Ok(r) => r,
            Err(_) => panic!("Unwinding graph contains cycles")
        };
        let sz = gr.node_count();
        let mut sels = Vec::with_capacity(args.len());
        let tp_bool = b.tp_bool()?;
        for n in 0..args.len() {
            let sel = b.declare_var(tp_bool.clone(),Some(format!("tr{}",n)))?;
            sels.push(sel);
        }
        let mut transl = Vec::with_capacity(sz);
        for _ in 0..sz {
            transl.push(TStatus::Untranslated)
        }
        Ok(GraphUnwinding {
            module: m,
            backend: b,
            selectors: selectors,
            graph: gr,
            queue: qs.into_iter(),
            translation: transl,
            trace_selector: sels,
            trace_args: args,
            debugging: debugging
        })
    }
    pub fn step(&mut self) -> Result<bool,Em::Error> {
        let nxt_nd_id = match self.queue.next() {
            None => return Ok(false),
            Some(n) => n
        };
        let nxt_nd = self.graph.node_weight(nxt_nd_id).unwrap();
        let starts = nxt_nd.start.len();
        let (prog,prog_inp,dom,dom_full,mut path_cond) = if starts>0 {
            let fun = nxt_nd.id.fun;
            let argc_bw = match self.module.functions.get(fun) {
                None => panic!("Function {} not found in module",fun),
                Some(rfun) => if rfun.arguments.len()==2 {
                    let argc_tp = &rfun.arguments[0].1;
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
            let mut argc: Option<(V,Vec<Em::Expr>)> = None;
            let mut aux_inp = Vec::new();
            let mut aux = Choice::empty(&mut aux_inp,self.backend)?;
            
            let (ptr_bw,_,_) = self.module.datalayout.pointer_alignment(0);

            /*let (argv0,argv0_inp) = choice_empty();
            let (argv1,argv1_inp) = choice_insert(OptRef::Owned(argv0),argv0_inp,
                                                  Transformation::const_bool(true,self.backend)?,
                                                  OptRef::Owned((PointerTrg::AuxArray,
                                                                 (Data((0,(ptr_bw/8) as usize)),None))),
                                                  Transformation::id(0))?;
            let (argv,argv_inp) = V::from_pointer((ptr_bw/8) as usize,argv1,argv1_inp);*/
            let mut inp = Vec::with_capacity(starts);

            for (n,start) in nxt_nd.start.iter().enumerate() {
                let sel_var = self.trace_selector[*start].clone();
                let cond = self.backend.var(sel_var)?;
                let arg = &self.trace_args[*start];
                let nargc = {
                    let mut cargc_inp = Vec::new();
                    let cargc = V::const_int(argc_bw,BigUint::from(arg.len()),
                                             &mut cargc_inp,self.backend)?;
                    match argc {
                        None => (cargc,cargc_inp),
                        Some((oargc,oargc_inp)) => {
                            let mut nargc_inp = Vec::new();
                            let nargc = ite(&cond,
                                            &Id,&cargc,&cargc_inp[..],
                                            &Id,&oargc,&oargc_inp[..],
                                            &mut nargc_inp,
                                            self.backend)?.unwrap();
                            (nargc,nargc_inp)
                        }
                    }
                };
                Choice::insert(&Id,&mut aux,&mut aux_inp,
                               Data(arg.clone()),&mut Vec::new(),
                               cond.clone(),self.backend)?;
                argc = Some(nargc);
                
                inp.push(cond);
            }
            let (argc_,argc_inp) = argc.unwrap();

            let mut prog_inp = Vec::new();
            let prog = translate_init(
                self.module,fun,
                |res,em| CompVec::construct(
                    0..1,
                    |n,res,em| match n {
                        0 => {
                            res.extend_from_slice(&argc_inp[..]);
                            Ok(argc_.clone())
                        },
                        1 => {
                            let mut argv_inp = Vec::new();
                            let argv = Choice::singleton(
                                |res,em| Ok((PointerTrg::AuxArray,
                                             (Data((0,(ptr_bw/8) as usize)),None))),
                                &mut argv_inp,em)?;
                            V::from_pointer((ptr_bw/8) as usize,
                                            &Id,&argv,&argv_inp[..],res,em)
                        },
                        _ => unreachable!()
                    },res,em),
                |res,em| {
                    res.append(&mut aux_inp);
                    Ok(aux)
                },
                &mut prog_inp,self.backend)?;
                    
            let dom_none: Dom = Dom::full(&prog);
            let dom_init = <Dom as Domain<Program<V>>>::derive(
                &dom_none,&prog_inp[..],self.backend,
                &|_| { None }
            )?;
            let mut path_sels = Vec::with_capacity(starts);
            for start in nxt_nd.start.iter() {
                path_sels.push(self.backend.embed(expr::Expr::Var(self.trace_selector[*start].clone()))?);
            }
            let path_cond = vec![self.backend.or(path_sels)?];
            (prog,prog_inp,dom_init.clone(),dom_init,path_cond)
        } else {
            let mut incoming = self.graph.neighbors_directed(nxt_nd_id,
                                                             Direction::Incoming);
            // If it is not a starting node, it must have at least one
            // predecessor:
            let first_id = incoming.next().unwrap();
            let first : &TNode<_,_,_> = match self.translation[first_id.index()] {
                TStatus::Translated(ref nd) => &**nd,
                TStatus::Untranslated => panic!("Incoming node is untranslated"),
                TStatus::Finished => panic!("Incoming node is finished")
            };
            let mut prog = first.prog.clone();
            let mut prog_inp = first.prog_inp.clone();
            let mut dom = first.domain.clone();
            let mut dom_full = first.domain_full.clone();
            let mut path_cond = first.path_cond.clone();
            let mut one_inc = true;
            for inc_id in incoming {
                if one_inc {
                    one_inc = false;
                    let ncond = self.backend.and(path_cond)?;
                    path_cond = vec![ncond];
                }
                let inc : &TNode<_,_,_> = match self.translation[inc_id.index()] {
                    TStatus::Translated(ref nd) => &**nd,
                    TStatus::Untranslated => panic!("Incoming node is untranslated"),
                    TStatus::Finished => panic!("Incoming node is finished")
                };
                let (nprog,nprog_inp,ndom,ndom_full,cond) = merge_edge(&prog,&prog_inp[..],&dom,&dom_full,inc,self.backend)?;
                prog = nprog;
                prog_inp = nprog_inp;
                dom = ndom;
                dom_full = ndom_full;
                path_cond.push(cond);
            }
            let rpath_cond = if one_inc {
                path_cond
            } else {
                let ncond = self.backend.or(path_cond)?;
                let ncond_def = self.backend.define(ncond)?;
                vec![ncond_def]
            };
            (prog,prog_inp,dom,dom_full,rpath_cond)
        };
        let fun = self.module.functions.get(nxt_nd.id.fun)
            .expect("Function not found");
        let (instr,instr_ref) = match fun.body {
            None => panic!("Function has no body"),
            Some(ref blks) => {
                let blk = &blks[nxt_nd.id.blk];
                (&blk.instrs[nxt_nd.id.instr],
                 InstructionRef { function: &fun.name,
                                  basic_block: &blk.name,
                                  instruction: nxt_nd.id.instr })
            }
        };
        debug!(self,1,"Instruction {}.{}.{}",
               instr_ref.function,
               instr_ref.basic_block,
               instr_ref.instruction);
        debug!(self,3,"Content: {:?}",instr);
        let use_full = use_full_domain(instr);
        let mut nprog = prog.clone();
        let (ninp,nprog_inp,act,mut ndom,ndom_full,extra_sel) = match nxt_nd.ext {
            MultiCallKind::Internal => {
                let lib = StdLib {};
                step(self.module,&lib,&mut nprog,self.trace_selector.len(),
                     if use_full {
                         &dom_full
                     } else {
                         &dom
                     },
                     &dom,
                     &dom_full,
                     nxt_nd.id.thread_id,nxt_nd.id.call_id,instr_ref)
            },
            MultiCallKind::External(ref exts) => {
                let lib = FalcoMultiLib {
                    exts: exts,
                    sel_offset: prog_inp.len()
                };
                step(self.module,&lib,&mut nprog,self.trace_selector.len(),
                     if use_full {
                         &dom_full
                     } else {
                         &dom
                     },
                     &dom,
                     &dom_full,
                     nxt_nd.id.thread_id,nxt_nd.id.call_id,instr_ref)
            }
        };
        let num_inp = ninp.num_elem();

        let mut cinp = Vec::with_capacity(num_inp);
        for i in 0..num_inp {
            let tp = ninp.elem_sort(i,self.backend).unwrap();
            let var = self.backend.declare(tp).unwrap();
            cinp.push(var);
        }
        let prog_sz = prog.num_elem();
        let nprog_sz = nprog.num_elem();
        // Number of traces
        let nr_trs = self.trace_selector.len();
        let tr_sels = &self.trace_selector;
        let mut nprogram_input = Vec::with_capacity(nprog_inp.len());
        for e in nprog_inp.iter() {
            let ne = e.translate(&mut |n,em:&mut Em| if n<prog_sz {
                Ok(prog_inp[n].clone())
            } else if n<prog_sz+nr_trs {
                em.embed(expr::Expr::Var(tr_sels[n-prog_sz].clone()))
            } else {
                Ok(cinp[n-prog_sz-nr_trs].clone())
            },self.backend).unwrap();
            nprogram_input.push(ne);
        }
        if let Some(l) = get_dbg_loc(instr,self.module) {
            let sel = self.selectors.get(&l).expect("Selector not found");
            let sel_expr = self.backend.embed(expr::Expr::Var(sel.clone())).unwrap();
            let sel_exprs = if extra_sel.len()==0 {
                sel_expr
            } else {
                let mut sels = Vec::with_capacity(extra_sel.len()+1);
                sels.push(sel_expr);
                for extr in extra_sel.iter() {
                    let ne = extr.translate(&mut |n,em:&mut Em| if n<prog_sz {
                        Ok(prog_inp[n].clone())
                    } else if n<prog_sz+nr_trs {
                        em.embed(expr::Expr::Var(tr_sels[n-prog_sz].clone()))
                    } else {
                        Ok(cinp[n-prog_sz-nr_trs].clone())
                    },self.backend).unwrap();
                    sels.push(ne);
                }
                self.backend.and(sels).unwrap()
            };
            let old_semantics = {
                let mut sem = Vec::with_capacity(prog_sz);
                match prog.first_meaning() {
                    None => {},
                    Some((mut ctx,mut m)) => {
                        sem.push(m.clone());
                        while prog.next_meaning(&mut ctx,&mut m) {
                            sem.push(m.clone());
                        }
                    }
                }
                sem
            };
            let new_semantics = {
                let mut sem = Vec::with_capacity(nprog_sz);
                match nprog.first_meaning() {
                    None => {},
                    Some((mut ctx,mut m)) => {
                        sem.push(m.clone());
                        while nprog.next_meaning(&mut ctx,&mut m) {
                            sem.push(m.clone());
                        }
                    }
                }
                sem
            };
            for (idx,m) in new_semantics.iter().enumerate() {
                // Is this a data variable?
                if !m.is_pc() {
                    // Has the data variable changed?
                    match *nprog_inp[idx].0 {
                        expr::Expr::Var(ref old_idx)
                            if old_semantics[old_idx.0]==*m => {},
                        _ => {
                            debug!(self,2,"Meaning: {}",MeaningOf::new(&nprog,m));
                            // Variable has changed
                            let tp = nprog.elem_sort(idx,self.backend).unwrap();
                            let nondet = self.backend.declare(tp).unwrap();
                            let ne = self.backend.ite(sel_exprs.clone(),nprogram_input[idx].clone(),nondet).unwrap();
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
                            debug!(self,2,"New PC: {} = {}",MeaningOf::new(&nprog,m),nprogram_input[idx]);
                        }
                    }
                }
            }
        }
        match act {
            None => {},
            Some(act_) => {
                let nact = act_.translate(&mut |n,em:&mut Em| if n<prog_sz {
                    Ok(prog_inp[n].clone())
                } else if n<prog_sz+nr_trs {
                    em.embed(expr::Expr::Var(tr_sels[n-prog_sz].clone()))
                } else {
                    Ok(cinp[n-prog_sz-nr_trs].clone())
                },self.backend).unwrap();
                debug!(self,2,"Activation: {}",nact);
                path_cond.push(nact);
            }
        }
        if nxt_nd.end.len() > 0 {
            let path = self.backend.and(path_cond.clone())?;
            let cond = self.backend.not(path)?;
            self.backend.assert(cond)?;
        }
        self.translation[nxt_nd_id.index()] = TStatus::Translated(
            Box::new(TNode { prog: nprog,
                             prog_inp: nprogram_input,
                             domain: ndom,
                             domain_full: ndom_full,
                             path_cond: path_cond }));
        Ok(true)
    }
    pub fn declare_traces(&mut self) -> Result<(),Em::Error> {
        for i in 0..self.trace_selector.len() {
            self.backend.comment(&format!("Trace {}",i))?;
            for (j,v) in self.trace_selector.iter().enumerate() {
                let e = self.backend.embed(expr::Expr::Var(v.clone()))?;
                let ne = if i==j { e } else { self.backend.not(e)? };
                self.backend.assert(ne)?;
            }
        }
        Ok(())
    }
}

fn merge_edge<'a,V,Em,Dom>(
    prog: &Program<'a,V>,
    prog_inp: &[Em::Expr],
    dom: &Dom,
    dom_full: &Dom,
    inc: &TNode<'a,V,Em,Dom>,
    em: &mut Em
) -> Result<(Program<'a,V>,
             Vec<Em::Expr>,
             Dom,
             Dom,
             Em::Expr),Em::Error>
    where
    V: 'a+Bytes<'a>+FromConst<'a>+Semantic+Debug,
    Dom: Domain<Program<'a,V>>,
    Em: Embed
{
    let cur_sz = prog_inp.len();
    let inc_sz = inc.prog_inp.len();
    let mut comp = Comp { referenced: (&SINGLETON_BOOL,
                                       &inc.prog,prog) };
    let mut work = Vec::with_capacity(cur_sz+inc_sz+1);
    for i in 0..cur_sz+inc_sz+1 {
        work.push(comp.embed(expr::Expr::Var(CompVar(i))).unwrap());
    }
    let cond = comp.embed(expr::Expr::Var(CompVar(0))).unwrap();
    let mut ninp = Vec::new();
    let nprog = ite(&cond,
                    &then(Id,Offset::new(1)),&inc.prog,&work[..],
                    &then(Id,Offset::new(1+inc_sz)),&prog,&work[..],
                    &mut ninp,
                    &mut comp).unwrap().unwrap();
    let ndom = Dom::derives(&ninp[..],&mut comp,&|&CompVar(n)| {
        if n==0 {
            return None
        }
        if n<inc_sz+1 {
            return Some((&inc.domain,n-1))
        }
        Some((dom,n-1-inc_sz))
    }).unwrap();
    let ndom_full = Dom::derives(&ninp[..],&mut comp,&|&CompVar(n)| {
        if n==0 {
            return None
        }
        if n<inc_sz+1 {
            return Some((&inc.domain_full,n-1))
        }
        Some((dom_full,n-1-inc_sz))
    }).unwrap();
    let mut nprog_inp = Vec::with_capacity(ninp.len());
    let rcond = match inc.path_cond.len() {
        0 => em.const_bool(true),
        1 => Ok(inc.path_cond[0].clone()),
        _ => em.and(inc.path_cond.clone())
    }?;
    for e in ninp.iter() {
        let ne = e.translate(&mut |i,em| {
            if i==0 {
                Ok(rcond.clone())
            } else if i<inc_sz+1 {
                Ok(inc.prog_inp[i-1].clone())
            } else {
                Ok(prog_inp[i-1-inc_sz].clone())
            }
        },em)?;
        nprog_inp.push(ne);
    }
    Ok((nprog,nprog_inp,
        ndom,ndom_full,
        rcond))
}

fn update_on_semantic_change<'a,C,D,It,Dom,Em,F>(new: &C,
                                                 old_semantics: &[C::Meaning],
                                                 new_semantics: &mut Semantics<'a,D>,
                                                 input_abstract: &[CompExpr<C>],
                                                 input_concrete: &mut Vec<Em::Expr>,
                                                 selector: &Em::Expr,
                                                 domain: &mut Dom,
                                                 em: &mut Em,
                                                 debugging: bool,
                                                 update: F)
                                                 -> Result<(),Em::Error> 
    where
    C: Semantic+Composite<'a>,
    D: Semantic<Meaning=C::Meaning>,
    Dom: Domain<C>,
    F: Fn(&C::Meaning) -> bool,
    Em: Backend,
    Em::Expr: Display {

    let mut idx = 0;
    while let Some(m) = new_semantics.next_ref() {
        // Should this variable be updated?
        if update(m) {
            // Has the variable changed?
            match *input_abstract[idx].0 {
                expr::Expr::Var(ref old_idx)
                    if old_semantics[old_idx.0]==*m => {},
                _ => {
                    // Variable has changed
                    if debugging {
                        em.comment(&format!("Meaning: {}",MeaningOf::new(new,m)))?
                    }
                    let tp = new.elem_sort(idx,em)?;
                    let nondet = em.declare(tp)?;
                    let ne = em.ite(selector.clone(),input_concrete[idx].clone(),nondet)?;
                    let nne = em.define(ne)?;
                    input_concrete[idx] = nne;
                    domain.forget_var(idx);
                }
            }
        } else if debugging {
            match *input_abstract[idx].0 {
                expr::Expr::Var(ref old_idx)
                    if old_semantics[old_idx.0]==*m => {},
                _ => em.comment(&format!("New PC: {} = {}",MeaningOf::new(new,m),input_concrete[idx]))?
            }
        }
        idx+=1;
    }
    Ok(())
}

fn main() {
    #[cfg(feature="cpuprofiling")]
    PROFILER.lock().unwrap().start("./falco-enc.profile").unwrap();
    let opts = clap_app!(("falco-enc") =>
                         (version: "0.1")
                         (author: "Henning Günther <guenther@forsyte.at>")
                         (about: "Encodes a falco trace into an SMT instance")
                         (@arg bmc: -b --bmc "Encode all traces into one BMC instance")
                         (@arg fun_spec: -f --fun_spec <FILE> !required +takes_value "Use a tracing specification file")
                         (@arg debug: -d --debug !required +multiple "Add extra debugging information to the trace")
                         (@arg llvm_file: +required "The LLVM file")
                         (@arg trace: +required +multiple "The trace file")
    );

    let args = opts.get_matches();

    let llvm_file = args.value_of("llvm_file").unwrap();
    let m = parse_module(llvm_file).expect("Cannot parse llvm module");
    //println!("Module: {:#?}",m);
    let debugging = args.occurrences_of("debug");
    let fun_spec = match args.value_of("fun_spec") {
        None => fun_spec::FunSpecs::empty(),
        Some(file) => fun_spec::FunSpecs::read(file)
    };
    let mut p = Simplify::new(Pipe::new(io::empty(),io::stdout()));
    let selectors = make_selectors(&m,&mut p).unwrap();

    if args.is_present("bmc") {
        let mut builder = GraphBuilder::new();
        let mut all_args = Vec::with_capacity(args.occurrences_of("trace") as usize);
        for (nr,tr) in args.values_of("trace").unwrap().enumerate() {
            let (args,mut reader) = falco::StepReader::new(
                &m,&fun_spec,
                File::open(tr).unwrap());
            builder.add_trace(nr,&mut reader);
            all_args.push(args);
        }
        let gr = builder.finish();
        let mut unw : GraphUnwinding<_,Val,AttributeDomain<Const>>
            = GraphUnwinding::new(&m,&mut p,&selectors,gr,all_args,debugging).unwrap();
        while unw.step().unwrap() {}
        unw.declare_traces().unwrap();
    } else {
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
    }
    #[cfg(feature="cpuprofiling")]
    PROFILER.lock().unwrap().stop().unwrap();
}
