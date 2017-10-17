use num_bigint::{BigInt,BigUint};
use nom::*;
use std::str::FromStr;
use std::str;
use std::io::Read;
use std::cmp::min;
use llvm_ir;
use symbolic_llvm::symbolic::llvm::thread::CallId;
use symbolic_llvm::symbolic::llvm::InstructionRef;
use fun_spec::*;
use std::collections::hash_map::{HashMap,Entry};

#[derive(Debug,PartialEq,Eq)]
pub enum Value {
    Int { bw: u64, val: BigUint },
    Address(BigInt),
    Bin(Vec<u8>)
}

#[derive(Debug,PartialEq,Eq)]
enum Type {
    String,
    Int(u64),
    Address,
    Bin
}

#[derive(Debug,PartialEq,Eq)]
pub enum Element {
    BasicBlockMapping(usize,String,String),
    MainArgumentCount(usize),
    MainArgument(Vec<u8>),
    BasicBlock(usize),
    CallArgument(bool,Value),
    CallReturn(bool,Value),
    End
}

#[derive(Debug,PartialEq,Eq,Clone)]
pub enum Val {
    Int { bw: u64, val: BigUint },
    Mem { address: BigInt, content: Vec<u8> }
}

#[derive(Debug,PartialEq,Eq,Hash,Clone)]
pub struct StepId<'a> {
    pub call_id: CallId<'a>,
    pub fun: &'a String,
    pub blk: usize,
    pub instr: usize
}

#[derive(Debug,PartialEq,Eq)]
pub struct Step<'a> {
    pub id: StepId<'a>,
    pub ext: CallKind<'a>
}

#[derive(Debug,PartialEq,Eq)]
pub enum CallKind<'a> {
    Internal,
    External(External<'a>)
}

#[derive(Debug,PartialEq,Eq,Clone)]
pub struct External<'a> {
    pub function: &'a String,
    pub args: Vec<Option<Val>>,
    pub ret: Option<Val>
}

/*pub struct Witness<'a> {
    trace: usize,
    basic_block: usize,
    instr: usize,*/
    

pub type Witnesses<'a> = HashMap<&'a String,Vec<(usize,Vec<Option<Val>>,Option<Val>)>>;

named!(ws,eat_separator!(" \t"));

named!(parse_usize<usize>,
       map_res!(map_res!(digit,str::from_utf8),
                FromStr::from_str));

named!(parse_u64<u64>,
       map_res!(map_res!(digit,str::from_utf8),
                FromStr::from_str));

fn parse_escaped(inp: &[u8]) -> IResult<&[u8],Vec<u8>> {
    let mut res = Vec::new();
    let mut pos = 0;
    loop {
        if inp.len()<=pos {
            return IResult::Incomplete(Needed::Size(1))
        }
        if inp[pos]==b'\"' {
            return IResult::Done(&inp[pos..],res)
        }
        if inp[pos]==b'\\' {
            if inp.len()<=pos+1 {
                return IResult::Incomplete(Needed::Size(2))
            }
            match inp[pos+1] {
                b'n' => res.push(b'\n'),
                b't' => res.push(b'\t'),
                b'0' => res.push(b'\0'),
                b'r' => res.push(b'\r'),
                b'\"' => res.push(b'\"'),
                _ => return IResult::Error(ErrorKind::Custom(0))
            }
            pos+=2;
        } else {
            res.push(inp[pos]);
            pos+=1;
        }
    }
}

named!(parse_type<Type>,
       alt!(do_parse!(tag!("i8x") >>
                      digit >>
                      (Type::String)) |
            do_parse!(char!('i') >>
                      bw: parse_u64 >>
                      (Type::Int(bw))) |
            do_parse!(tag!("ptr") >>
                      (Type::Address)) |
            do_parse!(char!('m') >>
                      digit >>
                      (Type::Bin))));

named!(parse_string<Value>,do_parse!(char!('\"') >>
                                     res: parse_escaped >>
                                     char!('\"') >>
                                     (Value::Bin(res.to_vec()))));
                                      
named_args!(parse_int(bw: u64)<Value>,
            map!(map_opt!(digit,|v| BigUint::parse_bytes(v,10)),
                 |val| Value::Int { bw: bw, val: val }));

named!(parse_address<Value>,
       alt!(do_parse!(tag!("(nil)") >> (Value::Address(BigInt::from(0)))) |
            do_parse!(tag!("0x") >>
                      val: map_opt!(hex_digit,|v| BigInt::parse_bytes(v,16)) >>
                      (Value::Address(val)))));

named!(parse_bin<Value>,
       map!(separated_list_complete!(ws,map_res!(map_res!(hex_digit,str::from_utf8),|s| u8::from_str_radix(s,16))),
            Value::Bin));

fn parse_value<'a>(inp: &'a [u8],tp: &Type) -> IResult<&'a [u8],Value> {
    match tp {
        &Type::String => parse_string(inp),
        &Type::Int(bw) => parse_int(inp,bw),
        &Type::Address => parse_address(inp),
        &Type::Bin => parse_bin(inp)
    }
}

named!(parse_element<Element>,
       do_parse!(ws >> digit >> // Element index, should be consecutive
                 ws >>
                 el: alt!(do_parse!(char!('I') >> ws >>
                                    // Block id also denotes the length of name, ignore
                                    blk_id: parse_usize >> char!('x') >> digit >> ws >>
                                    digit >> ws >> // Thread id
                                    char!('\"') >>
                                    blk_name: map_res!(is_not!("\"@"),str::from_utf8) >>
                                    char!('@') >>
                                    fun_name: map_res!(is_not!("\""),str::from_utf8) >>
                                    char!('\"') >>
                                    (Element::BasicBlockMapping(blk_id,
                                                                String::from(blk_name),
                                                                String::from(fun_name)))) |
                          do_parse!(char!('C') >> ws >>
                                    tag!("i32") >> ws >>
                                    digit >> ws >> // thread id
                                    n: parse_usize >>
                                    (Element::MainArgumentCount(n))) |
                          do_parse!(char!('V') >> ws >>
                                    tag!("i8x") >> digit >> ws >> // length of the argument
                                    digit >> ws >> // thread id
                                    char!('\"') >>
                                    arg: parse_escaped >>
                                    char!('\"') >>
                                    (Element::MainArgument(arg))) |
                          do_parse!(char!('B') >> ws >>
                                    bid: parse_usize >> ws >>
                                    digit >> ws >> // thread id
                                    tag!("---") >>
                                    (Element::BasicBlock(bid))) |
                          do_parse!(deref: opt!(char!('*')) >>
                                    char!('R') >> ws >>
                                    tp: parse_type >> ws >>
                                    digit >> ws >> // thread id
                                    val: call!(parse_value,&tp) >>
                                    (Element::CallReturn(deref.is_some(),val))) |
                          do_parse!(deref: opt!(char!('*')) >>
                                    char!('A') >> ws >>
                                    tp: parse_type >> ws >>
                                    digit >> ws >>
                                    val: call!(parse_value,&tp) >>
                                    (Element::CallArgument(deref.is_some(),val))) |
                          do_parse!(char!('E') >> ws >>
                                    tag!("---") >> ws >>
                                    tag!("---") >> ws >>
                                    tag!("---") >>
                                    (Element::End))
                 ) >>
                 ws >> newline >>
                 (el)));

pub struct StepReader<'a,R> {
    module: &'a llvm_ir::Module,
    spec: &'a FunSpecs,
    parser: ElementParser<R>,
    mapping: Vec<(String,String)>,
    stack: Vec<(&'a String,usize,usize)>,
    next_block: usize,
    next_instr: usize
}

pub struct ElementParser<R> {
    reader: R,
    buffer: Vec<u8>
}

impl<'a,R : Read> StepReader<'a,R> {
    pub fn new(m: &'a llvm_ir::Module,spec: &'a FunSpecs,reader: R) -> (Vec<Vec<u8>>,Self) {
        let mut parser = ElementParser::new(reader);
        let (mapping,nargs) = parser.get_mapping();
        let args = parser.get_args(nargs);
        let fun = {
            let &(_,ref fun_id) = match parser.next() {
                None => panic!("Unexpected end of trace"),
                Some(Element::BasicBlock(n)) => &mapping[n-1],
                Some(el) => panic!("Unexpected element: {:#?}",el)
            };
            m.functions.get(fun_id)
                .expect("Entry function not found in module")
        };
        (args,StepReader { module: m,
                           spec: spec,
                           parser: parser,
                           mapping: mapping,
                           stack: vec![(&fun.name,0,0)],
                           next_block: 0,
                           next_instr: 0 })
    }
    pub fn into_witnesses(self,nr: usize,wit: &mut Witnesses<'a>) -> () {
        for step in self {
            match step.ext {
                CallKind::External(ext) => match wit.entry(ext.function) {
                    Entry::Occupied(mut occ) => {
                        occ.get_mut().push((nr,ext.args,ext.ret));
                    },
                    Entry::Vacant(vac) => {
                        vac.insert(vec![(nr,ext.args,ext.ret)]);
                    }
                },
                _ => {}
            }
        }
    }
    fn call_id(&self) -> CallId<'a> {
        match self.stack.len() {
            0 => panic!("call_id called on empty stack"),
            1 => {
                let main = self.stack[0].0;
                (None,main)
            },
            n => {
                let (fun_id,blk_id,nxt_instr) = self.stack[n-1];
                let (call_fun,_,_) = self.stack[n-2];
                let fun = self.module.functions.get(call_fun).expect("Function not found");
                let blk = match fun.body {
                    None => panic!("Function has no body"),
                    Some(ref blks) => &blks[blk_id].name
                };
                (Some(InstructionRef { function: call_fun,
                                       basic_block: blk,
                                       instruction: nxt_instr-1 }),fun_id)
            }
        }
    }
}

impl<'a,R : Read> Iterator for StepReader<'a,R> {
    type Item = Step<'a>;
    fn next(&mut self) -> Option<Step<'a>> {
        let cid = self.call_id();
        let cfun = match self.stack.last() {
            Some(&(fname,_,_)) => self.module.functions.get(fname).expect("Function not found in module"),
            None => return None
        };
        let instr = match cfun.body {
            None => panic!("Function has no body"),
            Some(ref bdy) => &bdy[self.next_block].instrs[self.next_instr]
        };
        match &instr.content {
            &llvm_ir::InstructionC::Call(_,_,ref rtp,ref called,ref args,_) => {
                match called {
                    &llvm_ir::Value::Constant(llvm_ir::Constant::Global(ref name)) => {
                        let fun = match self.module.functions.get(name) {
                            None => panic!("Function {} not found in module",name),
                            Some(fun) => fun
                        };
                        if fun.body.is_some() && !name.starts_with("__falco_ignore") {
                            match self.parser.next() {
                                None => panic!("Unexpected end of trace"),
                                Some(Element::BasicBlock(n)) => {
                                    let (_,ref fun_name) = self.mapping[n-1];
                                    assert_eq!(*fun_name,fun.name);
                                },
                                Some(el) => panic!("Unexpected element: {:#?}",el)
                            }
                            self.stack.push((&fun.name,self.next_block,self.next_instr+1));
                            let cblk = self.next_block;
                            let cinstr = self.next_instr;
                            self.next_block = 0;
                            self.next_instr = 0;
                            Some(Step { id: StepId { call_id: cid,
                                                     fun: &cfun.name,
                                                     blk: cblk,
                                                     instr: cinstr },
                                        ext: CallKind::Internal })
                        } else {
                            let fspec = self.spec.get(name,false,rtp.is_some());
                            let cinstr = self.next_instr;
                            let rret = match fspec.ret() {
                                &None => None,
                                &Some(TraceSpec::Std) => match rtp {
                                    &None => panic!("Function specification has return type for {}, but module doesn't",name),
                                    &Some((ref rtp_,_)) => match rtp_ {
                                        &llvm_ir::types::Type::Pointer(ref ptp,_) => match **ptp {
                                            llvm_ir::types::Type::Function(ref ret,_,_) => match ret {
                                                &None => None,
                                                &Some(ref rtp__) => self.parser.get_val(true,rtp__,fspec.ret())
                                            },
                                            _ => self.parser.get_val(true,rtp_,fspec.ret())
                                        },
                                        _ => self.parser.get_val(true,rtp_,fspec.ret())
                                    }
                                },
                                &Some(ref s) => panic!("Tracing return arguments with {:?} not supported",s)
                            };
                            let rargs = args.iter()
                                .enumerate()
                                .map(|(nr,tval)| {
                                    let def = fspec.arg(nr);
                                    self.parser.get_val(false,
                                                        &tval.tp,
                                                        def)
                                }).collect();
                            self.next_instr+=1;
                            Some(Step { id: StepId { call_id: cid,
                                                     fun: &cfun.name,
                                                     blk: self.next_block,
                                                     instr: cinstr },
                                        ext: CallKind::External(External { function: name,
                                                                           args: rargs,
                                                                           ret: rret }) })
                        }
                    },
                    _ => panic!("Function pointers not supported")
                }
            },
            &llvm_ir::InstructionC::Term(llvm_ir::Terminator::Unreachable) => {
                // Terminate the trace when we hit unreachable
                None
            },
            &llvm_ir::InstructionC::Term(llvm_ir::Terminator::Br(ref trg)) => {
                // Get the next block in the trace
                match self.parser.next() {
                    None => None,
                    Some(Element::BasicBlock(n)) => {
                        let (ref blk_name,_) = self.mapping[n-1];
                        assert_eq!(*trg,*blk_name);
                        let cblk = self.next_block;
                        let cinstr = self.next_instr;
                        self.next_block = match cfun.body {
                            None => panic!("Function has no body"),
                            Some(ref bdy) => bdy.iter().position(|blk| blk.name==*blk_name).expect("Basic block not found")
                        };
                        self.next_instr = 0;
                        Some(Step { id: StepId { call_id: cid,
                                                 fun: &cfun.name,
                                                 blk: cblk,
                                                 instr: cinstr },
                                    ext: CallKind::Internal })
                    },
                    Some(el) => panic!("Unexpected element: {:#?}",el)
                }
            },
            &llvm_ir::InstructionC::Term(llvm_ir::Terminator::BrC(_,ref trg_t,ref trg_f)) => {
                match self.parser.next() {
                    None => None,
                    Some(Element::BasicBlock(n)) => {
                        let (ref blk_name,_) = self.mapping[n-1];
                        assert!(*trg_t==*blk_name || *trg_f==*blk_name);
                        let cblk = self.next_block;
                        let cinstr = self.next_instr;
                        self.next_block = match cfun.body {
                            None => panic!("Function has no body"),
                            Some(ref bdy) => bdy.iter().position(|blk| blk.name==*blk_name).expect("Basic block not found")
                        };
                        self.next_instr = 0;
                        Some(Step { id: StepId { call_id: cid,
                                                 fun: &cfun.name,
                                                 blk: cblk,
                                                 instr: cinstr },
                                    ext: CallKind::Internal })
                    },
                    Some(el) => panic!("Unexpected element: {:#?}",el)
                }
            },
            &llvm_ir::InstructionC::Term(llvm_ir::Terminator::Switch(_,_,ref def,ref trgs)) => {
                match self.parser.next() {
                    None => None,
                    Some(Element::BasicBlock(n)) => {
                        let (ref blk_name,_) = self.mapping[n-1];
                        if *def!=*blk_name {
                            assert!(trgs.iter().find(|&&(_,ref trg)| *trg==*blk_name).is_some())
                        }
                        let cblk = self.next_block;
                        let cinstr = self.next_instr;
                        self.next_block = match cfun.body {
                            None => panic!("Function has no body"),
                            Some(ref bdy) => bdy.iter().position(|blk| blk.name==*blk_name).expect("Basic block not found")
                        };
                        self.next_instr = 0;
                        Some(Step { id: StepId { call_id: cid,
                                                 fun: &cfun.name,
                                                 blk: cblk,
                                                 instr: cinstr },
                                    ext: CallKind::Internal })
                    },
                    Some(el) => panic!("Unexpected element: {:#?}",el)
                }
            },
            &llvm_ir::InstructionC::Term(llvm_ir::Terminator::Ret(_)) => {
                match self.stack.pop() {
                    None => panic!("Stack exhausted"),
                    Some((_,nxt_blk,nxt_instr)) => match self.stack.last() {
                        None => panic!("Stack exhausted"),
                        Some(_) => {
                            let cblk = self.next_block;
                            let cinstr = self.next_instr;
                            self.next_block = nxt_blk;
                            self.next_instr = nxt_instr;
                            Some(Step { id: StepId { call_id: cid,
                                                     fun: &cfun.name,
                                                     blk: cblk,
                                                     instr: cinstr },
                                        ext: CallKind::Internal })
                        }
                    }
                }
            },
            _ => {
                let cinstr = self.next_instr;
                self.next_instr+=1;
                Some(Step { id: StepId { call_id: cid,
                                         fun: &cfun.name,
                                         blk: self.next_block,
                                         instr: cinstr },
                            ext: CallKind::Internal })
            }
        }
    }
}

fn skip_line<R : Read>(reader: &mut R,buf: &mut Vec<u8>) -> () {
    for i in 0..buf.len() {
        if buf[i]==b'\n' {
            buf.drain(0..i+1);
            return ()
        }
    }
    buf.resize(1024,0);
    loop {
        let sz = reader.read(&mut buf[..]).expect("Failed to skip line");
        for i in 0..sz {
            if buf[i]==b'\n' {
                buf.truncate(sz);
                buf.drain(0..i+1);
                return ()
            }
        }
    }
}

impl<R : Read> ElementParser<R> {
    pub fn new(mut reader: R) -> Self {
        let mut buf = Vec::with_capacity(1024);
        // Skip the first two lines
        skip_line(&mut reader,&mut buf);
        skip_line(&mut reader,&mut buf);
        ElementParser { reader: reader,
                        buffer: buf }
    }
    pub fn get_mapping(&mut self) -> (Vec<(String,String)>,usize) {
        let mut pos = 1;
        let mut res = Vec::new();
        while let Some(el) = self.next() {
            match el {
                Element::BasicBlockMapping(i,blk,fun) => {
                    if pos!=i {
                        panic!("Basic block mapping isn't ordered")
                    }
                    res.push((blk,fun));
                    pos+=1;
                },
                Element::MainArgumentCount(n) => return (res,n),
                _ => panic!("Unexpected element: {:#?}",el)
            }
        }
        panic!("Unexepected end of trace")
    }
    pub fn get_args(&mut self,num: usize) -> Vec<Vec<u8>> {
        let mut res = Vec::with_capacity(num);
        for _ in 0..num {
            match self.next() {
                None => panic!("Unexpected end of trace"),
                Some(Element::MainArgument(arg)) => res.push(arg),
                Some(el) => panic!("Unexpected trace element: {:#?}",el)
            }
        }
        res
    }
    fn get_value(&mut self,is_ret: bool) -> (bool,Value) {
        match self.next() {
            None => panic!("Unexpected end of trace"),
            Some(Element::CallArgument(i,v))
                => if is_ret {
                    panic!("Unexpected call argument, expected return argument")
                } else {
                    (i,v)
                },
            Some(Element::CallReturn(i,v))
                => if is_ret {
                    (i,v)
                } else {
                    panic!("Unexpected return argument, expected call argument")
                },
            Some(el) => panic!("Unexpected element: {:#?}",el)
        }
    }
    fn get_val(&mut self,
               is_ret: bool,
               tp: &llvm_ir::types::Type,
               spec: &Option<TraceSpec>)
               -> Option<Val> {
        match spec {
            &None => None,
            &Some(_) => match tp {
                &llvm_ir::types::Type::Int(bw_)
                    => match self.get_value(is_ret) {
                        (false,Value::Int { bw, val }) => {
                            assert_eq!(bw_,bw);
                            Some(Val::Int { bw: bw, val: val })
                        },
                        r => panic!("Unexpected value {:#?}, expected int",r)
                    },
                &llvm_ir::types::Type::Pointer(_,_) => match self.get_value(is_ret) {
                    (false,Value::Address(addr)) => match self.get_value(is_ret) {
                        (true,Value::Bin(cont)) => Some(Val::Mem { address: addr, content: cont }),
                        el => panic!("Unexpected value {:#?}, expected bin",el)
                    },
                    el => panic!("Unexpected value {:#?}, expected address",el)
                },
                _ => panic!("Don't know how to trace {:#?}",*tp)
            }
        }
    }
}

impl<R : Read> Iterator for ElementParser<R> {
    type Item = Element;
    fn next(&mut self) -> Option<Element> {
        loop {
            let res = match parse_element(&self.buffer[..]) {
                IResult::Done(ninp,el) => Some((ninp.len(),el)),
                IResult::Incomplete(_) => None,
                IResult::Error(err) => {
                    let limit = min(120,self.buffer.len());
                    panic!("Cannot parse entry: {}; {}",err,str::from_utf8(&self.buffer[0..limit]).unwrap())
                }
            };
            if let Some((rest_sz,el)) = res {
                let sz = self.buffer.len();
                self.buffer.drain(0..sz-rest_sz);
                if el==Element::End {
                    return None
                } else {
                    return Some(el)
                }
            }
            let pos = self.buffer.len();
            self.buffer.resize(pos+1024,0);
            match self.reader.read(&mut self.buffer[pos..]) {
                Ok(sz) => {
                    self.buffer.truncate(pos+sz);
                },
                Err(err) => panic!("IO error: {}",err)
            }
        }
    }
}
