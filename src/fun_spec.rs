use serde::Deserialize;
use serde_json::{from_reader};
use serde::de::*;
use std::fs::File;
use std::collections::HashMap;
use std::fmt;

#[derive(Debug)]
pub enum LengthOp {
    Add,Mul,Sub,Div
}

#[derive(Debug)]
pub enum LengthSpec {
    Arg(usize),
    Const(usize),
    Op(LengthOp,Box<LengthSpec>,Box<LengthSpec>)
}

impl<'de> Deserialize<'de> for LengthSpec {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de> {

        struct LengthSpecVisitor;
        #[derive(Deserialize)]
        enum Field {
            #[serde(rename = "arg")]
            Arg,
            #[serde(rename = "const")]
            Const,
            #[serde(rename = "add")]
            Add,
            #[serde(rename = "mul")]
            Mul,
            #[serde(rename = "sub")]
            Sub,
            #[serde(rename = "div")]
            Div
        }
        impl<'nde> Visitor<'nde> for LengthSpecVisitor {
            type Value = LengthSpec;
            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a length specification")
            }
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                where A: SeqAccess<'nde> {
                match seq.next_element()? {
                    None => Err(Error::invalid_length(0,&"2")),
                    Some(Field::Arg) => match seq.next_element()? {
                        Some(n) => Ok(LengthSpec::Arg(n)),
                        None => Err(Error::invalid_length(1,&"2"))
                    },
                    Some(Field::Const) => match seq.next_element()? {
                        Some(n) => Ok(LengthSpec::Const(n)),
                        None => Err(Error::invalid_length(1,&"2"))
                    },
                    Some(Field::Add) => match seq.next_element()? {
                        Some(lhs) => match seq.next_element()? {
                            Some(rhs) => Ok(LengthSpec::Op(LengthOp::Add,lhs,rhs)),
                            None => Err(Error::invalid_length(2,&"3"))
                        },
                        None => Err(Error::invalid_length(1,&"3"))
                    },
                    Some(Field::Sub) => match seq.next_element()? {
                        Some(lhs) => match seq.next_element()? {
                            Some(rhs) => Ok(LengthSpec::Op(LengthOp::Sub,lhs,rhs)),
                            None => Err(Error::invalid_length(2,&"3"))
                        },
                        None => Err(Error::invalid_length(1,&"3"))
                    },
                    Some(Field::Mul) => match seq.next_element()? {
                        Some(lhs) => match seq.next_element()? {
                            Some(rhs) => Ok(LengthSpec::Op(LengthOp::Mul,lhs,rhs)),
                            None => Err(Error::invalid_length(2,&"3"))
                        },
                        None => Err(Error::invalid_length(1,&"3"))
                    },
                    Some(Field::Div) => match seq.next_element()? {
                        Some(lhs) => match seq.next_element()? {
                            Some(rhs) => Ok(LengthSpec::Op(LengthOp::Div,lhs,rhs)),
                            None => Err(Error::invalid_length(2,&"3"))
                        },
                        None => Err(Error::invalid_length(1,&"3"))
                    }
                }
            }
        }
        deserializer.deserialize_seq(LengthSpecVisitor)
    }
}

#[derive(Debug)]
pub enum TraceSpec {
    Std,
    CStr,
    Mem(LengthSpec)
}

static TRACE_SPEC_VARIANTS : [&'static str;2] = ["std","cstr"];

impl<'de> Deserialize<'de> for TraceSpec {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where D: Deserializer<'de> {

        struct TraceSpecVisitor;
        #[derive(Deserialize)]
        enum MemField {
            #[serde(rename = "mem")]
            MemField
        }
        
        impl<'nde> Visitor<'nde> for TraceSpecVisitor {
            type Value = TraceSpec;
            fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str("a tracing specification")
            }
            fn visit_str<E>(self,v: &str) -> Result<Self::Value, E>
                where E : Error {
                match v {
                    "std" => Ok(TraceSpec::Std),
                    "cstr" => Ok(TraceSpec::CStr),
                    _ => Err(Error::unknown_variant(v,&TRACE_SPEC_VARIANTS))
                }
            }
            fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
                where A: SeqAccess<'nde> {
                match seq.next_element()? {
                    Some(MemField::MemField) => match seq.next_element()? {
                        Some(len) => Ok(TraceSpec::Mem(len)),
                        None => Err(Error::invalid_length(1,&"2"))
                    },
                    None => Err(Error::invalid_length(0,&"2"))
                }
            }
        }
        deserializer.deserialize_any(TraceSpecVisitor)
    }
}

#[derive(Deserialize,Debug)]
pub struct FunSpec {
    pub is_variadic: bool,
    pub args: Vec<Option<TraceSpec>>,
    pub ret: Option<TraceSpec>
}

pub struct FunSpecs {
    specs: HashMap<String,FunSpec>,
    ignored: FunSpec,
    ignored_ret: FunSpec
}

pub enum OptFunSpec<'a> {
    Spec(&'a FunSpec),
    Default(bool,bool),
    Ignore
}

static OPT_TRACE_SPEC_STD : Option<TraceSpec> = Some(TraceSpec::Std);
static OPT_TRACE_SPEC_NONE : Option<TraceSpec> = None;

impl<'a> OptFunSpec<'a> {
    pub fn ignore(&self) -> bool {
        match self {
            &OptFunSpec::Ignore => true,
            _ => false
        }
    }
    pub fn is_variadic(&self) -> bool {
        match self {
            &OptFunSpec::Spec(sp) => sp.is_variadic,
            &OptFunSpec::Default(variadic,_) => variadic,
            &OptFunSpec::Ignore => false
        }
    }
    pub fn arg(&self,p: usize) -> &'a Option<TraceSpec> {
        match self {
            &OptFunSpec::Spec(sp) => if p < sp.args.len() {
                &sp.args[p]
            } else {
                &OPT_TRACE_SPEC_NONE
            },
            &OptFunSpec::Default(_,_) => &OPT_TRACE_SPEC_STD,
            &OptFunSpec::Ignore => &OPT_TRACE_SPEC_NONE
        }
    }
    pub fn ret(&self) -> &'a Option<TraceSpec> {
        match self {
            &OptFunSpec::Spec(sp) => &sp.ret,
            &OptFunSpec::Default(_,has_ret) => if has_ret {
                &OPT_TRACE_SPEC_STD
            } else {
                &OPT_TRACE_SPEC_NONE
            },
            &OptFunSpec::Ignore => &OPT_TRACE_SPEC_NONE
        }
    }
}

impl FunSpecs {
    pub fn empty() -> Self {
        FunSpecs { specs: HashMap::new(),
                   ignored: FunSpec { is_variadic: false,
                                      args: vec![],
                                      ret: None },
                   ignored_ret: FunSpec { is_variadic: false,
                                          args: vec![],
                                          ret: Some(TraceSpec::Std) }
        }
    }
    pub fn read(file: &str) -> Self {
        let reader = File::open(file).expect("Failed to open function specification file");
        FunSpecs { specs: from_reader(reader).unwrap(),
                   ignored: FunSpec { is_variadic: false,
                                      args: vec![],
                                      ret: None },
                   ignored_ret: FunSpec { is_variadic: false,
                                          args: vec![],
                                          ret: Some(TraceSpec::Std) }
        }
    }
    pub fn get<'a>(&'a self,
                   name: &String,
                   variadic: bool,
                   has_ret: bool) -> OptFunSpec<'a> {
        match self.specs.get(name) {
            Some(r) => OptFunSpec::Spec(r),
            None => if name.starts_with("llvm.dbg.") {
                OptFunSpec::Ignore
            } else if name.starts_with("llvm.expect.") {
                OptFunSpec::Ignore
            } else {
                OptFunSpec::Default(variadic,has_ret)
            }
        }
    }
}
