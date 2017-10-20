
use falco::{Step,StepId,External,CallKind};
use petgraph::graph::{Graph,NodeIndex};
use symbolic_llvm::symbolic::llvm::thread::CallId;
use std::collections::HashMap;
use std::collections::hash_map::Entry;
use petgraph::dot;

pub type FalcoGraph<'a> = Graph<MultiStep<'a>,()>;

pub fn debug_graph<'a>(gr: &FalcoGraph<'a>) {
    println!("{:?}",dot::Dot::with_config(gr,&[dot::Config::NodeIndexLabel]))
}

#[derive(Debug)]
pub enum MultiCallKind<'a> {
    Internal,
    External(Vec<(usize,External<'a>)>)
}

#[derive(Debug)]
pub struct MultiStep<'a> {
    pub id: StepId<'a>,
    pub ext: MultiCallKind<'a>,
    pub start: Vec<usize>,
    pub end: Vec<usize>
}

struct NodeUse {
    nodes: Vec<NodeIndex>,
    pos: usize
}

pub struct GraphBuilder<'a> {
    graph: FalcoGraph<'a>,
    nodes: HashMap<StepId<'a>,NodeUse>,
}

impl<'a> GraphBuilder<'a> {
    pub fn new() -> Self {
        GraphBuilder {
            graph: Graph::new(),
            nodes: HashMap::new()
        }
    }
    pub fn finish(self) -> FalcoGraph<'a> {
        self.graph
    }
    fn insert_node(&mut self,start: bool,end: bool,nr: usize,step: Step<'a>) -> NodeIndex {
        let entr = match self.nodes.entry(step.id.clone()) {
            Entry::Vacant(vac) => vac.insert(NodeUse { nodes: vec![],
                                                       pos: 0 }),
            Entry::Occupied(occ) => occ.into_mut()
        };
        if entr.pos >= entr.nodes.len() {
            // No node can be reused
            let mstep = MultiStep {
                id: step.id,
                ext: match step.ext {
                    CallKind::Internal => MultiCallKind::Internal,
                    CallKind::External(ext)
                        => MultiCallKind::External(vec![(nr,ext)]),
                },
                start: if start { vec![nr] } else { vec![] },
                end: if end { vec![nr] } else { vec![] }
            };
            let nd = self.graph.add_node(mstep);
            entr.nodes.push(nd);
            entr.pos+=1;
            nd
        } else {
            // Reuse existing node
            let nd = entr.nodes[entr.pos];
            // If the step is an external call, we must update the graph
            match step.ext {
                CallKind::Internal => if start {
                    let mstep = self.graph.node_weight_mut(nd).unwrap();
                    mstep.start.push(nr);
                },
                CallKind::External(ext) => {
                    let mstep = self.graph.node_weight_mut(nd).unwrap();
                    match mstep.ext {
                        MultiCallKind::Internal => panic!("A step cannot be internal in one trace and external in another"),
                        MultiCallKind::External(ref mut exts) => {
                            // Assume that trace numbers are ascending
                            exts.push((nr,ext));
                        }
                    }
                    if start {
                        mstep.start.push(nr);
                    }
                    if end {
                        mstep.end.push(nr);
                    }
                }
            }
            entr.pos+=1;
            nd
        }
    }
    pub fn add_trace<It>(&mut self,nr: usize,tr: &mut It)
        where It : Iterator<Item=Step<'a>> {
        // Reset positions
        for usage in self.nodes.values_mut() {
            usage.pos = 0;
        }
        let first = match tr.next() {
            None => return,
            Some(s) => s
        };
        let mut ntr = tr.peekable();
        let last = !ntr.peek().is_some();
        let mut prev_nd = self.insert_node(true,last,nr,first);
        while let Some(step) = ntr.next() {
            let last = !ntr.peek().is_some();
            let next_nd = self.insert_node(false,last,nr,step);
            self.graph.update_edge(prev_nd,next_nd,());
            prev_nd = next_nd;
        }
    }
}
