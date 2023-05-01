use std::{
    collections::{HashMap, HashSet},
    sync::Mutex,
};

use nom::sequence::pair;
use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "pest_parser/grammar.pest"]
struct QParser;

#[derive(Clone, Debug)]
pub(crate) enum Node {
    Program {
        prog: String,
        ops: Vec<String>,
        expr: Box<Node>,
    },
    Number(f64),
    Ident(String),
    Types(String),
    Apply(Box<(Node, Node)>),
    // Lambda(Box<(Node, Node, Node)>),
    Ctrl(Box<(Node, Node, Vec<(Node, Node)>, Node)>),
    Prog {
        name: String,
        args: Vec<Node>,
    },
    Rphase {
        r#type: Box<Node>,
        // arg: Box<Node>,
        phase1: Box<Node>,
        phase2: Box<Node>,
    },
    Lambda {
        // thsi is kind of a hack
        args: Vec<String>,
        body: Box<Node>, // FIXME:
    },
    Chain(Vec<Node>),
}

struct CompilerContext {
    // variable_bindings: HashMap<String, Node>,
    // program_names: HashMap<String, Node>,
    variable_bindings: HashSet<String>,
    program_names: HashSet<String>,
}

lazy_static! {
    static ref ctx: Mutex<CompilerContext> = Mutex::new(CompilerContext {
        variable_bindings: HashSet::new(),
        program_names: HashSet::new(),
    });
}

pub(crate) fn parse(source: &str) -> Result<Vec<Node>, pest::error::Error<Rule>> {
    let mut ast = vec![];

    let pairs = QParser::parse(Rule::program, source)?;

    for pair in pairs {
        if let Rule::program = pair.as_rule() {
            // println!("{:#?}", pair);
            ast.push(build_ast(pair))
        } else {
            panic!("LOL")
        }
    }

    Ok(ast)
}

fn build_ast(pair: pest::iterators::Pair<Rule>) -> Node {
    match pair.as_rule() {
        Rule::program => {
            let children: Vec<pest::iterators::Pair<Rule>> = pair.into_inner().collect();

            let program_name = children[0].as_span().as_str();
            let idents = &children[1..children.len() - 1];

            let program_def = children.last().unwrap().clone();
            Node::Program {
                prog: program_name.to_string(),
                ops: idents
                    .iter()
                    .map(|pair| pair.as_span().as_str().to_string())
                    .collect(),
                expr: Box::new(build_ast(program_def)),
            }
        }
        Rule::number => Node::Number(pair.as_span().as_str().parse::<f64>().unwrap()),
        Rule::ident => Node::Ident(pair.as_span().as_str().into()),
        Rule::types => Node::Types(pair.as_span().as_str().into()),
        Rule::ctrl => {
            let pair_inner: Vec<_> = pair.into_inner().collect();
            let ctrl_list = pair_inner[2].clone();
            let ctrl_matcher: Vec<(Node, Node)> = ctrl_list
                .into_inner()
                .map(|arm| {
                    assert!(matches!(arm.as_rule(), Rule::arm));
                    let inner: Vec<_> = arm.into_inner().collect();
                    assert_eq!(inner.len(), 2);
                    (build_ast(inner[0].clone()), build_ast(inner[1].clone()))
                })
                .collect();
            Node::Ctrl(Box::new((
                build_ast(pair_inner[0].clone()),
                build_ast(pair_inner[1].clone()),
                ctrl_matcher,
                build_ast(pair_inner[3].clone()),
            )))
        }
        Rule::arm => {
            panic!("Arms should be parsed in the ctrl arm; should not be standalone!")
        }
        Rule::lambda => {
            let pair_inner: Vec<_> = pair.into_inner().collect();
            let split = pair_inner.split_last().unwrap();
            Node::Lambda {
                args: split
                    .1
                    .iter()
                    .map(|p| p.as_span().as_str().into())
                    .collect(),
                body: Box::new(build_ast(split.0.clone())),
            }
        }
        Rule::chain => {
            let pair_vec: Vec<_> = pair.into_inner().collect(); // hack so that it doesn't DFS all the way
            Node::Chain(pair_vec.iter().map(|p| build_ast(p.clone())).collect())
        }
        Rule::list => {
            todo!()
        }
        Rule::gphase => {
            // Node::Ident("Placeholder gphase".to_string());
            let mut inner = pair.into_inner().map(|pair| Box::new(build_ast(pair)));
            let arg_type = inner.next().unwrap();
            // let arg = inner.next().unwrap();
            let phase = inner.next().unwrap();
            Node::Rphase {
                r#type: arg_type,
                // arg: (),
                phase1: phase.clone(),
                phase2: phase.clone(),
            }
        }
        Rule::rphase => {
            // Node::Ident("Placeholder rphase".to_string());
            let mut inner = pair.into_inner().map(|pair| Box::new(build_ast(pair)));
            Node::Rphase {
                r#type: inner.next().unwrap(),
                // arg: inner.next().unwrap(),
                phase1: inner.next().unwrap(),
                phase2: inner.next().unwrap(),
            }
        }
        rule => {
            todo!("{}", format!("{:?}", rule))
        }
    }
}
