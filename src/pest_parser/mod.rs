use std::{
    collections::{HashMap, HashSet},
    sync::Mutex,
};

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
    Apply(Box<(Node, Node)>),
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
            println!("{:#?}", pair);
            // ast.push(Node::Program(Box::new(build_ast(pair))))
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
            let _program_name = children[0].as_span().as_str();
            let idents = &children[1..children.len() - 1];
            {
                let mut ctx_lock = ctx.lock().unwrap();

                // ctx.program_names.insert(program_name, v)

                ctx_lock.variable_bindings.extend(
                    idents
                        .iter()
                        .map(|pair| pair.as_span().as_str().to_string()),
                );
            }
            let program_def = children.last().unwrap().clone();
            Node::Program {
                prog: _program_name.to_string(),
                ops: idents
                    .iter()
                    .map(|pair| pair.as_span().as_str().to_string())
                    .collect(),
                expr: Box::new(build_ast(program_def)),
            }
        }
        Rule::prog => {
            todo!()
        }
        Rule::number => {
            todo!()
        }
        Rule::ident => {
            todo!()
        }
        Rule::ctrl => {
            todo!()
        }
        Rule::lambda => {
            todo!()
        }
        Rule::chain => {
            todo!()
        }
        Rule::list => {
            todo!()
        }
        _ => {
            todo!()
        }
    }
}
