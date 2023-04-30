extern crate pest;
#[macro_use]
extern crate pest_derive;

mod pest_parser;
mod nom_parser;

#[macro_use]
extern crate nom;

#[macro_use]
extern crate lazy_static;

pub mod parser;

use std::collections::{hash_map, HashMap};

use nom::IResult;

type TokenName = String;
enum TokenType {
    Expression,
    Type,
    Program,
    // TypeContext,
}

enum ValueType {
    Void,
    Unit, // ()
    Sum,  // ?
    Pair, // ?
}



struct Value {}

struct CompilerContext {
    scope_stack: Vec<Scope>,
}

struct Scope {
    name: Option<String>,
    bindings: HashMap<TokenName, TokenType>,
}

fn parse() -> IResult<String, Value> {
    todo!()
}

fn main() {
    println!("Hello, world!");
}
