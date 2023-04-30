use pest::Parser;
use pest_derive::Parser;

#[derive(Parser)]
#[grammar = "pest_parser/grammar.pest"]
struct QParser;

#[derive(Debug)]
pub(crate) enum Node {}

pub(crate) fn parse(source: &str) -> Result<Vec<Node>, pest::error::Error<Rule>> {
    let mut ast = vec![];

    let pairs = QParser::parse(Rule::program, source)?;

    for pair in pairs {
        println!("{:#?}", pair);
    }

    Ok(ast)
}
