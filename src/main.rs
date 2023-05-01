extern crate pest;
extern crate pest_derive;

mod pest_parser;

#[macro_use]
extern crate lazy_static;

pub mod parser;

fn main() {
    let file = std::fs::read_to_string("lol.q").expect("Noo file?");
    let astnode = self::pest_parser::parse(file.as_str()).expect("bad ast");
    println!("{:#?}", astnode);
}
