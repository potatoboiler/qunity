use core::panic;

use crate::pest_parser::Node;

use super::TypeJudgement;

pub(crate) fn build_type_tree(ast: &mut Node) {
  match ast {
    Node::Lambda { args, body, typing } => {
      if args.len() % 2 != 0 {
        panic!("Expected [variable, type] pairs in lambda");
      }
      let input = args.len() / 2;
      let output = build_type_tree(ast);



      // *typing = Some(Box::new(TypeJudgement::Function(test)));
    },
    _ => panic!("Expected lambda"),
  }
}
