use crate::ast::Node;

/// For raw OpenQASM generation.
/// Does not include meta-techniques e.g. 
enum Directive {
    gate_define,
    gate_apply,
    qubit,
    qubit_register,
}

/// Since the fundamental type is the qubit, can we hold a vector of initial types and track the flow of each wire?
/// 
pub fn compile(tree: Node) {}