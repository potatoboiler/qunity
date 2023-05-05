use self::super::Node;

enum TypeNode {
    ValueExpr,
    TypeExpr,
    CtrlExpr,
}

fn build_type_judgement(node: Node) -> TypeNode {
    match node {
        Node::Number(asd) => todo!(),
        Node::U3(asd) => todo!(),
        Node::Chain(_) => todo!(),
        node => todo!("{:#?}", node),
    }
}
