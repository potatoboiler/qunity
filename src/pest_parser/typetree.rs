use self::super::Node;

pub(crate) enum TypeNode {
    ValueExpr(f64),
    TypeExpr(TypeNodeS), // for qubit or array types
    _CtrlExpr,
    _LambdaExpr((TypeNodeS, Box<LambdaS>)),
}

pub(crate) struct TypeNodeS {
    _nprep: i64,
    _nflag: i64,
    _ngarb: i64,
    _nsize_in: i64,
    _nsize_out: i64,
    _children: Vec<TypeNode>,
}

pub(crate) struct LambdaS {
    _input_type: TypeNode,
    _output_type: TypeNode,
}

pub(crate) fn build_type_judgement(node: Node) -> TypeNode {
    match node {
        Node::Program(_, _, _) => todo!(),
        Node::Number(val) => TypeNode::ValueExpr(val),
        Node::U3(_) => todo!(),
        Node::Rapply(_) => todo!(),
        Node::Array(_, size) => TypeNode::TypeExpr(TypeNodeS {
            // ignore subnode typing for now
            _nprep: 0,
            _nflag: 0,
            _ngarb: 0,
            _nsize_in: size,
            _nsize_out: size,
            _children: vec![],
        }),
        Node::Ctrl(_) => todo!(),
        Node::Ident(_) => todo!(),
        Node::Rphase(_) => todo!(),
        Node::Types(_) => todo!(),
        Node::Lambda(_, _) => todo!(),
    }
}

pub(crate) enum _Gate {
    Unit,
    ClassicalVar,
    QuantumVar,
    PurePair,
    Ctrl,
    PureApp,
    PurePerm, // no need to use this?
    Gate,
    Left,
    Right,
    PureAbs, // ???
    Rphase,

    Erase,
    
}

pub(crate) fn _assemble_output() {}
