#[macro_use]
use nom::{bytes::complete::tag, IResult};

struct List {
    buffer: Vec<Expr>,
}
enum Prog {}
enum Expr {
    Null,
    Var(String), // Variable(name: String)
    QPair(Box<(Expr, Expr)>),
    Ctrl(Box<(Expr, Type, List, Type)>),
    Try(Box<(Expr, Expr)>),
    Apply(Box<(Prog, Expr)>),
}

enum Z {}

enum Type {
    Void,
    Qunit,
    Superpos(Box<(Type, Type)>),
    Joint(Box<(Type, Type)>),
}

enum Real {
    Pi,
    Const(Z),
    Negate(Box<Real>),
    Plus(Box<(Real, Real)>),
    Times(Box<(Real, Real)>),
    Div(Box<(Real, Real)>),
    Sin(Box<Real>),
    Cos(Box<Real>),
    Tan(Box<Real>),
    Arcsin(Box<Real>),
    Arccos(Box<Real>),
    Arctan(Box<Real>),
    Exp(Box<Real>),
    Ln(Box<Real>),
    Sqrt(Box<Real>),
}

fn foo() {}
