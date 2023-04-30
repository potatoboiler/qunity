use nom::{
    branch::alt,
    bytes::complete::{tag, take},
    character::complete::{anychar, char, multispace0, none_of},
    combinator::{map, map_opt, map_res, value, verify},
    error::ParseError,
    multi::separated_list0,
    number::complete::double,
    sequence::{delimited, preceded, separated_pair},
    IResult, Parser,
};

// Compiler types
struct List {
    buffer: Vec<Expr>,
}
enum Prog {
    U3(Box<(Real, Real, Real)>),
    Left(Box<(Type, Type)>),
    Right(Box<(Type, Type)>),
    Lambda(Box<(Expr, Type, Expr)>),
    Rphase(Box<(Type, Expr, Real, Real)>),
}
enum Expr {
    Null,
    Var(String), // Variable(name: String)
    QPair(Box<(Expr, Expr)>),
    Ctrl(Box<(Expr, Type, List, Type)>),
    Try(Box<(Expr, Expr)>),
    Apply(Box<(Prog, Expr)>),
}

enum Z {}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Type {
    Void,
    Qunit,
    Superpos(Box<(Type, Type)>), // sum type
    Joint(Box<(Type, Type)>),    // product type
}

lazy_static! {
    static ref BIT: Type = Type::Superpos(Box::new((Type::Qunit, Type::Qunit)));
    static ref ZERO: Type = BIT.left();
    static ref ONE: Type = BIT.right();
}

impl Type {
    fn left(&self) -> Self {
        match self {
            Self::Superpos(p) => p.0.clone(),
            _ => panic!(),
        }
    }
    fn right(&self) -> Self {
        match self {
            Self::Superpos(p) => p.1.clone(),
            _ => panic!(),
        }
    }
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

struct Constant;

// Compiler internals
struct Context {}
impl Context {
    fn merge(&self, other: &Self) -> Self {
        todo!()
    }
}

trait Visitable<T> {
    fn visit(&self) -> T {
        todo!()
    }
}

fn nom_parse() {}

fn expr(input: &str) -> IResult<&'static str, Node> {
    todo!()
}

fn real(input: &str) -> IResult<&'static str, Node> {
    todo!()
}

fn prog(input: &str) -> IResult<&'static str, Node> {
    // alt()
    todo!()
}

struct Node;
