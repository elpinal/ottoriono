#[derive(Debug, PartialEq)]
pub enum Expr {
    Add(Box<Expr>, Term),
    Sub(Box<Expr>, Term),
    Term(Term),
}

#[derive(Debug, PartialEq)]
pub enum Term {
    Var(String),
    Abs(String, Type, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Int(isize),
}

#[derive(Debug, PartialEq)]
pub enum Type {
    Int,
    Arr(Box<Type>, Box<Type>),
}

impl Term {
    pub fn app(e1: Expr, e2: Expr) -> Term {
        Term::App(Box::new(e1), Box::new(e2))
    }
}

impl Type {
    pub fn arr(t1: Type, t2: Type) -> Type {
        Type::Arr(Box::new(t1), Box::new(t2))
    }
}
