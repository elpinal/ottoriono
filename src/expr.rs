use std::fmt;

#[derive(Debug, PartialEq)]
pub enum Expr {
    Add(Box<Expr>, Box<Expr>),
    Sub(Box<Expr>, Box<Expr>),
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

impl Expr {
    pub fn add(e1: Expr, e2: Expr) -> Expr {
        Expr::Add(Box::new(e1), Box::new(e2))
    }

    pub fn sub(e1: Expr, e2: Expr) -> Expr {
        Expr::Sub(Box::new(e1), Box::new(e2))
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use self::Type::*;
        match *self {
            Int => write!(f, "int"),
            Arr(ref t1, ref t2) => write!(f, "({} -> {})", t1, t2),
        }
    }
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
