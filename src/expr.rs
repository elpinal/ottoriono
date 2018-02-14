pub enum Expr {
    Add(Box<Expr>, Term),
    Sub(Box<Expr>, Term),
    Term(Term),
}

pub enum Term {
    Var(String),
    Abs(String, Type, Box<Expr>),
    App(Box<Expr>, Box<Expr>),
    Int(isize),
}

pub enum Type {
    Int,
    Arr(Box<Type>, Box<Type>),
}

impl Term {
    pub fn app(e1: Expr, e2: Expr) -> Term {
        Term::App(Box::new(e1), Box::new(e2))
    }
}
