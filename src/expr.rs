pub enum Expr {
    Add(Box<Expr>, Term),
    Sub(Box<Expr>, Term),
    Term(Term),
}

pub enum Term {
    Var(String),
    Abs(String, Type, Box<Term>),
    App(Box<Term>, Box<Term>),
    Int(isize),
}

pub enum Type {
    Int,
    Arr(Box<Type>, Box<Type>),
}
