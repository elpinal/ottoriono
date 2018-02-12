pub enum Expr {
    Add(Box<Expr>, Term),
    Sub(Box<Expr>, Term),
    Term(Term),
}

pub enum Term {
    Var(usize, usize),
    Abs(String, Box<Term>),
    App(Box<Term>, Box<Term>),
    Int(isize),
}
