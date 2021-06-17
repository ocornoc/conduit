use std::fmt::{Display, Formatter, Result as FmtResult};
mod level;
use level::*;

pub type DeBruijn = u32;
pub type GlobalDef = u32;

macro_rules! ctors_un {
    ($($name:ident => $e:expr),* $( ,)?) => {
        $(
            #[allow(dead_code)]
            pub fn $name(self) -> Self {
                $e(Box::new(self))
            }
        )*
    };
}

macro_rules! ctors_bi {
    ($($name:ident => $arg:ident => $e:expr),* $( ,)?) => {
        $(
            #[allow(dead_code)]
            pub fn $name(self, $arg: Self) -> Self {
                $e(Box::new(self), Box::new($arg))
            }
        )*
    };
}

#[derive(Debug, PartialEq, Clone)]
pub enum Term {
    Sort(LevelVar),
    Bound(DeBruijn),
    Free(GlobalDef),
    Lam(Box<Term>, Box<Term>),
    Pi(Box<Term>, Box<Term>),
    App(Box<Term>, Box<Term>),
    SelfLam(Box<Term>),
}

impl Term {
    ctors_un! {
        slam => Term::SelfLam,
    }

    ctors_bi! {
        lam => e => Term::Lam,
        pi => e => Term::Pi,
        app => r => Term::App,
    }

    pub fn shift_up(&mut self, by: DeBruijn, cutoff: DeBruijn) {
        match self {
            Term::Sort(_) | Term::Free(_) => (),
            Term::Bound(db) => if *db >= cutoff {
                *db += by;
            },
            Term::Lam(t, e) | Term::Pi(t, e) => {
                t.shift_up(by, cutoff);
                e.shift_up(by, cutoff + 1);
            },
            Term::App(l, r) => {
                l.shift_up(by, cutoff);
                r.shift_up(by, cutoff);
            },
            _ => todo!(),
        }
    }

    pub fn shift_down(&mut self, by: DeBruijn, cutoff: DeBruijn) {
        match self {
            Term::Sort(_) | Term::Free(_) => (),
            Term::Bound(db) => if *db >= cutoff {
                //*db -= by;
                *db = db.checked_sub(by).unwrap();
            },
            Term::Lam(t, e) | Term::Pi(t, e) => {
                t.shift_down(by, cutoff);
                e.shift_down(by, cutoff + 1);
            },
            Term::App(l, r) => {
                l.shift_down(by, cutoff);
                r.shift_down(by, cutoff);
            },
            _ => todo!(),
        }
    }

    pub fn subst(&mut self, new: &Term, i: DeBruijn) {
        match self {
            Term::Sort(_) | Term::Free(_) => (),
            Term::Bound(db) => if *db == i {
                self.clone_from(new);
            },
            Term::Lam(t, e) | Term::Pi(t, e) => {
                t.subst(new, i);
                e.subst(new, i + 1);
            },
            Term::App(l, r) => {
                l.subst(new, i);
                r.subst(new, i);
            },
            _ => todo!(),
        }
    }

    pub fn is_sort(&self) -> bool {
        matches!(self, Term::Sort(_))
    }
}

#[derive(Debug, Default, PartialEq, Clone)]
pub struct Closure {
    pub terms: Vec<(Term, Term)>,
    pub ctors: Vec<(LevelVar, Term)>,
}

impl Closure {
    pub fn shift_up(&mut self, by: DeBruijn, cutoff: DeBruijn) {
        for (ty, term) in &mut self.terms {
            ty.shift_up(by, cutoff);
            term.shift_up(by, cutoff);
        }

        for (_, ty) in &mut self.ctors {
            ty.shift_up(by, cutoff);
        }
    }

    pub fn shift_down(&mut self, by: DeBruijn, cutoff: DeBruijn) {
        for (ty, term) in &mut self.terms {
            ty.shift_down(by, cutoff);
            term.shift_down(by, cutoff);
        }

        for (_, ty) in &mut self.ctors {
            ty.shift_down(by, cutoff);
        }
    }

    pub fn subst(&mut self, new: &Term, i: DeBruijn) {
        for (ty, term) in &mut self.terms {
            ty.subst(new, i);
            term.subst(new, i);
        }

        for (_, ty) in &mut self.terms {
            ty.subst(new, i);
        }
    }
}

#[derive(Debug, Default, Clone)]
pub struct GlobalContext {
    levels: LevelSystem,
    pub defs: Vec<(Term, Term)>,
    tyctx: Vec<Term>,
}

impl GlobalContext {
    pub fn fresh(&mut self) -> LevelVar {
        self.levels.fresh_level(0)
    }

    pub fn sort(&mut self) -> Term {
        Term::Sort(self.fresh())
    }

    pub fn sort_at_least(&mut self, offset: u32) -> Term {
        Term::Sort(self.levels.fresh_level(offset as i32))
    }

    pub fn sort_at_most(&mut self, offset: u32) -> Term {
        let level = self.levels.fresh_level(0);
        self.levels.add_le_constraint(level, 0, LevelSystem::bottom(), offset as i32);
        Term::Sort(level)
    }

    pub fn sort_eq(&mut self, offset: u32) -> Term {
        let level = self.levels.fresh_level(offset as i32);
        self.levels.add_eq_constraint(level, 0, LevelSystem::bottom(), offset as i32);
        Term::Sort(level)
    }

    pub fn assert_le(&mut self, l: &Term, r: &Term) -> bool {
        match (l, r) {
            (&Term::Sort(l), &Term::Sort(r)) => {
                self.levels.add_le_constraint(l, 0, r, 0);
                true
            },
            (Term::Pi(lt, lb), Term::Pi(rt, rb)) => {
                self.assert_le(rt, lt) && self.assert_le(lb, rb)
            },
            _ => todo!(),
            (l, r) => l == r,
        }
    }

    pub fn assert_lt(&mut self, l: &Term, r: &Term) -> bool {
        match (l, r) {
            (&Term::Sort(l), &Term::Sort(r)) => {
                self.levels.add_lt_constraint(l, 0, r, 0);
                true
            },
            (Term::Pi(lt, lb), Term::Pi(rt, rb)) => {
                self.assert_lt(rt, lt) && self.assert_lt(lb, rb)
            },
            _ => todo!(),
            (l, r) => l == r,
        }
    }

    fn typecheck_normalize(&mut self, t: &Term) -> Option<Term> {
        let t = self.typecheck_aux(t)?;
        Some(self.normalize(t))
    }

    fn typecheck_aux(&mut self, t: &Term) -> Option<Term> {
        match t {
            &Term::Sort(lvl) => {
                let newlvl = self.levels.fresh_level(0);
                self.levels.add_lt_constraint(lvl, 0, newlvl, 0);
                Some(Term::Sort(newlvl))
            },
            &Term::Bound(db) => Some(self.tyctx[self.tyctx.len() - db as usize - 1].clone()),
            &Term::Free(def) => Some(self.defs[def as usize].0.clone()),
            Term::Lam(t, e) => {
                if !self.typecheck_normalize(t)?.is_sort() {
                    println!("t wasn't sort in lam");
                    return None;
                }

                self.tyctx.push(t.as_ref().clone());
                let et = self.typecheck_normalize(e)?;
                self.tyctx.pop();
                Some(Term::Pi(t.clone(), Box::new(et)))
            },
            Term::Pi(t, e) => {
                let tlvl = if let Term::Sort(lvl) = self.typecheck_normalize(t)? {
                    lvl
                } else {
                    println!("t wasn't sort in pi");
                    return None;
                };

                self.tyctx.push(t.as_ref().clone());
                let elvl = if let Term::Sort(lvl) = self.typecheck_normalize(e)? {
                    lvl
                } else {
                    println!("e wasn't sort in pi");
                    return None;
                };
                self.tyctx.pop();
                let newlvl = self.fresh();
                self.levels.add_le_constraint(tlvl, 0, newlvl, 0);
                self.levels.add_le_constraint(elvl, 0, newlvl, 0);
                Some(Term::Sort(newlvl))
            },
            Term::App(l, r) => {
                let (tl, etl) = if let Term::Pi(tl, etl) = self.typecheck_normalize(l)? {
                    (*tl, *etl)
                } else {
                    println!("l wasn't pi in app");
                    return None;
                };

                println!("in app:\nl: {:?}\nr: {:?}", l, r);
                let rt = self.typecheck_normalize(r)?;
                if self.assert_le(&rt, &tl) {
                    Some(etl)
                } else {
                    println!(
                        "r didn't have l arg type in app\nl arg ty: {:?}\nr: {:?}\nr ty: {:?}",
                        tl,
                        r,
                        rt,
                    );
                    None
                }
            },
            _ => todo!(),
        }
    }

    pub fn typecheck(&mut self, t: &Term) -> Option<Term> {
        let t = self.typecheck_normalize(t)?;
        if self.levels.is_consistent() {
            Some(t)
        } else {
            println!("inconsistent levels");
            None
        }
    }

    pub fn typecheck_defs(&mut self) -> bool {
        let defs = self.defs.clone();
        for (mut ty, t) in defs {
            if let Some(mut real_ty) = self.typecheck_aux(&t) {
                self.normalize_in_place(&mut real_ty);
                self.normalize_in_place(&mut ty);
                if !self.assert_le(&real_ty, &ty) {
                    return false;
                }
            } else {
                return false;
            }
        }

        true
    }

    pub fn normalize_in_place(&self, ot: &mut Term) {
        match ot {
            Term::Sort(_) | Term::Bound(_) | Term::Free(_) => (),
            Term::Lam(t, e) | Term::Pi(t, e) => {
                self.normalize_in_place(t);
                self.normalize_in_place(e);
            },
            Term::App(l, r) => {
                self.normalize_in_place(l);
                self.normalize_in_place(r);

                match l.as_mut() {
                    Term::Lam(t, e) | Term::Pi(t, e) => {
                        e.subst(t.as_ref(), 0);
                        e.shift_down(1, 1);
                        *ot = e.as_ref().clone();
                    },
                    _ => (),
                }
            },
            _ => todo!(),
        }
    }

    pub fn normalize(&self, mut t: Term) -> Term {
        self.normalize_in_place(&mut t);
        t
    }
}

impl Display for GlobalContext {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(&self.levels, f)
    }
}
