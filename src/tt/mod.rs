use std::fmt::{Display, Formatter, Result as FmtResult};
use std::error::Error;
mod level;
use level::*;

pub type DeBruijn = u32;
pub type SDeBruijn = i32;
pub type GlobalDef = u32;
pub type TorN = u16;

macro_rules! default {
    ($default:tt, $_:tt, $real:tt $(, )?) => {
        $real
    };
    ($default:tt,, $_:tt $(, )?) => {
        $default
    };
    ($default:tt, $real:tt $(, )?) => {
        $real
    };
    ($default:tt $(, )?) => {
        $default
    };
}

macro_rules! ctors {
    ($($name:ident : $p:expr $(=> $arg:ident $(: $ty:ty = $e:expr)?)*),* $( ,)?) => {
        $(
            #[allow(dead_code)]
            pub fn $name(self $(, $arg: default!(Self, $($ty)?))*) -> Self {
                $p(Box::new(self) $(, default!((Box::new($arg).into()), $($ty, $e)?))*)
            }
        )*
    };
}

#[derive(Debug, PartialEq, Clone, Default)]
pub struct TyArgs(pub Vec<Ty>);

impl TyArgs {
    pub fn shift_tm(&mut self, by: SDeBruijn, cutoff: &mut DeBruijn) {
        for arg in &mut self.0 {
            arg.shift_tm(by, *cutoff);
            *cutoff += 1;
        }
    }

    pub fn shift_ty(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        for arg in &mut self.0 {
            arg.shift_ty(by, cutoff);
        }
    }

    pub fn subst_tm(&mut self, new: &Term, i: &mut DeBruijn) {
        for arg in &mut self.0 {
            arg.subst_tm(new, *i);
            *i += 1;
        }
    }

    pub fn subst_ty(&mut self, new: &Ty, i: DeBruijn) {
        for arg in &mut self.0 {
            arg.subst_ty(new, i);
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Subst {
    pub args: TyArgs,
    pub out: Vec<Term>,
}

impl Subst {
    fn shift_out_tm(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        for t in &mut self.out {
            t.shift_tm(by, cutoff);
        }
    }

    pub fn shift_tm(&mut self, by: SDeBruijn, cutoff: &mut DeBruijn) {
        self.args.shift_tm(by, cutoff);
        self.shift_out_tm(by, *cutoff);
    }

    fn shift_out_ty(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        for t in &mut self.out {
            t.shift_ty(by, cutoff);
        }
    }

    pub fn shift_ty(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        self.args.shift_ty(by, cutoff);
        self.shift_out_ty(by, cutoff);
    }

    pub fn subst_tm(&mut self, new: &Term, i: &mut DeBruijn) {
        self.args.subst_tm(new, i);

        for t in &mut self.out {
            t.subst_tm(new, *i);
        }
    }

    pub fn subst_ty(&mut self, new: &Ty, i: DeBruijn) {
        self.args.subst_ty(new, i);

        for t in &mut self.out {
            t.subst_ty(new, i);
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct SubstData {
    pub subst: Subst,
    pub data: Ty,
}

impl SubstData {
    pub fn shift_tm(&mut self, by: SDeBruijn, mut cutoff: DeBruijn) {
        self.subst.shift_tm(by, &mut cutoff);
        self.data.shift_tm(by, cutoff);
    }

    pub fn shift_ty(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        self.subst.shift_ty(by, cutoff);
        self.data.shift_ty(by, cutoff);
    }

    pub fn subst_tm(&mut self, new: &Term, mut i: DeBruijn) {
        self.subst.subst_tm(new, &mut i);
        self.data.subst_tm(new, i);
    }

    pub fn subst_ty(&mut self, new: &Ty, i: DeBruijn) {
        self.subst.subst_ty(new, i);
        self.data.subst_ty(new, i);
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Ind {
    pub args: TyArgs,
    /// The type of `out` must be `args` for all subs
    pub ctors: Vec<SubstData>,
}

impl Ind {
    pub fn shift_tm(&mut self, by: SDeBruijn, mut cutoff: DeBruijn) {
        let orig = cutoff;
        self.args.shift_tm(by, &mut cutoff);

        for ctor in &mut self.ctors {
            ctor.shift_tm(by, orig);
        }
    }

    pub fn shift_ty(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        self.args.shift_ty(by, cutoff);

        for ctor in &mut self.ctors {
            ctor.shift_ty(by, cutoff + 1);
        }
    }

    pub fn subst_tm(&mut self, new: &Term, mut i: DeBruijn) {
        let orig = i;
        self.args.subst_tm(new, &mut i);

        for ctor in &mut self.ctors {
            ctor.subst_tm(new, orig);
        }
    }

    pub fn subst_ty(&mut self, new: &Ty, i: DeBruijn) {
        self.args.subst_ty(new, i);

        for ctors in &mut self.ctors {
            ctors.subst_ty(new, i + 1);
        }
    }

    fn reduce_tm(&mut self) {
        for arg in &mut self.args.0 {
            arg.reduce();
        }

        for SubstData { subst: Subst { args, out }, data } in &mut self.ctors {
            for arg in &mut args.0 {
                arg.reduce();
            }

            for t in out {
                t.reduce();
            }

            data.reduce();
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct Coind {
    pub args: TyArgs,
    /// The type of `out` must be `args` for all subs
    pub dtors: Vec<SubstData>,
}

impl Coind {
    pub fn shift_tm(&mut self, by: SDeBruijn, mut cutoff: DeBruijn) {
        let orig = cutoff;
        self.args.shift_tm(by, &mut cutoff);

        for dtor in &mut self.dtors {
            dtor.shift_tm(by, orig);
        }
    }

    pub fn shift_ty(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        self.args.shift_ty(by, cutoff);

        for dtor in &mut self.dtors {
            dtor.shift_ty(by, cutoff + 1);
        }
    }

    pub fn subst_tm(&mut self, new: &Term, mut i: DeBruijn) {
        let orig = i;
        self.args.subst_tm(new, &mut i);

        for dtor in &mut self.dtors {
            dtor.subst_tm(new, orig);
        }
    }

    pub fn subst_ty(&mut self, new: &Ty, i: DeBruijn) {
        self.args.subst_ty(new, i);

        for dtors in &mut self.dtors {
            dtors.subst_ty(new, i + 1);
        }
    }

    fn reduce_tm(&mut self) {
        for arg in &mut self.args.0 {
            arg.reduce();
        }

        for SubstData { subst: Subst { args, out }, data } in &mut self.dtors {
            for arg in &mut args.0 {
                arg.reduce();
            }

            for t in out {
                t.reduce();
            }

            data.reduce();
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Ty {
    Sort(LevelVar),
    BoundTy(DeBruijn),
    Raise(Term),
    Unit,
    App(Box<Ty>, Term),
    Abs(Box<Ty>, Box<Ty>),
    Ind(Ind),
    Coind(Coind),
}

impl Ty {
    ctors! {
        app: Ty::App => r: Term = r,
        abs: Ty::Abs => arg,
    }

    pub fn shift_tm(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        match self {
            Ty::Sort(_) | Ty::Unit | Ty::BoundTy(_) => (),
            Ty::Raise(t) => {
                t.shift_tm(by, cutoff);
            },
            Ty::App(l, r) => {
                l.shift_tm(by, cutoff);
                r.shift_tm(by, cutoff);
            },
            Ty::Abs(t, e) => {
                t.shift_tm(by, cutoff);
                e.shift_tm(by, cutoff + 1);
            },
            Ty::Ind(ind) => {
                ind.shift_tm(by, cutoff);
            },
            Ty::Coind(coind) => {
                coind.shift_tm(by, cutoff);
            },
        }
    }

    pub fn shift_ty(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        match self {
            Ty::Sort(_) | Ty::Unit => (),
            Ty::BoundTy(db) => if *db >= cutoff {
                let temp = (*db as SDeBruijn) + by;
                debug_assert!(temp >= 0);
                *db = temp as DeBruijn;
            },
            Ty::Raise(t) => {
                t.shift_ty(by, cutoff);
            },
            Ty::App(l, r) => {
                l.shift_ty(by, cutoff);
                r.shift_ty(by, cutoff);
            },
            Ty::Abs(t, e) => {
                t.shift_ty(by, cutoff);
                e.shift_ty(by, cutoff);
            },
            Ty::Ind(ind) => {
                ind.shift_ty(by, cutoff);
            },
            Ty::Coind(coind) => {
                coind.shift_ty(by, cutoff);
            },
        }
    }

    pub fn subst_tm(&mut self, new: &Term, i: DeBruijn) {
        match self {
            Ty::Sort(_) | Ty::BoundTy(_) | Ty::Unit => (),
            Ty::Raise(t) => {
                t.subst_tm(new, i);
            },
            Ty::App(l, r) => {
                l.subst_tm(new, i);
                r.subst_tm(new, i);
            },
            Ty::Abs(t, e) => {
                t.subst_tm(new, i);
                e.subst_tm(new, i + 1);
            },
            Ty::Ind(ind) => {
                ind.subst_tm(new, i);
            },
            Ty::Coind(coind) => {
                coind.subst_tm(new, i);
            },
        }
    }

    pub fn subst_ty(&mut self, new: &Ty, i: DeBruijn) {
        match self {
            Ty::Sort(_) | Ty::Unit => (),
            &mut Ty::BoundTy(db) => if db == i {
                *self = new.clone();
            },
            Ty::Raise(t) => {
                t.subst_ty(new, i);
            },
            Ty::App(l, r) => {
                l.subst_ty(new, i);
                r.subst_ty(new, i);
            },
            Ty::Abs(t, e) => {
                t.subst_ty(new, i);
                e.subst_ty(new, i);
            },
            Ty::Ind(ind) => {
                ind.subst_ty(new, i);
            },
            Ty::Coind(coind) => {
                coind.subst_ty(new, i);
            },
        }
    }

    pub fn reduce(&mut self) {
        match self {
            Ty::Sort(_) | Ty::Unit | Ty::BoundTy(_) => (),
            Ty::Raise(t) => {
                t.reduce();
                if let Term::Lower(t) = t {
                    *self = t.as_ref().clone();
                }
            },
            Ty::App(l, r) => {
                l.reduce();
                r.reduce();
                match l.as_mut() {
                    Ty::Ind(Ind { args, .. }) | Ty::Coind (Coind { args, .. }) => {
                        args.0.remove(0);
                        l.subst_tm(r, 0);
                        l.shift_tm(-1, 1);
                        *self = l.as_ref().clone();
                    },
                    _ => (),
                }
            },
            Ty::Abs(t, e) => {
                t.reduce();
                e.reduce();
            },
            Ty::Ind(Ind { args, ctors: tors }) | Ty::Coind(Coind { args, dtors: tors }) => {
                for arg in &mut args.0 {
                    arg.reduce();
                }

                for SubstData { subst: Subst { args, out }, data } in tors {
                    for arg in &mut args.0 {
                        arg.reduce()
                    }
                    data.reduce();
                    for t in out {
                        t.reduce();
                    }
                }
            },
        }
    }
}

impl From<Ind> for Ty {
    fn from(i: Ind) -> Self {
        Ty::Ind(i)
    }
}

impl From<Coind> for Ty {
    fn from(c: Coind) -> Self {
        Ty::Coind(c)
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum Term {
    BoundTm(DeBruijn),
    Lower(Box<Ty>),
    Star,
    App(Box<Term>, Box<Term>),
    Ctor(Ind, TorN),
    Elim(Coind, TorN),
    Iter { ind: Ind, out: Vec<Term>, out_ty: Box<Ty> },
    Coiter { coind: Coind, args: Vec<Term>, arg_ty: Box<Ty> },
}

impl Term {
    ctors! {
        app: Term::App => r,
    }

    pub fn shift_tm(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        match self {
            Term::Star => (),
            Term::BoundTm(db) => if *db >= cutoff {
                let temp = (*db as SDeBruijn) + by;
                debug_assert!(temp >= 0);
                *db = temp as DeBruijn;
            },
            Term::Lower(ty) => {
                ty.shift_tm(by, cutoff);
            },
            Term::App(l, r) => {
                l.shift_tm(by, cutoff);
                r.shift_tm(by, cutoff);
            },
            Term::Ctor(ind, _) => {
                ind.shift_tm(by, cutoff);
            },
            Term::Elim(coind, _) => {
                coind.shift_tm(by, cutoff);
            },
            Term::Iter { ind, out, out_ty } => {
                ind.shift_tm(by, cutoff);
                out_ty.shift_tm(by, cutoff);

                for (i, t) in out.iter_mut().enumerate() {
                    t.shift_tm(by, cutoff + ind.ctors[i].subst.args.0.len() as u32);
                }
            },
            Term::Coiter { coind, args: arg, arg_ty } => {
                coind.shift_tm(by, cutoff);
                arg_ty.shift_tm(by, cutoff);

                for (i, t) in arg.iter_mut().enumerate() {
                    t.shift_tm(by, cutoff + coind.dtors[i].subst.args.0.len() as u32);
                }
            },
        }
    }

    pub fn shift_ty(&mut self, by: SDeBruijn, cutoff: DeBruijn) {
        match self {
            Term::BoundTm(_) | Term::Star => (),
            Term::Lower(ty) => {
                ty.shift_ty(by, cutoff);
            },
            Term::App(l, r) => {
                l.shift_ty(by, cutoff);
                r.shift_ty(by, cutoff);
            },
            Term::Ctor(ind, _) => {
                ind.shift_ty(by, cutoff);
            },
            Term::Elim(coind, _) => {
                coind.shift_ty(by, cutoff);
            },
            Term::Iter { ind, out, out_ty } => {
                ind.shift_ty(by, cutoff);
                out_ty.shift_ty(by, cutoff);

                for t in out {
                    t.shift_ty(by, cutoff);
                }
            },
            Term::Coiter { coind, args: arg, arg_ty } => {
                coind.shift_ty(by, cutoff);
                arg_ty.shift_ty(by, cutoff);

                for t in arg {
                    t.shift_ty(by, cutoff);
                }
            },
        }
    }

    pub fn subst_tm(&mut self, new: &Term, i: DeBruijn) {
        match self {
            Term::Star => (),
            &mut Term::BoundTm(db) => if db == i {
                *self = new.clone();
            },
            Term::Lower(ty) => {
                ty.subst_tm(new, i);
            },
            Term::App(l, r) => {
                l.subst_tm(new, i);
                r.subst_tm(new, i);
            },
            Term::Ctor(ind, _) => {
                ind.subst_tm(new, i);
            },
            Term::Elim(coind, _) => {
                coind.subst_tm(new, i);
            },
            Term::Iter { ind, out, out_ty } => {
                ind.subst_tm(new, i);
                out_ty.subst_tm(new, i);

                for (i, t) in out.iter_mut().enumerate() {
                    t.subst_tm(new, (i + ind.ctors[i].subst.args.0.len()) as DeBruijn);
                }
            },
            Term::Coiter { coind, args, arg_ty } => {
                coind.subst_tm(new, i);
                arg_ty.subst_tm(new, i);

                for (i, t) in args.iter_mut().enumerate() {
                    t.subst_tm(new, (i + coind.dtors[i].subst.args.0.len()) as DeBruijn);
                }
            },
        }
    }

    pub fn subst_ty(&mut self, new: &Ty, i: DeBruijn) {
        match self {
            Term::BoundTm(_) | Term::Star => (),
            Term::Lower(ty) => {
                ty.subst_ty(new, i);
            },
            Term::App(l, r) => {
                l.subst_ty(new, i);
                r.subst_ty(new, i);
            },
            Term::Ctor(ind, _) => {
                ind.subst_ty(new, i);
            },
            Term::Elim(coind, _) => {
                coind.subst_ty(new, i);
            },
            Term::Iter { ind, out, out_ty } => {
                ind.subst_ty(new, i);
                out_ty.subst_ty(new, i);

                for t in out {
                    t.subst_ty(new, i);
                }
            },
            Term::Coiter { coind, args: arg, arg_ty } => {
                coind.subst_ty(new, i);
                arg_ty.subst_ty(new, i);

                for t in arg {
                    t.subst_ty(new, i);
                }
            },
        }
    }

    fn get_tor_id(&self) -> TorN {
        match self {
            Term::App(l, _) => l.get_tor_id(),
            &Term::Ctor(_, n) | &Term::Elim(_, n) => n,
            _ => unreachable!(),
        }
    }

    fn get_ctor_data(&self) -> (TorN, &Self) {
        if let Term::App(l, r) = self {
            match l.as_ref() {
                Term::App(..) => l.get_ctor_data(),
                &Term::Ctor(Ind { ref args, .. }, n) if args.0.is_empty() => (n, r),
                _ => unreachable!(),
            }
        } else {
            unreachable!()
        }
    }

    pub fn reduce(&mut self) {
        match self {
            Term::BoundTm(_) | Term::Star => (),
            Term::Lower(ty) => {
                ty.reduce();
                if let Ty::Raise(t) = ty.as_mut() {
                    *self = t.clone();
                }
            },
            Term::App(l, r) => {
                l.reduce();
                r.reduce();
                match l.as_mut() {
                    Term::Iter { ind, out, .. } => if ind.args.0.is_empty() {
                        let (tor, data) = r.get_ctor_data();
                        let mut body = out.swap_remove(tor as usize);
                        body.subst_tm(data, 0);
                        body.shift_tm(-1, 1);
                        body.reduce();
                        *self = body;
                    } else {
                        ind.args.0.remove(0);
                        ind.subst_tm(r, 0);
                        ind.shift_tm(-1, 0);
                        ind.reduce_tm();
                        *self = l.as_mut().clone();
                    },
                    &mut Term::Ctor(ref mut ind, n)
                        if !ind.ctors[n as usize].subst.args.0.is_empty()
                    => {
                        let ctor = &mut ind.ctors[n as usize];
                        ctor.subst_tm(r, 0);
                        ctor.shift_tm(-1, 1);
                        ctor.subst.args.0.remove(0);

                        if ctor.subst.args.0.is_empty() {
                            for sarg in ctor.subst.out.clone().iter() {
                                ind.subst_tm(&sarg, 0);
                                ind.shift_tm(-1, 1);
                            }

                            ind.args.0 = Vec::new();
                        }

                        ind.reduce_tm();
                    },
                    Term::Ctor(ind, _) => {
                        ind.reduce_tm();
                    },
                    Term::Coiter { coind, args, arg_ty } => todo!(),
                    _ => (),
                }
            },
            Term::Ctor(ind, _) => {
                ind.reduce_tm();
            },
            Term::Elim(coind, _) => {
                coind.reduce_tm();
            },
            Term::Iter { ind, out, out_ty } => {
                for t in out {
                    t.reduce();
                }

                out_ty.reduce();
                ind.reduce_tm();
            },
            Term::Coiter { coind, args, arg_ty } => {
                for t in args {
                    t.reduce();
                }

                arg_ty.reduce();
                coind.reduce_tm();
            },
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub struct TermType {
    pub args: TyArgs,
    pub out: Ty,
}

impl From<Ty> for TermType {
    fn from(out: Ty) -> Self {
        TermType {
            args: TyArgs::default(),
            out,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum TermTypeErr {
    ExpectedFunction,
    NotFullyInit,
    ArgTypeMismatch,
    InvalidTorId,
    IterIndArgsMismatch,
}

impl Display for TermTypeErr {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            TermTypeErr::ExpectedFunction => write!(f, "expected a function"),
            TermTypeErr::NotFullyInit => write!(f, "type not fully initialized"),
            TermTypeErr::ArgTypeMismatch => write!(f, "argument type mismatched"),
            TermTypeErr::InvalidTorId => write!(f, "invalid ctor/dtor index"),
            TermTypeErr::IterIndArgsMismatch => write!(f,
                "inductive and iter type have mismatching type arguments",
            ),
        }
    }
}

impl Error for TermTypeErr {}

#[derive(Debug, PartialEq, Clone)]
pub struct TyType {
    pub args: TyArgs,
    pub out: LevelVar,
}

#[derive(Debug, PartialEq, Clone)]
pub enum TyTypeErr {
    ExpectedFunction,
    NotFullyInit,
    ArgTypeMismatch,
    SubstArgMismatch,
    RaiseNotSort,
}

impl Display for TyTypeErr {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            TyTypeErr::ExpectedFunction => write!(f, "expected a function"),
            TyTypeErr::NotFullyInit => write!(f, "type not fully initialized"),
            TyTypeErr::ArgTypeMismatch => write!(f, "argument type mismatched"),
            TyTypeErr::SubstArgMismatch => write!(
                f,
                "the number of args and terms in a subst mismatch",
            ),
            TyTypeErr::RaiseNotSort => write!(f, "raise term must return sort"),
        }
    }
}

impl Error for TyTypeErr {}

#[derive(Debug, PartialEq, Clone)]
pub enum TypeErr {
    TyTypeErr(TyTypeErr),
    TermTypeErr(TermTypeErr),
    BadUniverses,
}

impl Display for TypeErr {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        match self {
            TypeErr::TyTypeErr(e) => Display::fmt(e, f),
            TypeErr::TermTypeErr(e) => Display::fmt(e, f),
            TypeErr::BadUniverses => write!(f, "universe constraints unsatisfiable"),
        }
    }
}

impl Error for TypeErr {}

impl From<TermTypeErr> for TypeErr {
    fn from(e: TermTypeErr) -> Self {
        TypeErr::TermTypeErr(e)
    }
}

impl From<TyTypeErr> for TypeErr {
    fn from(e: TyTypeErr) -> Self {
        TypeErr::TyTypeErr(e)
    }
}

#[derive(Debug, Default, Clone)]
pub struct GlobalContext {
    levels: LevelSystem,
    ctx: Vec<TermType>,
    tyctx: Vec<TyType>,
}

impl GlobalContext {
    pub fn fresh(&mut self) -> LevelVar {
        self.levels.fresh_level(0)
    }

    pub fn sort(&mut self) -> Ty {
        Ty::Sort(self.fresh())
    }

    pub fn sort_at_least(&mut self, offset: u32) -> Ty {
        Ty::Sort(self.levels.fresh_level(offset as i32))
    }

    pub fn sort_at_most(&mut self, offset: u32) -> Ty {
        let level = self.levels.fresh_level(0);
        self.levels.add_le_constraint(level, 0, LevelSystem::bottom(), offset as i32);
        Ty::Sort(level)
    }

    pub fn sort_eq(&mut self, offset: u32) -> Ty {
        let level = self.levels.fresh_level(offset as i32);
        self.levels.add_eq_constraint(level, 0, LevelSystem::bottom(), offset as i32);
        Ty::Sort(level)
    }

    fn assert_le_aux_ty(&mut self, l: &Ty, r: &Ty) -> bool {
        match (l, r) {
            (&Ty::Sort(l), &Ty::Sort(r)) => {
                self.levels.add_le_constraint(l, 0, r, 0);
                true
            },
            (Ty::App(ll, lr), Ty::App(rl, rr)) =>
                self.assert_le_aux_ty(ll, rl) && self.assert_le_aux_tm(lr, rr),
            (Ty::Abs(lt, le), Ty::Abs(rt, re)) =>
                self.assert_le_aux_ty(lt, rt) && self.assert_le_aux_ty(le, re),
            (
                Ty::Ind(Ind { args: largs, ctors: ltors }),
                Ty::Ind(Ind { args: rargs, ctors: rtors }),
            ) => {
                if largs.0.len() != rargs.0.len() || ltors.len() != rtors.len() {
                    return false;
                }

                for (larg, rarg) in largs.0.iter().zip(&rargs.0) {
                    if !self.assert_le_aux_ty(larg, rarg) {
                        return false;
                    }
                }

                for (ltor, rtor) in ltors.iter().zip(rtors) {
                    if ltor.subst.args.0.len() != rtor.subst.args.0.len()
                        || ltor.subst.out.len() != rtor.subst.out.len()
                        || !self.assert_le_aux_ty(&ltor.data, &rtor.data)
                    {
                        return false;
                    }

                    for (larg, rarg) in ltor.subst.args.0.iter().zip(rtor.subst.args.0.iter()) {
                        if !self.assert_le_aux_ty(larg, rarg) {
                            return false;
                        }
                    }

                    for (l, r) in ltor.subst.out.iter().zip(rtor.subst.out.iter()) {
                        if !self.assert_le_aux_tm(l, r) {
                            return false;
                        }
                    }
                }

                true
            },
            (
                Ty::Coind(Coind { args: largs, dtors: ltors }),
                Ty::Coind(Coind { args: rargs, dtors: rtors }),
            ) => {
                if largs.0.len() != rargs.0.len() || ltors.len() != rtors.len() {
                    return false;
                }

                for (larg, rarg) in largs.0.iter().zip(&rargs.0) {
                    if !self.assert_le_aux_ty(larg, rarg) {
                        return false;
                    }
                }

                for (ltor, rtor) in ltors.iter().zip(rtors) {
                    if ltor.subst.args.0.len() != rtor.subst.args.0.len()
                        || ltor.subst.out.len() != rtor.subst.out.len()
                        || !self.assert_le_aux_ty(&ltor.data, &rtor.data)
                    {
                        return false;
                    }

                    for (larg, rarg) in ltor.subst.args.0.iter().zip(rtor.subst.args.0.iter()) {
                        if !self.assert_le_aux_ty(larg, rarg) {
                            return false;
                        }
                    }

                    for (l, r) in ltor.subst.out.iter().zip(rtor.subst.out.iter()) {
                        if !self.assert_le_aux_tm(r, l) { // is this appropriate for coind?
                            return false;
                        }
                    }
                }

                true
            },
            (l, r) => l == r,
        }
    }

    fn assert_le_aux_tm(&mut self, l: &Term, r: &Term) -> bool {
        match (l, r) {
            (Term::Lower(l), Term::Lower(r)) => self.assert_le_aux_ty(l, r),
            (Term::App(ll, lr), Term::App(rl, rr)) =>
                self.assert_le_aux_tm(ll, rl) && self.assert_le_aux_tm(lr, rr),
            (Term::Ctor(l, ln), Term::Ctor(r, rn)) =>
                // TODO: optimize out this clone by reading and forgetting
                ln == rn && self.assert_le_aux_ty(&Ty::Ind(l.clone()), &Ty::Ind(r.clone())),
            (Term::Elim(l, ln), Term::Elim(r, rn)) =>
                // TODO: optimize out this clone by reading and forgetting
                ln == rn && self.assert_le_aux_ty(&Ty::Coind(l.clone()), &Ty::Coind(r.clone())),
            // one day: (Term::Iter { ind, out, out_ty }, Term::Iter { ind, out, out_ty }) => todo!(),
            // one day: (Term::Coiter { coind, arg, arg_ty }, Term::Coiter { coind, arg, arg_ty }) => todo!(),
            (l, r) => l == r,
        }
    }

    pub fn assert_le_ty(&mut self, l: &Ty, r: &Ty) -> bool {
        let old_levels = self.levels.clone();
        if self.assert_le_aux_ty(l, r) {
            true
        } else {
            self.levels = old_levels;
            false
        }
    }

    fn typecheck_aux_ty(&mut self, ty: &Ty) -> Result<TyType, TypeErr> {
        match ty {
            &Ty::Sort(lvl) => Ok(TyType {
                args: TyArgs::default(),
                out: {
                    let new = self.fresh();
                    self.levels.add_lt_constraint(lvl, 0, new, 0);
                    new
                },
            }),
            &Ty::BoundTy(db) => Ok(self.tyctx[self.tyctx.len() - db as usize - 1].clone()),
            Ty::Raise(t) => {
                let mut tty = self.typecheck_aux_tm(t)?;
                tty.out.reduce();
                if let Ty::Sort(old) = tty.out {
                    let lvl = self.fresh();
                    self.levels.add_le_constraint(lvl, 0, old, 0);
                    Ok(TyType {
                        args: tty.args,
                        out: lvl,
                    })
                } else {
                    Err(TyTypeErr::RaiseNotSort.into())
                }
            },
            Ty::Unit => Ok(TyType {
                args: TyArgs::default(),
                out: self.fresh(),
            }),
            Ty::App(l, r) => {
                let mut lty = self.typecheck_aux_ty(l)?;
                let mut rty = self.typecheck_aux_tm(r)?;

                if lty.args.0.is_empty() {
                    return Err(TyTypeErr::ExpectedFunction.into());
                } else if !rty.args.0.is_empty() {
                    return Err(TyTypeErr::NotFullyInit.into());
                }

                let mut first = lty.args.0.remove(0);
                first.reduce();
                rty.out.reduce();
                if self.assert_le_ty(&rty.out, &first) {
                    Ok(lty)
                } else {
                    Err(TyTypeErr::ArgTypeMismatch.into())
                }
            },
            Ty::Abs(t, e) => {
                let tty = self.typecheck_aux_ty(ty)?;

                if !tty.args.0.is_empty() {
                    return Err(TyTypeErr::NotFullyInit.into());
                }

                self.tyctx.push(tty.clone());
                let mut ety = self.typecheck_aux_ty(e)?;
                self.tyctx.pop();
                ety.args.0.insert(0, t.as_ref().clone());

                Ok(TyType {
                    args: ety.args,
                    out: {
                        let lvl = self.fresh();
                        self.levels.add_lt_constraint(tty.out, 0, lvl, 0);
                        self.levels.add_lt_constraint(ety.out, 0, lvl, 0);
                        lvl
                    },
                })
            },
            Ty::Ind(Ind { args, ctors: tors }) | Ty::Coind(Coind { args, dtors: tors }) => {
                let lvl = self.fresh();
                let old_ctx_len = self.ctx.len();

                for arg in &args.0 {
                    let argty = self.typecheck_aux_ty(arg)?;
                    if !argty.args.0.is_empty() {
                        return Err(TyTypeErr::NotFullyInit.into());
                    }
                    self.levels.add_lt_constraint(argty.out, 0, lvl, 0);
                    //self.tyctx.push(argty);
                    self.ctx.push(arg.clone().into());
                }

                self.ctx.resize_with(old_ctx_len, rwft);
                let args_len = args.0.len();
                let args = args.0
                    .iter()
                    .cloned()
                    .map(|mut ty| {
                        ty.reduce();
                        ty
                    })
                    .collect::<Vec<_>>();
                let mut me = TyType {
                    args: TyArgs(args),
                    out: lvl,
                };

                self.tyctx.push(me.clone());
                for SubstData { subst: Subst { args: sargs, out }, data } in tors {
                    for (i, arg) in sargs.0.iter().enumerate() {
                        let argty = self.typecheck_aux_ty(arg)?;
                        if !argty.args.0.is_empty() {
                            return Err(TyTypeErr::NotFullyInit.into());
                        }
                        self.levels.add_lt_constraint(argty.out, 0, lvl, 0);
                        let mut out = arg.clone();
                        for prev in &sargs.0[..i] {
                            out.subst_ty(prev, 0);
                            out.shift_ty(-1, 1);
                        }
                        out.reduce();
                        self.ctx.push(out.into());
                    }

                    if out.len() != args_len {
                        return Err(TyTypeErr::SubstArgMismatch.into());
                    }

                    for (i, (arg, t)) in me.args.0.iter().zip(out).enumerate() {
                        let mut tty = self.typecheck(t)?;
                        debug_assert!(tty.args.0.is_empty());
                        tty.out.reduce();
                        let mut arg = arg.clone();
                        for prev in &me.args.0[..i] {
                            arg.subst_ty(prev, 0);
                            arg.shift_tm(-1, 1);
                        }
                        arg.reduce();
                        if !self.assert_le_ty(&arg, &tty.out) {
                            return Err(TyTypeErr::ArgTypeMismatch.into());
                        }
                    }

                    self.tyctx.push(me);
                    let dataty = self.typecheck_aux_ty(data)?;
                    if !dataty.args.0.is_empty() {
                        return Err(TermTypeErr::NotFullyInit.into())
                    }
                    self.levels.add_le_constraint(dataty.out, 0, lvl, 0);
                    me = self.tyctx.pop().unwrap();
                    self.ctx.resize_with(old_ctx_len, rwft);
                }

                self.tyctx.pop();
                Ok(me)
            }
        }
    }

    fn typecheck_aux_tm(&mut self, t: &Term) -> Result<TermType, TypeErr> {
        match t {
            &Term::BoundTm(db) => Ok(self.ctx[self.ctx.len() - db as usize - 1].clone()),
            Term::Lower(ty) => {
                let tyty = self.typecheck_aux_ty(ty)?;
                let lvl = self.fresh();
                self.levels.add_lt_constraint(tyty.out, 0, lvl, 0);
                Ok(TermType {
                    args: tyty.args,
                    out: Ty::Sort(lvl),
                })
            },
            Term::Star => Ok(Ty::Unit.into()),
            Term::App(l, r) => {
                let mut lty = self.typecheck_aux_tm(l)?;
                let mut rty = self.typecheck_aux_tm(r)?;

                if lty.args.0.is_empty() {
                    return Err(TermTypeErr::ExpectedFunction.into());
                } else if !rty.args.0.is_empty() {
                    return Err(TermTypeErr::NotFullyInit.into());
                }

                let mut first = lty.args.0.remove(0);
                first.reduce();
                rty.out.reduce();
                if self.assert_le_ty(&rty.out, &first) {
                    let mut db = 0;
                    lty.args.subst_tm(r, &mut db);
                    lty.args.shift_tm(-1, &mut 0);
                    lty.out.subst_tm(r, db);
                    lty.out.shift_tm(-1, db);
                    Ok(lty)
                } else {
                    Err(TermTypeErr::ArgTypeMismatch.into())
                }
            },
            &Term::Ctor(ref ind, n) => {
                self.typecheck_aux_ty(&Ty::Ind(ind.clone()))?;
                if ind.ctors.len() <= n as usize {
                    return Err(TermTypeErr::InvalidTorId.into());
                }

                let SubstData { mut subst, mut data } = ind.ctors[n as usize].clone();
                subst.shift_out_tm(1, 0);
                // TODO: optimize out this clone by reading and forgetting
                data.subst_ty(&Ty::Ind(ind.clone()), 0);
                data.shift_ty(-1, 1);
                subst.args.0.push(data);
                let mut ind = ind.clone();

                for mut t in subst.out {
                    t.shift_tm(1, 0);
                    ind.subst_tm(&t, 0);
                    ind.shift_tm(-1, 1);
                }

                Ok(TermType {
                    args: subst.args,
                    out: Ty::Ind(ind),
                })
            },
            &Term::Elim(ref coind, n) => {
                self.typecheck_aux_ty(&Ty::Coind(coind.clone()))?;
                if coind.dtors.len() <= n as usize {
                    return Err(TermTypeErr::InvalidTorId.into());
                }

                let SubstData { mut subst, mut data } = coind.dtors[n as usize].clone();
                subst.shift_out_tm(1, 0);
                // TODO: optimize out this clone by reading and forgetting
                data.subst_ty(&Ty::Coind(coind.clone()), 0);
                data.shift_ty(-1, 1);
                let mut coind = coind.clone();

                for t in subst.out {
                    coind.subst_tm(&t, 0);
                    coind.shift_tm(-1, 1);
                }

                subst.args.0.push(Ty::Coind(coind));

                Ok(TermType {
                    args: subst.args,
                    out: data,
                })
            },
            Term::Iter { ind, out, out_ty } => {
                let out_tyty = self.typecheck_aux_ty(out_ty)?;
                // todo: give ind.ctors.len() != out.len() own err
                if ind.args.0.len() != out_tyty.args.0.len() || ind.ctors.len() != out.len() {
                    return Err(TermTypeErr::IterIndArgsMismatch.into());
                }

                let mut args = TyArgs(Vec::with_capacity(ind.args.0.len()));

                for (argty, ty) in ind.args.0.iter().zip(out_tyty.args.0.iter()) {
                    let mut argty = argty.clone();
                    let mut ty = ty.clone();
                    argty.reduce();
                    ty.reduce();

                    if !self.assert_le_ty(&argty, &ty) {
                        return Err(TermTypeErr::IterIndArgsMismatch.into());
                    }

                    args.0.push(argty);
                }

                let old_ctx_len = self.ctx.len();

                for (SubstData { subst, data }, t) in ind.ctors.iter().zip(out.iter()) {
                    self.ctx.extend(subst.args.0.iter().cloned().map(|out| TermType {
                        args: TyArgs::default(),
                        out,
                    }));
                    let mut data = data.clone();
                    data.subst_ty(out_ty, 0);
                    data.shift_ty(-1, 1);
                    self.ctx.push(data.into());
                    let mut ty = self.typecheck_aux_tm(t)?;
                    ty.out.reduce();
                    debug_assert!(ty.args.0.is_empty());
                    let mut out_ty = out_ty.as_ref().clone();

                    for mut s in subst.out.iter().cloned() {
                        s.shift_tm(1, 0);
                        out_ty.subst_tm(&s, 1);
                        out_ty.shift_tm(-1, 2);
                    }

                    out_ty.reduce();

                    if !self.assert_le_ty(&ty.out, &out_ty) {
                        return Err(TermTypeErr::ArgTypeMismatch.into());
                    }

                    self.ctx.resize_with(old_ctx_len, rwft);
                }

                let arg = Ty::Ind(Ind {
                    args: TyArgs::default(),
                    ..ind.clone()
                });
                let mut out = out_ty.as_ref().clone();
                out.shift_tm(1, 0);
                args.0.push(arg);

                Ok(TermType {
                    args,
                    out,
                })
            },
            Term::Coiter { coind, args, arg_ty } => {
                let arg_tyty = self.typecheck_aux_ty(arg_ty)?;
                // todo: give ind.ctors.len() != out.len() own err
                if coind.args.0.len() != arg_tyty.args.0.len() || coind.dtors.len() != args.len() {
                    return Err(TermTypeErr::IterIndArgsMismatch.into());
                }

                let mut ci_args = TyArgs(Vec::with_capacity(coind.args.0.len()));

                for (argty, ty) in coind.args.0.iter().zip(arg_tyty.args.0.iter()) {
                    let mut argty = argty.clone();
                    let mut ty = ty.clone();
                    argty.reduce();
                    ty.reduce();

                    if !self.assert_le_ty(&argty, &ty) {
                        return Err(TermTypeErr::IterIndArgsMismatch.into());
                    }

                    ci_args.0.push(argty);
                }

                let old_ctx_len = self.ctx.len();

                for (SubstData { subst, data }, t) in coind.dtors.iter().zip(args.iter()) {
                    self.ctx.extend(subst.args.0.iter().cloned().map(|out| TermType {
                        args: TyArgs::default(),
                        out,
                    }));
                    let mut arg = arg_ty.as_ref().clone();

                    for s in subst.out.iter() {
                        arg.subst_tm(s, 0);
                        arg.shift_tm(-1, 1);
                    }
                    self.ctx.push(arg.into());
                    let mut ty = self.typecheck_aux_tm(t)?;
                    ty.out.reduce();
                    debug_assert!(ty.args.0.is_empty());
                    let mut data = data.clone();
                    data.subst_ty(arg_ty, 0);
                    data.shift_ty(-1, 1);
                    data.reduce();

                    if !self.assert_le_ty(&ty.out, &data) {
                        return Err(TermTypeErr::ArgTypeMismatch.into());
                    }

                    self.ctx.resize_with(old_ctx_len, rwft);
                }

                let out = Ty::Coind(Coind {
                    args: TyArgs::default(),
                    ..coind.clone()
                });
                let mut arg = arg_ty.as_ref().clone();
                arg.shift_tm(1, 0);
                ci_args.0.push(arg);

                Ok(TermType {
                    args: ci_args,
                    out,
                })
            },
        }
    }

    pub fn typecheck(&mut self, t: &Term) -> Result<TermType, TypeErr> {
        let ty = self.typecheck_aux_tm(t)?;
        if self.levels.is_consistent() {
            Ok(ty)
        } else {
            Err(TypeErr::BadUniverses)
        }
    }

    pub fn typecheck_ty(&mut self, ty: &Ty) -> Result<TyType, TypeErr> {
        let tyty = self.typecheck_aux_ty(ty)?;
        if self.levels.is_consistent() {
            Ok(tyty)
        } else {
            Err(TypeErr::BadUniverses)
        }
    }
}

impl Display for GlobalContext {
    fn fmt(&self, f: &mut Formatter) -> FmtResult {
        Display::fmt(&self.levels, f)
    }
}

#[cold]
fn resize_with_f() -> ! {
    if cfg!(debug_assertions) {
        unreachable!("somehow we LOST length");
    } else {
        unsafe { std::hint::unreachable_unchecked(); }
    }
}

#[cold]
fn rwft<T>() -> T {
    resize_with_f()
}
