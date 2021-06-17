mod tt;
use tt::*;

fn geneq(ctx: &mut GlobalContext) -> Result<(), TypeErr> {
    let eq = Ind {
        args: TyArgs(vec![ctx.sort(), Ty::Raise(Term::BoundTm(0)), Ty::Raise(Term::BoundTm(1))]),
        ctors: vec![SubstData {
            subst: Subst {
                args: TyArgs(vec![ctx.sort(), Ty::Raise(Term::BoundTm(0))]),
                out: vec![Term::BoundTm(1), Term::BoundTm(0), Term::BoundTm(0)],
            },
            data: Ty::Unit,
        }],
    };
    ctx.typecheck_ty(&Ty::Ind(eq.clone()))?;
    let ctor = Term::Ctor(eq.clone(), 0);
    println!("{:#?}", ctx.typecheck(&ctor)?);
    let ctor = ctor.app(Term::Lower(Box::new(Ty::Unit)));
    println!("{:#?}", ctx.typecheck(&ctor)?);
    let ctor = ctor.app(Term::Star).app(Term::Star);
    println!("{:#?}", ctx.typecheck(&ctor)?);
    Ok(())
}

fn main() -> Result<(), TypeErr> {
    let mut ctx = GlobalContext::default();
    let nat = Ind {
        args: TyArgs::default(),
        ctors: vec![
            SubstData {
                subst: Subst {
                    args: TyArgs::default(),
                    out: Vec::new(),
                },
                data: Ty::Unit,
            },
            SubstData {
                subst: Subst {
                    args: TyArgs::default(),
                    out: Vec::new(),
                },
                data: Ty::BoundTy(0),
            },
        ],
    };
    println!("{:#?}", ctx.typecheck_ty(&Ty::Ind(nat.clone()))?);
    let term = Term::Ctor(nat.clone(), 1);
    println!("{:#?}", ctx.typecheck(&term)?);
    let mut pred = Term::Iter {
        ind: nat.clone(),
        out: vec![
            Term::Ctor(nat.clone(), 0).app(Term::BoundTm(0)),
            Term::BoundTm(0),
        ],
        out_ty: Box::new(Ty::Ind(nat.clone())),
    }.app(
        Term::Ctor(nat.clone(), 1)
            .app(Term::Ctor(nat.clone(), 0).app(Term::Star)),
    );
    println!("{:#?}", ctx.typecheck(&pred)?);
    println!("simplifying");
    println!("{:#?}", pred);
    pred.reduce();
    println!("{:#?}", pred);
    let mut succ = Term::Iter {
        ind: nat.clone(),
        out: vec![
            Term::Ctor(nat.clone(), 0).app(Term::BoundTm(0)),
            Term::BoundTm(0),
        ],
        out_ty: Box::new(Ty::Ind(nat.clone())),
    }.app(
        Term::Ctor(nat.clone(), 1)
            .app(Term::Ctor(nat.clone(), 0).app(Term::Star)),
    );
    println!("{:#?}", ctx.typecheck(&succ)?);
    println!("simplifying");
    println!("{:#?}", succ);
    succ.reduce();
    println!("{:#?}", succ);
    let eq = Ind {
        args: TyArgs(vec![Ty::Ind(nat.clone()), Ty::Ind(nat.clone())]),
        ctors: vec![SubstData {
            subst: Subst {
                args: TyArgs(vec![Ty::Ind(nat.clone())]),
                out: vec![Term::BoundTm(0), Term::BoundTm(0)],
            },
            data: Ty::Unit,
        }],
    };
    ctx.typecheck_ty(&Ty::Ind(eq.clone()))?;
    let ctor = Term::Ctor(eq.clone(), 0);
    println!("{:#?}", ctx.typecheck(&ctor)?);
    let ctor = ctor.app(
        Term::Ctor(nat.clone(), 1)
            .app(Term::Ctor(nat.clone(), 0).app(Term::Star)),
    ).app(Term::Star);
    println!("{:#?}", ctx.typecheck(&ctor)?);
    let mut iter = Term::Iter {
        ind: eq.clone(),
        out: vec![
            Term::Ctor(eq.clone(), 0).app(
                Term::Ctor(nat.clone(), 1)
                    .app(Term::BoundTm(0)),
            ).app(Term::Star),
        ],
        out_ty: Box::new(Ty::Ind(eq.clone())),
    };
    println!("{:#?}", ctx.typecheck(&iter)?);
    //iter = iter.app();
    Ok(())
    //println!("graph:\n{}", ctx);
    //assert!(ctx.typecheck_defs());
}
