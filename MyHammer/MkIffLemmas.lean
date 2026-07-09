import Mathlib

open Mathlib.Tactic.MkIff Lean Meta

def mkIffOfInductivePropExpr (ind : Name) : MetaM Expr := do
  let .inductInfo inductVal ← getConstInfo ind |
    throwError "mk_iff only applies to inductive declarations"
  let constrs := inductVal.ctors
  let params := inductVal.numParams
  let type := inductVal.type

  let univNames := inductVal.levelParams
  let univs := univNames.map mkLevelParam

  let (thmTy, shape) ← Meta.forallTelescope type fun fvars ty ↦ do
    if !ty.isProp then throwError "mk_iff only applies to prop-valued declarations"
    let lhs := mkAppN (mkConst ind univs) fvars
    let fvars' := fvars.toList
    let shape_rhss ← constrs.mapM (constrToProp univs (fvars'.take params) (fvars'.drop params))
    let (shape, rhss) := shape_rhss.unzip
    pure (← mkForallFVars fvars (mkApp2 (mkConst `Iff) lhs (mkOrList rhss)), shape)

  let mvar ← withLCtx {} {} (mkFreshExprMVar (some thmTy))
  let mvarId := mvar.mvarId!

  let (fvars, mvarId') ← mvarId.intros
  let [mp, mpr] ← mvarId'.apply (mkConst `Iff.intro) | throwError "failed to split goal"
  toCases mp shape

  let ⟨mprFvar, mpr'⟩ ← mpr.intro1
  toInductive mpr' constrs ((fvars.toList.take params).map .fvar) shape mprFvar

  return mvar

syntax (name := mkIff) "mk_iff " ident : term

@[term_elab mkIff]
def mkIffInd : Elab.Term.TermElab := fun stx _expectedType? => do
  match stx with
  | `(mk_iff $id:ident) => do
    let indName ← realizeGlobalConstNoOverload id
    let result ← mkIffOfInductivePropExpr indName
    return result
  | _ => throwErrorAt stx "{indentD stx}"

def indDefIffTerms (currPremises : Array Term) : MetaM (Array (TSyntax `term))  := do
  let addMkIffOpt (term : Term) := do
    let termName : Name := Lean.Syntax.getId term
    let res : Option Term ← do 
      if ← isInductivePredicate termName then
        return some (← `(term| mk_iff $(mkIdent termName)))
      else 
        trace[myhammer.premises] "premise rejected for iff-thm : {termName}"
        return none
  let resTerms : (Array Term) ← Array.filterMapM addMkIffOpt currPremises
  return (resTerms)
