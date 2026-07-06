import Lean.Expr
import Mathlib


open Lean Meta Parser Elab Tactic Syntax

open Mathlib.Tactic.MkIff Lean Meta Elab
--elab "list_iff_ind" : tactic => do
--  let env ← Lean.MonadEnv.getEnv -- get the local environment
--  let constants := env.constants -- get the local constants.
--  for cnst in constants do
--    let (cnstName, cnstInfo) := cnst
--    match cnstInfo with
--    | .inductInfo inductVal =>
--          --dbg_trace "{cnstName}"
--          let indValTerm : Term ← PrettyPrinter.delab inductVal.type
--          let indValSyntax : Syntax := indValTerm.raw
--          try MetaM.run' do 
--            mkIffOfInductivePropImpl cnstName (cnstName.decapitalize.toString ++ "____iff").toName indValSyntax
--          catch _ => pure ()
--    | _ => pure ()


def addIndDefMkIff (currPremises : Array Term) := do
  let addMkIffOpt (term : Term) := do
    let termSyntax := term.raw
    let termName : Name := Lean.Syntax.getId term
    let thmName := (termName.decapitalize.toString ++ "___iff").toName
    let res : Option Term ← try do
      MetaM.run' (mkIffOfInductivePropImpl termName thmName termSyntax)
      return (some thmName)
    catch _ => return none
  let resTerms : (Array Name) ← Array.filterMapM addMkIffOpt currPremises
  return (resTerms)


def mkIffOfInductivePropExpr (ind : Name) : MetaM (List Name × Expr) := do
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

  let mvar ← mkFreshExprMVar (some thmTy)
  let mvarId := mvar.mvarId!
  let (fvars, mvarId') ← mvarId.intros
  let [mp, mpr] ← mvarId'.apply (mkConst `Iff.intro) | throwError "failed to split goal"

  toCases mp shape
  let ⟨mprFvar, mpr'⟩ ← mpr.intro1
  toInductive mpr' constrs ((fvars.toList.take params).map .fvar) shape mprFvar
  return (univNames, ← instantiateMVars mvar)

def mkIffOfInductivePropTerm (ind : Name) : MetaM Term := do
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

  let mvar ← mkFreshExprMVar (some thmTy)
  let mvarId := mvar.mvarId!

  let (fvars, mvarId') ← mvarId.intros
  let [mp, mpr] ← mvarId'.apply (mkConst `Iff.intro) | throwError "failed to split goal"
  toCases mp shape

  let ⟨mprFvar, mpr'⟩ ← mpr.intro1
  toInductive mpr' constrs ((fvars.toList.take params).map .fvar) shape mprFvar

  --let lvls ← univNames.mapM (fun _ => mkFreshLevelMVar)
  --let instantiatedMVar ← (instantiateMVars mvar)
  --let expr := (Expr.instantiateLevelParams mvar univNames univs)
  Term.TermElabM.run' (Term.exprToSyntax mvar)


def indDefIffTerms (currPremises : Array Term) := do
  let addMkIffOpt (term : Term) := do
    let termName : Name := Lean.Syntax.getId term
    let res : Option Term ← try do
      let resTerm ← (mkIffOfInductivePropTerm termName)
      return (some resTerm)
    catch _ => return none
  let resTerms : (Array Term) ← Array.filterMapM addMkIffOpt currPremises
  return (resTerms)
