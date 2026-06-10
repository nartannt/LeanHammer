import Lean.Expr
import Mathlib


open Lean Meta Parser Elab Tactic Syntax

-- TODO we want to apply this tactic after the premise selection to avoid generating useless lemmas
-- but we also want to do it before so that the premise selector can chose them
-- given how long the tactic takes to execute we may want to only apply it to selected definitions
open Mathlib.Tactic.MkIff Lean Meta Elab
elab "list_iff_ind" : tactic => do
  let env ← Lean.MonadEnv.getEnv -- get the local environment
  let constants := env.constants -- get the local constants.
  for cnst in constants do
    let (cnstName, cnstInfo) := cnst
      match cnstInfo with
        | .inductInfo inductVal =>
          if !cnstName.toString.contains "Lean." &&
             !cnstName.toString.contains "Std." then
            --dbg_trace "{cnstName}"
            let indValTerm : Term ← PrettyPrinter.delab inductVal.type
            let indValSyntax : Syntax := indValTerm.raw
            try MetaM.run' do 
              mkIffOfInductivePropImpl cnstName (cnstName.decapitalize.toString ++ "____iff").toName indValSyntax
            catch _ => pure ()
          else pure ()
        | _ => pure ()
