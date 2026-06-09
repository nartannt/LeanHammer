import Lean.Expr


open Lean Meta Parser Elab Tactic Syntax

def inductive_definitions : CoreM (List Expr) := do
    let env ← MonadEnv.getEnv
    let constants := Environment.constants env
    let cnstToIndDefs (defsAcc: List Expr) _ (nextCnstInfo: ConstantInfo): (List Expr) :=
        match nextCnstInfo with
          | ConstantInfo.inductInfo inductVal =>
            let ctors := inductVal.ctors
            let ctorsTypes := (List.filterMap (fun ctor ↦
                match Environment.find? env ctor with
                  | some val => some (ConstantInfo.toConstantVal val).type
                  | none => none) ctors )
            (ctorsTypes ++ defsAcc)
          | _ => defsAcc
    return SMap.fold cnstToIndDefs [] constants
