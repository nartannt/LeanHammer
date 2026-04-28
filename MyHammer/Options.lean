import Lean
import Auto

open Lean Parser Elab Tactic

-- An option to specify the external prover that `hammer` uses
declare_syntax_cat MyHammer.solverOption (behavior := symbol)
-- An option to specify the preprocessing that `hammer` uses
declare_syntax_cat MyHammer.preprocessing (behavior := symbol)
-- An option to specify other configuration options for `hammer`
declare_syntax_cat MyHammer.configOption (behavior := symbol)
-- An option to indicate a boolean value (used for toggling `disableAesop` and `disableAuto`)
declare_syntax_cat MyHammer.bool_lit (behavior := symbol)
syntax "true" : MyHammer.bool_lit
syntax "false" : MyHammer.bool_lit

register_option hammer.solverDefault : String := {
  defValue := "zipperposition_exe"
  descr := "The default value of the solver option"
}

register_option hammer.solverTimeoutDefault : Nat := {
  defValue := 10
  descr := "The default timeout for the solver (in seconds)"
}

register_option hammer.preprocessingDefault : String := {
  defValue := "aesop"
  descr := "The default value of the preprocessing option"
}

register_option hammer.disableAesopDefault : Bool := {
  defValue := false
  descr := "The default value of the disableAesop option"
}

register_option hammer.disableAutoDefault : Bool := {
  defValue := false
  descr := "The default value of the disableAuto option"
}

register_option hammer.autoPremisesDefault : Nat := {
  defValue := 16
  descr := "The default number of premises sent to auto"
}

register_option hammer.aesopPremisesDefault : Nat := {
  defValue := 32
  descr := "The default number of premises sent to aesop to be used as unsafe rules"
}

register_option hammer.aesopPremisePriorityDefault : Nat := {
  defValue := 20
  descr := "The default priority of premises sent to aesop"
}

register_option hammer.aesopAutoPriorityDefault : Nat := {
  defValue := 10
  descr := "The default priority of calls to auto within aesop"
}

namespace HammerCore

def getHammerSolverDefault (opts : Options) : String := hammer.solverDefault.get opts
def getHammerSolverTimeoutDefault (opts : Options) : Nat := hammer.solverTimeoutDefault.get opts
def getPreprocessingDefault (opts : Options) : String := hammer.preprocessingDefault.get opts
def getDisableAesopDefault (opts : Options) : Bool := hammer.disableAesopDefault.get opts
def getDisableAutoDefault (opts : Options) : Bool := hammer.disableAutoDefault.get opts
def getAutoPremisesDefault (opts : Options) : Nat := hammer.autoPremisesDefault.get opts
def getAesopPremisesDefault (opts : Options) : Nat := hammer.aesopPremisesDefault.get opts
def getAesopPremisePriorityDefault (opts : Options) : Nat := hammer.aesopPremisePriorityDefault.get opts
def getAesopAutoPriorityDefault (opts : Options) : Nat := hammer.aesopAutoPriorityDefault.get opts

def getHammerSolverDefaultM : CoreM String := do
  let opts ← getOptions
  return getHammerSolverDefault opts

def getHammerSolverTimeoutDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getHammerSolverTimeoutDefault opts

def getPreprocessingDefaultM : CoreM String := do
  let opts ← getOptions
  return getPreprocessingDefault opts

def getDisableAesopDefaultM : CoreM Bool := do
  let opts ← getOptions
  return getDisableAesopDefault opts

def getDisableAutoDefaultM : CoreM Bool := do
  let opts ← getOptions
  return getDisableAutoDefault opts

def getAutoPremisesDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getAutoPremisesDefault opts

def getAesopPremisesDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getAesopPremisesDefault opts

def getAesopPremisePriorityDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getAesopPremisePriorityDefault opts

def getAesopAutoPriorityDefaultM : CoreM Nat := do
  let opts ← getOptions
  return getAesopAutoPriorityDefault opts

syntax "zipperposition_exe" : MyHammer.solverOption
syntax "zipperposition" : MyHammer.solverOption
syntax "cvc5" : MyHammer.solverOption

syntax "simp_target" : MyHammer.preprocessing -- Corresponds to `simp`
syntax "simp_all" : MyHammer.preprocessing -- Corresponds to `simp_all`
syntax "no_preprocessing" : MyHammer.preprocessing -- Corresponds to skipping all preprocessing
syntax "aesop" : MyHammer.preprocessing -- Corresponds to integrating with `aesop` (thus using `aesop` for preprocessing)

inductive Solver where
| zipperposition_exe -- The default solver that uses the executable retrieved by `lean-auto`'s post-update hook
| zipperposition -- Calls a local installation of Zipperposition
| cvc5 -- Calls a local installation of cvc5
deriving ToExpr, BEq

inductive Preprocessing where
| simp_target
| simp_all
| no_preprocessing
| aesop
deriving BEq, ToExpr

open Solver Preprocessing

def elabSolverOption [Monad m] [MonadError m] (stx : TSyntax `MyHammer.solverOption) : m Solver :=
  withRef stx do
    match stx with
    | `(solverOption| zipperposition_exe) => return zipperposition_exe
    | `(solverOption| zipperposition) => return zipperposition
    | `(solverOption| cvc5) => return cvc5
    | _ => Elab.throwUnsupportedSyntax

def elabSolverOptionDefault : CoreM Solver := do
  let solverName ← getHammerSolverDefaultM
  match solverName with
  | "zipperposition_exe" => return zipperposition_exe
  | "zipperposition" => return zipperposition
  | "cvc5" => return cvc5
  | _ => throwError "Unsupported default solver option: {solverName}"

def elabPreprocessing [Monad m] [MonadError m] (stx : TSyntax `MyHammer.preprocessing) : m Preprocessing :=
  withRef stx do
    match stx with
    | `(preprocessing| simp_target) => return simp_target
    | `(preprocessing| simp_all) => return simp_all
    | `(preprocessing| no_preprocessing) => return no_preprocessing
    | `(preprocessing| aesop) => return aesop
    | _ => Elab.throwUnsupportedSyntax

def elabPreprocessingDefault : CoreM Preprocessing := do
  let preprocessingName ← getPreprocessingDefaultM
  match preprocessingName with
  | "simp_target" => return simp_target
  | "simp_all" => return simp_all
  | "no_preprocessing" => return no_preprocessing
  | "aesop" => return aesop
  | _ => throwError "Unsupported default preprocessing option: {preprocessingName}"

def elabBoolLit [Monad m] [MonadError m] (stx : TSyntax `MyHammer.bool_lit) : m Bool :=
  withRef stx do
    match stx with
    | `(bool_lit| true) => return true
    | `(bool_lit| false) => return false
    | _ => Elab.throwUnsupportedSyntax

syntax (&"solver" " := " MyHammer.solverOption) : MyHammer.configOption
syntax (&"solverTimeout" " := " numLit) : MyHammer.configOption
syntax (&"preprocessing" " := " MyHammer.preprocessing) : MyHammer.configOption
syntax (&"disableAuto" " := " MyHammer.bool_lit) : MyHammer.configOption
syntax (&"disableAesop" " := " MyHammer.bool_lit) : MyHammer.configOption
syntax (&"autoPremises" " := " numLit) : MyHammer.configOption -- The number of premises sent to `auto` (default: 16)
syntax (&"aesopPremises" " := " numLit) : MyHammer.configOption -- The number of premises sent to `aesop` (default: 32)
syntax (&"aesopPremisePriority" " := " numLit) : MyHammer.configOption -- The priority of premises sent to `aesop` (default: 20)
syntax (&"aesopAutoPriority" " := " numLit) : MyHammer.configOption -- The priority of calls to `auto` within `aesop` (default: 10)

structure ConfigurationOptions where
  solver : Solver
  solverTimeout : Nat
  preprocessing : Preprocessing
  disableAuto : Bool
  disableAesop : Bool
  aesopPremisePriority : Nat
  aesopAutoPriority : Nat
  autoPremises : Nat -- The number of premises sent to `auto` (default: 16)
  aesopPremises : Nat -- The number of premises sent to `aesop` (default: 32)
deriving ToExpr

syntax hammerStar := "*"
syntax (name := hammerCore) "hammerCore"
  (ppSpace "[" ((simpErase <|> simpLemma),*,?)  "]")
  (ppSpace "[" (hammerStar <|> term),* "]")
  (ppSpace "{"MyHammer.configOption,*,?"}")? : tactic

macro_rules | `(tactic| hammerCore [$simpLemmas,*] [$facts,*]) => `(tactic| hammerCore [$simpLemmas,*] [$facts,*] {})

/-- Checks to ensure that the set of given `configOptions` is usable. -/
def validateConfigOptions (configOptions : ConfigurationOptions) : TacticM ConfigurationOptions := do
  if configOptions.disableAesop && configOptions.disableAuto then
    throwError "Erroneous invocation of hammer: The aesop and auto options cannot both be disabled"
  if configOptions.disableAesop && configOptions.preprocessing == Preprocessing.aesop then
    throwError "Erroneous invocation of hammer: Preprocessing cannot be set to aesop when aesop is disabled"
  if !configOptions.disableAesop && configOptions.preprocessing != Preprocessing.aesop then
    throwError "Erroneous invocation of hammer: Preprocessing must be set to aesop when aesop is enabled"
  if !configOptions.disableAuto && configOptions.solver == Solver.zipperposition_exe then
    try
      let _ ← Auto.Solver.TPTP.getZipperpositionExePath -- This throws an error if the executable can't be found
    catch _ =>
      if configOptions.disableAesop then
        throwError "The bundled zipperposition executable could not be found. To retrieve it, run `lake update MyHammer`."
      else
        logWarning "The bundled zipperposition executable could not be found. To retrieve it, run `lake update MyHammer`. Continuing with auto disabled..."
        return {configOptions with disableAuto := true}
  return configOptions

def parseConfigOptions (configOptionsStx : TSyntaxArray `MyHammer.configOption) : TacticM ConfigurationOptions := do
  let mut solverOpt := none
  let mut solverTimeoutOpt := none
  let mut preprocessingOpt := none
  let mut disableAutoOpt := none
  let mut disableAesopOpt := none
  let mut autoPremisesOpt := none
  let mut aesopPremisesOpt := none
  let mut aesopPremisePriorityOpt := none
  let mut aesopAutoPriorityOpt := none
  for configOptionStx in configOptionsStx do
    match configOptionStx with
    | `(MyHammer.configOption| solver := $solverName:MyHammer.solverOption) =>
      if solverOpt.isNone then solverOpt ← elabSolverOption solverName
      else throwError "Erroneous invocation of hammer: The solver option has been specified multiple times"
    | `(MyHammer.configOption| solverTimeout := $userSolverTimeout:num) =>
      if solverTimeoutOpt.isNone then solverTimeoutOpt := some (TSyntax.getNat userSolverTimeout)
      else throwError "Erroneous invocation of hammer: The solverTimeout option has been specified multiple times"
    | `(MyHammer.configOption| preprocessing := $preprocessing:MyHammer.preprocessing) =>
      if preprocessingOpt.isNone then preprocessingOpt ← elabPreprocessing preprocessing
      else throwError "Erroneous invocation of hammer: The preprocessing option has been specified multiple times"
    | `(MyHammer.configOption| disableAuto := $disableAutoBoolLit:MyHammer.bool_lit) =>
      if disableAutoOpt.isNone then disableAutoOpt := some $ ← elabBoolLit disableAutoBoolLit
      else throwError "Erroneous invocation of hammer: The disableAuto option has been specified multiple times"
    | `(MyHammer.configOption| disableAesop := $disableAesopBoolLit:MyHammer.bool_lit) =>
      if disableAesopOpt.isNone then disableAesopOpt := some $ ← elabBoolLit disableAesopBoolLit
      else throwError "Erroneous invocation of hammer: The disableAesop option has been specified multiple times"
    | `(MyHammer.configOption| autoPremises := $userAutoPremises:num) =>
      if autoPremisesOpt.isNone then autoPremisesOpt := some (TSyntax.getNat userAutoPremises)
      else throwError "Erroneous invocation of hammer: The autoPremises option has been specified multiple times"
    | `(MyHammer.configOption| aesopPremises := $userAesopPremises:num) =>
      if aesopPremisesOpt.isNone then aesopPremisesOpt := some (TSyntax.getNat userAesopPremises)
      else throwError "Erroneous invocation of hammer: The aesopPremises option has been specified multiple times"
    | `(MyHammer.configOption| aesopPremisePriority := $userAesopPremisePriority:num) =>
      if aesopPremisePriorityOpt.isNone then aesopPremisePriorityOpt := some (TSyntax.getNat userAesopPremisePriority)
      else throwError "Erroneous invocation of hammer: The aesopPremisePriority option has been specified multiple times"
    | `(MyHammer.configOption| aesopAutoPriority := $userAesopAutoPriority:num) =>
      if aesopAutoPriorityOpt.isNone then aesopAutoPriorityOpt := some (TSyntax.getNat userAesopAutoPriority)
      else throwError "Erroneous invocation of hammer: The aesopAutoPriority option has been specified multiple times"
    | _ => throwUnsupportedSyntax
  -- Set default values for options that were not specified
  let solver ← -- **TODO** Will likely need to refactor/rethink `solver` option when incorporating lean-smt
    match solverOpt with
    | none => elabSolverOptionDefault
    | some solver => pure solver
  let solverTimeout ←
    match solverTimeoutOpt with
    | none => getHammerSolverTimeoutDefaultM
    | some solverTimeout => pure solverTimeout
  let disableAuto ←
    match disableAutoOpt with
    | none => getDisableAutoDefaultM
    | some disableAuto => pure disableAuto
  let disableAesop ←
    match disableAesopOpt with
    | none => getDisableAesopDefaultM
    | some disableAesop => pure disableAesop
  let preprocessing ←
    match preprocessingOpt with
    | none =>
      if disableAesop && (← getPreprocessingDefaultM) == "aesop" then pure Preprocessing.simp_all
      else elabPreprocessingDefault
    | some preprocessing => pure preprocessing
  let autoPremises ←
    match autoPremisesOpt with
    | none => getAutoPremisesDefaultM
    | some autoPremises => pure autoPremises
  let aesopPremises ←
    match aesopPremisesOpt with
    | none => getAesopPremisesDefaultM
    | some aesopPremises => pure aesopPremises
  let aesopPremisePriority ←
    match aesopPremisePriorityOpt with
    | none => getAesopPremisePriorityDefaultM
    | some aesopPremisePriority => pure aesopPremisePriority
  let aesopAutoPriority ←
    match aesopAutoPriorityOpt with
    | none => getAesopAutoPriorityDefaultM
    | some aesopAutoPriority => pure aesopAutoPriority
  let configOptions :=
    {solver := solver, solverTimeout := solverTimeout, preprocessing := preprocessing, disableAuto := disableAuto, disableAesop := disableAesop, autoPremises := autoPremises,
     aesopPremises := aesopPremises, aesopPremisePriority := aesopPremisePriority, aesopAutoPriority := aesopAutoPriority}
  let configOptions ← validateConfigOptions configOptions
  return configOptions

def withSolverOptions [Monad m] [MonadError m] [MonadWithOptions m] (configOptions : ConfigurationOptions) (x : m α) : m α :=
  match configOptions.solver with
  | zipperposition_exe =>
    withOptions
      (fun o =>
        let o := o.set `auto.tptp true
        let o := o.set `auto.tptp.timeout configOptions.solverTimeout
        let o := o.set `auto.smt false
        let o := o.set `auto.tptp.premiseSelection true
        let o := o.set `auto.tptp.solver.name "zipperposition_exe"
        let o := o.set `auto.mono.ignoreNonQuasiHigherOrder true
        o.set `auto.native true
      ) x
  | zipperposition =>
    withOptions
      (fun o =>
        let o := o.set `auto.tptp true
        let o := o.set `auto.tptp.timeout configOptions.solverTimeout
        let o := o.set `auto.smt false
        let o := o.set `auto.tptp.premiseSelection true
        let o := o.set `auto.tptp.solver.name "zipperposition"
        let o := o.set `auto.mono.ignoreNonQuasiHigherOrder true
        o.set `auto.native true
      ) x
  | cvc5 => throwError "cvc5 hammer support not implemented yet"

def withDuperOptions [Monad m] [MonadError m] [MonadWithOptions m] (x : m α) : m α :=
  withOptions
    (fun o =>
      let o := o.set `duper.ignoreUnusableFacts true
      o.set `auto.mono.ignoreNonQuasiHigherOrder true
    ) x

end HammerCore
