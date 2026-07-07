import MyHammer.Tactic
import MyHammer.DuperCore
import MyHammer.HammerCore
import MyHammer.Options
import MyHammer.SingleRuleTac
import MyHammer.MkIffLemmas

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
set_option hammer.preprocessingDefault "no_preprocessing"
set_option hammer.disableAesopDefault true
set_option hammer.autoPremisesDefault 16
set_option trace.hammer.premises true
set_option trace.debug true
set_option pp.rawOnError true


open Lean LibrarySuggestions in
set_library_suggestions mepoSelector (useRarity := false)

inductive A : Type

inductive B : A -> Prop where
  | b x : B x

--set_option trace.profiler true
--
--set_option trace.profiler.output "/tmp/profile.json"
--set_option trace.profiler.output.pp true

example : forall x: A, B x := by
  myhammer [] {autoPremises := 16, disableAesop:= true}
