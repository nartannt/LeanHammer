import MyHammer.Tactic
import MyHammer.DuperCore
import MyHammer.HammerCore
import MyHammer.Options
import MyHammer.SingleRuleTac

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true
example : forall x : Nat, False := by
  hammer [exists_true_left] {disableAesop := true, autoPremises := 0}
