
import robot
open tactic
meta def split_disjunctive_hypothesis : robot unit := do
    hs ← robot.get_hyps,
    h ← tactic.returnopt $ list.mfirst (λ h, (expr.is_or $ statement.type $ h) *> some h ) hs,
    tactic.cases_core h.body,
    pure ()

