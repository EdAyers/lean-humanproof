/- I'm going to define my own wrapper monad around `tactic`. 
Maybe this is a bad idea. But it will give me practice with typeclasses in Lean so it won't be a waste of time -/

import meta.expr
import table
open tactic expr dict table
universe u

namespace robot

meta inductive hyp_telescope
-- prev are values that have been substituted for the binder in the past.
|Take  (type : expr) (prev : table expr) (rest : hyp_telescope)
|Give  (type : expr) (rest : hyp_telescope)
|Premiss (prop: expr) (rest : hyp_telescope) 
|Conclusion (prop : expr)

meta structure hyp :=
    (body : expr) -- the proof term for the hyp
    (type : hyp_telescope) -- the type has been 'preunwound' to make the conclusion more accessible.
    (vuln : bool) -- if it is vulnerable then it is fair game for delete_dangling and delete_unmatchable
    (refs : table expr) -- a table of local_consts that the type depends on.

meta inductive bullet_type |Diamond |Circle

meta structure bullet :=
    (dependent : table expr) -- local-consts and metavariables that it depends on
    (independent : table expr) -- local-consts and metavariables that it is not allowed to depend on
    (type : bullet_type)

meta def hyps := dict expr hyp
meta structure robot_state :=
    (vars : list expr)
    (hyps : hyps)
    (target : expr)
    (bullets : dict expr bullet)
    
@[reducible] meta def robot := state_t robot_state tactic

private meta def mk_hyp_telescope : expr → tactic hyp_telescope
| (pi n bi a b) := do
    -- TODO; if `a` is a sigma or a product, convert to a Pi using Exists.elim
    p ← is_prop a,
    rest ← mk_hyp_telescope b,
    return $ if p then hyp_telescope.Take a table.empty rest
             else hyp_telescope.Premiss a rest
| (app (app `(Exists) a) p) := do
    p ← whnf p,
    match p with
    |(pi n bi _ b) := do
        rest ← mk_hyp_telescope b,
        return $ hyp_telescope.Give a rest
    |_ := none
    end
| x := return $ hyp_telescope.Conclusion x 

private meta def mk_hp_vars_and_hyps : (list expr) → hyps → (list expr) → tactic ((list expr) × hyps)
|(vs) (hs) ([]) := return ⟨vs, hs⟩
|(vs) (hs) (v :: t) := do
    -- TODO expand the definition of the type once?
    type ← infer_type v,
    isProp ← is_prop type,
    if (isProp) then do
        refs ← return $ table.from_list $ expr.list_local_const $ type,
        telescope ← mk_hyp_telescope type,
        hyp ← return $ hyp.mk v telescope false refs,
        mk_hp_vars_and_hyps vs (dict.insert v hyp hs) t 
    else mk_hp_vars_and_hyps (v :: vs) hs t

private meta def mk_robot_state : tactic robot_state := do
    ctx ← local_context,
    t ← target,
    ⟨vs, hs⟩ ← mk_hp_vars_and_hyps [] empty ctx,
    return $ {vars := vs, hyps := hs, target := t, bullets := empty }

meta def get_hyps : robot hyps := robot_state.hyps <$> get
meta def set_hyps (hs:hyps) : robot unit := modify $ λ s, {hyps := hs, ..s}
meta def get_vars : robot $ list expr := robot_state.vars <$> get
private meta def of_tactic {α : Type} : tactic α → robot α := state_t.lift --[HACK] I get weird name clash errors if I call it `lift`.
-- meta instance {α : Type} : has_coe (tactic α) (robot α) := ⟨lift⟩ 
meta def run {α : Type} (r : robot α) : tactic α := prod.fst <$> (mk_robot_state >>= r.run)

/--Remove a hypothesis. -/
meta def clear_hyp (e : expr) : robot unit := do
    hs ← get_hyps,
    hs' ← pure $ dict.filter (λ _ (h: hyp), decidable.to_bool $ e ≠ h.body) $ hs,
    of_tactic $ clear e,
    set_hyps hs'

    

end robot