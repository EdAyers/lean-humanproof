/- I'm going to define my own wrapper monad around `tactic`. 
Maybe this is a bad idea. But it will give me practice with typeclasses in Lean so it won't be a waste of time -/

import meta.expr
import table
open tactic expr dict table
universe u

namespace robot

meta structure statement :=
(body : expr)
(type : expr)
(refs : table expr)

meta inductive hyp_telescope
-- `prev` are values that have been substituted for the binder in the past.
|Take  (type : expr) (prev : table expr) (rest : hyp_telescope)
|Give  (type : expr) (rest : hyp_telescope)
|Premiss (prop: expr) (rest : hyp_telescope) 
|Conclusion (prop : expr)

meta structure hyp extends statement :=
    (telescope : hyp_telescope) -- the type has been 'preunwound' so that arguments can be tagged with data.
    (vuln : bool) -- if it is vulnerable then it is fair game for delete_dangling and delete_unmatchable

meta inductive bullet_mode |Diamond |Circle

meta structure bullet extends statement :=
    (dependent : table expr) -- local-consts and metavariables that it is allowed to depend on. This is different to `refs` which tells you the references in the type signature.
    (independent : table expr) -- local-consts and metavariables that it is not allowed to depend on
    (mode : bullet_mode)

@[inline] meta def target := statement
@[inline] meta def targets := dict expr target
meta def hyps := dict expr hyp
meta def bullets := dict expr bullet
meta structure robot_state :=
    (vars : list expr)
    (hyps : hyps)
    (targets : targets)
    (bullets : bullets)
    
@[reducible] meta def robot := state_t robot_state tactic

private meta def mk_hyp_telescope : expr → tactic hyp_telescope
| (pi n bi a b) := do
    -- [TODO] if `a` is a sigma or a product, convert to a Pi using Exists.elim
    -- [TODO] consider using `init/meta/fun_info.lean` to do this.
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

meta def expr.is_mvar : expr → bool
|(mvar _ _ _) := tt
|_ := ff

meta def get_refs (e : expr) : table expr :=
expr.fold e table.empty (λ e' _ es, if expr.is_local_constant e' ∨ expr.is_mvar e' then table.insert e' es else es)


private meta def mk_hp_vars_and_hyps : (list expr) → hyps → (list expr) → tactic ((list expr) × hyps)
|(vs) (hs) ([]) := return ⟨vs, hs⟩
|(vs) (hs) (v :: t) := do
    -- TODO expand the definition of the type once?
    type ← infer_type v,
    isProp ← is_prop type,
    if (isProp) then do
        refs ← return $ get_refs type,
        telescope ← mk_hyp_telescope type,
        hyp ← return $ {hyp . body :=  v, type:=type, telescope := telescope, vuln:=false, refs := refs},
        mk_hp_vars_and_hyps vs (dict.insert v hyp hs) t 
    else mk_hp_vars_and_hyps (v :: vs) hs t

private meta def mk_goals_and_bullets : list expr → tactic (targets × bullets)
| [] := pure ⟨empty, empty⟩
| (g :: gs) := do
    type ← infer_type g,
    refs ← get_refs type,
    isProp ← is_prop type,
    ⟨ts,bs⟩ ← mk_goals_and_bullets gs,
    if isProp then 
        let targ := {statement . body:=g, type:=type, refs:=refs} in
        pure (⟨dict.insert targ ts, bs⟩ : targets × bullets)
    else 
        let b := {bullet . body:= g, type:=type, refs:=refs, depends}

private meta def mk_robot_state : tactic robot_state := do
    ctx ← local_context,
    gs ← get_goals,
    ⟨vs, hs⟩ ← mk_hp_vars_and_hyps [] empty ctx,
    return $ {vars := vs, hyps := hs, target := t, bullets := empty }

meta def get_hyps : robot hyps := robot_state.hyps <$> get
meta def set_hyps (hs:hyps) : robot unit := modify $ λ s, {hyps := hs, ..s}
meta def get_vars : robot $ list expr := robot_state.vars <$> get
meta def get_targets : robot targets := robot_state.targets <$> get
private meta def of_tactic {α : Type} : tactic α → robot α := state_t.lift --[HACK] I get weird name clash errors if I call it `lift`.
-- meta instance {α : Type} : has_coe (tactic α) (robot α) := ⟨lift⟩ 
meta def run {α : Type} (r : robot α) : tactic α := prod.fst <$> (mk_robot_state >>= r.run)

/--Remove a hypothesis from the tactic_state and robot_state. -/
meta def clear_hyp (e : expr) : robot unit := do
    hs ← get_hyps,
    hs' ← pure $ dict.filter (λ _ (h: hyp), decidable.to_bool $ e ≠ h.body) $ hs,
    of_tactic $ clear e,
    set_hyps hs'


end robot