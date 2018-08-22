/- I'm going to define my own wrapper monad around `tactic`. 
Maybe this is a bad idea. But it will give me practice with typeclasses in Lean so it won't be a waste of time -/

import meta.expr
import exprset
open tactic expr
universe u

namespace robot

meta inductive hyp_telescope
-- prev are values that have been substituted for the binder in the past.
|Take  (type : expr) (prev : exprset) (rest : hyp_telescope)
|Give  (type : expr) (rest : hyp_telescope)
|Premiss (prop: expr) (rest : hyp_telescope) 
|Conclusion (prop : expr)

meta structure hyp :=
    (body : expr) -- the proof term for the hyp
    (type : hyp_telescope) -- the type has been 'preunwound' to make the conclusion more accessible.
    (vuln : bool) -- if it's vulnerable, it's fair game for delete_dangling and delete_unmatchable
    (refs : exprset) -- a table of local_consts that the type depends on.

meta inductive bullet_type |Diamond | Circle

meta structure bullet :=
    (dependent : exprset)
    (independent : exprset)
    (type : bullet_type)

meta def hyps := rbmap expr hyp
meta structure robot_state :=
    (vars : list expr)
    (hyps : hyps)
    (target : expr)
    (bullets : rbmap expr bullet)

-- Note that this is just `StateT robot_state tactic α` if we loved monad transformers.
-- The idea is that `robot` wraps `tactic` to ensure that the extra state remains up to date with the underlying goal structure.
@[reducible] meta def robot (α : Type u) := robot_state -> tactic (α × robot_state)

meta instance : monad robot :=
{ map := λ α β f x s, x s >>= (λ ⟨a,s⟩, pure ⟨f a, s⟩)
, pure := λ α a s, pure ⟨a,s⟩
, bind := λ α β x f s, x s >>= λ ⟨a,s⟩, f a s
}

meta instance : alternative robot :=
{ failure := λ α (s : robot_state), failure 
, orelse := λ α a b s, (a s : tactic _) <|> (b s)
}


private meta def mk_hyp_telescope : expr -> tactic hyp_telescope
| (pi n bi a b) := do
    -- TODO; if `a` is a sigma or a product, convert to a Pi using Exists.elim
    p <- is_prop a,
    rest <- mk_hyp_telescope b,
    return $ if p then hyp_telescope.Take a exprset.empty rest
            else hyp_telescope.Premiss a rest
| (app (app `(Exists) a) p) := do
    p <- whnf p,
    match p with
    |(pi n bi _ b) := do
        rest  <- mk_hyp_telescope b,
        return $ hyp_telescope.Give a rest
    |_ := none
    end
| x := return $ hyp_telescope.Conclusion x 

private meta def mk_hp_vars_and_hyps : (list expr) -> hyps -> (list expr) -> tactic ((list expr) × hyps)
|(vs) (hs) ([]) := return ⟨vs, hs⟩
|(vs) (hs) (v :: t) := do
    -- TODO expand the definition of the type once?
    type <- infer_type v,
    isProp <- is_prop type,
    if (isProp) then do
        refs <- return $ from_list $ expr.list_local_const $ type,
        telescope <- mk_hyp_telescope type,
        hyp <- return $ hyp.mk v telescope false refs,
        mk_hp_vars_and_hyps vs (rbmap.insert hs v hyp) t 
    else mk_hp_vars_and_hyps (v :: vs) hs t

private meta def mk_robot_state : tactic robot_state := do
    ctx <- local_context,
    t <- target,
    ⟨vs, hs⟩ <- mk_hp_vars_and_hyps [] (mk_rbmap _ _) ctx,
    return $ {vars := vs, hyps := hs, target := t, bullets := mk_rbmap _ _ }

meta def get_hyps : robot $ hyps := λ s, pure ⟨s.hyps, s⟩
meta def set_hyps : hyps -> robot unit := λ hs s, pure ⟨(), {hyps := hs, ..s}⟩
meta def get_vars : robot $ list expr := λ s, pure ⟨s.vars, s⟩
private meta def from_tactic {α : Type} : tactic α -> robot α := λ t s, t >>= λ a, pure ⟨a,s⟩
meta instance {α : Type} : has_coe (tactic α) (robot α) := ⟨from_tactic⟩ 
meta def run {α : Type} (r : robot α) : tactic α := prod.fst <$> (mk_robot_state >>= r)

/--Remove a hypothesis. -/
meta def clear_hyp (e : expr) : robot unit := do
    hs <- get_hyps,
    hs' <- pure $ rbmap (λ (h: hyp), e ≠ h.body) hs,
    clear e,
    set_hyps hs'

    

end robot