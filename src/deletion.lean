
-- deletion tactics for G&G prover

import meta.expr
import table
open tactic expr

universes u v w
def list.mchoose {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (f : α → m (option β)) : list α → m (list β)
| []       := return []
| (h :: t) := pure (λ (h : option β) (t : list β), option.rec_on h t (λ h, h :: t)) <*> f h <*> list.mchoose t

def list.some {α : Type u} (p : α -> bool) : list α -> bool
| [] := false
| (h :: t) := p h || list.some t

meta def get_local_consts (e : expr) : table expr := from_list $ expr.list_local_const $ e

meta structure formula :=
(term : expr)
(type : expr)
(deps : table expr)

meta def as_formula (h : expr) : tactic $ option formula :=
do
    y <- infer_type h,
    p <- is_prop y,
    let deps := get_local_consts y in
    return $ if p then some ⟨h, y, deps⟩ else none

/--Get all of the context entries which are propositions along with their types.-/
meta def local_hypotheses : tactic $ list formula :=
local_context >>= list.mchoose as_formula

/--Get the goals which are propositions along with their types -/
meta def local_targets : tactic $ list formula :=
get_goals >>= list.mchoose as_formula

meta def find_dangling : table expr -> list formula -> list formula -> list formula
| d acc [] := acc
| d acc  (h :: hs) :=
    find_dangling (union d h.deps) (
        if list.some (λ h, (not $ contains d h) && list.all hs (λ h', not $ contains h'.deps h)) $ to_list h.deps
        then h :: acc else acc
    ) (hs)

meta def delete_dangling : tactic unit :=
do
    hyps <- local_hypotheses,
    targets <- local_targets,
    target_deps <- return $ list.foldl union empty $ list.map (λ t : formula, t.deps) targets,
    list.mmap' (λ (h : formula), clear h.term) $ find_dangling target_deps [] hyps

meta def scratch_tac : tactic unit :=
do v ← mk_meta_var `(ℕ),
   e ← mk_app ``eq [v, v],
   assert_core "h" e,
   skip

variables a b c : Prop
example : a -> (a -> b) -> c -> b :=
begin
  intros h1 h2 h3,
  scratch_tac,
  sorry
end
