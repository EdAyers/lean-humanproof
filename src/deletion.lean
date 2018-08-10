
-- deletion tactics for G&G prover

import meta.expr
open tactic expr

universes u v w
def list.mchoose {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (f : α → m (option β)) : list α → m (list β)
| []       := return []
| (h :: t) := pure (λ (h : option β) (t : list β), option.rec_on h t (λ h, h :: t)) <*> f h <*> list.mchoose t

def list.some {α : Type u} (p : α -> bool) : list α -> bool
| [] := false
| (h :: t) := p h || list.some t

namespace exprset
meta def exprset := rbmap expr unit expr.lt_prop
meta def from_list (l : list expr) : exprset := rbmap.from_list $ list.map (λ x, ⟨x,unit.star⟩) l
meta def to_list (d : exprset) : list expr := list.map prod.fst $ rbmap.to_list d
meta def empty : exprset := mk_rbmap expr unit expr.lt_prop
meta def union : exprset -> exprset -> exprset := rbmap.fold(λ x u a, rbmap.insert a x u)
meta def contains : exprset -> expr -> bool := rbmap.contains
end exprset

open exprset

meta def get_local_consts (e : expr) : exprset := from_list $ expr.list_local_const $ e

meta structure formula :=
(term : expr)
(type : expr)
(deps : exprset)

meta def as_prop (h : expr) : tactic $ option formula :=
do
    y <- infer_type h,
    p <- is_prop y,
    let deps := get_local_consts y in
    return $ if p then some ⟨h, y, deps⟩ else none

/--Get all of the context entries which are propositions along with their types.-/
meta def local_hypotheses : tactic $ list formula :=
local_context >>= list.mchoose as_prop

/--Get the goals which are propositions along with their types -/
meta def local_targets : tactic $ list formula :=
get_goals >>= list.mchoose as_prop

meta def find_dangling : exprset -> list formula -> list formula -> list formula
| d acc [] := acc
| d acc  (h :: hs) :=
    find_dangling (union d h.deps) (
        if list.some (λ h, (not $ contains d h) && list.all hs (λ h', not $ contains h'.deps h)) $ to_list h.deps
        then h :: acc else acc
    ) (hs)

meta def deleteDangling : tactic unit :=
do
    hyps <- local_hypotheses,
    targets <- local_targets,
    target_deps <- return $ list.foldl union empty $ list.map (λ t : formula, t.deps) targets,
    list.mmap' (λ (h : formula), clear h.term) $ find_dangling target_deps [] hyps

variables a b c : Prop
example : a -> (a -> b) -> c -> b :=
begin
  intros,
  deleteDangling,
  sorry
end
