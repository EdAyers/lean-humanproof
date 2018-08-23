
-- deletion tactics for G&G prover

import meta.expr
import table
import robot
open tactic expr
open table robot
universes u v w
def list.mchoose {m : Type u → Type v} [monad m] {α : Type w} {β : Type u} (f : α → m (option β)) : list α → m (list β)
| []       := return []
| (h :: t) := pure (λ (h : option β) (t : list β), option.rec_on h t (λ h, h :: t)) <*> f h <*> list.mchoose t



meta def get_local_consts (e : expr) : table expr := table.from_list $ expr.list_local_const $ e

/- We say that a statement is __dangling__ when it references a variable that no other statements reference. -/

/--Arguments:
   - an accumulating table of local constants that all of the hyps considered so far.
     add the references of all of the goals to this.
   - an accumulator full of the statements that are dangling
   - a queue of statements yet to check.
   Returns: a list of dangling statements.
-/
meta def find_dangling : table expr → list hyp → list hyp → list hyp
| d acc [] := acc
| d acc  (h :: hs) :=
    find_dangling (d ∪ h.refs) (  
        -- If there is a variable `x ∈ h.deps` that doesn't appear in any of these then add it to the list of condemned statements
        if table.any (λ x, (not $ contains x d) && list.all hs (λ h', not $ contains x h'.refs)) h.refs 
        then h :: acc else acc
    ) (hs)

meta def delete_dangling : robot unit :=
do
    hyps ← get_hyps,
    targets ← get_targets,
    target_deps ← return $ dict.fold (λ _, union) empty $ dict.map (statement.refs) targets,
    list.mmap' (λ h : statement, clear h.body) $ find_dangling target_deps [] hyps

meta def scratch_tac : tactic unit :=
do v ← mk_meta_var `(ℕ),
   e ← mk_app ``eq [v, v],
   assert_core "h" e,
   skip

variables a b c : Prop
example : a → (a → b) → c → b :=
begin
  intros h1 h2 h3,
  scratch_tac,
  sorry
end
