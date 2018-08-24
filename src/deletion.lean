-- deletion tactics for G&G prover

import robot
open tactic expr
open table

namespace robot

/--
   We say that a statement is __dangling__ when it references a variable that no other statements reference.  
   Arguments:
   - an accumulating table of local constants that all of the hyps considered so far.
     add the references of all of the goals to this.
   - an accumulator full of the statements that are dangling
   - a queue of statements yet to check.
   
   Returns: a list of dangling statements.
-/
meta def find_dangling : table expr → list statement → list statement → list statement
| d acc [] := acc
| d acc  (h :: hs) :=
    find_dangling (d ∪ h.refs) (  
        -- If there is a variable `x ∈ h.deps` that doesn't appear in any of these then add it to the list of condemned statements
        if table.any (λ x, (not $ contains x d) && list.all hs (λ h', not $ contains x h'.refs)) h.refs 
        then h :: acc else acc
    ) (hs)

meta def delete_dangling : robot unit := do
    hyps ← robot.get_vuln_hyps,
    targets ← robot.get_targets,
    target_deps ← return $ list.foldl union empty $ list.map (statement.refs) targets,
    list.mmap' (λ h : statement, clear_hyp h.body) $ find_dangling target_deps [] hyps


/- How to implement 'delete unmatchable'?

    We first need to write a `match` routine.
    This takes a pi-type hypothesis and attempts to find an argument within 

   Take a hyp H, get its type. We are interested if it is an atomic formula.
   Now we look at all of the other hypotheses and targets
   if H can't be applied to any of these then we discard it.
-/

meta def try_on_all_goals_aux (check : robot unit) : ℕ → robot unit
|0 := fail "it didn't work on any of the goals"
|(nat.succ n) := hypothetically check <|> (rotate 1 *> try_on_all_goals_aux n)
meta def try_on_all_goals (check : robot unit) : robot unit := num_goals >>= try_on_all_goals_aux check

/--Returns tt if `A` can be applied as one of the arguments to `H`-/
meta def is_matchable (A : expr) (H : expr) : robot bool := hypothetically $ 
    (do
        --trace "____",
        m ← mk_mvar,
        set_goals [m],
        --robot.of_tactic (tactic.infer_type H >>= tactic.trace),
        ms ← apply H {unify := tt, new_goals := new_goals.non_dep_only},
        --robot.of_tactic (tactic.target >>= tactic.trace),
        cannot_substitute ← get_cannot_substitute H,
        ms' ← pure $ @list.mapi (name × expr) (expr × table expr) (λ n ⟨l,e⟩, ⟨e, dict.get_default empty n cannot_substitute⟩) ms,
        --trace ms',
        -- rotate through all of the goals, seeing if H can be applied.
        try_on_all_goals (do
            apply A,
            --trace A,
            @list.mmap' _ _ (expr × table expr) unit (λ ⟨e, x⟩, do 
                e' ← instantiate_mvars e,
                assert $ not $ contains e' x,
                return ()
            ) ms',
            --trace A,
            return ()
        ),
        pure tt)
    <|> pure ff
    
meta def is_result (h : statement) : robot bool := expr.is_pi <$>  whnf (h.type)
meta def is_atom (h : statement) : robot bool := (bnot ∘ expr.is_pi) <$> whnf (h.type)

meta def delete_unmatchable : robot unit := do
    lc ← get_hyps, -- [NOTE] needlessly recalculating `refs`. [TODO] should only select vulnerable ones.
    atoms ← list.filterm is_atom lc, -- [NOTE] perhaps write `list.partitionm`.
    --tactic.trace atoms,
    results ← list.filterm is_result lc,
    --tactic.trace results,
    clear_these ← list.filterm (λ a,
      list.allm (λ r,
        
        bnot <$> is_matchable (statement.body a) (statement.body r)
      ) results
    ) atoms,
    list.mmap' (λ c, clear_hyp (statement.body c)) clear_these
    
end robot

section TEST
variables (α : Type) (A B C : set α) (x : α)
example : (x ∈ A) → (x ∈ B) → ((x ∈ B) → (x ∈ C)) → (x ∈ C) := begin
  intros,
  robot.run (do
    tactic.get_local `a >>= robot.set_vuln,
    robot.delete_unmatchable
  ),
  -- [TODO] write a check here that makes sure that `x ∈ A` got deleted.
  apply a_2 a_1,
end

end TEST

section SCRATCH

end SCRATCH