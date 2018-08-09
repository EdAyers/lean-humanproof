-- The *moves* as explained in the G&G paper.
--
-- --Deletion
-- deleteDone,                                        -- done by Lean.
-- deleteDoneDisjunct,                                -- done by Lean.
-- deleteDangling,                                    -- need to detect this, then use `clear`.
-- deleteUnmatchable,                                 -- need to detect this, then use `clear`.
-- --Tidying
-- peelAndSplitUniversalConditionalTarget,            -- this would be `intros`, or do we need something more specialised?
-- splitDisjunctiveHypothesis,                        -- this would be `cases`, but again that might be too general.
-- splitConjunctiveTarget,                            -- there is a general purpose tactic called `split`. It might be to aggressive. See Remark (1) below.
-- splitDisjunctiveTarget,                            -- in Lean you can't have two goals (=boxes) joined by `∨`. Need to thing about the tagging.
-- peelBareUniversalTarget,                           -- this would also be `intros`. So a couple lines up we need something specialised. Also see Remark (2).
-- removeTarget,                                      -- this is a class of moves. No direct equivalent in Lean.
-- collapseSubboxTarget,                              -- probably done by Lean.
-- --Applying
-- forwardsReasoning,                                 -- no direct equivalent in Lean.
-- forwardsLibraryReasoning,                          -- no direct equivalent in Lean.
-- expandPreExistentialHypothesis,                    -- no direct equivalent in Lean. This seems to be a conditional `unfold` followed by `cases`.
-- elementaryExpansionOfHypothesis,                   -- would this be something like `unfold * at *` or `dsimp at *`? Currently `at *` also effects the goal.
-- backwardsReasoning,                                -- no direct equivalent in Lean.
-- backwardsLibraryReasoning,                         -- no direct equivalent in Lean.
-- elementaryExpansionOfTarget,                       -- some sort of `unfold *`. Maybe `dsimp`.
-- expandPreUniversalTarget,                          -- this would also be `intros`. So a couple lines up we need something specialised.
-- solveBullets,                                      -- no direct equivalent in Lean.
-- automaticRewrite,                                  -- no direct equivalent in Lean. See Remark (3).
-- --Suspension
-- unlockExistentialUniversalConditionalTarget,       -- no direct equivalent in Lean.
-- unlockExistentialTarget,                           -- no direct equivalent in Lean.
-- expandPreExistentialTarget,                        -- this seems to be a conditional `unfold`.
-- convertDiamondToBullet,                            -- no direct equivalent in Lean.
-- --EqualitySubstitution
-- rewriteVariableVariableEquality,                   -- no direct equivalent in Lean. See Remark (3).
-- rewriteVariableTermEquality                        -- no direct equivalent in Lean. See Remark (3).

/-
Remark (1). We will have to think about types. In the G&G setting there is no such thing as a type.
I guess humans have a pretty intuitive way of thinking about inductive types. And maybe the `split`
tactic is exactly what we need.

Remark (2). In the G&G paper, during the explanation of `peelBareUniversalTarget` there is some
discussion about "background information". There is no natural analogue of this in Lean. Indeed,
it seems quite a psychological notion. Maybe this can be dealt with using some sort of tagging.

Remark (3). Scott has a tactic called `rewrite_search`. It uses an edit-distance heuristic to look
for a chain of rewrites that will discharge goals of the form A = B.
 (i)  One could imagine a non-finishing version of this tactic. That will rewrite the goal into
      something like A' = B' with an improved edit-distance.
 (ii) A student of Scott is currently writing an improved version of this tactic. It will use machine
      learning to find the chain of rewrites.
There is a tactic `rewrite` but it doesn't do any reasoning or automation. It has to be told explicitly
what the use for the rewrite. 

-/