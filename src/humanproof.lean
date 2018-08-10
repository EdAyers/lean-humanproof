-- The *moves* as explained in the G&G paper.
--
-- --Deletion
-- deleteDone,                                        -- done by Lean.
-- deleteDoneDisjunct,                                -- done by Lean.
-- deleteDangling,                                    -- need to detect this, then use `clear`.
-- deleteUnmatchable,                                 -- need to detect this, then use `clear`.
-- --Tidying
-- peelAndSplitUniversalConditionalTarget,            -- this would be `intros`, or do we need something more specialised? -- It's intros applied only when has form `∀(a:α), (∀(a:α), | (P->)) Q` and it does them all in one go.
-- splitDisjunctiveHypothesis,                        -- this would be `cases`, but again that might be too general. -- Yep it's a specialisation of cases (E)
-- splitConjunctiveTarget,                            -- there is a general purpose tactic called `split`. It might be to aggressive. See Remark (1) below. -- will need to read up on split (E)
-- splitDisjunctiveTarget,                            -- in Lean you can't have two goals (=boxes) joined by `∨`. Need to thing about the tagging. -- We can do this by `try {refine (inj _), ...rest_of_tactic}` or similar.
-- peelBareUniversalTarget,                           -- this would also be `intros`. So a couple lines up we need something specialised. Also see Remark (2).
-- removeTarget,                                      -- this is a class of moves. No direct equivalent in Lean. -- I'll have to look at the source to remind myself what this does.
-- collapseSubboxTarget,                              -- probably done by Lean.
-- --Applying
-- forwardsReasoning,                                 -- `have h₃ : X := h₁ h₂, ` where h₁ h₂ are in context
-- forwardsLibraryReasoning,                          -- `have h₃ : X := l h₂, ` where h₁ in context and l is found through a search procedure.
-- expandPreExistentialHypothesis,                    -- no direct equivalent in Lean. This seems to be a conditional `unfold` followed by `cases`.
-- elementaryExpansionOfHypothesis,                   -- would this be something like `unfold * at *` or `dsimp at *`? Currently `at *` also effects the goal.
-- backwardsReasoning,                                -- this is something like; `apply assumption`.
-- backwardsLibraryReasoning,                         -- search through the library and find results whose conclusion can be `apply`ed. We can use an algorithm like SInE to search sensibly.
-- elementaryExpansionOfTarget,                       -- some sort of `unfold *`. Maybe `dsimp`.
-- expandPreUniversalTarget,                          -- this would also be `intros`. So a couple lines up we need something specialised.
-- solveBullets,                                      -- synthesize placeholders.
-- automaticRewrite,                                  -- no direct equivalent in Lean. See Remark (3). -- will be overhauled (E)
-- --Suspension
-- unlockExistentialUniversalConditionalTarget,       -- this is making a placeholder `_` to fill in later, so kind of reminds me of `refine` but not really.
-- unlockExistentialTarget,                           -- see above ^
-- expandPreExistentialTarget,                        -- this seems to be a conditional `unfold`.
-- convertDiamondToBullet,                            -- no direct equivalent in Lean.-- tag identifiers in some way
-- --EqualitySubstitution
-- rewriteVariableVariableEquality,                   -- no direct equivalent in Lean. See Remark (3). -- Me and Tim want to overhaul these anyway so let's not worry about them too much. (E)
-- rewriteVariableTermEquality                        -- no direct equivalent in Lean. See Remark (3). -- In the original GG implementation they just had a library of carefully chosen rewrite rules, so I don't think these will scale anyway (E)

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

Remark (4). For the suspension moves we might be able to use Lean's metavariables. On the other hand,
I have bad experiences with using metavariables before specifying their value.

-/