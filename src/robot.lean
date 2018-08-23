import meta.expr
import table

open expr table dict

section
    universes u v w
    /--Monadic version of `choose` aka `filter_map`. -/
    def list.choosem {m : Type u → Type v} [applicative m] {α : Type w} {β : Type u} (f : α → m (option β)) : list α → m (list β)
    | []       := pure []
    | (h :: t) := pure (λ (h : option β) (t : list β), option.rec_on h t (λ h, h :: t)) <*> f h <*> list.choosem t
    section
        variables {α: Type u} {β : Type v}
        private def mapi_aux (f : ℕ → α → β) : ℕ → list α → list β
        |n [] := []
        |n (h :: t) := (f n h) :: (mapi_aux (nat.succ n) t)
        def list.mapi (f : ℕ → α → β) := mapi_aux f 0
    end
    variables {m : Type → Type} [applicative m] {α : Type} -- [HACK] I got bored trying to get the universe poly to work.
    def list.filterm (pred : α → m (bool)) : list α → m (list α)
    |[] := pure []
    |(h::t) := pure (λ (b:bool) t, if b then h::t else t) <*> pred h <*> list.filterm t
    def list.anym (pred : α → m bool) : list α → m bool
    |[] := pure ff
    |(h::t) := pure bor <*> pred h <*> list.anym t
    def list.allm (pred : α → m bool) : list α → m bool
    |[] := pure tt
    |(h::t) := pure band <*> pred h <*> list.allm t
end 

/--Run the given tactic, get the returned value. But don't keep the tactic's state. -/
meta def tactic.hypothetically {α} (tb : tactic α) : tactic α :=
    λ s, result.cases_on (tb s)
        (λ a s, interaction_monad.result.success a s)
        interaction_monad.result.exception

/--This information is needed so frequently I'm bundling them into their own structure.-/
meta structure statement :=
(body : expr)
(type : expr)
(refs : table expr)

/--Robot needs some extra data on hypotheses to track when things can be deleted and so on.-/
meta structure hyp_datum :=
(vuln : bool) -- the hypothesis has been used previously and so is vulnerable for deletion.
(cannot_substitute : dict nat (table expr)) -- The expressions that have previously been used on the nth argument.

@[reducible] meta def hyp_data := dict expr hyp_datum

meta structure robot_state :=
(hyp_data : hyp_data)

@[reducible] meta def robot := state_t robot_state tactic
namespace robot
    meta def get_hyp_data : robot hyp_data := robot_state.hyp_data <$> get
    meta def set_hyp_data (hs:hyp_data) : robot unit := modify $ λ s, {robot_state . hyp_data := hs, ..s}
    meta def map_hyp_data (f : hyp_data → hyp_data) : robot unit := f <$> get_hyp_data >>= set_hyp_data
    meta def of_tactic {α : Type} : tactic α → robot α := state_t.lift --[HACK] I get weird name clash errors if I call it `lift`.
    meta instance {α : Type} : has_coe (tactic α) (robot α) := ⟨of_tactic⟩
    meta def get_statement (e : expr) : robot $ option statement := do
        type ← tactic.infer_type e,
        is_prop ← tactic.is_prop type,
        if not is_prop then pure none else do
        refs ← pure $ table.from_list $ expr.list_local_const $ e,
        pure $ some $ {body := e, type := type, refs := refs}
    meta def get_hyps : robot (list statement) := -- [TODO] consider memoising this?
        tactic.local_context >>= list.choosem get_statement
    meta def get_vuln_hyps : robot (list statement) := do
        hd ← get_hyp_data,
        cs ← list.filter (λ x, show bool, from option.cases_on (get x hd) ff hyp_datum.vuln) <$> tactic.local_context,
        list.choosem get_statement cs
    meta def get_cannot_substitute (hyp:expr) : robot (dict nat (table expr)) := do
        hd ←  dict.get hyp <$> get_hyp_data,
        pure $ option.get_or_else (hyp_datum.cannot_substitute <$> hd) empty
    meta def get_targets : robot $ list $ statement :=
        tactic.get_goals >>= list.choosem get_statement
    /--Clear the hyp but also update the hyp_data entry.-/
    meta def clear_hyp (h : expr) : robot unit := do
        tactic.clear h,
        map_hyp_data (dict.erase h)
    /--Run given tactic. But throw away the state made by the tactic.-/
    meta def hypothetically {α} (t : robot α) : robot α :=
        ⟨λ rs, tactic.hypothetically (t.run rs)⟩

end robot
