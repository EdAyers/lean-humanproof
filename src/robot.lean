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
    section
    variables {m : Type → Type} [applicative m] {α : Type} -- [HACK] I got bored trying to get the universe poly to work.
        def list.filterm (pred : α → m (bool)) : list α → m (list α)
        |[] := pure []
        |(h::t) := pure (λ (b:bool) t, if b then h::t else t) <*> pred h <*> list.filterm t
    end
    section
        variables {m : Type → Type} [monad m] {α : Type}
        def list.anym (pred : α → m bool) : list α → m bool
        |[] := pure ff
        |(h::t) := do b ← pred h, if b then pure tt else list.anym t
        def list.allm (pred : α → m bool) : list α → m bool
        |[] := pure tt
        |(h::t) := do b ← pred h, if b then list.allm t else pure ff
    end
end 

/--Run the given tactic, get the returned value. But don't keep the tactic's state. -/
meta def tactic.hypothetically {α} (tb : tactic α) : tactic α :=
    λ s, result.cases_on (tb s)
        (λ a _, interaction_monad.result.success a s)
        interaction_monad.result.exception

/--This information is needed so frequently I'm bundling them into their own structure.-/
meta structure statement :=
(body : expr)
(type : expr)
(refs : table expr)

meta instance : has_to_tactic_format statement := ⟨λ a, do bpp ← tactic.pp a.body, tpp ← tactic.pp a.type, pure $ bpp ++ " : " ++ tpp⟩

/--Robot needs some extra data on hypotheses to track when things can be deleted and so on.-/
meta structure hyp_datum :=
(vuln : bool) -- the hypothesis has been used previously and so is vulnerable for deletion.
(cannot_substitute : dict nat (table expr)) -- The expressions that have previously been used on the nth argument.
meta def hyp_datum.init : hyp_datum := {vuln := ff , cannot_substitute := empty}

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
    meta def is_vuln (h : expr) : robot bool := do
        hd ← get_hyp_data,
        pure $  option.cases_on (get h hd) ff hyp_datum.vuln
    meta def set_vuln (h : expr) : robot unit :=
        -- [TODO] make sure it really is a hypothesis and not just some random expression.
        map_hyp_data (dict.modify_default hyp_datum.init (λ hd, {vuln := tt, ..hd}) h)
    meta def get_cannot_substitute (hyp:expr) : robot (dict nat (table expr)) := do
        hd ←  dict.get hyp <$> get_hyp_data,
        pure $ option.get_or_else (hyp_datum.cannot_substitute <$> hd) empty
    meta def get_targets : robot $ list $ statement :=
        tactic.get_goals >>= list.choosem get_statement
    /--Clear the hyp but also update the hyp_data entry.-/
    meta def clear_hyp (h : expr) : robot unit := do
        tactic.clear h,
        map_hyp_data (dict.erase h)
    /--Run the given tactic. But throw away the state made by the tactic.-/
    meta def hypothetically {α} (t : robot α) : robot α :=
        ⟨λ rs, tactic.hypothetically (t.run rs)⟩
    meta def init : tactic (robot_state) := pure {hyp_data := empty}
    meta def run {α} (r : robot α) : (tactic α) := do
        i ← init,
        ⟨a,s⟩ ← state_t.run r i,
        pure a
end robot

section TEST
--test `hypothetically`
variables (p q r : Prop)
example : p → q → q := begin
    intros,
    tactic.hypothetically (do tactic.set_goals []),
    assumption
end
end TEST