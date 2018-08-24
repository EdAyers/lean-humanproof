
open expr
open native
/-Lightweight wrapper around `rbtree` because I keep swapping out which dictionary implementation I am using -/
meta def table (α : Type) : Type := rb_set α
namespace table
    variables {α : Type} [has_lt α] [decidable_rel ((<) : α → α → Prop)]
    meta def empty : table α := rb_map.mk α unit
    meta instance table_has_emptyc : has_emptyc (table α) := ⟨empty⟩
    meta def from_list (l : list α) : table α  := rb_map.set_of_list l
    meta def to_list (d : table α) : list α := rb_set.to_list d
    meta def union  (l : table α ) (r : table α) := rb_set.fold r l (λ x s, rb_set.insert s x)
    meta instance table_has_union : has_union (table α) := ⟨union⟩
    meta def subtract (l : table α) (r : table α) := rb_set.fold r l (λ x s, rb_set.erase s x)
    meta instance table_has_sub : has_sub (table α) := ⟨subtract⟩
    meta def contains : α → table α → bool := λ a t, rb_set.contains t a
    meta def insert : α → table α → table α := λ a t, rb_set.insert t a
    meta instance table_has_insert : has_insert α (table α) := ⟨insert⟩
    meta def erase : table α → α → table α := rb_set.erase
    -- hmm. I don't know what the folding convention is.
    meta def fold {β} : (α → β → β) → β → table α → β  := λ r z t, rb_set.fold t z r
    meta def mfold {T} [monad T] {β} (f : α → β → T β) (init : β) (t : table α) : T β := rb_set.mfold t init f
    meta def all (p : α → bool) : table α → bool := option.is_some ∘ mfold (λ a _, if p a then some () else none) ()
    /--Return `tt` if at least one of the elements satisfies the predicate-/
    meta def any (p : α → bool) : table α → bool := option.is_none ∘ mfold (λ a (x : unit), if p a then none else some ()) ()
    meta def filter (p : α → bool) : table α → table α := fold (λ k t, if p k then insert k t else t) empty
    meta instance [has_to_tactic_format α] : has_to_tactic_format (table α) := ⟨λ t, mfold (λ a f, do ap ← tactic.pp a, pure $ f ++ ap ++ ", ") ("") t >>= (λ f, pure $ "{|" ++ f ++ "|}" ) ⟩
end table

meta def dict (k : Type) (α : Type) : Type := rb_map k α
namespace dict
    variables {k : Type} [has_lt k] [decidable_rel ((<) : k → k → Prop)]
    variable {α : Type}
    meta def empty : dict k α := rb_map.mk k α
    meta instance : has_emptyc (dict k α) := ⟨empty⟩
    meta def insert : k → α → dict k α → dict k α := λ k a d, rb_map.insert d k a
    meta def get : k → dict k α → option α := λ k d, rb_map.find d k
    meta def modify (f : option α → α) (key : k) (d : dict k α) : dict k α := insert key (f $ get key d) d
    meta def modify_default (default : α) (f : α → α) : k → dict k α → dict k α := modify (λ o, f $ option.get_or_else o default)
    meta def get_default (default : α)  (key : k) (d: dict k α) : α := option.get_or_else (get key d) default
    meta def erase : k → dict k α → dict k α := λ k d, rb_map.erase d k
    meta def merge (l r : dict k α) := rb_map.fold r l insert
    meta instance : has_append (dict k α) := ⟨merge⟩
    meta def fold {β} (r : k → α → β → β) (z : β) (d : dict k α) : β := rb_map.fold d z r
    meta def mfold {T} [monad T] {β} (f : k → α → β → T β) (z : β) (d : dict k α) : T β := rb_map.mfold d z f
    meta def map {β} (f : α → β) (d : dict k α) : dict k β := rb_map.map f d
    meta def filter (p : k → α → bool) (d : dict k α) := fold (λ k a d, if p k a then insert k a d else d) empty d
    meta def collect {β} (f : k → α → dict k β) := fold (λ k a d, d ++ f k a) empty
    meta def choose {β} (f : k → α → option β) := fold (λ k a d, match f k a with (some b) := insert k b d | none := d end) empty
end dict

/--dictionary with a default if it doesn't exist. You define the default when you make the dictionary. -/
meta structure dictd (k : Type) (α : Type) : Type :=
(dict : dict k α)
(default : k → α)
namespace dictd
  variables {k : Type} [has_lt k] [decidable_rel ((<) : k → k → Prop)] {α : Type}
  private meta def empty (default : k → α) : dictd k α := ⟨dict.empty, default⟩
  meta def get (key : k) (dd : dictd k α) : α := dict.get_default (dd.2 key) key dd.1
  meta def insert (key : k) (a : α) (dd : dictd k α) : dictd k α := ⟨dict.insert key a dd.1, dd.2⟩
  meta def modify (f : α → α) (key : k) (dd : dictd k α) : dictd k α := ⟨dict.modify (λ o, f $ option.get_or_else o (dd.2 key)) key dd.1, dd.2⟩

end dictd