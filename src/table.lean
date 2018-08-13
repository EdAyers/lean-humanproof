
open expr
open native
/-Lightweight wrapper around `rbtree` because I keep swapping out which table I am using -/
universes u
meta def table (α : Type u) := rb_set α 
namespace table
    variables {α : Type u} [has_lt α] [decidable_rel ((<) : α -> α -> Prop)]
    meta def empty : table α := mk_rb_set
    meta def from_list (l : list α) : table α  := rb_map.set_of_list l
    meta def to_list (d : table α) : list α := rb_set.to_list d
    meta def union  (l : table α ) (r : table α) := rb_set.fold r l (λ x s, rb_set.insert s x)
    meta def contains : table α  -> α -> bool := rb_set.contains
end table
export table
