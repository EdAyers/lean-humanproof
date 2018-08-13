

universe u
variables (σ : Type u) (m : Type u -> Type u) [monad m]
@[reducible] def stateT (α : Type u) := σ  -> m (σ × α)
instance : monad (stateT σ m) :=
    { map := λ α β (f :α -> β) (sa : stateT σ m α) s, sa s >>= λ ⟨s,a⟩, pure ⟨s, f a ⟩
    , pure := λ α a s, pure ⟨s, a⟩ 
    , bind := λ α β (sa : stateT σ m α) (f : α -> stateT σ m β) s, sa s >>= λ ⟨s,a⟩, f a s
    }