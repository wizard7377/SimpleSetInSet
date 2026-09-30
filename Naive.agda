module Naive where
    
    open import Base
    open SetOps
    open import Data.Nat
    open import Agda.Builtin.Equality
    
    just : {A : Set} → A → [ A ]
    just {A} a = λ x → x ≡ a
    postulate

        card : [ A ] → ℕ

        card∪ : (p q : [ A ]) → ((card (p ∪ q)) ≡ (((card p) + (card q)) ∸ (card (p ∩ q))))

        card⊆ : (p : [ A ]) → (q : [ B ]) → (f : A → B) → (p ⊆⟨ f ⟩ q) → ((card p) ≤ (card q))

        card1 : (p : [ A ]) → card ⊤ 