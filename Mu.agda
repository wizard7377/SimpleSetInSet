{-# OPTIONS --type-in-type #-}
module Mu where

    open import Base 

    {-# TERMINATING #-}
    μ : ((A → B) → (A → B)) → A → B
    μ f x = f (μ f) x

    Δ : {A : Set} → ((A → ⊥) → (A → ⊥)) → A → ⊥
    Δ = μ

    ⊤⊥ : ⊥
    ⊤⊥ = Δ (λ f → f) unit 