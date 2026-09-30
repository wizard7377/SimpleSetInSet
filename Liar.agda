module Liar where
    open import Base

    {-# NO_POSITIVITY_CHECK #-}
    data Δ : Set where

        ¬Δ→Δ : ¬ Δ → Δ 

    ¬Δ : ¬ Δ
    ¬Δ (¬Δ→Δ f) = f (¬Δ→Δ f)

    ⊤Δ : Δ
    ⊤Δ = ¬Δ→Δ ¬Δ

    ⊤⊥ : ⊥
    ⊤⊥ = ¬Δ ⊤Δ