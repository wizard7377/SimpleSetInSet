{-# OPTIONS --type-in-type #-}
module Girard where
    open import Base hiding (ι) public

    U' : Set -> Set -- A singlular layer of the universe (effectivly one eliminator over the universe)
    U' X = lower X -> X

    -- Rather than having U be defined inductivly (as U : Set, with comp : ⟦ U ⟧ → U),
    -- we instead define it using a generic eliminator, which is always as general as the
    -- universe (as the universe has no structure beyond this property)
    U : Set -- The generic eliminator
    U = (X : Set) → U' X

    _⊂_ : [ A ] → ⟦ A ⟧ → Set 
    A ⊂ B = A ∈ B

    _⊃_ : ⟦ A ⟧ → [ A ] → Set 
    A ⊃ B = B ⊂ A


    spec : {X : Set} -> U -> U' X
    spec {X} u = u X

    spec-set : {X : Set} -> ⟦ U ⟧ → ⟦ U' X ⟧
    spec-set {X} u = map (spec {X}) u

    {-# INLINE spec #-}

    ↓ : lower U -- Sets of universes correspond to universes
    ↓
        u -- : ⟦ U ⟧ ie, the input 
        = -- : U
        λ
        X -- The carrier type
        l -- The lowering requirement, that ⟦ X ⟧ → X
        → let

        u' : ⟦ U' X ⟧ -- We specify u to specifically having the carrier X (ie, ⟦ lower X → X ⟧)
        u' = spec-set u

        r : ⟦ X ⟧ -- We already had lower X, so we apply it, yielding just a double set of X
        r = amap u' l 
        in l r -- Use the lowering function again to get X back

    ↓' : lower ⟦ U ⟧
    ↓' = map ↓

    ↑ : raise U
    ↑
        u -- : U , the input
        = -- : ⟦ U ⟧, the output
        u ⟦ U ⟧ ↓' -- This is much simpler than the lowering one
        -- Simply specify this to lower ⟦ U ⟧ → ⟦ U ⟧, noting that we already have lower U, and mapping it, thus yielding the desired result

    ρ : fixed U
    ρ = ↓ ∘ ↑ -- The way this works is interesting. First, we apply ↑ , which uses the ↓ as a justification for why U can be a carrier, then itself applies ↓ to the same, thus yielding back a form that is almost, but not exactly, the same

    -- Note that this has recursive terms
    -- ρ with only ↑ unfolded
    ρ' : fixed ⟦ U ⟧
    ρ' = map ρ

    -- comprehension ⟨ x / P ⟩ is opaque, so ↑ (↓ w) no longer reduces to ρ' w; bridge it with map fusion
    ↑↓⊂ρ' : ∀ {w p} → p ∈ ↑ (↓ w) → p ∈ ρ' w
    ↑↓⊂ρ' p∈ = map-fuse (map-fuse p∈)

    ρ'⊂↑↓ : ∀ {w p} → p ∈ ρ' w → p ∈ ↑ (↓ w)
    ρ'⊂↑↓ p∈ = map-split (map-split p∈)

    ρ↑ : fixed U
    ρ↑ u = ↓ (u ⟦ U ⟧ ↓')

    ι : ∀ {T : Set} → T → T
    ι = λ x → x -- Identity function

    {-# INLINE ι #-}

    _∈ᵤ_ : U → U → Set
    x ∈ᵤ y = ∀ q → q ⊂ ↑ y → x ∈ q 

    γ₁ : {A B : Set} → [ A ∧ B ] → [ A ]
    γ₁ p = ⟨ x / (∀ y → p ∋ (x , y)) ⟩

    γ₂ : {A B : Set} → [ A ∧ B ] → [ B ]
    γ₂ p = ⟨ y / (∀ x → p ∋ (x , y)) ⟩


    M : (A → B) → (A → ⟦ B ⟧) → [ A ∧ [ B ] ]
    -- The set of all pairs q, r such that if r in q then q in r
    -- r is a subset of q and r contains q
    M ↘ ↗ = ⟨ qr / curry (λ q r →
        r ⊂ ↗ q →
        r ∋ ↘ q) qr ⟩

    -- The family of sets such that each subset (say, S) such that every superset of S in contained in S (well foundedness) (∀ T . S ⊂ T → S ∋ T) 
    Ω : ⟦ U ⟧
    Ω = γ₂ (M ι ↑)

    make∈Ω : ∀ {p} → (∀ x → p ⊂ ↑ x → p ∋ x) → p ∈ Ω
    make∈Ω prf = make∋ λ x → make∋ (curry-intro (prf x))

    elim∈Ω : ∀ {p} → p ∈ Ω → (∀ x → p ⊂ ↑ x → p ∋ x)
    elim∈Ω p∈Ω x = curry-elim (elim∋ (elim∋ p∈Ω x))
    -- λ y → (x : U) → (x , y) ∈ M ι ↑


    -- (∀ S . S ⊂ T → S ∋ T) (the family of sets) (say, T) such that every subset of T contains T (ie, T is self-membered) (T ∉ T)
    δ : [ ⟦ U ⟧ ]
    δ = γ₁ (M ↓ ι)
    -- Rusell set
    Δ = (cmap ↑ δ) 

    make∈Δ : ∀ {u} → (∀ p → p ⊂ ↑ u → p ∋ ρ u) → u ∈ Δ
    make∈Δ prf = make∋ (make∋ λ p → make∋ (curry-intro (prf p)))

    elim∈Δ : ∀ {u} → u ∈ Δ → (∀ p → p ⊂ ↑ u → p ∋ ρ u)
    elim∈Δ u∈Δ p = curry-elim (elim∋ (elim∋ (elim∋ u∈Δ) p))
    ~Δ = ~ Δ

    wf : ⟦ U ⟧
    wf = ⟨ p / (∀ x → p ⊂ ↑ x → x ∈ p) ⟩

    atomic : [ U ]
    atomic = ⟨ p / ρ p ∈ᵤ p ⟩

    -- By the definition of M and (↓ Ω)
    p∈Ω→p∈ρΩ : (p : [ U ]) → p ⊂ Ω → p ∈ ρ' Ω
    p∈Ω→p∈ρΩ p prf = make∋ (make∈Ω λ x ρp⊂↑x → make∋ (elim∈Ω prf (ρ x) (ρ'⊂↑↓ (make∋ ρp⊂↑x))))

    -- If something is ill founded everywhere, then it must be ill founded at Ω, and because (↓ Ω) is a set, (↓ Ω) must form an infinte chain wrt p
    p∈Ω→Ω∈p : (p : [ U ]) → p ⊂ Ω → ↓ Ω ∈ p
    p∈Ω→Ω∈p p prf₀ = prf₁ prf₂
        where

        prf₁ : (p ⊂ (↑ (↓ Ω)) → p ∋ (↓ Ω))
        prf₁ = elim∈Ω prf₀ (↓ Ω)

        prf₂ : (↑ (↓ Ω) ∋ p)
        prf₂ = ρ'⊂↑↓ (p∈Ω→p∈ρΩ p prf₀)

    -- If u contains the set of non-chains, then u itself must not form a chain
    ~Δ∈Ω : ~Δ ∈ Ω
    ~Δ∈Ω = make∈Ω λ u prf₀ → make∋ λ u∈Δ → let

        prf₁ : ∀ p → p ⊂ ↑ u → p ∋ ρ u
        prf₁ = elim∈Δ u∈Δ

        prf₂ : ~Δ ⊂ ↑ u → ~Δ ∋ ρ u 
        prf₂ = prf₁ ~Δ

        prf₃ : ~Δ ∋ ρ u
        prf₃ = prf₂ prf₀

        prf₄ : ∀ p → p ⊂ (↑ (ρ u)) → p ∋ (ρ (ρ u))
        prf₄ p p⊂↑ρu = elim∋ (prf₁ (cmap ρ p) (elim∋ (↑↓⊂ρ' p⊂↑ρu)))
        in elim∋ prf₃ (make∈Δ prf₄)

    -- p contains only descrending chains
    Ω∈Δ : ↓ Ω ∈ Δ
    Ω∈Δ = make∈Δ λ p prf → elim∋ (p∈Ω→Ω∈p (cmap ρ p) (elim∋ (↑↓⊂ρ' prf)))

    -- But because ~~Δ forms a descending chain it must also be true that (↓ Ω) does not form a descending chain
    Ω∉Δ : ↓ Ω ∉ Δ
    Ω∉Δ = elim∋ (p∈Ω→Ω∈p ~Δ ~Δ∈Ω)

    -- Ergo, the (↓ Ω) set must both contain only descending chains and non descending chains
    paradox : ⊥
    paradox = Ω∉Δ Ω∈Δ


    module Notes where

        -- With comprehension ⟨ x / P ⟩ opaque, Ω and wf are no longer definitionally equal, only equal in membership
        Ω⊆wf : ∀ {p} → p ∈ Ω → p ∈ wf
        Ω⊆wf p∈Ω = make∋ λ x → elim∈Ω p∈Ω x

        wf⊆Ω : ∀ {p} → p ∈ wf → p ∈ Ω
        wf⊆Ω p∈wf = make∈Ω (elim∋ p∈wf)


