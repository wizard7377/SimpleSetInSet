{-# OPTIONS --type-in-type #-}
-- Hurkens-style paradox with a single powerset:
--   lower A = [ A ] → A,   raise A = A → [ A ]
-- No postulates; everything comes from Base (Church ∃, ∧, _===_, ⊆, fiber_at_, ⊥ = ∀ α → α).
module Paradox where
    open import Base hiding (map; lower; raise)

    -- Base's lower/raise use the double powerset ⟦_⟧; this file uses the single one
    lower raise : Set → Set
    lower A = [ A ] → A
    raise A = A → [ A ]
    opaque 

        U : Set
        U = (SET : Set) → lower SET → SET

        makeU : ((SET : Set) → lower SET → SET) → U
        makeU prf = prf

        elimU : U → ((SET : Set) → lower SET → SET) 
        elimU prf = prf


    -- [_] is contravariant, so the covariant action is the direct image:
    -- b is in the image when p meets the fiber of f over b
    opaque

        map : {A B : Set} → (A → B) → [ A ] → [ B ]
        map {A} f a = ⟨ y / Σ [ x of A ] ((x ∈ a) ∧ (x ∈ (fiber f at y))) ⟩
    opaque

        _⊂_on_ : [ A ] → [ B ] → (A → B) → Set
        x ⊂ y on f = ∀ e → e ∈ x → f e ∈ y

        make⊂ : ∀ {f : A → B} {x : [ A ]} {y : [ B ]} → (∀ e → e ∈ x → f e ∈ y) → x ⊂ y on f
        make⊂ f = f 

        elim⊂ : ∀ {f : A → B} {x : [ A ]} {y : [ B ]} → x ⊂ y on f → (∀ e → e ∈ x → f e ∈ y)
        elim⊂ f = f
    

    -- def is the defining equation of each function
    ↓X→U→X : {X : Set} → lower X → U → X
    ↓X→U→X {X} l u = elimU u X l


    opaque

        ↓ : lower U
        ↓ [u] =
          makeU λ X ↓X →
            ↓X (map (↓X→U→X ↓X) [u])

        ↑ : raise U
        ↑ u = elimU u [ U ] (map ↓)

    ρ : U → U
    ρ = ↓ ∘ ↑

    η : [ U ] → [ U ]
    η [u] = map ↓ (map ↑ [u])

    ↓' : lower U
    ↓' p = makeU λ X l → l (map (λ u → elimU u X l) p)

    ↑' : raise U
    ↑' u = elimU u [ U ] (map ↓)

    ρ' : U → U
    ρ' = ↓ ∘ ↑

    η' : [ U ] → [ U ]
    η' p = map ↓ (map ↑ p)
    opaque
        unfolding ↓ ↑
        def↓ : ↓ === ↓'
        def↓ = refl

        def↑ : ↑ === ↑'
        def↑ = refl

        defρ : ρ === ρ'
        defρ = refl

        defη : η === η'
        defη = refl

    {-# INLINE ↓' #-}
    {-# INLINE ↑' #-}
    {-# INLINE ρ' #-}
    {-# INLINE η' #-}

    opaque
        unfolding map
        unfolding U

        -- introduction: a witness in p whose image is b
        image :
          ∀ {f : A → B}
          {p y} x →
          x ∈ p →
          f x === y →
          y ∈ map f p
        image  {f = f} {p = p} {y = y} x x∈p fx≡y = make∋ (Σ-intro x prf)
          where
            fxy-fiber : x ∈ (fiber f at y)
            fxy-fiber = make∋ fx≡y

            prf : (p ∋ x) ∧ (x ∈ (fiber f at y))
            prf = (x∈p , fxy-fiber)
          

        map∈ : ∀ {p} → (f : A → B) → p ⊂ map f p on f
        map∈ _ = make⊂ λ _ x∈p → image _ x∈p refl

        -- elimination: map f p ⊂ q whenever f sends p into q
        map⊂ : ∀ (f : A → B) {p} q → p ⊂ q on f → map f p ⊂ q on ι
        map⊂ f {p} q x∈p→fx∈q = prf₄
          where

            prf₁ : ∀ {e} → e ∈ map f p → Σ [ x of _ ] ((x ∈ p) ∧ (x ∈ (fiber f at e)))
            prf₁ e∈fp = elim∋ e∈fp

            prf₂ : ∀ {e} x → x ∈ (fiber f at e) → f x === e
            prf₂ x fx≡e = elim∋ fx≡e

            prf₃ : ∀ e x → x ∈ p → x ∈ (fiber f at e) → e ∈ q
            prf₃ e x x∈p fx≡e = replace {P = q ∋_} _ (prf₂ x fx≡e) (elim⊂ x∈p→fx∈q _ x∈p)

            prf₄ : map f p ⊂ q on ι
            prf₄ = make⊂ λ e e∈fp → Σ-elim (prf₁ e∈fp) (curry2 (prf₃ e))

        map-∘ : ∀ {f : A → B} {g : B → C} {p} → map g (map f p) ⊂ map (g ∘ f) p on ι
        map-∘ {f = f} {g = g} {p = p} = prf₅
          where

            prf₁ : ∀ {e} → e ∈ map g (map f p) → Σ [ y of _ ] ((y ∈ map f p) ∧ (y ∈ (fiber g at e)))
            prf₁ e∈gfp = elim∋ e∈gfp

            prf₂ : ∀ {e} x y → x ∈ (fiber f at y) → y ∈ (fiber g at e) → g (f x) === e
            prf₂ x y fx≡y gy≡e = trans (cong (elim∋ fx≡y)) (elim∋ gy≡e)

            prf₃ : ∀ e y → y ∈ (fiber g at e) → ∀ x → x ∈ p → x ∈ (fiber f at y) → e ∈ map (g ∘ f) p
            prf₃ e y gy≡e x x∈p fx≡y = image x x∈p (prf₂ x y fx≡y gy≡e)

            prf₄ : ∀ e y → y ∈ map f p → y ∈ (fiber g at e) → e ∈ map (g ∘ f) p
            prf₄ e y y∈fp gy≡e = Σ-elim (elim∋ y∈fp) (curry2 (prf₃ e y gy≡e))

            prf₅ : map g (map f p) ⊂ map (g ∘ f) p on ι
            prf₅ = make⊂ λ e e∈gfp → Σ-elim (prf₁ e∈gfp) (curry2 (prf₄ e))

        -- U, ↓, ↑ and η are opaque, so ↑ (↓ p) no longer reduces to η p; bridge it here
        -- by unfolding η, then ↑, then ↓ (everywhere at once), after which both sides compute to the same set
        ↑↓⊂η : ∀ {p} → ↑ (↓ p) ⊂ η p on ι
        ↑↓⊂η {p} =
          (replace {P = λ h → h (↓ p) ⊂ map ↓ (map h p) on ι} _ (sym def↑)
          (replace {P = λ h → elimU (h p) [ U ] (map h) ⊂ map h (map (λ u → elimU u [ U ] (map h)) p) on ι} _ (sym def↓)
          (make⊂ λ _ e∈ → e∈)))

        η⊂↑↓ : ∀ {p} → η p ⊂ ↑ (↓ p) on ι
        η⊂↑↓ {p} =
          (replace {P = λ h → map ↓ (map h p) ⊂ h (↓ p) on ι} _ (sym def↑)
          (replace {P = λ h → map h (map (λ u → elimU u [ U ] (map h)) p) ⊂ elimU (h p) [ U ] (map h) on ι} _ (sym def↓)
          (make⊂ λ _ e∈ → e∈)))

        lift∈ : ∀ {p} → p ⊂ ↑ (↓ p) on ρ
        lift∈ {p} = make⊂ λ u u∈p → replace {P = λ h → h u ∈ ↑ (↓ p)} _ (sym defρ) (elim⊂ η⊂↑↓ _ (elim⊂ prf₂ _ (elim⊂ prf₁ u u∈p)))
          where

            prf₁ : p ⊂ map ↑ p on ↑
            prf₁ = map∈ ↑

            prf₂ : map ↑ p ⊂ η p on ↓
            prf₂ = replace {P = λ h → map ↑ p ⊂ h p on ↓} _ (sym defη) (map∈ ↓)

        -- η(S) ∈ ρ'(S) (because (ρ ~ ↓ ∘ ↑) and (η ~ map ↓ ∘ map ↑)) then (η p ~ map ↓ (map ↑ p) ⊂ map ↓ (map ↑ p) ~ ρ' p)
        lift⊂ : ∀ {p} → ↑ (↓ p) ⊂ map ρ p on ι
        lift⊂ {p} = make⊂ λ e e∈ →
          replace {P = λ h → e ∈ map h p} _ (sym defρ) (elim⊂ map-∘ e (replace {P = λ h → e ∈ h p} _ defη (elim⊂ ↑↓⊂η e e∈)))

        comp⊂ :
          {A B C : Set} →
          {p : [ A ]} → {q : [ B ]} {r : [ C ]}
          {g : B → C} {f : A → B} →
          p ⊂ q on f →
          q ⊂ r on g →
          p ⊂ r on (g ∘ f)
        comp⊂ {A} {B} {C} {p} {q} {r} {f} {g} p⊂q q⊂r = make⊂ λ e e∈p → elim⊂ q⊂r (g e) (elim⊂ p⊂q e e∈p)
    opaque

        V : [ [ U ] ] -- The set of all complete universes (sets that contain all their subsets)
        V = ⟨ p / (∀ x → ↑ x ⊂ p on ι → x ∈ p) ⟩
        
        make∈V : ∀ {p} → ((∀ x → ↑ x ⊂ p on ι → x ∈ p) → p ∈ V)
        make∈V p∈V = make∋ p∈V

        elim∈V : ∀ {p} → (p ∈ V → (∀ x → ↑ x ⊂ p on ι → x ∈ p))
        elim∈V p∈V = elim∋ p∈V
    opaque

        Ω : [ U ]                   -- the well-founded elements (the minimal universe) ie, elements in every universe, (which is equivalent to the minimal definition))
        Ω = ⟨ x / (∀ p → p ∈ V → x ∈ p) ⟩

    Ω' : U 
    Ω' = ↓ Ω
    opaque
      unfolding Ω

      make∈Ω : ∀ {x} → (∀ p → p ∈ V → x ∈ p) → x ∈ Ω 
      make∈Ω prf = make∋ prf

      elim∈Ω : ∀ {x} → x ∈ Ω → (∀ p → p ∈ V → x ∈ p)
      elim∈Ω prf = elim∋ prf

    ↬ : U → Set
    ↬ x = ρ x ∈ ↑ x

    -- if a universe contains a given set, we don't generate anything by applying ρ to it
    p∈V→ρp∈V : ∀ {p} → p ∈ V → (cmap ρ p) ∈ V
    p∈V→ρp∈V {p} p∈V = make∈V (λ _ → prf₅)
      where
        variable

          x : U

        prf₁ :
          ↑ x ⊂ cmap ρ p on ι →
          ↑ x ⊂ p on ρ
        prf₁ ↑x⊂p∘ρ = make⊂ (λ u u∈↑x → elim∋ (elim⊂ ↑x⊂p∘ρ u u∈↑x))

        prf₂ :
          ↑ x ⊂ cmap ρ p on ι →
          map ρ (↑ x) ⊂ p on ι -- mapping over the args of one equiv to mapping over the results of another
        prf₂ ↑x⊂p∘ρ = map⊂ ρ p ((prf₁ ↑x⊂p∘ρ))

        prf₃ :
          ↑ x ⊂ cmap ρ p on ι →
          ↑ (ρ x) ⊂ p on ι -- perform the mapping
        prf₃ {x} ↑x⊂p∘ρ = make⊂ λ e e∈↑ρx → elim⊂ (prf₂ ↑x⊂p∘ρ) e (elim⊂ lift⊂ e (replace {P = λ h → e ∈ ↑ (h x)} _ defρ e∈↑ρx))

        prf₄ :
          ↑ x ⊂ cmap ρ p on ι →
          ρ x ∈ p -- Recalling that V is the set of all things that contain their subsets, we must have x in p
        prf₄ ↑x⊂p∘ρ = elim∈V p∈V (ρ _) (prf₃ ↑x⊂p∘ρ)

        prf₅ :
          ↑ x ⊂ cmap ρ p on ι →
          x ∈ cmap ρ p
        prf₅ ↑x⊂p∘ρ = make∋ (prf₄ ↑x⊂p∘ρ)

    -- Well-founded sets are a subset of well founded sets with ρ
    Ω⊂ρΩ : Ω ⊂ (cmap ρ Ω) on ι
    Ω⊂ρΩ = prf₄
      where
        variable

          p : [ U ]

          x : U

        prf₁ :
          x ∈ Ω →
          p ∈ V →
          x ∈ cmap ρ p
        prf₁ x∈Ω p∈V = elim∈Ω x∈Ω (cmap ρ _) (p∈V→ρp∈V p∈V)

        prf₂ :
          x ∈ Ω →
          p ∈ V →
          ρ x ∈ p
        prf₂ x∈Ω p∈V = elim∋ (prf₁ x∈Ω p∈V)

        prf₃ : Ω ⊂ Ω on ρ
        prf₃ = make⊂ λ _ x∈Ω → make∈Ω (λ _ → prf₂ x∈Ω)

        prf₄ : Ω ⊂ cmap ρ Ω on ι
        prf₄ = make⊂ λ _ x∈Ω → make∋ (elim⊂ prf₃ _ x∈Ω)


    Ω⊂Ω : Ω ⊂ Ω on ρ
    Ω⊂Ω = make⊂ λ u u∈Ω → elim∋ (elim⊂ Ω⊂ρΩ u u∈Ω)

    -- Ω is the minimal V
    Ω-minV : ∀ u → u ∈ V → Ω ⊂ u on ρ
    Ω-minV u u∈V = make⊂ λ u' u'∈Ω → elim∈Ω (elim⊂ Ω⊂Ω _ u'∈Ω) _ u∈V 

    -- u∈V→Ω⊂u
    -- Ω contains itself
    Ω∈Ω : ↓ Ω ∈ Ω
    Ω∈Ω = make∈Ω (λ _ → prf₅)
      where

        variable u : [ U ]

        prf₃ :
          u ∈ V →
          map ρ Ω ⊂ u on ι
        prf₃ u∈V = map⊂ ρ _ (Ω-minV _ u∈V)

        prf₄ :
          u ∈ V →
          ↑ (↓ Ω) ⊂ u on ι
        prf₄ u∈V = make⊂ λ e e∈↑Ω → elim⊂ (prf₃ u∈V) e (elim⊂ lift⊂ e e∈↑Ω)

        prf₅ :
          u ∈ V →
          ↓ Ω ∈ u
        prf₅ u∈V = elim∈V u∈V _ (prf₄ u∈V)

    -- Ω' is self-membered, up to ρ  (uses (A) at p := W)
    ↬Ω : ↬ (↓ Ω)
    ↬Ω = elim⊂ lift∈ _ Ω∈Ω

    Δ : [ U ]
    Δ = ⟨ x / ¬ (↬ x) ⟩

    ↬u→↬ρu : ∀ u → ↬ u → ↬ (ρ u)
    ↬u→↬ρu u prf = replace {P = λ h → ρ (ρ u) ∈ ↑ (h u)} _ (sym defρ) (elim⊂ lift∈ _ prf)

    Δ∈V : Δ ∈ V
    Δ∈V = make∈V (λ _ → prf₄)
      where

        variable u : U

        prf₁ :
          ↑ u ⊂ Δ on ι →
          ↬ u →
          ¬ ↬ (ρ u)
        prf₁ u⊂Δ ρu∈u = elim∋ (elim⊂ u⊂Δ _ ρu∈u)

        prf₃ :
          ↑ u ⊂ Δ on ι →
          ¬ ↬ u
        prf₃ u⊂Δ ρu∈u = prf₁ u⊂Δ ρu∈u (↬u→↬ρu _ ρu∈u)

        prf₄ :
          ↑ u ⊂ Δ on ι →
          u ∈ Δ
        prf₄ u⊂Δ = make∋ (prf₃ u⊂Δ)
    

    p∈V→Ω∈p :
      ∀ p →
      p ∈ V →
      ↓ Ω ∈ p
    p∈V→Ω∈p p p∈V = elim∈Ω Ω∈Ω p p∈V 

    Ω∈Δ : ↓ Ω ∈ Δ
    Ω∈Δ = p∈V→Ω∈p _ Δ∈V -- Ω∈Ω Δ Δ∈V

    ¬↬Ω : ¬ (↬ (↓ Ω))
    ¬↬Ω = elim∋ Ω∈Δ

    paradox : ⊥
    paradox = ¬↬Ω ↬Ω
