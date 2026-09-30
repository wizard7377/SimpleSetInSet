{-# OPTIONS --type-in-type -WnoInstanceWithExplicitArg #-}
module Base where

    variable

        A B C : Set

    module Pair where
        opaque

            _∧_ : Set -> Set -> Set -- Church encoding of pairs
            A ∧ B = ∀ R → (A → B → R) → R

            _,_ : A → B → A ∧ B -- Church encoding based constructor of pairs
            _,_ x y = λ R f → f x y

            π₁ : (A ∧ B) → A -- First elem (by elim)
            π₁ {A} p = p A (λ x _ → x)

            π₂ : (A ∧ B) → B -- Second elem (by elim)
            π₂ {A} {B} p = p B (λ _ y → y)

            Σ : (A : Set) → (A → Set) → Set -- Church encoding of existential quantification
            Σ A B = ∀ R → ((x : A) → B x → R) → R

            Σ-intro : {B : A → Set} → (x : A) → B x → Σ A B -- a witness and its proof
            Σ-intro x prf = λ R f → f x prf

            Σ-elim : {B : A → Set} {R : Set} → Σ A B → ((x : A) → B x → R) → R
            Σ-elim {R = R} p f = p R f

            curry : {A B C : Set} → (A → B → C) → (A ∧ B) → C
            curry f p = f (π₁ p) (π₂ p)
        syntax Σ A (λ x → B) = Σ [ x of A ] B

        -- curry computes on pairs, but with ∧ opaque this only holds up to transport
        opaque
            unfolding _∧_

            curry-intro : {P : A → B → Set} {x : A} {y : B} → P x y → curry P (x , y)
            curry-intro prf = prf

            curry-elim : {P : A → B → Set} {x : A} {y : B} → curry P (x , y) → P x y
            curry-elim prf = prf

        curry2 : {A : Set} {B C D : A → Set} → ((X : A) → B X → C X → D X) → (X : A) → (B X ∧ C X) → D X
        curry2 f x p = f x (π₁ p) (π₂ p)

    module IdId where



      opaque 
        _===_ : {A : Set} → A → A → Set
        _===_ {A} x y = ∀ (p : A → Set) → p x → p y

        mkId : {A : Set} → {x : A} → {y : A} → (∀ (p : A → Set) → p x → p y) → (x === y)
        mkId prf = prf 

        unId : {A : Set} → {x y : A} → (x === y) → (∀ (p : A → Set) → p x → p y)
        unId prf = prf

        refl : {x : A} → x === x
        refl = mkId λ p z → z

        sym : {x y : A} → x === y → y === x
        sym {x = x} p = unId p (λ z → z === x) refl

        trans : {x y z : A} → x === y → y === z → x === z
        trans p q = mkId λ r prf → unId q r (unId p r prf)

        cong : {f : A -> B} → {x y : A} → x === y → f x === f y
        cong p = mkId λ q prf → unId p _ prf

        replace : {P : A → Set} → {x : A} → (y : A) → x === y -> P x → P y
        replace {P = P} y prf p = prf P p

    module Basis where

        ⊥ : Set _ -- Falsehood as ∀ α . α (we don't even assert false, as this is equivalent)
        ⊥ = ∀ α → α

        ⊤ : Set _
        ⊤ = ∀ α → α → α

        unit : ⊤
        unit = λ α x → x

        ¬_ : Set _ -> Set _ -- Negation
        ¬_ A = A -> ⊥

        _∘_ : ∀ {A B C : Set _} → (B -> C) -> (A -> B) -> A -> C -- Restricted composition. In here we only need the independent version
        g ∘ f = λ x → g (f x)

        ι : {A : Set _} → A → A
        ι x = x
    module Base where
        open Basis

        opaque

          [_] : Set → Set
          [ S ] = S → Set

          comp : (A → Set) → [ A ]
          comp P = P
          syntax comp (λ X → Y) = ⟨ X / Y ⟩

          _∋_ : [ A ] → A → Set
          A ∋ x = A x

          make∋ : {p : A → Set} → {x : A} → p x → comp p ∋ x
          make∋ prf = prf

          elim∋ : {p : A → Set} → {x : A} → comp p ∋ x → p x
          elim∋ prf = prf 

        

        ⟦_⟧ : Set -> Set -- A shorthand for doubled sets
        ⟦ S ⟧ = [ [ S ] ]

        ~_ : [ A ] -> [ A ] -- Inversion of sets (where the comprehension predicate is false)
        ~ S = ⟨ x / ¬ (S ∋ x) ⟩

        _∈_ : {S : Set} -> S -> [ S ] -> Set -- Membership is defined as comprehension predicate holding at a value
        A ∈ B = B ∋ A


        _∉_ : {S : Set} -> S -> [ S ] -> Set
        A ∉ B = ¬ (A ∈ B)

        -- Subset operator
        _⊆⟨_⟩_ : {S T : Set} → [ S ]  → (S → T) → [ T ] → Set
        S ⊆⟨ f ⟩ T = ∀ {x} → x ∈ S → f x ∈ T

        -- Powerset operator (the set of all subsets of this)

    module SetOps where
        open Basis
        open Base
        open Pair public

    module Rank where
        open Basis
        open Base

        -- lower A corresponds to the set of all sets of A is a valid element
        lower : Set -> Set -- lower A corresponds to "double sets of this are valid elements"
        lower S = ⟦ S ⟧ → S

        raise : Set -> Set -- raise A corresponds to "elements of this are valid double sets"
        raise S = S → ⟦ S ⟧


        fixed : Set -> Set
        fixed S = S → S

        -- Not really a property of universes, but because [ A ] is contravariant in A,
        -- then ⟦ A ⟧ is covariant
        map : (A -> B) -> ⟦ A ⟧ -> ⟦ B ⟧
        map f x = ⟨  s / (x ∋ ( ⟨ y / s ∋ (f y) ⟩ ))  ⟩

        amap : ⟦ (A -> B) ⟧ → A -> ⟦ B ⟧
        amap t x = map (λ f → f x) t

        cmap : (A → B) → [ B ] → [ A ]
        cmap f p = ⟨ y / p ∋ f y ⟩

        -- map is functorial, but with ⟨_⟩ opaque this only holds up to membership
        opaque
          unfolding comp

          map-fuse : {f : A → B} {g : B → C} {x : ⟦ A ⟧} {s : [ C ]} → s ∈ map g (map f x) → s ∈ map (g ∘ f) x
          map-fuse s∈ = s∈

          map-split : {f : A → B} {g : B → C} {x : ⟦ A ⟧} {s : [ C ]} → s ∈ map (g ∘ f) x → s ∈ map g (map f x)
          map-split s∈ = s∈

    module Topos where
        open Pair
        open IdId
        open Basis
        open Base

        Fiber_at_ : {A : Set} {B : Set} → (A → B) → B → Set

        Fiber_at_ {A} {B} f y = Σ [ x of A ] (f x === y)

        Give : {A B : Set} → (f : A → B) (x : A) {y : B} → (f x === y) → Fiber f at y
        Give f x prf = Σ-intro x prf

        -- Fibers as subsets: x ∈ (fiber f at y) is exactly f x === y.
        -- Unlike Fiber (a Church Σ), membership keeps the point and its proof together,
        -- so nothing needs a dependent projection.
        fiber_at_ : {A B : Set} → (A → B) → B → [ A ]
        fiber f at y = ⟨ x / f x === y ⟩


    open Pair public
    open IdId public
    open Basis public
    open Base public
    open Rank public
    open Topos public
