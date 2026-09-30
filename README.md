# Agda Paradox

A simpler proof of Girard's paradox, without using induction or pattern matching, using a simpler type-theoretic basis.

A quick overview is given here.

> [!WARNING]
> We make liberal use of opaques, to make it so that terms have simple "normal forms".[^1]
> In addition, we use some syntax here that differs from the source, but the rough idea is the same.

## Universal Properties

We note that a predicate `φ` on `A` may have a "least element" `x` such that `φ x <-> (y : A) -> φ y`.
One example of this is the von Neumann universe.
Namely, let `V(S, 0) := S`, and `V(S, n + 1) := [ V(S, n) ]`, i.e., `V(S, ω)` is the universe of ZF, but extended by a set of atomic symbols `S`.
It must be true that `V(S, n) ⊂ V(T, n) <-> S ⊂ T`, and therefore, to get the "normal" VN universe, we can take `V(∅, ω) = Vω`, but also, because `∅ ⊂ S` always holds, we can also define it "universally", as the set of all things common to each: `Vω := ⋂ (S : *) -> V(S, ω)`, which is the "least" universe of sets.

## Basis of the Paradox

The following are a couple of preliminary definitions.

### Σ types

For any type `A` and a family on `A`, `B`, we define `Σ A B := (C : *) -> ((x : A) -> B x -> C) -> C`.
We then define the following:[^2]

- `x , y := λ C f -> f x y`
- `π1 := λ _ f -> f (λ x y -> x)`
- `π2 := λ _ f -> f (λ x y -> y)`

We can then define `A × B := Σ A (λ _ -> B)`, and `A + B := (C : *) -> (A -> C) -> (B -> C) -> C`, with similar definitions.

> [!NOTE]
> From here on out we write `Σ (x : A) B` for `Σ A (λ x -> B)`

### Equality

Define equality on `A` as `x = y := (φ : A -> *) -> φ x -> φ y`.
Then, we have `refl := λ _ x φ -> φ x`, and `sym := λ _ x y p φ -> p (λ z -> φ z)`.

Furthermore, we have `Fiber f y := Σ (x : A) (f x = y)`.

### Set Theory

A set over element type `A` is just a family over that type, i.e., `[ A ] := A -> *` (`2^A`).
We then identify the comprehension, `< x | P x >` with `λ x -> P x`, and the membership relation, `x ∈ S` with `S x`.

These sets are not "traditional" set theoretic sets.
Firstly, every set only contains things that are either:

- not sets
- sets of a rank one lower than the current set
  i.e., `A` doesn't even describe sets, `[ A ]` only describes sets of rank 0 (the aforementioned elements), `[ [ A ] ]` describes sets of rank exactly 1 (not sets of rank 0), and so on.
  We identify the ability of a set to be "lowered", that is, `[ A ] -> A`, the ability to "take sets and turn them into elements", as `lower`, and the inverse is `raise`.

We also note subsets of heterogeneous sets, `S ⊂ T on f` where `S : [ A ]`, `T : [ B ]`, and `f : A -> B` is defined as `S ⊂ T on f := (e : A) -> e ∈ S -> f e ∈ T`.

## Universes

A universe `U` is `U := (SET : *) -> ([ SET ] -> SET) -> SET`, which, notably, is recursive.
Informally, a universe is a set of anything that can itself be made into a set.
Even more simply, because this is universal, `U` just is the ZF universe.

### Lowering and Raising

There exists a

[^1]: In reality, upon delta-expansions, all these terms become much more complex or non-terminating, but it's still useful to see how we reach them.

[^2]: So that this remains "simple" we don't give most of the actual definitions.
