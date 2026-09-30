
#import "common.typ": *

#show ref: theoretic.show-ref
= Basis of the Paradoxes

While the previous paradoxes are based in naive set theory, the Girard–Hurkens paradox is formulated in a formal type theory.
For this reason, several changes have to be made to the definitions and proofs, from the logical formulation to the definition of sets.

Note that we continue to use $forall_(x in alpha) beta$ to represent $Pi_(x : alpha) beta$, and $A -> B$ to represent $Pi_(x : A) B$ where $x$ does not occur in $B$.
The reasoning behind this involves the Curry-Howard correspondence, which equates proofs of propositions with terms of types.

== Logical Formulation

While many are familiar with the logical formulations of type theory with respect to inductive types, inductive types pose their own scheme, which is not actually necessary for this paradox, so we avoid them.
Instead, we take advantage of a certain embedding of the logical forms that acts equivalently to a view pattern.

#definition(<def:falsehood>)[
  Define the falsehood type as $bot := forall_(A in st) A$, and the negation of a type $A$ as $not A := A -> bot$.
]

#definition(<def:truth>)[
  The truth type is $top := bot -> bot$
]

The constructor for $top$ and eliminator for $bot$ are omitted.

=== Logical Connectives

The usual definitions of the logical connectives of conjunction and disjunction are well known.
Slightly less known are their non-inductive impredicative definitions, which we will use here.

#definition(<def:logic_and>)[
  Define the logical conjunction of two types $A$ and $B$ as $A and B := forall_(C in st) (A -> B -> C) -> C$.
  We define the pair of two elements $(x , y)$ in $A$ and $B$ as $(x , y) := Lambda C . lambda p . p x y$.
  We also define the projections $pi_1 : A and B -> A$ and $pi_2 : A and B -> B$ as $pi_1 := lambda p . p A (lambda x y . x)$ and $pi_2 := lambda p . p B (lambda x y . y)$.
]

Similar to truth, we won't end up using disjunction, but we define it for completeness.
#definition(<def:logic_or>)[
  Define the logical disjunction of two types $A$ and $B$ as $A or B := forall_(C in st) (A -> C) -> (B -> C) -> C$.
  We define the injection of an element $x$ in $A$ as $"inL"(x) := Lambda C . lambda f g . f x$, and the injection of an element $y$ in $B$ as $"inR"(y) := Lambda C . lambda f g . g y$.
]

We leave the elimination rules for the reader to deduce.

=== Sigma types

The remaining type is the $Sigma$ (dependent pair) type.
Somewhat surprisingly, even the $Sigma$ type can be defined using an encoding.

#definition(<def:sigma>)[
  Given a type $A$ and a dependent type $B : A => st$, we define $Sigma A B := forall_(C in st) (forall_(x in A) B(x) -> C) -> C$.
]

For brevity, we shall write the above $Sigma A B$ as $Sigma_(x : A) B(x)$#footnote[$x$ not occurring in $B$] as well as $exists_(x in A) B(x)$ for the same.

The projections and constructor are defined as follows:
#definition(<def:sigma_util>)[
  Given a type $A$, a dependent type $B : A => st$, an element $x : A$, and an element $y : B(x)$, we define the pair $(x , y) := Lambda C . lambda p . p x y$.

  In addition, we define the projections $pi_1 : Sigma_(x : A) B(x) -> A$ and $pi_2 : forall_(p in Sigma_(x : A) B(x)) B(pi_1(p))$ as $pi_1 := lambda p . p A (lambda x y . x)$ and $pi_2 := lambda p . p (B(pi_1(p))) (lambda x y . y)$.
]
Because of the slightly more complex nature of the $Sigma$ type, we will explicitly prove that the elimination rules are as expected.
#lemma[
  Given a type $A$, a dependent type $B : A => st$, as well as a dependent type $C : Pi_(x : A) Pi_(y : B(x)) st$, and a function $f : Pi_(x : A) Pi_(y : B(x)) -> C(x, y)$, and a $p : Sigma_(x : A) B(x)$, we have $C(pi_1(p), pi_2(p))$.

  In addition, if $p := (x , y)$, then $C(x, y) equiv C(pi_1(p), pi_2(p))$
]
#proof[
  // TODO
]

=== Equality
Equality, for as much discussion as it is given in Homotopy Type Theory, Cubical Type Theory, and many other theories, is defined quite simply here.
Namely, equality is defined as yet another encoding, and is also required to be homogeneous.

The obvious choice for this description is the indiscernibility of identicals (id-id), also called Leibniz equality.

#definition(<def:equality>)[
  Given a type $A$, and two elements $x, y : A$, we define $x =_? y := forall_(phi in A => st) phi(x) -> phi(y)$.
]

#lemma[
  Leibniz equality is a rewriting equivalence relation
]
#proof[
  The proof of this, while non-trivial, is well known and outside of the scope of this paper. Suffice it to say, everything shares properties with itself, universality is symmetric, and transitivity is composition.
]

We actually will take a concept from Homotopy Type Theory, that of the "fiber" type.
#definition(<def:fiber>)[
  A fiber of $f : A -> B$ at $b : B$ is defined as $fiber(f, b) := Sigma_(x : A) f(x) =_? b$.
  That is, a fiber is a solution of $f$ for $b$.
  Importantly, we have $value : forall_(fiber(f, b)) A$ (refer to the above for the types), where $value(p) =_? b$, as well as $mkfiber(f, a) : fiber(f, f(a))$, where $mkfiber(f, a) := (a, refl(f(a)))$.
]

Fibers are important to the first paradox, but not the second.
=== Basic Sets

While both of our systems use sets in slightly different ways, there are nonetheless commonalities we can exploit.
#definition(<def:set>)[
  Given a type $A$, the set of $A$, $[ A ] := A => st$.
  We write $x in A$ to mean that $A(x)$ is derivable, i.e., $in(x, A) := A(x)$
]

Interestingly, just like in set theory, the simplest set to define is the empty set
#lemma(<def:empty_set>)[Existence of empty set][
  There is a set $emptyset : [ A ]$ (for any $A$) where $emptyset := lambda x bot$.
]

We can also define (we will end up using this only in the first paradox) what it means for a set to be a subset of another:

#definition(<def:subset>)[
  Given a type $A$, and two sets $S, T : [ A ]$, we define $S subset T := forall_(x in A) x in S -> x in T$#footnote[Given that we don't particularly care about set equality, we use this in lieu of the slightly more accurate $subset.eq$]. Predicate-wise, a predicate $phi$ describes a subset of the set described by $psi$ if $phi(alpha) -> psi(alpha)$
]

Also, we define two pairs of set operations, raising and lowering.

#definition(<def:lower1>)[
  Given a type $A$, a lowering function $down : lower_1(A)$ $lower_1(A) := [ A ] -> A$ is a mapping from sets to elements (i.e., sets can be(come) "corresponding" elements#footnote[Note that these are not _equal_, but they should be equivalent])
]
#definition(<def:raise1>)[
  Given a type $A$, a raising function $up : raise_1(A)$ $raise_1(A) := A -> [ A ]$ is a mapping from elements to sets (i.e., elements can be(come) "corresponding" sets)
]

#note[
  These are for the first paradox, in the second we will instead use $lower_2(A) := [[ A ]] -> A$ and $raise_2(A) := A -> [[ A ]]$
]

=== Mappings

Rather interestingly, as it turns out, $[...]$ is a contravariant functor (by composition).
However, there does exist a mapping from $A -> B$ to $[ A ] -> [ B ]$, although the mapping is not as simple, it is still a useful mapping.

#definition(<def:set_map>)[
  There is a function $map : (A -> B) -> ([ A ] -> [ B ])$ ($A$ and $B$ are arbitrary types) such that $map(f, S) := { y : B | Sigma_(v : fiber(f, y)) (value(v) in S) }$
]

This maps a function on the elements $f : A -> B$ to an injection on the sets $F : A arrow.hook.r B$, which is that every element of the range has a corresponding element of the domain.

#note[
  While we will not use it, it is noteworthy that this is how some cardinalities are defined in infinite set theory (i.e., $|"Nat"| <= |"Even"|$) because there exists a mapping from $"Nat" arrow.hook.r "Even"$.
  As we will demonstrate, there exists a type $uni$ such that $uni arrow.hook.r [ uni ]$ exists, and $[ uni ] arrow.hook.r uni$ exists, and that, while not _bijections_ per se, they are "close enough" to indicate a separate problem relating to Cantor's paradox (and indeed these are the functions at issue here).
]

#definition(<def:set_rmap>)[
  As a utility as we end up using it quite a bit, given a function $map : (A -> B) -> F[A] -> F[B]$, where $F$ is a functor, we can also define $rmap : F[A -> B] -> A -> F[B]$, as $rmap(f, x) := map(lambda g . g(x), f)$
]

This is to say, $map$ takes a function and returns the set of all things that are solutions to that function over a certain domain.
Even more simply, if $g$ inverts $f$, then $map(f, S) = { y : B | g(y) in S }$.


=== Universes
What is important about these is that they say a given type has sets that behave like elements of the type.
Of course, there aren't any good examples of (useful) types that have either of these properties, but they are still useful, for the following reason:
#definition(<def:universes>)[
  A universe, $uni$, is defined as a function from a carrier type, to a lowering function#footnote[A corresponding lowering function, again, for now we will use $uni_1$, but the second uses $uni_2$, in which case the relevant function is actually $lower_2$] of that type, to an instance of the carrier type.
  That is, $uni := forall_(X in st) lower(X) -> X$
]

Universes are important because they represent a type whose elements are effectively "sets".
The way it does this is through cleverly avoiding induction by instead using an encoding.

The way it does this is quite fascinating.
Given that $mu$ is the fixed point combinator, define $uni' := mu(lambda u . lower(u))$, that is, $uni' <=> [uni'] => uni'$. This is slightly more obviously the usual definition of a ZF set (every set is just a predicate over sets, and nothing else).
We can then discover that, there is a unique mapping from $uni$ to $uni'$, although not vice versa, and the reason is that if we have $"comp" : [ uni' ] => uni'$, then if we have $u : uni$ then we can simply do $u(uni', "comp") : uni'$ ($uni'$ is lowerable so we can construct it)#footnote[For the second paradox, change every $[...]$ in this paragraph to $[[...]]$].


Even more interestingly, despite the earlier observation that almost no interesting raising and lowering functions exist, the universe has both.

#lemma(<lem:lower_uni>)[
  There exists a lowering function $down : lower(uni)$
]
#proof[
  First, we deal with the lowering function.
  We first take our argument, $U : [uni]$, and note that the goal is $uni$.
  We then note that $uni equiv forall_(X in st) lower(X) -> X$, and thus introduce $X : st$ and $down' : lower(X)$.
  We then specify the inner universe to have carrier $X$, thus yielding $U' := map(U, x)$, of type $[ lower(X) -> X ]$.
  By then applying @def:set_rmap to $U'$ and $down'$ we can get $U'' := rmap(U', down')$, of type $[ X ]$, finally, we apply $down'$ again thus yielding the goal.
]

Intuitively, this function specializes the inner universe, then uses the fact that the inner universe has a lowering function to yield a set of carrier types, then lowers that result (i.e., it "squashes" two universes into one).

#lemma[
  There exists a raising function $up : raise(uni)$
]
#proof[
  This proof is simpler (at least in explanation) than the previous.
  The reason for this is that we can introduce the universe $u$, and then set the _carrier_ to itself be $[ uni ]$. This means that if we have $[[ uni ]] -> [ uni ]$, we also have $[ uni ]$, and the function can be obtained as $rmap(down)$.
]

#definition(<def:eta_rho>)[
  There are two interesting functions we wish to define: $eta : [ uni ] -> [ uni ]$ and $rho : uni -> uni$.
  The way they are defined is _almost_ the same.
  $rho := down compose up$, and $eta := map(down) compose map(up)$
]
#note[
  $eta$ and $rho$ are not provable inverses of each other.
  As a matter of fact, if they were this would yield Cantor's paradox (a bijection between a set and its power set). However, while these are not _identities_ they have certain properties that nonetheless make them in certain cases act like identities.
]


