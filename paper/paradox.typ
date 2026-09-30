#import "common.typ": *

#show ref: theoretic.show-ref
= Simpler Paradox

The paradox described here is heavily inspired by the work#inline-note[Cite trouble with typing type in type]

However, unlike the original website's implementation, we make several design changes:
1. `SET` (which is now $uni$) is no longer (defined) inductivly, but instead as a simple alias
2. We do not make use of the standard library's $top$ and $bot$, and $"bool"$, instead making use of variants that are both simple type aliases and not inductive // FIXME include link to above definitions


We also#footnote[In particular, our identity types have no properties beyond there type, while the structure of $equiv$ is special in Agda] do not make use of either built-in $Sigma$ types or equality types, instead making our own (again, as above)

A number of these make reference to a generalization of the subset relation, specically one where we compare elements of different underlying types

#definition(<def:subset_tt>)[
  Given types $A$ and $B$, a set $p : [ A ]$, and a set $q : [ B ]$, alongside a projection $f : A -> B$, we define $p subset_f q := forall_(x in A) x in p -> f(x) in q$
]

Note that $A$ and $B$ need to be equivalent.
Per as a matter of fact, in the extreme case of either $A equiv bot$ or $B equiv top$, they will never be related to each other.
However, for any "sensible"#footnote[These "sensible" relations end up being the ones where $f$ is injective], $A$ and $B$ will in fact be meaningfully related by $f$.

At this point, one could argue that $p subset_f q$ dosen't define a subset relation, but rather a ordering on the cardinalities of $p$ and $q$ (assuming, again, that $f$ is injective).
This is quite reasonable that when we consider that by the above definition, $bb(N)^+ subset_abs bb(N)^-$, and vice versa.
However, the distinction is irrelevant, ultimately,


== Mapping Properties
There are several important properties of the function $map$ that will be exceptionally important here

#lemma(<lem:map_image>)[
  Given a function $f : A -> B$, a set $S : [ A ]$, and an element $x in A$, a value $y : B$, as well as a proof that $f(x) =_? y$, then we have that $y in map(f, S)$
]
#proof[
  Rewrite the goal to $y in {y' in B | Sigma_(v : fiber(f, y')) value(v) in S }$, or even more simply, $exists_(v : fiber(f, y)) value(v) in S$.
  The first part of the fiber is $x$, and we already have a proof that $f(x) =_? y$, so we can use $v := (x, proof)$, and then we have $value(v) =_? x$, and since $x in S$ we have the goal
]

Next, we prove that mapping indeed preserves elements (that is, if $x in A$ then $f(x) in F(A)$)

#lemma(<lem:map_in>)[
  Given a function $f : A -> B$, a set $S : [ A ]$, $x : A$, then if $x in S$ then $f(x) in map(f, S)$.
]

#proof[
  Apply #ref(<lem:map_image>), thereby yielding the requirements $g : A -> B$, $x' in A$, $y : B$, and a proof that $g(x') =_? y$, with $g equiv f$ and with $y equiv f(x)$, where we then have $x' in A$, and a proof that $f(x') =_? f(x)$, to which we can provide $x equiv x'$ and reflexivity
]

This seems trivial, but is actually quite useful to split these and the following into compact lemmas

#lemma(<lem:map_subset>)[
  Given a function $f : A -> B$, two sets $S$ of $A$ and $T$ of $B$, then, if we have $forall_(x in S) f(x) in T$, we also have $forall_(y in map(f, S)) y in T$
]

#proof[
  Introduce everything up to $y in T$, (all the hypothesis are not listed here as there are several), however, the one of note is that $y : B$ and $y in map(f, S)$, which we rewrite as $Sigma_(v : fiber(f, y)) value(v) in S$, and then we introduce $v : fiber(f, y)$ and $value(v) in S$, the goal being $y in T$.

  Thereby the hypothesis $forall_(x in S) f(x) in T$ (with $x equiv value(v)$), we have $f(value(v)) in T$.
  // TODO
]

#lemma(<lem:map_comp>)[
  Mapping distributes (one-way) over composition, that is, $f : A -> B$, $g : B -> C$, and $S : [ A ]$, then $map(g, map(f, S)) subset map(g compose f, S)$
]

#proof[
  Introduce all the premises, and also turn the goal into $e in map(g, map(f, S)) -> e in map(g compose f, S)$, and then introduce $e : C$ and $e in map(g, map(f, S))$, which leaves the goal as $e in map(g compose f, S)$.

  Rewrite the hypothesis, thus yielding $exists_(v : fiber(g, e)) value(v) in map(f, S)$, and then introduce $v : fiber(g, e)$ and $value(v) in map(f, S)$.
  We can then rewrite this _again_, yielding $exists_(v' : fiber(f, value(v))) value(v') in S$, and then introduce $v' : fiber(f, value(v))$ and $value(v') in S$.

  We then rewrite using both fibers, thus yielding that $g(f(value(v'))) =_? e$, we then use #ref(<lem:map_image>) to yield $e in map(g compose f, S)$, which is the goal
]

#lemma(<lem:eta_rho>)[
  For universes $x$ and sets of universes $U$ if $x in U$ then $rho(x) in eta(U)$
]

#proof[
  Expand $eta$ and $rho$, yielding $(down compose up)(x) in map(down(map(up, U)))$, and then first note that by #ref(<lem:map_comp>), we have the goal as $(down compose up)(x) in map(down compose up, U)$, then, by #ref(<lem:map_comp>), we have the goal
]

== Problematic Sets

