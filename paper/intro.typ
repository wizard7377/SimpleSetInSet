#import "common.typ": *

#show ref: theoretic.show-ref
= Introduction

To understand the Girard–Hurkens paradox, we must first understand its two influences, the Burali-Forti paradox and the Russell paradox.
Both of these are paradoxes of set theory, specifically set theory that does not distinguish between sets and classes.

The (naive) set theory needed is constructed as follows:

#axiom[
  The sets, $st$, are defined by any predicate over sets $phi$#footnote[That is, $phi : st => "Prop"$], where ${ phi }$ is the set of all sets $x$ such that $phi(x)$ is true.
  We also denote the same as ${ x | phi(x) }$ (assuming $x$ does not occur in $phi$).
  We relate sets and their predicates by defining membership to be $x in { phi } := phi(x)$.
]

This definition of sets allows us to construct the empty set, $0 := { x | bot }$, as well as the singleton for any set $x$, where ${ x } := { y | y =_? x }$.
Also, by the equivalence of predicates and sets, we can also define $A union B = { x | x in A or x in B}$ and $A inter B = { x | x in A and x in B }$.
Likewise, the negation of a set $A$ is defined as $~ A := { x | x in.not A }$.

We include some helpful notations to make the definitions more readable:
#note[
  We write $forall_(x in A) p$ for $forall_(x in st) (x in A => p)$
]

== Russell's Paradox

Because the definition never requires that the predicate $phi$ have any properties, we can define the following set:

#definition[
  Let the "Russell set" be defined as $Delta := { x | x in.not x }$, that is, $Delta$ contains the sets that are not members of themselves
]

#remark[
  At first, it might seem that $Delta$ should contain every set.
  Apart from the contradiction that arises, there actually are sets that are not members of $Delta$.
  For instance, in Quine's New Foundations, there are "Quine atoms" which are defined as $"atom" := { "atom" }$.
]

From this, we can derive a contradiction as follows:

#lemma[
  $Delta$ is not a member of itself, $Delta in.not Delta$.
] <lem:delta_nin_delta>
#proof[
  Introduce the assumption that $Delta in Delta$.
  By the definition of $Delta$ and membership, we have $Delta in { x | x in.not x }$, then $Delta in.not Delta$.
]

#lemma[
  $Delta$ is a member of itself $Delta in Delta$.
]

#proof[
  Reduce the goal to $Delta in { x | x in.not x }$, then $Delta in.not Delta$.
  This is @<lem:delta_nin_delta> .
]

Obviously, these two are contradictory.

== Burali-Forti Paradox (simplified)

To understand Burali-Forti, we must first understand what "well-founded sets" are.

#definition(<def:well_founded>)[
  A set $A$ is well founded if it is one of:
  1. The empty set, $bot$
  2. A set that only contains well founded sets, i.e., $forall_B B in A => "is well founded"(B)$ is true
]

#lemma[
  @def:well_founded is equivalent to the following definition:
  A set is well founded if and only if all its elements are, that is, $wellFounded(A) := forall_(B in A) wellFounded(B)$
]

#proof[
  Since the only other part of this is that $wellFounded(bot)$, we prove that $wellFounded(bot)$ by our definition, that is, $forall_(A in bot) wellFounded(A)$, which is vacuously true.
]

#definition(<def:set_order>)[
  Define the size#footnote[Not the cardinality] of a set, $|A|$ to be:
  1. Zero for the empty set
  2. The sum of the sizes of the elements of $A$ for a non-empty set, plus 1
]

#definition(<def:set_omega>)[
  Define the set of well founded sets, $Omega := { A | wellFounded(A) }$.
  Likewise, define the size of this set as $omega$
]

#lemma(<lem:set_large_ord>)[
  for any choice of $A in Omega$, $|A| < omega$.
]
#proof[
  The proof is trivial and irrelevant enough to be omitted here.
]

#lemma(<lem:set_omega_wf>)[
  $Omega$ is well founded, that is, $wellFounded(Omega)$.
]
#proof[
  $wellFounded(Omega)$ becomes $forall_(A in Omega) wellFounded(A)$, which is true by the definition of $Omega$.
]

#lemma(<lem:set_omega_omega>)[
  The set $Omega$ is a member of itself
]
#proof[
  By @<lem:set_omega_wf>, $Omega$ is well founded, and by @<def:set_omega>, $Omega in Omega$.
]

From this, we can prove that $|Omega|$ must be less than itself.
#theorem[Burali-Forti Paradox][
  $|Omega| < |Omega|$.
]

#proof[
  By @<lem:set_large_ord>, for any $A in Omega$, $|A| < omega$, however, by @<lem:set_omega_omega>, $Omega in Omega$, so $|Omega| < omega$, which we can rewrite as $|Omega| < |Omega|$.
]

=== A second definition of well-foundedness

While the above definition for well foundedness is sufficient, there are a couple parts about it that are less than ideal.
Firstly, it requires recursion (the elements have to follow the same predicate).
Fortunately, there is an even simpler definition of well foundedness that doesn't involve self reference, or even loops of any sort.

#definition(<def:quasi_universes>)[
  The set of quasi-universes, $V_+$ is defined as ${ p | forall_(x in st) x subset p -> x in p }$, that is, a quasi-universe is its own powerset
]

#lemma[
  If we do not assume the axiom of foundation (or equivalent axioms), then $V_+$ may contain sets that are _not_ $Omega$.
]
#proof[
  Let $A$ be some arbitrary set.
  Form $Omega(A)$ through the same process as $Omega$, but instead of starting with the empty set, start with $A$'s powerset, thus yielding a set which is not well founded (and therefore not $Omega$) but is a quasi-universe.
]

While this does mean that every quasi-universe might not be $Omega$, they still must all _contain_ $Omega$, as the empty set's powerset is a subset of every other set's powerset, and therefore $Omega(emptyset)$ ($Omega$) is a subset of every other $Omega(A)$.


