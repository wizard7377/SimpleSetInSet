
#include "common.typ"

#import "@preview/unequivocal-ams:0.1.2": ams-article
#import "@preview/color-my-agda:0.2.0": init-color-my-agda
#show: init-color-my-agda
#show: ams-article.with(
  title: [Girard's Paradox Simplified],
  authors: (
    (
      name: "Asher Frost",
      department: [Department of Mathematics],
      organization: [University of Exampleville],
      location: [Tennessee, TN 59341],
      email: "jdoe@math.ue.edu",
      url: "math.ue.edu/~jdoe",
    ),
  ),
  abstract: [
    The Girard–Hurkens paradox is the basis for much hierarchical type theory, and proves a shockingly general result about the nature of universes.
    Despite this, no accessible proof of the paradox that does not require induction exists.
    Here, we present a step-by-step explanation of the paradox, with lemmas, using nothing but definitions.
  ],
  bibliography: bibliography("refs.bib"),
)


#include "intro.typ"
#include "basis.typ"
#include "paradox.typ"

#let basesrc = read("./Base.agda")
#let paradoxsrc = read("./Paradox.agda")

= Appendix

== Agda Code
#raw(basesrc, lang: "Agda", block: true)
=== The Paradox Itself
#raw(paradoxsrc, lang: "Agda", block: true)
