#import "@preview/ctheorems:1.1.0": *
#import "@preview/commute:0.2.0": node, arr, commutative-diagram
#import "@preview/cetz:0.1.2"

#let TODO(body) = text(blue)[*TODO* #body]

#let oo = [$compose$]

#let cx = [$circle.filled.small$]

#let Vect = [$bold("Vect")$]
#let VF = [$bold("Vect")_FF$]
#let FV = [$bold("FinVec")$]
#let FVR = [$bold("FinVec")_RR$]
#let cC = [$cal(C)$]
#let cD = [$cal(D)$]
#let bC = [$bold(C)$]
#let bH = [$bold(H)$]
#let Im  = [$op("Im")$]
#let Ker  = [$op("Ker")$]
#let over = [$\/$]
#let mapsto = [$|->$]
#let FK = [$underline(FF)_K$]

#let thmboxparams = (
  breakable: true,
  separator: [#h(0em).#h(0.2em)],
  padding: (top: 0.2em, bottom: 0.2em),
  inset: 0em,
  base_level: 1,
)

#let thmboxparams2 = (
  bodyfmt: emph,
)

#let theorem = thmbox(
  "theorem",
  "Theorem",
  ..thmboxparams,
  ..thmboxparams2,
)

#let axiom = thmbox(
  "axiom",
  "Axiom",
  ..thmboxparams,
  ..thmboxparams2,
)


#let lemma = thmbox(
  "theorem",
  "Lemma",
  ..thmboxparams,
  ..thmboxparams2,
)

#let proposition = thmbox(
  "theorem",
  "Proposition",
  ..thmboxparams,
  ..thmboxparams2,
)

#let definition = thmbox(
  "theorem",
  "Definition",
  ..thmboxparams,
)

#let example = thmbox(
  "theorem",
  "Example",
  breakable: true,
  separator: [#h(0em).#h(0.2em)],
  ..thmboxparams,
)

#let remark = thmplain(
  "theorem",
  "Remark",
  breakable: true,
  separator: [#h(0em).#h(0.2em)],
)

#let notation = thmplain(
  "theorem",
  "Notation",
  breakable: true,
  separator: [#h(0em).#h(0.2em)],
)

#let corollary = thmbox(
  "theorem",
  "Corollary",
  ..thmboxparams,
  ..thmboxparams2,
)


#let fw(doc) = box(width: 100%)[#doc]

#let proof(title: "Proof", term) = block(width: 100%, breakable: true)[_#title._ #term #h(1fr) $qed$]

#let project(title: "", subtitle: "", university: "University of Oxford", author: "", date: none, body) = {
  // Set the document's basic properties.
  set document(author: author, title: title)
  set page(
    numbering: "1", 
    number-align: center,
    paper: "a4",
    margin: (
      top: 3.6cm, // Allocating half of the vertical remaining space to the top
      bottom: 3.6cm, // And the other half to the bottom
      inside: 3.5cm, // Larger margin for binding
      outside: 2.5cm // Remaining space for the outer margin
    )
  )
    // width: 15cm,
    // height: 22.5cm,
  set text(
    font: "Linux Libertine", 
    lang: "en", 
    size: 12pt,
  )

  // Title row.
  align(right)[
    #image("imgs/ox-logo.png", width: 8em)
  ]
  align(center)[
    #v(1fr)
    #block(text(weight: 700, 2.3em, title))
    #v(1.5em)
    #block(text(1.5em, author))
    #v(1fr)
    #block(text(1.5em, university))
    #v(2em)
    #block(text(1.5em, subtitle))
    #v(2em)
    #text(1.5em, date)

  ]



  // Main body.
  set par(justify: true)
  set heading(numbering: "1.1.")
  set enum(numbering: "(1)")
  show heading: it => pad(bottom: 2pt, it)
  body
}

