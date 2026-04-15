#import "@preview/cetz:0.4.1"
#import "@preview/algorithmic:1.0.7"
#import algorithmic: algorithm
#import "@preview/touying:0.6.1": *
#import themes.simple: *

#show: simple-theme.with(
  aspect-ratio: "16-9",
  //config-common(handout: true)
)

#let ip(a,b) = $ chevron.l #a, #b chevron.r $

#let learning(body) = rect(fill: green.lighten(80%), width: 100%, stroke: green + 0.05em, radius: 0.5em, inset: 0.5em)[_Learning:_ #body]

#title-slide[
  = Letting AI Formalize the Perceptron Mistake Bound

  #v(2em, weak: true)
  #text(1.3em)[#smallcaps[Johann Birnick]]
  #v(2em, weak: true)
  15 April 2026, UCSD
  #v(1em, weak: true)
  Formal Learning Theory Course by Prof. Tianhao Wang
]

== Recall: Perceptron Algorithm

#text(0.8em, [
  Lecture 1: #link("https://teach-learning-theory.tianhaowang.com/notes/notes_1#linear")[#text(blue, [`https://teach-learning-theory.tianhaowang.com/notes/notes_1#linear`])]
])

#image("assets/algorithm2.png")

== Perceptron Mistake Bound

#image("assets/theorem4.png")
#pause
#align(center, [Let's (let AI) formalize this in Lean 4!])

== Perceptron Mistake Bound - Lemmas

#image("assets/theorem4_lemmas.png")

== Perceptron Mistake Bound - Proof

#image("assets/theorem4_proof.png")

= Phase I \ _Prepare Project+Context for the AI_

== Creating the Project

`$ lake +4.28.0 new formalization-perceptron-claude math`

#pause

#text(0.9em)[
- `lake` is the project manager for Lean #pause
- we use Lean version `4.28.0` because that's what `aristotle` supports
  (this is from February 2026, the newest version is `4.29.1`) #pause
- `new` creates a new project #pause
- `formalization-perceptron-claude` is the project name #pause
- `math` is a template which automatically adds `mathlib4` as dependency #pause

#learning[This always takes _multiple minutes_, since it's re-downloading `matlib4` every time, which is multiple GB in size.]
]

== Providing Context and the Informal Proof

#grid(columns: (1fr, auto), [
  I just asked Claude to convert Tianhao's nice website into a Markdown file. #pause

  #text(0.5em)[
  ```md
  ### 1.1 The prediction protocol

  We fix an *instance space* $\mathcal{X}$, which is the set of all possible inputs (images, emails, points in $\mathbb{R}^d$, etc.), and a binary *label space* $\mathcal{Y} = \{0, 1\}$. A *hypothesis* is any function $h : \mathcal{X} \to \mathcal{Y}$ that assigns a label to each instance.

  > **Definition 1** (Online Prediction Protocol).
  > The online prediction protocol proceeds in rounds $t = 1, 2, \ldots, T$:
  >
  > 1. An instance $x_t \in \mathcal{X}$ arrives.
  > 2. The learner predicts $\hat{y}_t \in \mathcal{Y}$.
  > 3. The true label $y_t \in \mathcal{Y}$ is revealed.
  >
  > The *history* available to the learner at the start of round $t$ is $H_{t-1} = ((x_1, y_1), \ldots, (x_{t-1}, y_{t-1}))$.
  ```
  #pause
  ]
], image("assets/claude_website.png", height: 12em))

== Directory Structure

```
formalization-perceptron-claude
├── FormalizationPerceptronClaude
│   └── Basic.lean
├── FormalizationPerceptronClaude.lean
├── lakefile.toml
├── lake-manifest.json
├── lean-toolchain
└── Notes.md       <-- generated from the Lecture 1 website
```

== Making a Prompt

#text(0.9em, font: "LiterationMono Nerd Font Mono")[
  I want you to formalize a mathematical proof in Lean4 (version 4.28.0). #pause The working directory is a new Lean4 project with mathlib4 as a dependency. #pause Read the Notes.md file. Formalize the Perceptron Mistake Bound (Theorem 4) which bounds the number of mistakes that the Perceptron Algorithm (Algorithm 2) can make. #pause Note that the proof uses Lemma 1 and Lemma 2. In the formalized Lean proof, make sure that these two lemmas are also separate lemmas. #pause Make sure the code quality closely follows Mathlib standards.
]

= Phase II \ _Let the AI Work_

== Claude Code (Opus 4.6)

- tried _max_ effort, and after a few minutes of thinking...#pause #image("assets/claude_limit.png") #pause
- when limit was reset, tried _high_ effort, which did the job
- Time: 17min
- Lines of Lean Code: 136 #h(1em) (but many of them are comments)
- #sym.checkmark compiles

== Codex CLI (gpt-5.4 xhigh)

- used 90% of the weekly limit (ChatGPT Pro)
- Time: 10min
- Lines of Lean Code: 235
- #sym.checkmark compiles

== Gemini CLI (gemini-3.1-pro-preview)

- Time: 10min
- Lines of Lean Code: 93 #h(1em) (+ a bunch of test files)
- #sym.checkmark compiles

== Aristotle

```
$ aristotle submit "I want you to [...] follows Mathlib standards." --project-dir ./ --wait
```
#pause
```
Project created: 4002c9ff-fae1-4cff-a677-dc13ce1d280f
Project complete! Getting results...
Project saved to 4002c9ff-fae1-4cff-a677-dc13ce1d280f-aristotle.tar.gz
```
#pause
- provided an additional `ARISTOTLE_SUMMARY.md` file
- Time: 36min
- Lines of Lean Code: 143 #h(1em) (but many of them are comments)
- #sym.checkmark compiles

= Phase III \ _Evaluate_

== Correct Translation of Statement

- they all generalize to arbitrary inner product spaces #pause

- Gemini simplifies samples to $z_i = y_i dot phi.alt(x_i)$ #pause

- Codex is the only one to do a full formalization of the algorithm
  - It doesn't just look at mistake rounds, but formalizes all kind of rounds
  - It even makes a separate datatype for the labels!
  - It's the only one to formalize the feature map $phi.alt$

== Code Quality

- Aristotle and Claude provided the most comments #pause

- Aristotle, Claude, and Gemini are concise.
  Codex has more code, but is the only one to implement/formalize the full algorithm.
  Gemini strips away so much that it might not be obvious that it's equivalent to the natural language statement.

== AI ranking

#grid(columns: (1fr, 1fr, 1fr), [
  Claude ranks:
  1. Codex
  2. Aristotle
  3. Claude
  4. Gemini
], [
  Codex ranks:
  1. Codex
  2. Claude
  3. Aristotle
  4. Gemini
],[
  Gemini ranks:
  1. Codex
  2. Aristotle
  3. Claude
  4. Gemini
])

== Ideas for Future

- ask for more complicated setups/proofs \
  #text(0.9em)[(I want to do the regret bound for Zinkevich's online gradient descent)]

- ask for a Lean proof without providing a natural language proof, or even without a natural language statement (just a Lean statement)

- test open source models (normal coding agents)

- test Google's and Math Inc's Lean proving models \ 
 (How to get access?!)

- test open source Lean proving models
