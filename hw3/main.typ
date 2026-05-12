#let homework(number: [TODO], date: [TODO], course: [TODO], quarter: [TODO], instructor: [TODO], body) = {
  set document(author: "Johann Birnick", title: [Homework #number Submission])
  set page(paper: "us-letter", numbering: "1 / 1", number-align: center)
  set text(lang: "en")

  let sep = [#h(0.5em) • #h(0.5em)]

  align(center, {
    text(2em, [Homework #number Submission])
    v(1em, weak: true)
    text(1.2em, [#smallcaps[Johann Birnick] #sep #link("mailto:jbirnick@ucsd.edu", raw("jbirnick@ucsd.edu")) #sep #date])
  })
  v(2em, weak: true)
  [
    *Course*: #course \
    *Quarter*: #quarter  \
    *Instructor*: #instructor \
  ]
  v(3em, weak: true)

  set par(justify: true, spacing: 0.85em)
  show heading: it => {
    set block(above: 2em, below: 1em)
    set align(center)
    set text(1.2em)
    it
  }

  let linkcolor = blue.darken(25%)
  show link: set text(fill: linkcolor)

  body
}

#let VCdim = math.op("VCdim")

#let proof(body) = [
  _Proof._ #body #h(1fr) $square$
]

#show: homework.with(
  number: 3,
  date: [17 May 2026],
  course: [DSC 291 -- Learning Theory through Formal Proof and Proof Presentation],
  quarter: [Spring 2026],
  instructor: [Tianhao Wang]
)

= Part A

Provided in separate file.

= Part B

1. *Proof of the No-Free-Lunch theorem.*
  The universal objects are the learner $A$, the domain $cal(X)$, and the sample size $n$ with $n < abs(cal(X))/2$.
  The adversary may choose the distribution $cal(D)$ and the realizable target $f^*$ after seeing $A$ and $n$, but before the random sample is drawn.
  I write the proof for deterministic $A$; for a randomized learner, condition also on its internal random seed, so that the same calculation applies after averaging over that seed.

  #proof[
    Assume $n >= 1$.
    For $n = 0$, choose any $x in cal(X)$, let the target label be the opposite of the fixed prediction $A(())(x)$, and put all mass on that labeled point.
    Then the learner has loss $1$, so the theorem is immediate.
    Choose a set
    $
      C = {x_1, dots, x_(2n)} subset.eq cal(X)
    $
    of $2n$ distinct points, which exist because $2n < abs(cal(X))$.
    For every labeling $f : C -> {0,1}$, let $cal(D)_f$ be the uniform distribution on the labeled examples
    $
      {(x, f(x)) mid(|) x in C}.
    $
    Extend $f$ arbitrarily to all of $cal(X)$.
    Then $L_(cal(D)_f)(f)=0$.

    We now average over a uniformly random labeling $F : C -> {0,1}$, equivalently independent fair bits $F(x)$ for $x in C$.
    Draw sample points $X_1, dots, X_n$ independently and uniformly from $C$ (independently of $F$), give the learner the labeled sample
    $
      S = ((X_1,F(X_1)), dots, (X_n,F(X_n))),
    $
    and evaluate it under $cal(D)_F$.

    Let $U(S_X)$ be the number of points of $C$ that do not appear among $X_1, dots, X_n$.
    The output $A(S)$ is a deterministic function of $S$, hence determined by the unlabeled sample points $S_X$ and the labels observed by the learner.
    Conditional on these, the label $F(x)$ of any unseen point $x$ is still an independent fair bit, since $F$ is independent of $S_X$ and its coordinates are mutually independent.
    Hence, for every unseen $x$, the prediction $A(S)(x)$ is fixed while $F(x)$ is an independent fair bit, so
    $
      EE[1[A(S)(x) != F(x)] | S_X, "observed labels"] = 1/2.
    $
    Therefore
    $
      EE_(F,S)[L_(cal(D)_F)(A(S))]
      >= EE[U(S_X)/(2n) dot 1/2]
      = EE[U(S_X)] / (4n).
    $

    For each fixed $x in C$,
    $
      PP[x " is unseen"] = (1 - 1/(2n))^n >= 1/2,
    $
    where the last inequality follows from Bernoulli's inequality:
    $(1 - 1/(2n))^n >= 1 - n/(2n)=1/2$.
    Thus
    $
      EE[U(S_X)]
      = sum_(x in C) PP[x " is unseen"]
      >= 2n dot 1/2
      = n.
    $
    We have shown
    $
      EE_(F,S)[L_(cal(D)_F)(A(S))] >= 1/4.
    $

    Let
    $
      W := L_(cal(D)_F)(A(S)) in [0,1].
    $
    If $p := PP[W >= 1/8]$, then
    $
      EE[W] <= 1/8 dot (1-p) + 1 dot p = 1/8 + 7p/8.
    $
    Since $EE[W] >= 1/4$, it follows that $p >= 1/7$.
    But
    $
      PP_(F,S)[W >= 1/8]
      = EE_F [PP_S[L_(cal(D)_F)(A(S)) >= 1/8]].
    $
    Hence there exists a labeling $f^* : C -> {0,1}$ such that
    $
      PP_S[L_(cal(D)_(f^*))(A(S)) >= 1/8] >= 1/7.
    $
    Taking $cal(D) = cal(D)_(f^*)$ proves the theorem.
  ]

2. *Application to the lower-bound direction of the Fundamental Theorem.*
  The corollary is:
  if $VCdim(cal(H)) = infinity$, then $cal(H)$ is not PAC learnable, even in the realizable setting.

  #proof[
    Suppose, for contradiction, that a learner $A$ PAC learns $cal(H)$ in the realizable setting.
    Apply the PAC guarantee with
    $
      epsilon = 1/9
      quad "and" quad
      delta = 1/8.
    $
    Let $n = n_(cal(H))(1/9, 1/8)$ be the corresponding sample size.
    Since $VCdim(cal(H)) = infinity$, there is a set $C subset.eq cal(X)$ of size $2n$ shattered by $cal(H)$.

    Run the averaging argument from the proof of NFL above on this shattered set $C$.
    That argument uses only that $C$ has $2n$ points; the hypothesis $n < abs(cal(X))/2$ in the theorem statement served only to guarantee such a set exists, which here is supplied directly by infinite VC dimension.
    It produces a distribution $cal(D)$ supported on $C$ and a labeling $f^*$ of $C$ such that
    $
      PP[L_cal(D)(A(S)) >= 1/8] >= 1/7.
    $
    Because $C$ is shattered, some $h^* in cal(H)$ agrees with $f^*$ on all of $C$.
    Since $cal(D)$ is supported on $C$, we have $L_cal(D)(h^*) = 0$.
    Thus $cal(D)$ is realizable by $cal(H)$.

    But the PAC guarantee would require
    $
      PP[L_cal(D)(A(S)) > 1/9] <= 1/8,
    $
    while NFL gives, using $1/8 > 1/9$,
    $
      PP[L_cal(D)(A(S)) > 1/9] >= PP[L_cal(D)(A(S)) >= 1/8] >= 1/7 > 1/8.
    $
    This is a contradiction.
  ]

  A concrete infinite-VC class is the class of finite-subset indicators on $NN$:
  $
    cal(H)_("fin") := {h_A : NN -> {0,1} mid(|) A subset.eq NN " finite"},
    quad
    h_A(x) := 1[x in A].
  $
  This class has infinite VC dimension.
  Indeed, for any finite set $S subset.eq NN$ and any labeling of $S$, let $T subset.eq S$ be the positively labeled points.
  Since $T$ is finite, $h_T in cal(H)_("fin")$ realizes exactly that labeling on $S$.
  Thus every finite $S$ is shattered.
  Applying the corollary, $cal(H)_("fin")$ is not PAC learnable.

3. *Worked construction.*
  Let the domain be
  $
    cal(X) = {a,b,c}
  $
  and consider the following learning rule for one training example:
  after seeing $S=((x_1,y_1))$, output
  $
    A(S)(x) :=
    cases(
      y_1 & "if" x = x_1,
      0 & "otherwise."
    )
  $
  This is the memorization rule that predicts $0$ away from the observed point.
  The domain has three points so that the single training example ($n=1$) satisfies the NFL hypothesis $n < abs(cal(X))/2$; the bad distribution constructed below is supported on the two-point set ${a,b}$.

  Define the target
  $
    f^*(a)=1,
    quad
    f^*(b)=1,
    quad
    f^*(c)=0,
  $
  and let $cal(D)$ be uniform on $(a,1)$ and $(b,1)$.
  Then $L_cal(D)(f^*)=0$.
  If $S=((a,1))$, the learned rule is wrong on $b$ and correct on $a$, so
  $
    L_cal(D)(A(S)) = 1/2.
  $
  If $S=((b,1))$, the learned rule is wrong on $a$ and correct on $b$, so again
  $
    L_cal(D)(A(S)) = 1/2.
  $
  Therefore
  $
    PP_(S " drawn from " cal(D))[L_cal(D)(A(S)) >= 1/8] = 1.
  $
  This example makes the NFL mechanism explicit: the learner has no information about an unobserved point, and the adversary puts the opposite of the learner's default behavior there.

4. *Comparison with the Week 1 No-Free-Lunch theorem.*
  The Week 1 theorem lives in an online prediction setting on a finite domain.
  The learner predicts labels sequentially, and the proof adversary is adaptive: it can choose the next label after seeing the learner's prediction.
  Because the learner is deterministic, the entire interaction is predetermined, so these adaptive choices can be folded into a single fixed target $f$ and ordering -- which is why the statement can be phrased without reference to an adaptive adversary.
  The conclusion is deterministic.
  For a deterministic learner, there exist a target function and an ordering of the domain on which the learner makes a mistake on every round.

  The Week 3 theorem lives in the batch i.i.d. / PAC setting.
  The adversary is oblivious to the realized sample: it chooses a distribution and target labeling before sampling occurs.
  The conclusion is probabilistic.
  With constant probability over the random training sample, the learner's output has constant population loss, even though the distribution is realizable.

  The two statements are quantitatively different because they measure different failures.
  Week 1 measures the number of online mistakes against an adaptive sequence.
  Week 3 measures population risk after a random training sample.
  They are both called "No-Free-Lunch" because the underlying obstruction is the same: without structural restrictions on the target class, labels on unseen points are unconstrained, so no learner can be uniformly reliable.

= Part C

1. I used AI (in a human loop) to write and improve the mini course and the solution to part B.

2. I accepted the general proofs/solutions/sketch it provided.

3. I don't like the writing style of the AI, so I read through the whole solutions and constantly ask it to change phrasing and adapt the write-up, or I change it myself.

4. I read through everything by myself and didn't find any mistakes. (I also asked AI to check it carefully again in the end.)

*AI Workflow.*
Since Codex is faster and allows for more usage in \$20 plan, but Claude can have a more detailed look sometimes, I found it helpful to use Codex for "initial generation" and Claude for improving the manuscript.
I also added more instructions to the `CLAUDE.md`/`AGENTS.md` for my typesetting standards (like using $EE[...]$ for expectation and $PP[...]$ for probability).
