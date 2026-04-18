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

#let proof(body) = [
  _Proof._ #body #h(1fr) $square$
]

#let VCdim = math.op("VCdim")

#show: homework.with(
  number: 2,
  date: [17 April 2026],
  course: [DSC 291 -- Learning Theory through Formal Proof and Proof Presentation],
  quarter: [Spring 2026],
  instructor: [Tianhao Wang]
)

= Part A

1. A labeling $(y_1, dots, y_n) in {0,1}^n$ is realizable by $cal(H)_2$ if and only if the set of positive indices
  $
    S := {i in {1, dots, n} mid(|) y_i = 1}
  $
  is a union of at most two intervals of integers.
  Equivalently, as we scan the labels $y_1, dots, y_n$ from left to right, the labeling switches from $0$ to $1$ at most two times.

  #proof[
    Suppose first that $y_i = 1[x_i in I_1 union I_2]$ for some intervals $I_1, I_2 subset.eq RR$.
    Since $x_1 < dots < x_n$, the sample points that lie in a single interval always form a consecutive block (possibly empty).
    Therefore the positive sample points for $I_1 union I_2$ form a union of at most two consecutive blocks, so as we scan from left to right we can enter the label $1$ region at most twice.

    Conversely, suppose the labeling switches from $0$ to $1$ at most two times.
    Then the positive indices form a union of at most two intervals.
    If both blocks are nonempty, then for some $1 <= a <= b < c <= d <= n$ the positive sample points are exactly
    $
      {x_a, dots, x_b} union {x_c, dots, x_d} .
    $
    Choosing $I_1 = [x_a, x_b]$ and $I_2 = [x_c, x_d]$ realizes exactly this labeling on the sample.
    If there is only one nonempty block, we use just one interval.
    If there is no nonempty block, we use two empty intervals.
  ]

2. By item 1, we only need to count binary strings for which the labeling switches from $0$ to $1$ at most two times.

  There is exactly one such labeling with no $1$'s.

  A labeling with exactly one $0$-to-$1$ switch is determined by choosing its left and right boundary gaps.
  Concretely, choose integers
  $
    0 <= a < b <= n
  $
  and label exactly $x_(a+1), dots, x_b$ by $1$.
  This gives a bijection with $2$-subsets of ${0,1,dots,n}$, hence there are
  $
    binom(n+1, 2)
  $
  such labelings.

  Similarly, a labeling with exactly two $0$-to-$1$ switches is determined by choosing
  $
    0 <= a < b < c < d <= n
  $
  and labeling exactly
  $
    x_(a+1), dots, x_b quad and quad x_(c+1), dots, x_d
  $
  by $1$.
  Hence there are
  $
    binom(n+1, 4)
  $
  such labelings.

  Therefore the exact growth function is
  $
    Gamma_(cal(H)_2)(n) = 1 + binom(n+1, 2) + binom(n+1, 4) .
  $

3. From the formula above,
  $
    Gamma_(cal(H)_2)(4) = 1 + binom(5, 2) + binom(5, 4) = 16 = 2^4
  $
  and
  $
    Gamma_(cal(H)_2)(5) = 1 + binom(6, 2) + binom(6, 4) = 31 < 32 = 2^5 .
  $
  Thus every $4$-point ordered sample is shattered, but no $5$-point sample is.
  Hence
  $
    VCdim(cal(H)_2) = 4 .
  $

  In the realizable online transductive setting on an $n$-point pool, the Halving algorithm therefore makes at most
  $
    floor(log_2 Gamma_(cal(H)_2)(n))
    = floor(log_2(1 + binom(n+1, 2) + binom(n+1, 4)))
  $
  mistakes.

  The Sauer--Shelah bound with $d = 4$ gives
  $
    Gamma_(cal(H)_2)(n) <= sum_(k=0)^4 binom(n, k) .
  $
  In this case the bound is actually exact, because Pascal's identity gives
  $
    1 + binom(n+1, 2) + binom(n+1, 4)
    = binom(n,0) + binom(n,1) + binom(n,2) + binom(n,3) + binom(n,4) .
  $
  So for $cal(H)_2$ the VC-dimension-based upper bound is tight for every $n$.
  This shows that VC dimension can sometimes capture the exact finite-pool richness of a class, although this is not true in general.

4. *Note:* As the task is written, the domain $cal(X)$ and hypothesis class $cal(H)$ can _depend on $n$_.
  We will make use of this.
  A stronger argument would be to find a domain $cal(X)$ and hypothesis class $cal(H)$ that depend only on $d$ and still realize the Sauer--Shelah bound.

  Fix integers $n >= d >= 0$. Take the domain
  $
    cal(X) := {1,2,dots,n}
  $
  and the hypothesis class
  $
    cal(H) := {1_A : A subset.eq cal(X), abs(A) <= d} .
  $
  Then
  $
    abs(cal(H)) = sum_(k=0)^d binom(n, k) .
  $
  Since $cal(X)$ itself is the only $n$-point subset of the domain, we get
  $
    Gamma_(cal(H))(n) = sum_(k=0)^d binom(n, k) .
  $

  Also $VCdim(cal(H)) = d$.
  Indeed, every $d$-point subset $S subset.eq cal(X)$ is shattered, because for every $T subset.eq S$ the hypothesis $1_T$ belongs to $cal(H)$.
  On the other hand, no $(d+1)$-point subset can be shattered, because the all-$1$ labeling on such a subset would require a set $A$ of size $d+1$, which is not allowed.

  Thus this example attains the Sauer--Shelah bound exactly.
  So the Sauer--Shelah inequality is best possible as a function of $n$ and $d$ alone.

5. The final conclusion of the AI assistant is correct, but the argument is not.

  First, it mixes up two different notions of "switch."
  The right structural property is that the labeling switches from $0$ to $1$ at most two times.
  This is not the same as saying that the total number of label changes is at most four and then choosing arbitrary sample positions for them.
  If one instead thinks of entering or leaving the positive region on the real line, then the relevant objects are the $n+1$ gaps before $x_1$, between consecutive sample points, and after $x_n$, not the $n$ sample positions.

  Second, even after one uses the correct $n+1$ gaps, one cannot choose an arbitrary set of at most four of them.
  The switches must come in alternating enter/leave pairs, so only $0$, $2$, or $4$ boundary gaps are possible.

  The correct statement is therefore:
  a labeling on an ordered $n$-point sample is realizable by $cal(H)_2$ if and only if, when scanned from left to right, it switches from $0$ to $1$ at most two times.
  Consequently,
  $
    Gamma_(cal(H)_2)(n) = binom(n+1,0) + binom(n+1,2) + binom(n+1,4)
    = sum_(k=0)^4 binom(n,k),
  $
  and hence
  $
    VCdim(cal(H)_2) = 4 .
  $

#pagebreak()
= Part B

#let ip(a,b) = $chevron.l #a , #b chevron.r$

In this part, let $cal(H)$ denote the quadratic threshold class.

1. Under the stated assumption, we have
  $
    VCdim(cal(H)) <= D .
  $

  #proof[
    Suppose $x_1, dots, x_m in cal(X)$ are shattered by $cal(H)$.
    Then for every labeling $(y_1, dots, y_m) in {0,1}^m$ there is $w in RR^D$ such that
    $
      y_i = 1[ip(w, phi(x_i)) >= 0]
    $
    for all $i$.

    If $phi(x_i) = phi(x_j)$ for some $i != j$, then the labeling with $y_i = 1$ and $y_j = 0$ would be impossible.
    Hence $phi(x_1), dots, phi(x_m)$ are distinct.
    Therefore the set
    $
      {phi(x_1), dots, phi(x_m)} subset.eq RR^D
    $
    is shattered by homogeneous halfspaces in $RR^D$.

    By the Week 2 result, homogeneous halfspaces in $RR^D$ have VC dimension $D$.
    So $m <= D$.
    Since every shattered set has size at most $D$, we conclude that $VCdim(cal(H)) <= D$.
  ]

2. We choose
  $
    phi(x) := (x^2, x, 1) in RR^3 .
  $
  If
  $
    h(x) = 1[a x^2 + b x + c >= 0]
  $
  belongs to $cal(H)$ and $w := (a,b,c)$, then
  $
    ip(w, phi(x)) = a x^2 + b x + c
  $
  and therefore
  $
    h(x) = 1[ip(w, phi(x)) >= 0] .
  $
  Applying item 1 with $D = 3$ yields
  $
    VCdim(cal(H)) <= 3 .
  $

3. A labeling $(y_1, dots, y_n) in {0,1}^n$ is realizable by $cal(H)$ if and only if, when scanned from left to right, the labels change at most twice.

  #proof[
    Let $p(x) = a x^2 + b x + c$ be a nonzero polynomial.

    Suppose first that $y_i = 1[p(x_i) >= 0]$ for all $i$.
    Since $p$ has degree at most $2$, the set
    $
      E := {x in RR : p(x) >= 0}
    $
    is one of the following: $emptyset$, $RR$, a closed ray, a closed interval, or the union of two closed rays.
    Indeed, this is immediate for constant and linear polynomials.
    For a genuine quadratic, there are at most two real roots, so depending on the leading coefficient the nonnegative region is either the interval between the roots or the two outer rays; the repeated-root case gives either the singleton root or all of $RR$.
    As we scan the ordered sample $x_1 < dots < x_n$, membership in any such set can change at most twice.
    Therefore the labeling changes at most twice.

    Conversely, suppose the labeling changes at most twice.
    If it changes zero times, then it is either all $0$ or all $1$, realized by $p(x) = -1$ or $p(x) = 1$.

    If it changes once, then for some $a in {1, dots, n-1}$ the change occurs between $x_a$ and $x_(a+1)$.
    Choose $t in (x_a, x_(a+1))$.
    The labeling is realized by the linear polynomial $p(x) = x - t$ or $p(x) = t - x$, according to whether the labels go from $0$ to $1$ or from $1$ to $0$.

    If it changes twice, then for some $1 <= a < b < n$ the changes occur between $x_a, x_(a+1)$ and between $x_b, x_(b+1)$.
    Choose $s in (x_a, x_(a+1))$ and $t in (x_b, x_(b+1))$ with $s < t$.
    If the middle block $x_(a+1), dots, x_b$ should be labeled by $1$, use
    $
      p(x) = - (x - s)(x - t) .
    $
    If the middle block should be labeled by $0$, use
    $
      p(x) = (x - s)(x - t) .
    $
    In both cases the sign pattern on $x_1, dots, x_n$ is exactly the desired one.
  ]

4. By item 3, we only need to count binary strings of length $n$ with at most two changes.

  There are exactly $2$ such labelings with no changes.

  A labeling with exactly one change is determined by choosing one of the $n-1$ gaps between consecutive sample points and choosing the initial label.
  Hence there are
  $
    2 binom(n-1, 1)
  $
  such labelings.

  Similarly, a labeling with exactly two changes is determined by choosing two of the $n-1$ gaps and choosing the initial label.
  Hence there are
  $
    2 binom(n-1, 2)
  $
  such labelings.

  Therefore the exact growth function is
  $
    Gamma_(cal(H))(n) = 2 sum_(j=0)^2 binom(n-1, j) = n^2 - n + 2 .
  $

  From this formula,
  $
    Gamma_(cal(H))(3) = 8 = 2^3
  $
  and
  $
    Gamma_(cal(H))(4) = 14 < 16 = 2^4 .
  $
  Thus every $3$-point ordered sample is shattered, but no $4$-point sample is.
  Hence
  $
    VCdim(cal(H)) = 3 .
  $

  The Sauer--Shelah bound with $d = 3$ gives
  $
    Gamma_(cal(H))(n) <= sum_(k=0)^3 binom(n, k) .
  $
  This bound is not tight in general.
  Already for $n = 4$ it gives $15$, whereas the exact value is $14$.
  More strongly, our exact formula grows like $Theta(n^2)$, while the Sauer--Shelah bound grows like $Theta(n^3)$.
  So in this example VC dimension captures the shattering threshold correctly, but it does not capture the exact finite-pool richness of the class.

5. The final conclusion of the AI assistant is correct, but the argument as stated is not sufficient and its counting step is wrong.

  First, the counting step misses a factor of $2$.
  After choosing the change-gaps, one must still choose the initial label ($0$ or $1$).
  So even from the necessary condition "at most two changes" one gets only
  $
    Gamma_(cal(H))(n) <= 2 sum_(j=0)^2 binom(n-1, j) .
  $

  Second, the root argument only proves a necessary condition: every realizable labeling has at most two changes.
  To turn this into an exact formula, one must also prove the converse: every binary string with at most two changes is realizable by some quadratic threshold.
  That converse is the content of item 3, using constants for zero changes, linear polynomials for one change, and quadratics with two chosen roots for two changes.

  The correct theorem is therefore:
  a labeling on an ordered $n$-point sample is realizable by $cal(H)$ if and only if, when scanned from left to right, it changes at most twice.
  Consequently,
  $
    Gamma_(cal(H))(n) = 2 sum_(j=0)^2 binom(n-1, j) = n^2 - n + 2 ,
  $
  and hence
  $
    VCdim(cal(H)) = 3 .
  $

#pagebreak()
= Part C

1. I used AI heavily this time. I asked it to solve the problems completely for me and to write down the solution in Typst, similar in style to how I wrote the solution to the theory problem on the first homework (which I wrote myself without AI).
  
  Then I used another AI to check the solution rigorously, and fix mistakes.

2. I accepted their general mathematical ideas/solutions.
  Concretely, for example, the Sauer-Shelah-bound-attaining example (part A subtask 4).

3. I manually checked what the AI wrote and asked it for changes, mostly that was when I was unhappy with formulations.

  For example, in part A subtask 1, it described the valid labelings just as a union of at most two intervals, which I felt like was not much insight beyond essentially copying the description of the hypothesis class.
  So I asked it to describe it as something like "the label should switch from 0 to 1 at most two times".
  Then it changed it, however when I later let another AI check the solution, it correctly pointed out that this formulation is not entirely correct (e.g. `10101` switches from 0 to 1 just two times but is still not a valid labeling), so I had to revert back from my "human" change.

4. I read the solution myself and checked that it's mathematically correct.
  Stylewise I would have probably written it slightly differently (more concise), but I'm okay with the style after I asked for a few adjustments.
  I also let another (different) AI check the solution.

*Workflow changes.*
I added the slides to the repo, and I added the list of topics for each week into `CLAUDE.md`, so that for a new conversation it's directly more aware of the course context.
I also added `AGENTS.md` because I started using Codex.
(Actually, I let AI do these changes to `CLAUDE.md` and `AGENTS.md`. In particular I asked it to use best practices for `AGENTS.md`, which made the file longer than my mostly handwritten `CLAUDE.md`.)