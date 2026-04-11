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

#show: homework.with(
  number: 1,
  date: [10 April 2026],
  course: [DSC 291 -- Learning Theory through Formal Proof and Proof Presentation],
  quarter: [Spring 2026],
  instructor: [Tianhao Wang]
)

= Part A

1. #sym.checkmark Created public GitHub repository.
2. #sym.checkmark Created `README.md`.
3. #sym.checkmark Created `CLAUDE.md`.
4. #sym.checkmark Created `hw1/`.
5. I couldn't find anything on Canvas to submit it, but the repository link is: #link("https://github.com/jbirnick/dsc-291-spring-2026/")[`https://github.com/jbirnick/dsc-291-spring-2026/`]

= Part B

#let sign = math.op("sign")

1. Fix $Delta > 0$. We say a set $G subset.eq [0,1]$ is _$Delta$-close_ if for all $x in [0,1]$ there is $g in G$ with $abs(x - g) < Delta$.

  All we will need is a $Delta$-close set $G$.
  For example, we can choose the following grid:
  $
    G := {n dot 0.9 dot Delta mid(|) n=1,2,..., floor(1/(0.9 dot Delta))}
  $

  Now let $((x_t, y_t))_(t=1)^N$ be a $Delta$-separated threshold-realizable sequence.
  So there is $theta^* in [0,1]$ such that $y_t = h_(theta^*) (x_t)$ and $abs(x_t - theta^*) >= Delta$ for all $t$. 
  Since $G$ is $Delta$-close, there is $tilde(theta) in G$ with:
  $abs(theta^* - tilde(theta)) < Delta$.

  Now for any $t$ we have:
  $
    h_tilde(theta) (x_t) = sign(x_t - tilde(theta)) = sign((x_t - theta^*) + (theta^* - tilde(theta)))
  $
  For the two terms in the parenthesis, notice $abs(theta^* - tilde(theta)) < Delta <= abs(x_t - theta^*)$.
  Hence we can apply a Lemma.

  *Lemma.* For $abs(epsilon) < abs(a)$, we have $sign(a + epsilon) = a$. \
  #proof[Left to the reader (or Claude). #h(1fr) $square$]

  Applying the Lemma to $a = x_t - theta^*$ and $epsilon = theta^* - tilde(theta)$ yields:
  $
    sign((x_t - theta^*) + (theta^* - tilde(theta))) = sign(x_t - theta^*) = h_(theta^*)  (x_t) = y_t
  $
  Combining our equations, we have $h_tilde(theta) (x_t) = y_t$ for all $t$ as desired.

  Now we can apply the Halving algorithm from the lecture to the hypothesis class $cal(H) = {h_theta | theta in G}$.
  Note that it has size $abs(cal(H)) = abs(G) = floor(1/(0.9 dot Delta))$.
  Hence our theorem guarantees a mistake bound of:
  $
    floor(log_2 abs(cal(H))) = floor(log_2(floor(1/(0.9 dot Delta)))) = O(log(1/Delta))
  $

#pagebreak()

#let ip(a,b) = $chevron.l #a , #b chevron.r$

2. We choose $phi.alt(x) = (x,1) in RR^2$.
  Then $u^* := ((1, -theta^*)) / norm((1, -theta^*)) in RR^2$ is a unit vector satisfiying
  $
    ip(u^*, phi.alt(x)) >= 0 wide <==> wide x dot 1 + 1 dot (-theta^*) >= 0 wide <==> wide sign(x - theta^*) = +1 thick ,
  $
  so the linear classifier given by $u^*$ and the threshold classifier $h_(theta^*)$ are equivalent.

  Note that $norm(phi.alt(x)) = sqrt(x^2 + 1^2) <= sqrt(2)$ for any $x in [0,1]$.
  Also note that any $Delta$-separated threshold-realizable sequence becomes linearly separable with margin $Delta \/ sqrt(2)$ when mapped with $phi.alt$.
  Indeed, suppose $abs(x - theta^*) >= Delta$.
  Then:
  $
    abs(ip(u^*,phi(x))) = 1/sqrt(1 + (theta^*)^2) abs(x - theta^*) >= 1/sqrt(1 + 1) abs(x - theta^*) >= Delta/sqrt(2)
  $

  Applying the Perceptron theorem with $R = sqrt(2)$ and margin $gamma = Delta \/ sqrt(2)$ yields the mistake bound:
  $
    R^2 / gamma^2 = 4 / Delta^2 = O(1 / Delta^2)
  $

3. While our threshold hypothesis space is parametrized by a continuous variable, our results do _not_ contradict the adversarial impossibility theorem from the lecture.
  This is because we make additional assumptions on the input sequence.
  (And if you look at the proof of the impossibility result, you can see how the adversary pushes points arbitrarily close to the true threshold $theta^*$, which they cannot do if the $x_t$ have to be $Delta$-separated from $theta^*$.)

  For the halving algorithm and the Perceptron algorithm we obtained mistake bounds of $O(log(1\/Delta))$ and $O(1\/Delta^2)$ respectively.
  Thus we see that the halving algorithm is to be preferred in this case.

  The different scaling of the mistake bounds comes because the algorithms fundamentally work in a different way.
  We could formulate a $d$-dimensional analog of the same problem, and for the Halving algorithm we would need to pack a $d$-dimensional unit ball, leading to grid of size $Theta((1\/Delta)^d)$, and therefore a final dimension-dependent mistake bound of $O(d log(Delta))$.
  In contrast, the Perceptron algorithm only needs the $Delta$-separability of the $x_t$ from $theta^*$ and an upper bound on the $theta^*$, but is dimension independent.

4. Mistakes:
  - must make #strike[most] *least* $O(log(1/Delta))$ mistakes
  - on #strike[every] *some* $Delta$-separated threshold-realizable sequence.

  So the correct statement goes as follows:
  For every $Delta > 0$ and every learner $A$ there exists a $Delta$-separated threshold-realizable sequence for which $A$ makes at least $Omega(log(1\/Delta))$ many mistakes.

  #proof[
    Fix $Delta > 0$ and a learner $A$.
    We will copy the exact same proof from the "continuous threshold impossibility" result, but we only continue until the point where the constructed sequence $x_1, x_2, ...$ is still $Delta$-separated threshold-realizable.

    Without loss of generality we can assume that $Delta = 2^(-k)$ for some $k$.
    Choose $x_1 = 1\/2$.
    Now _as long as t < k - 1_, if the learner $A$ makes a prediction $y_t^((A))$, choose $y_t := - y_t^((A))$, so that the learner is always wrong, and let
    $
      x_(t+1) := x_t - y_t dot 2^(-(t+1)) quad .
    $
    For $t >= k - 1$, we can let $x_(t+1) = x_t$ and $y_(t+1) = y_t$ (and $y_(k-1) = - y_(k-1)^((A)))$ still).
    Finally, define the correct threshold as:
    $
      theta^* := x_(k-1) - y_(k-1) 2^(-k)
    $
    Now one can check that $y_t = h_(theta^*) (x_t)$, $abs(x_t - theta^*) >= 2^(-k) = Delta$, so the sequence is $Delta$-separated threshold-realizable.
    Furthermore, $A$ makes a mistake on at least $x_1,...,x_(k-1)$, so it makes at least
    $
      k-1 = log_2(1\/Delta) - 1 = Omega(log(1\/Delta))
    $
    many mistakes.
  ]

= Part C

1. You can choose a distribution like a uniform distribution on a ball or a Gaussian distribution, and then reject all samples which violate the bound $R$ or the $gamma$-margin condition.
  You have to choose $R$, $gamma$, the base distribution, and the separator $w^*$.

2. #align(center, image("plot_mistakes.png", width: 70%))

3. For the distribution that I chose (generated as described above with base distribution being the uniform distribution on a ball) it performs better in practice, as we can see it the plot above.

4. #align(center, image("plot_dimension.png", width: 70%))

  #strike[
    We vary $d in {2, 5, 10, 20, 50}$ with fixed $gamma = 0.1$, $R = 1$, $T = 2000$, averaged over 30 trials.

    The average number of mistakes stays well below the bound $R^2 \/ gamma^2 = 100$ across all dimensions and shows no dramatic growth with $d$, confirming that the Perceptron mistake bound is indeed dimension-independent.
    (The mild increase is due to the higher-dimensional orthogonal components making examples harder to classify early on, but the bound still holds uniformly.)
  ]

  _This is what Claude did, but I'm not happy with it, so I won't submit it._

5. #image("plot_gamma_zero.png")

  #strike[
    As $gamma -> 0$, the Perceptron mistakes grow roughly as $1\/gamma^2$ (the log-log plot shows a linear trend), diverging to infinity.
    This is consistent with the threshold counterexample from lecture: when points can be placed arbitrarily close to $theta^*$ (i.e.\ $gamma -> 0$), no online learner can achieve a finite mistake bound.
    The Perceptron bound $R^2 \/ gamma^2$ faithfully captures this --- it guarantees finitely many mistakes only when $gamma > 0$, and becomes vacuous as the margin vanishes.
  ]

  _This is what Claude did, but I'm not happy with it, so I won't submit it._

6. I skimmed over the implementation to see it's doing what I instructed it to do. (Verifying code is faster than writing it.)
  I also observed that the AI did some basic tests while it was developing the code.
  Ideally one should write unit tests (or let the AI write them and check the implementation), but I didn't do it this time (due to time constraints).

= Part D

1. I didn't use it at all in part A, I only used it in part B.
  It was mostly helpful with writing code.
  This time I also let it solve question 4 and 5 completely on its own.
  I wouldn't usually do that, but since this course is trying to push more AI usage and I also wanted to "improve" at that or try it out, I wanted to see how it performs at solving the tasks completely by itself.
  Unfortunately it didn't perform well, so I ended up not submitting these tasks.

2. I accepted the code it wrote (after repeatedly telling it how to adapt it).

3. When it generated the code, it didn't initially do it the way I wanted.
  For example, it generated the $gamma$-separated data differently from how I wanted it to do it.
  So I instructed it to change it.
  Similarly, its first implementation would fix the separator $w^*$ to be the first standard basis vector.
  So I instructed it to change it so that it accepts an arbitrary $w^*$ as an argument.

4. For the code of part B question 2, I already explained it above. (I skimmed it to check it's doing what I want. Ideally one would write unit tests.)
  For the tasks 4 and 5 of Part B that it did on its own, unfortunately I didn't have time this time to check everything and I was unhappy with the results anyway, which is why I didn't submit them.

_(The assignment asks to put the report of Part D in a PDF or MD file. I assume it's enough that it's part of this united PDF file.)_