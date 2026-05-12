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
#let sign = math.op("sign")

#show: homework.with(
  number: 6,
  date: [17 May 2026],
  course: [DSC 291 -- Learning Theory through Formal Proof and Proof Presentation],
  quarter: [Spring 2026],
  instructor: [Tianhao Wang]
)

= Part A

1. Let $Q$ be any distribution supported on examples satisfying
  $y chevron.l w^star, phi(x) chevron.r >= 1$. Then
  $
    1
    <= EE_Q[y chevron.l w^star, phi(x) chevron.r]
    = sum_(j=1)^d w_j^star EE_Q[y phi_j(x)]
    <= norm(w^star)_1 max_(j in [d]) abs(EE_Q[y phi_j(x)]).
  $
  Therefore some coordinate $j$ has
  $abs(EE_Q[y phi_j(x)]) >= 1 / norm(w^star)_1$.
  Choose $sigma in {-1,+1}$ so that
  $sigma EE_Q[y phi_j(x)] = abs(EE_Q[y phi_j(x)])$ and set
  $b(x) = sigma phi_j(x)$. Its edge is
  $
    1/2 - L_Q(b) = EE_Q[y b(x)] / 2 >= 1 / (2 norm(w^star)_1),
  $
  hence $L_Q(b) <= 1/2 - 1/(2 norm(w^star)_1)$.
  Since $w^star$ is $s$-sparse and $norm(w^star)_infinity <= B$,
  $norm(w^star)_1 <= s B$, so
  $
    L_Q(b) <= 1/2 - 1/(2 s B).
  $

  For weighted examples with normalized weights $D_i$, compute for each coordinate
  $
    c_j = sum_i D_i y_i phi_j(x_i).
  $
  For $b_(j,sigma)(x)=sigma phi_j(x)$,
  $
    L_D(b_(j,sigma)) = sum_i D_i 1[sigma phi_j(x_i) != y_i]
      = (1 - sigma c_j) / 2.
  $
  Thus the weighted ERM rule is: compute all $c_j$, choose
  $j in arg max_j abs(c_j)$, and choose $sigma = sign(c_j)$, with either sign allowed if $c_j=0$.
  This takes $O(n d)$ time.

2. In every AdaBoost round the reweighted empirical distribution is still supported on the
  same margin-realizable sample. By the previous part the weak learner has edge at least
  $
    gamma = 1/(2 s B).
  $
  If $gamma_t$ is the edge in round $t$, the usual AdaBoost calculation gives
  $
    hat(L)_S(H_T)
      <= product_(t=1)^T 2 sqrt(epsilon_t(1 - epsilon_t))
      = product_(t=1)^T sqrt(1 - 4 gamma_t^2)
      <= exp(-2 gamma^2 T).
  $
  Therefore $hat(L)_S(H_T) < 1/n$, and hence the training error is zero, as soon as
  $
    T >= (log(n)) / (2 gamma^2) = 2 s^2 B^2 log(n).
  $

  The boosted classifier has the form
  $
    H_T(x) = sign(sum_(t=1)^T alpha_t sigma_t phi_(j_t)(x)),
  $
  so it is a linear classifier using $r <= min(T,d)$ coordinates. Applying the realizable VC
  bound to the class of $r$-sparse linear classifiers gives, with probability at least $1-delta$,
  true error at most $epsilon$ uniformly over all zero-training-error boosted classifiers whenever
  $
    n = tilde(O)(
      (r log(e d / r) + log(1/delta)) / epsilon
    ).
  $
  Since $r <= T$, substituting $T = O(s^2 B^2 log(n))$ and suppressing logarithmic
  factors gives
  $
    n = tilde(O)(
      (s^2 B^2 log(d) + log(1/delta)) / epsilon
    ).
  $

  Exact sparse ERM has sample complexity
  $
    tilde(O)((s log(e d / s) + log(1/delta)) / epsilon),
  $
  but is computationally difficult when $s$ is part of the input. Boosting pays statistically
  because the final support bound is $T = tilde(O)(s^2 B^2)$ instead of $s$, but each weak
  learning round is just the $O(n d)$ coordinate scan above. The coefficient bound $B$ is
  what turns sparse margin into a polynomial lower bound on the coordinate edge; large $B$
  makes the edge small and the number of rounds quadratic in $s B$.

3. Let $s=2m+1$ and index the rows by
  $0,(1,+),(1,-),...,(m,+),(m,-)$. Define weights
  $q_0=1$ and $q_(r,+)=q_(r,-)=2^(r-1)$, and let
  $
    Z = sum_i q_i = 2^(m+1)-1.
  $
  I construct an $s times s$ sign matrix $A$ whose columns all have $q$-weighted sum $1$.

  The first column $a^0$ has $a^0_0=+1$ and, on every pair, signs $(+,-)$.
  For each $r$, the flip column $f^r$ has $f^r_0=+1$, signs $(-,+)$ on pair $r$,
  and signs $(+,-)$ on all other pairs. For each $r$, the carry column $g^r$ has
  $g^r_0=-1$, signs $(-,-)$ on pairs $ell < r$, signs $(+,+)$ on pair $r$,
  and signs $(+,-)$ on pairs $ell > r$.

  Each of these columns has $q$-weighted sum $1$: the base and flip columns cancel pairwise
  and keep the row-$0$ contribution $1$; for $g^r$, the pair contribution is
  $
    - sum_(ell < r) 2^ell + 2^r = -(2^r - 2) + 2^r = 2,
  $
  and the row-$0$ contribution is $-1$.

  The matrix is invertible. Suppose
  $
    a a^0 + sum_r b_r f^r + sum_r c_r g^r = 0.
  $
  Adding the two row equations in pair $k$ eliminates $a$ and all $b_r$, and gives
  $
    c_k = sum_(r > k) c_r.
  $
  From $k=m$ downward this implies $c_m=...=c_1=0$. With all $c_r=0$, the plus row in
  pair $k$ gives $a + sum_r b_r - 2 b_k = 0$, while the row-$0$ equation gives
  $a + sum_r b_r = 0$. Hence every $b_k=0$, and then $a=0$.

  Now take the instance space to be the row set of $A$, all labels $y=+1$, and
  distribution probabilities $Q_i=q_i/Z$. Since $A$ is invertible, there is a vector
  $w^star$ satisfying $A w^star = bold(1)$. Thus every example has margin exactly $1$.
  For every coordinate $j$,
  $
    EE_Q[phi_j(x)] = (q^T A)_j / Z = 1/Z.
  $
  Therefore the best signed coordinate has edge exactly
  $
    1/(2Z) = 1 / (2(2^(m+1)-1)) = 2^(-Omega(s)).
  $

  Finally,
  $
    sum_j w_j^star
      = bold(1)^T w^star
      = q^T A w^star
      = q^T bold(1)
      = Z.
  $
  Since $abs(sum_j w_j^star) <= s norm(w^star)_infinity$, this implies
  $norm(w^star)_infinity >= Z/s = 2^(Omega(s))$.
  This shows that sparsity alone cannot give a polynomial-in-$s$ AdaBoost guarantee for
  the coordinate class: even though the realizing vector is $s$-sparse, the best initial
  coordinate edge may be exponentially small.

4. --

= Part B

1. Let $g = h_1 and ... and h_k$ realize the distribution, and write
  $p = PP[y=+1]$. If
  $
    p <= 1/2 - 1/(2 k^2),
  $
  then the constant $-1$ affine halfspace has error $p$, so we are done.

  Otherwise $p > 1/2 - 1/(2k^2)$. On every positive example, all $h_i$ are correct.
  On every negative example, at least one $h_i$ outputs $-1$ and is correct, so at most $k-1$ of the
  $h_i$ make an error. Averaging the errors of the $k$ defining halfspaces gives
  $
    1/k sum_(i=1)^k L_D(h_i)
      <= ((k-1)/k) PP[y=-1]
      = ((k-1)/k)(1-p).
  $
  Using $1-p < 1/2 + 1/(2k^2)$,
  $
    1/k sum_(i=1)^k L_D(h_i)
      < (1 - 1/k)(1/2 + 1/(2k^2))
      <= 1/2 - 1/(2k^2),
  $
  since the last inequality is equivalent to $(k-1)^2 >= 0$. Thus one of the $h_i$ has
  error at most $1/2 - 1/(2k^2)$.

2. Suppose affine halfspaces have an efficient proper agnostic PAC learner. On any distribution
  realized by $cal(I)_(d,k)$, run that learner on the halfspace class with excess
  error parameter
  $
    alpha = 1/(4 k^2).
  $
  By the previous part, the best halfspace has error at most $1/2 - 1/(2k^2)$, so the
  returned proper halfspace has error at most
  $
    1/2 - 1/(2k^2) + 1/(4k^2) = 1/2 - 1/(4k^2).
  $
  Thus it is a weak learner with
  $
    gamma = 1/(4 k^2).
  $
  If $k(d) <= d^c$ for fixed $c$, then $1/alpha = 4 k^2 <= 4 d^(2c)$, so the accuracy demand made of the
  agnostic learner is still polynomially bounded.

3. Apply AdaBoost using the weak learner above. Every reweighted distribution is supported
  on the same examples, and the same intersection still realizes them, so the weak-learning
  condition remains valid in every round. With $gamma = 1/(4k^2)$,
  $
    hat(L)_S(H_T) <= exp(-2 gamma^2 T).
  $
  Thus $T = O(k^4 log(n))$ rounds make the empirical error zero.

  The final classifier is a weighted majority of $T$ affine halfspaces. Using the boosted
  halfspace VC bound $tilde(O)(T d)$, a realizable uniform convergence bound gives true
  error at most $epsilon$ with probability at least $1-delta$ for
  $
    n = tilde(O)(
      (T d + log(1/delta)) / epsilon
    )
    = tilde(O)(
      (d k^4 + log(1/delta)) / epsilon
    ).
  $
  The runtime is $tilde(O)(k^4)$ calls to the agnostic halfspace learner, each with excess-error
  parameter $Theta(1/k^2)$ and the usual polynomial overhead for maintaining the AdaBoost
  weights. For polynomially bounded $k$, this is polynomial in $d$, $1/epsilon$, and
  $log(1/delta)$.

4. Combining the previous parts: an efficient proper agnostic PAC learner for affine
  halfspaces would imply an efficient realizable learner for intersections of
  $k(d) <= d^c$ affine halfspaces, for every fixed $c$. The learner is improper for the
  intersection class, because its final hypothesis is a boosted majority of halfspaces, but
  the black-box hardness facts rule out even improper efficient realizable learning.

  Under uSVP hardness, choose any fixed $r>0$ and set $k(d)=d^r$; this is covered by the
  reduction above and contradicts hardness of learning intersections of $d^r$ halfspaces.
  Under RSAT, any polynomially bounded unbounded $k(d)=omega(1)$ is also covered. Therefore,
  under either hardness assumption, affine halfspaces cannot be efficiently properly
  agnostically PAC learnable.

= Part C

I significantly used AI in this assignment in order to generate the proofs.
I was only able to spot-check the proofs, and I'm conviced of their correctness, however I admittedly didn't check them fully due to lack of time.
I'm happy to accept deductions for partly using AI as an oracle, unfortunately I was unable to finish the homework otherwise, so I'm happy to be graded as if I had not submitted parts of it.

I was not happy with the experiment it generated, so did explicitly exclude that.