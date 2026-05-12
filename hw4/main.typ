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
  number: 4,
  date: [17 May 2026],
  course: [DSC 291 -- Learning Theory through Formal Proof and Proof Presentation],
  quarter: [Spring 2026],
  instructor: [Tianhao Wang]
)

= Part A

Throughout this part, all logarithms are natural and universal constants may change from line to line.

1. *VC dimension through supports.*
  For $I subset.eq {1,dots,d}$ with $abs(I)=k$, let $cal(H)_I$ be the class of homogeneous halfspaces whose weight vector is supported on $I$.
  Then
  $
    cal(H)_k = union.big_(I subset.eq [d], abs(I)=k) cal(H)_I ,
  $
  because a vector with fewer than $k$ nonzero coordinates is supported on many $k$-subsets.
  For each fixed $I$, $cal(H)_I$ is just the class of homogeneous halfspaces in $RR^k$, so
  $
    VCdim(cal(H)_I) <= k .
  $
  We bound $VCdim(cal(H)_k)$ by showing that any set of $m$ points shattered by $cal(H)_k$ must satisfy $m = O(k log(e d/k))$.
  Since $VCdim(cal(H)_k)$ is the largest shattered size, this is exactly the desired bound.
  So fix any candidate set of $m$ points.
  If $m < k$, the bound $m = O(k log(e d/k))$ is immediate, because $log(e d/k) >= 1$ gives $m < k <= k log(e d/k)$.
  Thus assume $m >= k$.
  Then, by Sauer--Shelah, on these $m$ points each fixed-support class realizes at most
  $
    Gamma_(cal(H)_I)(m) <= sum_(j=0)^k binom(m,j) <= (e m / k)^k .
  $
  The union over supports can realize no more patterns than the sum of the patterns realized by the fixed-support classes.
  Therefore
  $
    Gamma_(cal(H)_k)(m)
    <= binom(d,k) (e m / k)^k
    <= (e d / k)^k (e m / k)^k .
  $
  If $cal(H)_k$ shatters $m$ points, then
  $
    2^m <= (e^2 d m / k^2)^k ,
  $
  i.e. $m log(2) <= k log(e^2 d / k) + k log(m / k)$.
  Setting $u := m/k$ and $A := e^2 d / k$ this is
  $
    u log(2) <= log(A) + log(u) .
  $
  Since $log(u) <= (log(2) / 2) u$ for all $u >= 4$, either $u < 4$ or $(log(2) / 2) u <= log(A)$, so
  $
    u <= max{4, (2 / log(2)) log(A)} = O(log(e d / k)).
  $
  Hence $m = k u = O(k log(e d / k))$, and therefore
  $
    VCdim(cal(H)_k) = O(k log(e d / k)).
  $

2. *Penalty-based SRM.*
  Choose any prior $p_k > 0$ with $sum_(k=1)^d p_k <= 1$; for example,
  $
    p_k = 6 / (pi^2 k^2).
  $
  Let
  $
    "pen"(k,n,delta)
    :=
    C_0 sqrt((k log(e d / k) + log(1 / p_k) + log(1 / delta)) / n)
  $
  for a large enough universal constant $C_0$, and define
  $
    hat(h) in arg min_(1 <= k <= d, h in cal(H)_k)
    { L_S(h) + "pen"(k,n,delta) } .
  $

  #proof[
    By item 1 and the class-level SRM theorem, with probability at least $1-delta$, simultaneously for every $k$ and every $h in cal(H)_k$,
    $
      abs(L_cal(D)(h) - L_S(h))
      <=
      C_1 sqrt((VCdim(cal(H)_k) + log(1 / p_k) + log(1 / delta)) / n)
      <= "pen"(k,n,delta)
    $
    after increasing $C_0$.

    On this event, let $hat(k)$ be an index used by the SRM rule together with $hat(h)$.
    For any $k$ and $h in cal(H)_k$,
    $
      L_cal(D)(hat(h))
      <= L_S(hat(h)) + "pen"(hat(k),n,delta)
      <= L_S(h) + "pen"(k,n,delta)
      <= L_cal(D)(h) + 2 "pen"(k,n,delta).
    $
    Taking the infimum over $k,h$ gives
    $
      L_cal(D)(hat(h))
      <=
      inf_(1 <= k <= d, h in cal(H)_k)
      {
        L_cal(D)(h)
        + C sqrt((k log(e d / k) + log(1 / p_k) + log(1 / delta)) / n)
      } .
    $
  ]

  The term $k log(e d / k)$ is the statistical cost of searching over sparse predictors with a fixed sparsity level: it contains the cost of choosing one of about $binom(d,k)$ supports and the cost of fitting a $k$-dimensional halfspace on that support.
  The term $log(1/p_k)$ is the additional price for allowing the data to choose the sparsity level.

3. *Comparison with dense halfspaces.*
  Suppose $w^*$ is $s$-sparse and $L_cal(D)(w^*) <= eta$.
  Applying the oracle inequality with $k=s$ and $h=w^*$ gives, with probability at least $1-delta$,
  $
    L_cal(D)(hat(h))
    <=
    eta
    + C sqrt((s log(e d / s) + log(1 / p_s) + log(1 / delta)) / n).
  $
  Thus it is enough to take
  $
    n >=
    C'
    (s log(e d / s) + log(1 / p_s) + log(1 / delta)) / epsilon^2 .
  $
  With the concrete prior $p_s = 6/(pi^2 s^2)$, this is
  $
    n =
    O((s log(e d / s) + log(s) + log(1 / delta)) / epsilon^2).
  $

  Learning over all homogeneous halfspaces in $RR^d$ gives the agnostic sample size
  $
    O((d + log(1 / delta)) / epsilon^2).
  $
  The sparse bound is smaller when
  $
    s log(e d / s) + log(1 / p_s) << d .
  $
  In particular, it improves substantially in the genuinely sparse regime $s << d$, up to the logarithmic support-selection factor.
  When $s$ is comparable to $d$, the sparse and dense bounds are of the same order.

4. *Validation as model selection.*
  Write $m=n/2$.
  For each $k$, let $w_k$ be an ERM over $cal(H)_k$ on $S_1$, and choose $hat(k)$ by minimizing $L_(S_2)(w_k)$.
  Let $hat(w) := w_(hat(k))$.

  #proof[
    First use a VC uniform-convergence bound on $S_1$, with failure probability $delta/(2d)$ for each $k$.
    With probability at least $1-delta/2$, for every $k$ and every $w in cal(H)_k$,
    $
      abs(L_cal(D)(w)-L_(S_1)(w))
      <=
      alpha_k
      :=
      C_1 sqrt((k log(e d/k) + log(d/delta)) / n),
    $
    where the factor $m=n/2$ has been absorbed into the constant.
    On this event, ERM optimality gives, for every $w in cal(H)_k$,
    $
      L_cal(D)(w_k)
      <= L_(S_1)(w_k) + alpha_k
      <= L_(S_1)(w) + alpha_k
      <= L_cal(D)(w) + 2 alpha_k .
    $

    Now condition on $S_1$.
    The candidates $w_1,dots,w_d$ are fixed, so the validation step is a finite-class selection problem of size at most $d$.
    By Hoeffding and a union bound, with conditional probability at least $1-delta/2$,
    $
      abs(L_cal(D)(w_k)-L_(S_2)(w_k))
      <=
      beta
      :=
      C_2 sqrt(log(d/delta) / n)
    $
    for all $k$.
    On this event, for every $k$,
    $
      L_cal(D)(hat(w))
      <= L_(S_2)(hat(w)) + beta
      <= L_(S_2)(w_k) + beta
      <= L_cal(D)(w_k) + 2 beta .
    $
    Combining the two displays and using $beta <= alpha_k$ gives
    $
      L_cal(D)(hat(w))
      <=
      L_cal(D)(w)
      + C sqrt((k log(e d/k) + log(d/delta)) / n)
    $
    for every $k$ and every $w in cal(H)_k$.
    Taking the infimum proves
    $
      L_cal(D)(hat(w))
      <=
      inf_(1 <= k <= d, w: abs("supp"(w)) <= k)
      {
        L_cal(D)(w)
        + C sqrt((k log(e d/k) + log(d/delta)) / n)
      } .
    $
  ]

  The validation rule uses $S_1$ only to fit one candidate predictor at each sparsity level, and it uses $S_2$ only to choose among the $d$ fitted candidates.
  Thus the model-selection price on the validation half is just $log(d)$.
  The price is that fitting uses only half the sample, and the final choice cannot revisit all predictors at a level $k$ after looking at $S_2$.
  The penalty-based SRM rule uses the full sample for both fitting and choosing $k$, but it must include an explicit prior cost $log(1/p_k)$ for the complexity level.

5. *Computation.*
  In the realizable case, the direct brute-force algorithm is:

  - enumerate all supports $I subset.eq [d]$ with $abs(I)=k$;
  - for each $I$, solve the feasibility problem in variables $w_I in RR^k$:
    $
      w_I^T x_(i,I) >= 0 quad "for all" i " with " y_i = +1,
    $
    and
    $
      w_I^T x_(i,I) <= -1 quad "for all" i " with " y_i = -1;
    $
  - if one support is feasible, output the corresponding $k$-sparse vector, with all coordinates outside $I$ set to $0$.

  The normalization $<= -1$ for negative examples is only a way to replace strict inequalities by closed linear constraints.
  If a support admits a consistent classifier and there is at least one negative example, then every negative score is strictly below $0$ under the convention $"sign"(0)=+1$; because the sample is finite, scaling $w$ makes all negative scores at most $-1$ while preserving the nonnegative scores on positive examples.
  If there are no negative examples, the zero vector already labels all sample points by $+1$ under the convention $"sign"(0)=+1$.

  There are
  $
    binom(d,k) <= (e d/k)^k
  $
  supports.
  Linear feasibility in $k$ variables and $n$ constraints is solvable in time polynomial in $n$ and $k$ (ignoring standard bit-complexity bookkeeping).
  Hence the runtime is
  $
    binom(d,k) dot "poly"(n,k)
    <=
    (e d/k)^k dot "poly"(n,k).
  $
  This is polynomial in $d$ for constant $k$.
  For $k = O(log(d))$ it is already quasi-polynomial in general, and for $k$ growing as a power of $d$ or as $Theta(d)$ it is super-polynomial or exponential.

  Thus the sample complexity and the computation tell different stories.
  Statistically, $k$-sparse halfspaces have complexity only about $k log(e d/k)$.
  Computationally, the naive search over supports pays the much larger combinatorial factor $binom(d,k)$.
  This is exactly the Week 4 distinction: a class can be sample-efficient because it has small VC complexity, while ERM or consistency search over that class can still be computationally expensive.

= Part B

1. *VC dimension and point-posterior PAC-Bayes.*
  The threshold class has VC dimension $1$.

  #proof[
    A singleton ${x}$ is shattered: choose $t=x$ to label it by $1$, and choose $t=x+1$ to label it by $0$.
    On the other hand, no two points $x_1 < x_2$ can be shattered, because the labeling
    $
      h(x_1)=1, quad h(x_2)=0
    $
    is impossible.
    Indeed, if $h_t(x_1)=1$, then $t <= x_1 < x_2$, so $h_t(x_2)=1$ as well.
    Hence $VCdim(cal(H)_N)=1$.
  ]

  Let $P$ be uniform on the $N+1$ thresholds.
  If $Q_S = delta_(h_(hat(t)))$ is a point mass on the deterministic ERM output, then
  $
    "KL"(Q_S parallel P)
    =
    log(1 / P(h_(hat(t))))
    =
    log(N+1).
  $
  In the realizable setting $L_S(Q_S)=0$, so the stated PAC-Bayes theorem gives, with probability at least $1-delta$,
  $
    L_cal(D)(Q_S)
    <=
    sqrt((log(N+1) + log(2 n / delta)) / (2(n-1))).
  $

  This certificate pays $log(N+1)$ because a point posterior has to identify one exact threshold under the uniform prior.
  VC theory does not pay this price for thresholds because it uses the order structure of the class: thresholds have only VC dimension $1$, no matter how large the finite ordered domain is.

2. *Version-space posterior.*
  Let
  $
    a(S) = max {x_i : y_i = 0}
  $
  with $a(S)=0$ if there are no negative examples, and let
  $
    b(S) = min {x_i : y_i = 1}
  $
  with $b(S)=N+1$ if there are no positive examples.

  #proof[
    A threshold $h_t$ is consistent with a negative example $(x_i,0)$ iff $h_t(x_i)=0$, which means $x_i < t$.
    Thus consistency with all negative examples is equivalent to $a(S) < t$.
    Similarly, $h_t$ is consistent with a positive example $(x_i,1)$ iff $x_i >= t$.
    Consistency with all positive examples is therefore equivalent to $t <= b(S)$.
    Combining the two conditions,
    $
      V(S) = {t : a(S) < t <= b(S)} .
    $
    Since thresholds are indexed by integers, this set has size
    $
      abs(V(S)) = b(S)-a(S).
    $
  ]

  Let $Q_V$ be uniform on the consistent thresholds.
  Under the uniform prior $P$,
  $
    "KL"(Q_V parallel P)
    =
    sum_(t in V(S)) 1/abs(V(S))
    log((1/abs(V(S))) / (1/(N+1)))
    =
    log((N+1)/abs(V(S))).
  $
  Also $L_S(Q_V)=0$, because every threshold in $V(S)$ is individually consistent with the sample.
  Compared with a point posterior, the KL term is smaller by $log(abs(V(S)))$.
  Thus when the version space is large, spreading the posterior across all consistent thresholds can give a much tighter PAC-Bayes certificate without increasing empirical risk.

3. *Spreading helps KL, but can hurt true risk.*
  Let labels be generated by $h_tau$ and let the marginal on $cal(X)_N$ be uniform.
  For a fixed threshold $t$, the two thresholds $h_t$ and $h_tau$ disagree exactly on the integer points between $t$ and $tau$.
  There are $abs(t-tau)$ such points, so
  $
    L_cal(D)(h_t) = abs(t-tau)/N .
  $
  Therefore, for the uniform posterior $Q_W$,
  $
    L_cal(D)(Q_W)
    =
    1/abs(W) sum_(t in W) L_cal(D)(h_t)
    =
    1/(N abs(W)) sum_(t in W) abs(t-tau).
  $

  A concrete example is $N=20$, $tau=10$, and
  $
    S = ((1,0),(20,1)).
  $
  This sample is realizable by $h_10$.
  Here $a(S)=1$, $b(S)=20$, and hence
  $
    V(S) = {2,3,dots,20},
    quad
    abs(V(S)) = 19.
  $
  The uniform version-space posterior satisfies
  $
    "KL"(Q_(V(S)) parallel P) = log(21/19) < log(21)
    =
    "KL"(delta_(h_10) parallel P).
  $
  However,
  $
    L_cal(D)(Q_(V(S)))
    =
    1/(20 dot 19) sum_(t=2)^20 abs(t-10)
    =
    91/380
    >
    0
    =
    L_cal(D)(delta_(h_10)).
  $

  There is no contradiction with PAC-Bayes.
  The theorem gives an upper bound on true risk in terms of empirical risk and KL; it does not say that lower KL always means lower true risk.
  In this example the version-space posterior has a better complexity term, but it spreads mass over thresholds that are far from the true threshold and therefore makes mistakes on many unsampled points.

4. *Every fixed prior can be attacked.*
  Let $P$ be any prior over $cal(H)_N$ and assume $N >= 3$.
  There are $N-1$ internal thresholds $tau in {2,dots,N}$.
  Since their total prior mass is at most $1$, at least one internal threshold satisfies
  $
    P(h_tau) <= 1/(N-1).
  $
  Fix such a $tau$.

  Under $cal(D)_tau$, each sample point is either $(tau-1,0)$ or $(tau,1)$, each with probability $1/2$.
  The probability that an $n$-sample fails to contain both support points is the probability that all draws are the first point or all draws are the second point:
  $
    2 dot (1/2)^n = 2^(1-n).
  $
  Hence with probability at least $1-2^(1-n)$, the sample contains both support points.

  On this event,
  $
    a(S)=tau-1
    quad "and" quad
    b(S)=tau,
  $
  so
  $
    V(S) = {t : tau-1 < t <= tau} = {tau}.
  $
  Therefore any posterior $Q$ with $L_S(Q)=0$ must put all its mass on $h_tau$; otherwise it gives positive mass to a threshold that misclassifies one of the two observed support points.
  Thus $Q = delta_(h_tau)$.
  Consequently,
  $
    "KL"(Q parallel P)
    =
    log(1/P(h_tau))
    >=
    log(N-1),
  $
  with the convention that the KL is infinite if $P(h_tau)=0$.

  This shows a limitation of zero-empirical-error PAC-Bayes certificates with a fixed prior: an adversarially chosen realizable threshold can force every consistent posterior to concentrate on a hypothesis with prior mass at most $1/(N-1)$.
  It does not prove that thresholds require $log(N)$ samples to learn.
  VC theory gives a distribution-free learning guarantee for thresholds with VC dimension $1$.
  The lower bound is about this particular style of fixed-prior, zero-training-error certificate, not about the information-theoretic sample complexity of threshold learning.

= Part C

I significantly used AI in this assignment in order to generate the proofs.
I was only able to spot-check the proofs, and I'm conviced of their correctness, however I admittedly didn't check them fully due to lack of time.
I'm happy to accept deductions for partly using AI as an oracle, unfortunately I was unable to finish the homework otherwise, so I'm happy to be graded as if I had not submitted parts of it.