#let Var = math.op("Var")
#let argmin = math.op("argmin")
#let proof(body) = [
  _Proof._ #body #h(1fr) $square$
]

= A mini-course on concentration inequalities

== Introduction

Toss a fair coin a million times.
The individual outcomes are unpredictable, yet the total number of heads is almost certain to land very near half a million.
Randomness in the small produces near-certainty in the large.
This is _concentration_: although each piece is unpredictable, a quantity assembled from many independent random pieces can be almost deterministic.

Concentration inequalities make this precise.
The central limit theorem describes fluctuations only in the limit $n -> infinity$.
A concentration inequality instead gives an explicit failure probability valid for every sample size $n$ --- exactly what one needs to guarantee a procedure run on finite data.

This self-contained mini-course develops four such inequalities: Hoeffding's inequality, Hoeffding's inequality for sampling without replacement, McDiarmid's inequality, and Bernstein's inequality.
All four are proved using the same technique, the moment-generating-function method.
The mini-course then applies them to prove a cornerstone of statistical learning theory: a learner that minimizes error on its training sample does, with high probability, almost as well on unseen data as the best hypothesis available to it.

The logical dependencies are as follows.

- Markov's inequality $arrow$ Chernoff's bound $arrow$ the MGF method.
- Hoeffding's lemma $arrow$ Hoeffding's inequality for independent bounded sums.
- Conditional Hoeffding lemma $arrow$ martingale bounded-differences bounds.
- Martingale bounded differences $arrow$ sampling without replacement and McDiarmid.
- Moment expansion plus Chernoff $arrow$ Bernstein.
- Symmetrization plus sampling without replacement plus McDiarmid $arrow$ the i.i.d. growth-function ERM guarantee.

== What concentration means

A concentration inequality is a finite-sample statement that a random quantity $Z$ is unlikely to be far from a typical value, usually its mean:
$
  PP[abs(Z - EE[Z]) >= t] <= "small"(t),
$
where the useful cases have a right-hand side that decays exponentially in the sample size or in $t^2$.

To make this concrete, return to the coin.
Let $X_1, dots, X_n in {0,1}$ be independent with $EE[X_i] = p$, and let $A_n := 1/n sum_(i=1)^n X_i$.
Hoeffding's inequality (proved below) gives
$
  PP[abs(A_n - p) >= epsilon] <= 2 exp(-2 n epsilon^2).
$
The right-hand side stays close to $1$ while $epsilon$ is of order $1 / sqrt(n)$ or smaller, and decays exponentially once $epsilon$ exceeds that scale.
Thus deviations much larger than $1 / sqrt(n)$ are exponentially unlikely, and $1 / sqrt(n)$ is the typical scale of $abs(A_n - p)$.
This is the central-limit scale, but here it comes with an explicit bound valid for every $n$.

The intuition is cancellation plus stability: no single bounded observation can move the average much, and independent fluctuations do not consistently agree in sign.
For a general function $f(X_1, dots, X_n)$, concentration should persist if changing one coordinate changes $f$ only slightly --- the bounded-differences idea behind McDiarmid's inequality.

== The common MGF technique

For a real random variable $Z$, define its log moment-generating function (MGF)
$
  psi_Z(lambda) := log(EE[exp(lambda Z)]).
$
For $lambda > 0$, Markov's inequality gives the Chernoff bound
$
  PP[Z >= t]
    = PP[exp(lambda Z) >= exp(lambda t)]
    <= exp(-lambda t) EE[exp(lambda Z)]
    = exp(psi_Z(lambda) - lambda t).
$
Since this holds for every $lambda > 0$, the best bound comes from optimizing over $lambda$.
Equivalently,
$
  PP[Z >= t] <= exp(- psi_Z^*(t)),
  quad
  psi_Z^*(t) := sup_(lambda > 0) (lambda t - psi_Z(lambda)).
$

Independence makes this powerful for sums: if $Z = sum_(i=1)^n Z_i$ with the $Z_i$ independent, then $psi_Z(lambda) = sum_(i=1)^n psi_(Z_i)(lambda)$, so it suffices to control one summand.
The key case is a sub-Gaussian MGF bound $psi_Z(lambda) <= v lambda^2 / 2$ for all $lambda$; Chernoff with $lambda = t / v$ then gives
$
  PP[Z >= t] <= exp(- t^2 / (2 v)).
$

The same idea works conditionally for martingales.
Let $D_i$ be martingale differences for a filtration $cal(F)_i$, so $EE[D_i | cal(F)_(i-1)] = 0$.
If $EE[exp(lambda D_i) | cal(F)_(i-1)] <= exp(lambda^2 c_i^2 / 8)$ almost surely, then iterating conditional expectations gives
$
  EE[exp(lambda sum_(i=1)^n D_i)]
    <= exp(lambda^2 / 8 sum_(i=1)^n c_i^2),
$
and Chernoff yields a Hoeffding-style tail.
Sampling without replacement and McDiarmid's inequality are both applications of this martingale variant.

== Statements and consequences

*Hoeffding's inequality.*
Let $X_1, dots, X_n$ be independent and suppose $X_i in [a_i,b_i]$ almost surely.
Set
$
  S := sum_(i=1)^n (X_i - EE[X_i]),
  quad
  A := sum_(i=1)^n (b_i - a_i)^2 .
$
Then for every $t > 0$,
$
  PP[S >= t] <= exp(- 2 t^2 / A),
  quad
  PP[abs(S) >= t] <= 2 exp(- 2 t^2 / A).
$
It controls sums of independent bounded variables.
It uses only the ranges $[a_i,b_i]$, not the variances.

For averages of independent $[0,1]$-valued variables, this becomes
$
  PP[abs(1/n sum_(i=1)^n X_i - 1/n sum_(i=1)^n EE[X_i]) >= epsilon]
  <= 2 exp(-2 n epsilon^2).
$

*Hoeffding without replacement.*
Let $z_1, dots, z_N in [a,b]$ be fixed.
Draw $T subset.eq {1, dots, N}$ uniformly among subsets of size $n$, and set
$
  mu := 1/N sum_(i=1)^N z_i.
$
Then for every $epsilon > 0$,
$
  PP_T [abs(1/n sum_(i in T) z_i - mu) >= epsilon]
  <= 2 exp(- (2 n epsilon^2) / (b-a)^2).
$
This controls a sample mean from a finite population sampled without replacement.
The draws are dependent but less variable than independent draws with replacement, so the rate matches the independent Hoeffding bound; this form is all the ERM proof needs.

*McDiarmid's inequality.*
Let $X_1, dots, X_n$ be independent random variables taking values in a set $cal(X)$.
Suppose $f : cal(X)^n -> RR$ satisfies the bounded-differences condition
$
  abs(f(x_1, dots, x_n) - f(x_1, dots, x_(i-1), x_i', x_(i+1), dots, x_n))
  <= c_i
$
for every coordinate $i$ and all inputs.
Then, for $Z := f(X_1, dots, X_n)$ and every $t > 0$,
$
  PP[Z - EE[Z] >= t] <= exp(- (2 t^2) / (sum_(i=1)^n c_i^2)),
$
and the same bound holds for $PP[Z - EE[Z] <= -t]$.
This controls well-behaved functions of many independent variables, not just sums.

*Bernstein's inequality.*
Let $X_1, dots, X_n$ be independent, mean-zero random variables with $abs(X_i) <= b$ almost surely.
Let
$
  sigma^2 := sum_(i=1)^n Var(X_i).
$
Then for every $t > 0$,
$
  PP[sum_(i=1)^n X_i >= t]
  <= exp(- t^2 / (2(sigma^2 + b t / 3))).
$
Applying the same bound to $-X_i$ gives the two-sided version with an additional factor of $2$.

Bernstein is stronger than Hoeffding when the variance is much smaller than the crude range bound: for $t << sigma^2 / b$ the tail is Gaussian, $exp(-t^2/(2 sigma^2))$, while for large $t$ boundedness takes over and it is exponential in $t/b$.
Hoeffding sees only the worst-case range; Bernstein also sees the variance.

*Comparison.*
The table below summarizes the four inequalities.
Hoeffding and Bernstein both control a sum of independent terms and differ only in what they measure: Hoeffding charges every term its full range $(b_i - a_i)$, whereas Bernstein replaces the range by the variance and pays the range only through the lower-order term $b t / 3$ --- a strict improvement whenever the variance is small.
Sampling without replacement controls the same kind of sample mean as Hoeffding but with _dependent_ draws; the dependence only helps, so the bound is unchanged.
McDiarmid keeps Hoeffding's exponent but replaces "sum" by an arbitrary function with bounded coordinatewise differences, which is what makes it applicable beyond sums.

#block(breakable: false)[
  #table(
    columns: 4,
    align: (left, left, left, left),
    inset: 6pt,
    table.header(
      [*Inequality*], [*Quantity controlled*], [*Key assumptions*], [*Tail bound*],
    ),
    [Hoeffding],
    [sum $S$ of independent bounded variables],
    [$X_i$ independent, $X_i in [a_i, b_i]$],
    [$exp(-2 t^2 / A)$, $A=sum_i (b_i-a_i)^2$],

    [Hoeffding, without replacement],
    [mean of a size-$n$ sample from a finite population],
    [population values in $[a,b]$, sample drawn without replacement],
    [$2 exp(-2 n epsilon^2 \/ (b-a)^2)$],

    [McDiarmid],
    [an arbitrary function $f(X_1, dots, X_n)$],
    [$X_i$ independent, $f$ has bounded differences $c_i$],
    [$exp(-2 t^2 \/ sum_i c_i^2)$],

    [Bernstein],
    [sum $S$ of independent bounded variables],
    [$X_i$ independent, mean-zero, $abs(X_i) <= b$],
    [$exp(-t^2 \/ (2(sigma^2 + b t \/ 3)))$],
  )
]

== Proofs

We first isolate the lemma that powers the sub-Gaussian bounds.

*Hoeffding's lemma.*
If $Y$ is centered and $Y in [a,b]$ almost surely, then for every $lambda in RR$,
$
  log(EE[exp(lambda Y)]) <= lambda^2 (b-a)^2 / 8.
$

#proof[
  Let $psi(lambda) = log(EE[exp(lambda Y)])$.
  Differentiating under the expectation,
  $
    psi'(lambda) = EE[Y exp(lambda Y)] / EE[exp(lambda Y)],
    quad
    psi''(lambda) = EE[Y^2 exp(lambda Y)] / EE[exp(lambda Y)] - psi'(lambda)^2 .
  $
  These are exactly the mean and variance of $Y$ under the tilted law $dif Q_lambda / dif PP = exp(lambda Y) / EE[exp(lambda Y)]$.
  Since $Q_lambda$ is supported in $[a,b]$, any random variable with this law lies in $[a,b]$, so by the well-known bound on the variance of a $[a,b]$-valued variable,
  $
    psi''(lambda) = Var_(Q_lambda)(Y) <= (b-a)^2 / 4 .
  $
  The variance bound follows because $EE[(Y-a)(b-Y)] >= 0$, which expands to $Var(Y) <= (b-EE[Y])(EE[Y]-a) <= (b-a)^2/4$.
  Centeredness gives $psi(0) = 0$ and $psi'(0) = EE[Y] = 0$, so Taylor's theorem with integral remainder yields
  $
    psi(lambda)
      = integral_0^lambda (lambda - s) psi''(s) dif s
      <= (b-a)^2 / 4 integral_0^lambda (lambda - s) dif s
      = lambda^2 (b-a)^2 / 8 .
  $
]

*Proof of Hoeffding's inequality.*
Let $S = sum_i (X_i - EE[X_i])$.
By independence and Hoeffding's lemma,
$
  log(EE[exp(lambda S)])
  = sum_(i=1)^n log(EE[exp(lambda (X_i - EE[X_i]))])
  <= lambda^2 / 8 sum_(i=1)^n (b_i - a_i)^2
  = lambda^2 A / 8 .
$
Chernoff gives, for every $lambda > 0$,
$
  PP[S >= t] <= exp(-lambda t + lambda^2 A / 8).
$
The right-hand side is minimized at $lambda = 4t/A$, yielding
$
  PP[S >= t] <= exp(-2 t^2 / A).
$
Applying the same argument to $-S$ and taking a union bound gives the two-sided inequality.

*Proof of Hoeffding without replacement.*
It suffices to consider an ordered sample $X_1, dots, X_n$ drawn without replacement from the fixed population $z_1, dots, z_N$; the unordered subset average has the same distribution.
If $n=N$, the sample mean equals the population mean exactly, so assume $n < N$.
Let
$
  S := sum_(i=1)^n X_i,
  quad
  cal(F)_k := sigma(X_1, dots, X_k),
  quad
  M_k := EE[S | cal(F)_k].
$
Then $(M_k)_(k=0)^n$ is a martingale and $M_n - M_0 = S - EE[S]$.

Fix $k$ and condition on $cal(F)_(k-1)$.
There are $m = N-k+1$ population elements still available; write their mean as $mu_(k-1)$.
If the next draw is $X_k=x$, then the remaining $m-1$ elements have mean
$
  (m mu_(k-1) - x)/(m-1).
$
Thus the conditional expectation of the final sum changes by
$
  M_k - M_(k-1)
  = (N-n)/(N-k) (x - mu_(k-1)).
$
As $x$ ranges over the remaining population, this martingale difference lies in an interval of length at most
$
  (N-n)/(N-k) (b-a) <= b-a.
$
Its conditional mean is zero, so the conditional form of Hoeffding's lemma gives
$
  EE[exp(lambda (M_k-M_(k-1))) | cal(F)_(k-1)]
  <= exp(lambda^2 (b-a)^2 / 8).
$
Iterating over $k=1,dots,n$ yields
$
  log(EE[exp(lambda (S - EE[S]))])
  <= n lambda^2 (b-a)^2 / 8.
$
Chernoff and the same optimization as before give
$
  PP[S - EE[S] >= t] <= exp(- (2 t^2) / (n (b-a)^2)).
$
Since $EE[S] = n mu$, set $t = n epsilon$ and repeat for the lower tail:
$
  PP[abs(1/n S - mu) >= epsilon]
  <= 2 exp(- (2 n epsilon^2) / (b-a)^2).
$

*Proof of McDiarmid's inequality.*
Let
$
  Z := f(X_1, dots, X_n),
  quad
  cal(F)_i := sigma(X_1, dots, X_i),
  quad
  M_i := EE[Z | cal(F)_i].
$
Then $M_i$ is the Doob martingale of $Z$.
We have
$
  Z - EE[Z] = sum_(i=1)^n (M_i - M_(i-1)).
$
Define
$
  g_i(x) := EE[f(X_1, dots, X_(i-1), x, X_(i+1), dots, X_n) | cal(F)_(i-1)] .
$
By independence of $X_i$ from $cal(F)_(i-1)$, $M_i = g_i(X_i)$ and $M_(i-1) = EE[g_i(X_i) | cal(F)_(i-1)]$.
The bounded-differences hypothesis gives $abs(g_i(x) - g_i(x')) <= c_i$ for all $x, x'$, so $g_i$ has range at most $c_i$.
Hence the martingale difference $M_i - M_(i-1) = g_i(X_i) - EE[g_i(X_i) | cal(F)_(i-1)]$ has conditional mean zero and conditional range length at most $c_i$.
By conditional Hoeffding's lemma,
$
  EE[exp(lambda (M_i-M_(i-1))) | cal(F)_(i-1)]
  <= exp(lambda^2 c_i^2 / 8).
$
Iterating conditional expectations gives
$
  log(EE[exp(lambda (Z - EE[Z]))])
  <= lambda^2 / 8 sum_(i=1)^n c_i^2.
$
Chernoff and optimization give
$
  PP[Z - EE[Z] >= t]
  <= exp(- (2 t^2) / (sum_(i=1)^n c_i^2)).
$
Apply the same argument to $-f$ for the lower tail.

*Proof of Bernstein's inequality.*
Let $S = sum_(i=1)^n X_i$ and let $v = sigma^2 = sum_i EE[X_i^2]$.
For $0 < lambda < 3/b$, using $EE[X_i]=0$, $abs(X_i) <= b$, and the elementary bound $q! >= 2 dot 3^(q-2)$ for $q >= 2$, we get
$
  EE[exp(lambda X_i)]
  = 1 + sum_(q=2)^infinity lambda^q EE[X_i^q] / q!
  <= 1 + sum_(q=2)^infinity lambda^q EE[abs(X_i)^q] / q!
$
$
  <= 1 + (lambda^2 EE[X_i^2])/2 sum_(q=0)^infinity (lambda b / 3)^q
  <= exp( (lambda^2 EE[X_i^2]) / (2(1 - lambda b / 3)) ).
$
By independence,
$
  log(EE[exp(lambda S)])
  <= (lambda^2 v) / (2(1 - lambda b / 3)).
$
Therefore
$
  PP[S >= t]
  <= exp(-lambda t + (lambda^2 v)/(2(1 - lambda b / 3))).
$
Choose
$
  lambda = t / (v + b t / 3).
$
Then $0 < lambda < 3/b$ and
$
  -lambda t + (lambda^2 v)/(2(1 - lambda b / 3))
  = - t^2 / (2(v + b t / 3)).
$
This proves Bernstein's upper-tail inequality; the lower tail follows by applying the same argument to $-X_i$.

All four proofs fit the same template:
construct a sum or martingale, prove a conditional MGF bound for each increment, multiply the bounds by independence or the tower rule, and optimize the Chernoff parameter.
What changes is the source of the MGF bound: range alone for Hoeffding, finite-population martingale ranges for sampling without replacement, coordinate stability for McDiarmid, and variance plus range for Bernstein.

== The payoff: a generalization guarantee for empirical risk minimization

Let $cal(H)$ be a binary hypothesis class and let $Z=(X,Y)$ be drawn from $cal(D)$.
For $h in cal(H)$ define the $0$-$1$ loss
$
  ell_h(Z) := 1[h(X) != Y],
$
the population risk
$
  L_cal(D)(h) := EE[ell_h(Z)],
$
and for an i.i.d. sample $S=(Z_1, dots, Z_n)$ drawn from $cal(D)^n$, the empirical risk
$
  L_n(h) := 1/n sum_(i=1)^n ell_h(Z_i).
$
Let
$
  hat(h) in argmin_(h in cal(H)) L_n(h)
$
be an empirical risk minimizer.

The goal is to prove that with high probability,
$
  L_cal(D)(hat(h))
  <= inf_(h in cal(H)) L_cal(D)(h)
    + O(sqrt((log(Gamma_cal(H)(2n)) + log(1/delta)) / n)).
$

=== Step 1: reduce ERM to uniform convergence

Define the uniform generalization gap
$
  Delta(S) := sup_(h in cal(H)) abs(L_cal(D)(h) - L_n(h)).
$
On any sample $S$, for every $h in cal(H)$,
$
  L_cal(D)(hat(h))
  <= L_n(hat(h)) + Delta(S)
  <= L_n(h) + Delta(S)
  <= L_cal(D)(h) + 2 Delta(S).
$
Taking the infimum over $h$ gives
$
  L_cal(D)(hat(h))
  <= inf_(h in cal(H)) L_cal(D)(h) + 2 Delta(S).
$
Thus it remains to bound $Delta(S)$ with high probability.

=== Step 2: concentration of the uniform gap around its mean

Changing one example $Z_i$ changes every empirical risk $L_n(h)$ by at most $1/n$, and leaves $L_cal(D)(h)$ fixed.
Therefore $Delta(S)$ changes by at most $1/n$ when one coordinate of $S$ is changed.
McDiarmid's inequality gives, for every $s>0$,
$
  PP[Delta(S) - EE[Delta(S)] >= s] <= exp(-2 n s^2).
$
Equivalently, with probability at least $1-delta$,
$
  Delta(S) <= EE[Delta(S)] + sqrt(log(1/delta)/(2n)).
$

=== Step 3: symmetrization

Let $S^g=(Z_1^g, dots, Z_n^g)$ be an independent ghost sample from $cal(D)^n$, and let
$
  L_n^g(h) := 1/n sum_(i=1)^n ell_h(Z_i^g).
$
For each fixed $h$, $EE_(S^g)[L_n^g(h)] = L_cal(D)(h)$, so $L_cal(D)(h) - L_n(h) = EE_(S^g)[L_n^g(h) - L_n(h)]$ pointwise in $S$.
By Jensen's inequality applied to the convex function $|dot|$, and then by exchanging $sup$ and $EE_(S^g)$ via monotonicity,
$
  abs(L_cal(D)(h) - L_n(h))
  <= EE_(S^g)[abs(L_n^g(h) - L_n(h))]
  quad ==> quad
  sup_(h in cal(H)) abs(L_cal(D)(h) - L_n(h))
  <= EE_(S^g)[sup_(h in cal(H)) abs(L_n^g(h) - L_n(h))] .
$
Taking expectation over $S$,
$
  EE[Delta(S)]
  <= EE_(S,S^g)[sup_(h in cal(H)) abs(L_n^g(h)-L_n(h))].
$
So the population-vs-empirical problem is reduced to comparing two empirical averages on two independent samples.

=== Step 4: condition on the combined sample

Condition on the unordered pool of the combined $2n$ observations in $S union S^g$.
Because the two samples are i.i.d. and exchangeable, after conditioning the only randomness is which $n$ of the $2n$ positions are assigned to $S$; this is a uniform split without replacement.

Fix a hypothesis $h$.
On the conditioned pool, the losses $ell_h(Z_i)$ are fixed numbers in $[0,1]$.
Let $L_P(h)$ be their average over the full $2n$-point pool.
Since $S$ and $S^g$ are complementary halves,
$
  abs(L_n^g(h) - L_n(h)) = 2 abs(L_n(h) - L_P(h)).
$
Hoeffding without replacement with $N=2n$ and sample size $n$ gives
$
  PP[abs(L_n^g(h) - L_n(h)) > t | S union S^g]
  <= 2 exp(- n t^2 / 2).
$

Now take a union bound over prediction patterns on the conditioned $2n$ feature points.
Each loss pattern is determined by a prediction pattern and the fixed labels in the pool, so the number of distinct loss patterns is at most the growth function $Gamma_cal(H)(2n)$.
Therefore, with
$
  Y := sup_(h in cal(H)) abs(L_n^g(h)-L_n(h)),
$
we have
$
  PP[Y > t | S union S^g]
  <= 2 Gamma_cal(H)(2n) exp(-n t^2/2).
$

Since $Y in [0,1]$, integrating this tail bound gives
$
  EE[Y | S union S^g]
  = integral_0^1 PP[Y > t | S union S^g] dif t
  <= t_0 + integral_(t_0)^infinity 2 Gamma_cal(H)(2n) exp(-n t^2 / 2) dif t .
$
Choose
$
  t_0 = sqrt(2 log(2 Gamma_cal(H)(2n)) / n) ;
$
the integrand at $t_0$ equals $1$ and the Gaussian tail integrates to at most $sqrt(2 pi / n) / 2$, so
$
  EE[Y | S union S^g]
  <= C sqrt(log(2 Gamma_cal(H)(2n)) / n)
$
for a universal constant $C$.
Taking expectation over the pool,
$
  EE[Delta(S)]
  <= C sqrt(log(2 Gamma_cal(H)(2n)) / n).
$

=== Step 5: finish the high-probability bound

Combining the expectation bound with McDiarmid's inequality, with probability at least $1-delta$,
$
  Delta(S)
  <= C sqrt(log(2 Gamma_cal(H)(2n)) / n)
     + sqrt(log(1/delta)/(2n)).
$
Absorbing constants and the harmless factor of $2$ inside the logarithm,
$
  Delta(S)
  = O(sqrt((log(Gamma_cal(H)(2n)) + log(1/delta)) / n)).
$
Using the ERM reduction from Step 1,
$
  L_cal(D)(hat(h))
  <= inf_(h in cal(H)) L_cal(D)(h)
    + O(sqrt((log(Gamma_cal(H)(2n)) + log(1/delta)) / n)).
$
This is the i.i.d. growth-function ERM guarantee, and it completes the mini-course.

== References

- Boucheron, Lugosi, and Massart, _Concentration Inequalities: A Nonasymptotic Theory of Independence_.
  See Lemma 2.2 for Hoeffding's lemma, Theorem 2.8 for Hoeffding's inequality, Theorem 2.10 and Corollary 2.11 for Bernstein-type bounds, Section 3.2 for the bounded-differences property, and Theorem 6.2 for McDiarmid's inequality.
- Shalev-Shwartz and Ben-David, _Understanding Machine Learning: From Theory to Algorithms_.
  See Chapters 2--4 for the ERM principle and the agnostic PAC setting, and Chapter 6 for the growth function and the uniform-convergence reduction.
- Vapnik and Chervonenkis, _On the Uniform Convergence of Relative Frequencies of Events to Their Probabilities_, Theory of Probability and Its Applications 16 (1971).
  This is the original source of the symmetrization argument and the growth-function bound used in the final section.
