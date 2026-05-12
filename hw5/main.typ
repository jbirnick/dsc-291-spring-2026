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
#let rank = math.op("rank")
#let poly = math.op("poly")
#let sign = math.op("sign")
#let NP = math.op("NP")
#let RP = math.op("RP")

#show: homework.with(
  number: 5,
  date: [17 May 2026],
  course: [DSC 291 -- Learning Theory through Formal Proof and Proof Presentation],
  quarter: [Spring 2026],
  instructor: [Tianhao Wang]
)

= Part A

1. Let
  $
    V =
    cases(
      O(k log(e d / k)) & "if" 1 <= k <= d/2,
      O(d) & "if" k > d/2.
    )
  $
  The VC bound implies the usual agnostic uniform-convergence sample complexity: if exact empirical risk minimization over $cal(H)_(d,k)$ were available, then with
  $
    m = O((V + log(1/delta)) / epsilon^2)
  $
  samples, an empirical-risk minimizer $hat(h) in cal(H)_(d,k)$ would satisfy
  $
    L_D(hat(h)) <= inf_(h in cal(H)_(d,k)) L_D(h) + epsilon
  $
  with probability at least $1-delta$.

  The realizable brute-force algorithm enumerates all supports $T subset.eq [d]$ with $abs(T) <= k$ and solves one linear feasibility problem on each support. Its runtime is
  $
    sum_(s=0)^k binom(d,s) dot poly(m,d)
    <= (e d / k)^k dot poly(m,d)
  $
  up to polynomial factors from the feasibility solver. This is polynomial in $d$ when $k$ is a fixed constant. It is quasi-polynomial for $k = O(log(d))$ and exponential when $k$ grows polynomially with $d$.

  There is no contradiction: the VC bound is statistical and says that not many samples are needed once an empirical optimizer is available. The support-enumeration bound is computational and says that finding the best sparse classifier may still be expensive when $k$ is part of the input.

2. Given a set-cover instance with universe $U = {u_1, dots, u_r}$, sets $A_1, dots, A_q$, and budget $k$, set $d = q$ and $M = q + 1$.
  The agreement value is the number of sample points classified correctly, counting repeated examples with multiplicity.
  We use one coordinate per set.
  For each $j in [q]$, add one positive example
  $
    (e_j, +1),
  $
  where $e_j$ is the $j$th standard basis vector. For each universe element $u_i$, define $a_i in RR^q$ by
  $
    (a_i)_j = 1[u_i in A_j].
  $
  Add $M$ copies of the negative example $(a_i, -1)$. Finally set
  $
    K = q - k + M r .
  $

  #proof[
    Suppose first that there is a cover $R subset.eq [q]$ with $abs(R) = s <= k$. Define $w_j = -1$ for $j in R$ and $w_j = 0$ otherwise. Then $w$ is $k$-sparse. The positive example $(e_j,+1)$ is correct exactly when $j$ is not in $R$, so at least $q-k$ positive examples are correct. Since $R$ covers every $u_i$,
    $
      chevron.l w, a_i chevron.r = - abs({j in R : u_i in A_j}) < 0
    $
    for every $i$. Hence all $M r$ repeated negative examples are correct. The total agreement is at least $q-k+M r = K$.

    Conversely, suppose some $k$-sparse $w$ correctly labels at least $K$ sample points. Let
    $
      R = {j in [q] : w_j < 0}.
    $
    Then $abs(R) <= norm(w)_0 <= k$. On the positive examples, exactly the coordinates with $w_j < 0$ are mistakes, since $sign(0)=+1$. For a negative example $(a_i,-1)$ to be correct, we need
    $
      chevron.l w, a_i chevron.r < 0.
    $
    This is possible only if some set containing $u_i$ has negative weight; that is, only if $u_i$ is covered by $R$.
    If $u_i$ is not covered by $R$, then all coordinates participating in $a_i$ are nonnegative, so $chevron.l w,a_i chevron.r >= 0$ and all $M$ copies of the negative example are wrong.

    Let $c$ be the number of universe elements covered by $R$. The total number of correct labels is at most $q + M c$. If $c <= r-1$, then
    $
      q + M c <= q + M(r-1) < q - k + M r = K,
    $
    because $M = q+1 > k$. This contradicts the assumed agreement. Thus $c=r$, so $R$ is a set cover of size at most $k$.
  ]

  The construction is polynomial in the size of the set-cover instance. Also, hypotheses in $cal(H)_(d,k)$ have polynomial-size descriptions and can be evaluated in polynomial time. The Week 5 learner-to-agreement theorem therefore applies to the family when both $d$ and $k$ are input parameters: an efficient proper agnostic PAC learner would give a randomized polynomial-time algorithm for this agreement problem. Since set cover reduces to it, such a learner would imply $NP subset.eq RP$. Therefore, if $NP != RP$, there is no efficient proper agnostic PAC learner for sparse linear classifiers when $k$ is part of the input.

3. --

#pagebreak()
= Part B

1. Introduce variables $w_j^+ >= 0$, $w_j^- >= 0$, and $xi_i >= 0$, with $w_j = w_j^+ - w_j^-$. The linear program is
  $
    min_(w^+, w^-, xi) 1/m sum_(i=1)^m xi_i
  $
  subject to
  $
    y_i sum_(j=1)^d (w_j^+ - w_j^-) x_(i,j) + xi_i >= 1
    quad "for all" i,
  $
  $
    sum_(j=1)^d (w_j^+ + w_j^-) <= B,
    quad
    w_j^+, w_j^-, xi_i >= 0 .
  $
  The first family of constraints enforces
  $
    xi_i >= 1 - y_i chevron.l w, x_i chevron.r.
  $
  Together with $xi_i >= 0$ and the objective, this makes $xi_i$ equal to the hinge loss at optimum.
  The variables $w_j^+$ and $w_j^-$ encode the positive and negative parts of $w_j$, so the constraint on $sum_j (w_j^+ + w_j^-)$ is the linear-program version of $norm(w)_1 <= B$.

  This LP is not solving empirical 0-1 agreement over $k$-sparse classifiers. It optimizes hinge loss rather than the discontinuous 0-1 loss, and it constrains $norm(w)_1$ rather than the support size $norm(w)_0$. Its output need not be $k$-sparse and need not maximize the number of correctly classified sample points.

2. The population hinge risk is
  $
    L_("hinge")(w) = (1-p)(1-w)_+ + p(1+M w)_+ .
  $
  There are breakpoints at $w=-1/M$ and $w=1$. For $w <= -1/M$,
  $
    L_("hinge")(w) = (1-p)(1-w),
  $
  which is strictly decreasing. For $-1/M <= w <= 1$,
  $
    L_("hinge")(w) = (1-p)(1-w) + p(1+M w)
    = 1 + (p M - (1-p)) w.
  $
  Since $M > (1-p)/p$, this is strictly increasing. For $w >= 1$,
  $
    L_("hinge")(w) = p(1+M w),
  $
  which is also strictly increasing. Hence the unique population hinge-risk minimizer is
  $
    w^* = -1/M .
  $

  For 0-1 loss with zero margin counted as an error, if $w>0$, then $(1,+1)$ is correct and $(-M,+1)$ is wrong, so the risk is $p$. If $w<0$, then $(1,+1)$ is wrong and $(-M,+1)$ is correct, so the risk is $1-p$. If $w=0$, both margins are zero and the risk is $1$. Therefore
  $
    inf_w L_("0-1")(f_w) = p,
  $
  achieved by every $w>0$, while the hinge minimizer $w^*=-1/M$ has 0-1 risk $1-p$.

  Given any $epsilon > 0$ and $alpha < 1$, choose
  $
    0 < p < min(epsilon, 1-alpha, 1/2)
  $
  and then choose $M > (1-p)/p$. Then
  $
    inf_w L_("0-1")(f_w) = p <= epsilon
  $
  but every hinge-risk minimizer has 0-1 risk $1-p > alpha$.

3. For $I subset.eq [d]$, write $chi_I(x)=product_(i in I) x_i$.
  Let $H$ be the $2^d times 2^d$ matrix whose rows are indexed by $I subset.eq [d]$, columns by $x in {-1,+1}^d$, and entries are
  $
    H_(I,x) = chi_I(x).
  $
  For two rows $I,J$,
  $
    sum_(x in {-1,+1}^d) chi_I(x) chi_J(x)
    = sum_(x in {-1,+1}^d) chi_(I Delta J)(x).
  $
  If $I=J$, this sum is $2^d$. If $I != J$, choose $a in I Delta J$ and pair each $x$ with the point obtained by flipping coordinate $a$; the terms cancel pairwise. Thus the rows of $H$ are nonzero and mutually orthogonal, so
  $
    rank(H) = 2^d .
  $

  If a fixed feature map $phi : {-1,+1}^d -> RR^D$ represents every parity exactly, then for each $I$ there is $w_I in RR^D$ with
  $
    chi_I(x) = chevron.l w_I, phi(x) chevron.r
  $
  for every $x$. Let $W$ be the $2^d times D$ matrix with row $w_I^T$, and let $Phi$ be the $D times 2^d$ matrix with column $phi(x)$. Then
  $
    H = W Phi.
  $
  Hence
  $
    2^d = rank(H) <= D,
  $
  so $D >= 2^d$.

  The matching upper bound uses one feature per parity:
  $
    phi(x) = (chi_I(x))_(I subset.eq [d]) in RR^(2^d).
  $
  To represent the parity $chi_J$, choose $w_J$ to be the coordinate vector that is $1$ at coordinate $J$ and $0$ elsewhere. Then
  $
    chevron.l w_J, phi(x) chevron.r = chi_J(x)
  $
  for every $x$.

  Thus exactly representing all parities by fixed linear features requires and suffices with $2^d$ features. The Week 5 message is that fixed-feature convex learning can make the optimization problem clean, but the feature map may need exponentially many coordinates to express the target class.

4. The two parameterizations represent the same set of predictors. For any network parameters $(u,v)$,
  $
    f_(u,v)(x) = v chevron.l u,x chevron.r = chevron.l v u, x chevron.r,
  $
  so the corresponding linear coefficient is $beta = v u$. Conversely, every $beta in RR^d$ is represented by $v=1$ and $u=beta$.

  The fixed-feature objective is convex because
  $
    L_("lin")(beta) = 1/m sum_(i=1)^m (chevron.l beta,x_i chevron.r - y_i)^2
  $
  is a sum of squares of affine functions. Equivalently its Hessian is
  $
    2/m sum_(i=1)^m x_i x_i^T,
  $
  which is positive semidefinite.

  The network objective is not necessarily convex. Take $d=1$, one example $x_1=1$, $y_1=1$. Then
  $
    L_("net")(u,v) = (u v - 1)^2 .
  $
  At $(u,v)=(1,1)$ and $(-1,-1)$ the loss is $0$, but at their midpoint $(0,0)$ the loss is $1$. Convexity would require
  $
    L_("net")(0,0) <= (L_("net")(1,1) + L_("net")(-1,-1))/2 = 0,
  $
  a contradiction.

  Finally, if $beta^*$ minimizes $L_("lin")$ and $beta^* = v u$, then
  $
    L_("net")(u,v) = L_("lin")(v u) = L_("lin")(beta^*).
  $
  For any other $(u',v')$,
  $
    L_("net")(u',v') = L_("lin")(v' u') >= L_("lin")(beta^*).
  $
  Hence every factorization of $beta^*$ is a global minimizer of $L_("net")$.

  This example separates representation from optimization geometry: the learned-feature parameterization represents the same linear predictors, but the map $(u,v) -> v u$ makes the empirical risk nonconvex.

#pagebreak()
= Part C

I significantly used AI in this assignment in order to generate the proofs.
I was only able to spot-check the proofs, and I'm conviced of their correctness, however I admittedly didn't check them fully due to lack of time.
I'm happy to accept deductions for partly using AI as an oracle, unfortunately I was unable to finish the homework otherwise, so I'm happy to be graded as if I had not submitted parts of it.

I was not happy with the experiment it generated, so did explicitly exclude that.