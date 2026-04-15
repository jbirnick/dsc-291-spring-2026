# The No-Free-Lunch Theorem

**Week 1 — Lecture Notes**
*April 2, 2026 · Topics in Learning Theory*

---

These notes accompany the Week 1 lecture. They cover the online prediction model, the no-free-lunch theorem, and the role of structural assumptions in making learning possible—culminating in the Perceptron algorithm and its mistake bound.

---

## 1. The Online Prediction Model

We begin with the simplest model of learning: a learner receives data points one at a time, makes a prediction for each, and then discovers whether it was right. There is no training set given in advance; the learner must predict as it goes. The fundamental question is: **how many mistakes must the learner make?**

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

The crucial feature of this protocol is that the learner must commit to a prediction *before* seeing the true label. Learning happens only through the feedback received after each prediction.

> **Example 1** (Threshold classifiers on $\mathbb{R}$).
> Let $\mathcal{X} = \mathbb{R}$ and consider the family of threshold classifiers $h_\theta(x) = \mathbf{1}[x \geq \theta]$ for some $\theta \in \mathbb{R}$. The classifier predicts 1 for points at or above the threshold and 0 below it. For instance, with $\theta = 5$:
>
> - $h_5(3) = 0$ — below the threshold.
> - $h_5(7) = 1$ — above the threshold.
> - $h_5(5) = 1$ — at the threshold.

### 1.2 What is a learner?

A *learner* (or *learning rule*) is a mapping

$$A : (\mathcal{X} \times \mathcal{Y})^* \;\to\; \mathcal{Y}^{\mathcal{X}}$$

that takes a history of past observations and returns a hypothesis. Given history $H_{t-1}$, the learner produces $h_t = A(H_{t-1})$ and predicts $\hat{y}_t = h_t(x_t)$. Two simple examples: the *constant learner* that always predicts $\hat{y}_t = 1$ regardless of history, and the *memorization learner* that returns the last label seen for a given input (or a default if the input is new).

### 1.3 Counting mistakes

> **Definition 2** (Mistake Count).
> A *mistake* occurs in round $t$ when $\hat{y}_t \neq y_t$. The total number of mistakes over $T$ rounds is
>
> $$M_T \;=\; \sum_{t=1}^{T} \mathbf{1}[\hat{y}_t \neq y_t].$$

The learner's goal is to keep $M_T$ small. But small relative to what? Can we hope for a learner that makes few mistakes against *all* possible label sequences, or only when the labels obey some structure? This is the question the no-free-lunch theorem answers.

> **Example 2** (A few rounds of online prediction).
> Suppose $\mathcal{X} = \mathbb{R}$, the true labeling rule is $h_3(x) = \mathbf{1}[x \geq 3]$, and the learner always predicts $\hat{y}_t = 1$.
>
> - **Round 1:** $x_1 = 5$ arrives. Learner predicts 1. True label: $h_3(5) = 1$. Correct.
> - **Round 2:** $x_2 = 1$ arrives. Learner predicts 1. True label: $h_3(1) = 0$. **Mistake.**
> - **Round 3:** $x_3 = 4$ arrives. Learner predicts 1. True label: $h_3(4) = 1$. Correct.
> - **Round 4:** $x_4 = 2$ arrives. Learner predicts 1. True label: $h_3(2) = 0$. **Mistake.**
>
> After 4 rounds, $M_4 = 2$.

---

## 2. The No-Free-Lunch Theorem

One might hope for a *universal learner*—one that makes few mistakes regardless of the labeling rule generating the data. The no-free-lunch theorem crushes this hope: for *any* deterministic learner, an adversary can construct a labeling function that forces the learner to be wrong on every single prediction.

> **Theorem 1** (No-Free-Lunch).
> For any finite instance space $\mathcal{X}$ and any deterministic learner $A$, there exists a function $f : \mathcal{X} \to \{0, 1\}$ and a sequence $x_1, \ldots, x_n$ of all $n = |\mathcal{X}|$ distinct elements of $\mathcal{X}$ such that $A$ makes $n$ mistakes on the sequence $(x_t,\; y_t = f(x_t))_{t=1}^n$.

*Proof.* Fix any ordering $x_1, \ldots, x_n$ of $\mathcal{X}$. We construct the function $f$ point by point to defeat the learner.

In round $t$, the learner has observed the history $H_{t-1} = ((x_1, f(x_1)), \ldots, (x_{t-1}, f(x_{t-1})))$ and predicts $\hat{y}_t = A(H_{t-1})(x_t)$. We define

$$f(x_t) \;:=\; 1 - \hat{y}_t,$$

i.e., the opposite of whatever the learner predicts.

**Why is $f$ well-defined?** Each $x_t$ is a distinct element of $\mathcal{X}$, so we never assign a value to the same point twice.

**Why does the learner make $n$ mistakes?** By construction, $\hat{y}_t \neq f(x_t)$ on every round $t = 1, \ldots, n$. $\blacksquare$

### 2.1 The stronger adversarial form

The theorem above is enough to conclude that no learner can guarantee fewer than $|\mathcal{X}|$ mistakes in the worst case. But the proof idea actually gives a stronger online statement: once the learner is handed *any* distinct sequence of query points, the adversary can still choose a single target function that makes the learner fail on every round of that sequence.

> **Stronger Form** (Adversarial Online No-Free-Lunch).
> Let $\mathcal{X}$ be any instance space and let $A$ be any deterministic learner. For every finite sequence $x_1, \ldots, x_T$ of distinct points in $\mathcal{X}$, there exists a function $f : \mathcal{X} \to \{0, 1\}$ such that $A$ makes $T$ mistakes on the sequence $(x_t,\; y_t = f(x_t))_{t=1}^T$.

*Proof.* Fix any distinct sequence $x_1, \ldots, x_T$. We define the labels one round at a time. In round $t$, after observing the history $H_{t-1} = ((x_1, f(x_1)), \ldots, (x_{t-1}, f(x_{t-1})))$, the learner predicts $\hat{y}_t = A(H_{t-1})(x_t)$. We then set

$$f(x_t) \;:=\; 1 - \hat{y}_t.$$

Because the points $x_1, \ldots, x_T$ are distinct, no point is labeled twice, so this prescription is well-defined on the queried set $\{x_1, \ldots, x_T\}$. Extend $f$ arbitrarily to the rest of $\mathcal{X}$.

By construction, at every round $t$ we have $\hat{y}_t \neq f(x_t)$, so the learner makes a mistake on every round. Hence the total number of mistakes is $T$. $\blacksquare$

#### Lean proof (Lean 4)

```lean
theorem mistakeCountOn_adversarialRounds {α : Type} (A : Learner α)
    (hist : History α) (xs : List α) :
    mistakeCountOn A hist (adversarialRounds A hist xs) = xs.length := by
  induction xs generalizing hist with
  | nil =>
      simp [adversarialRounds, mistakeCountOn]
  | cons x xs ih =>
      have ih' :
          mistakeCountOn A (hist ++ [(x, flip (A hist x))])
            (adversarialRounds A (hist ++ [(x, flip (A hist x))]) xs) = xs.length :=
        ih (hist ++ [(x, flip (A hist x))])
      calc
        mistakeCountOn A hist (adversarialRounds A hist (x :: xs))
            = 1 + mistakeCountOn A (hist ++ [(x, flip (A hist x))])
                (adversarialRounds A (hist ++ [(x, flip (A hist x))]) xs) := by
                  simp [adversarialRounds, mistakeCountOn]
        _ = 1 + xs.length := by
              rw [ih']
        _ = (x :: xs).length := by
              simp [Nat.add_comm]

theorem roundsFromFunction_adversarialLabeling {α : Type} [DecidableEq α]
    (A : Learner α) (hist : History α) :
    ∀ {xs : List α}, xs.Nodup →
      roundsFromFunction (adversarialLabeling A hist xs) xs = adversarialRounds A hist xs := by
  intro xs hxs
  induction xs generalizing hist with
  | nil =>
      simp [roundsFromFunction, adversarialLabeling, adversarialRounds]
  | cons x xs ih =>
      rcases List.nodup_cons.mp hxs with ⟨hnotin, hxs⟩
      have htail :
          roundsFromFunction (adversarialLabeling A hist (x :: xs)) xs
            = roundsFromFunction (adversarialLabeling A (hist ++ [(x, flip (A hist x))]) xs) xs := by
        unfold roundsFromFunction
        apply List.map_congr_left
        intro z hz
        have hz_ne : z ≠ x := by
          intro hzx
          subst hzx
          exact hnotin hz
        simp [adversarialLabeling, hz_ne]
      calc
        roundsFromFunction (adversarialLabeling A hist (x :: xs)) (x :: xs)
            = (x, flip (A hist x))
                :: roundsFromFunction (adversarialLabeling A hist (x :: xs)) xs := by
                    simp [roundsFromFunction, adversarialLabeling]
        _ = (x, flip (A hist x))
                :: roundsFromFunction (adversarialLabeling A (hist ++ [(x, flip (A hist x))]) xs) xs := by
                    rw [htail]
        _ = (x, flip (A hist x))
                :: adversarialRounds A (hist ++ [(x, flip (A hist x))]) xs := by
                    rw [ih (hist := hist ++ [(x, flip (A hist x))]) hxs]
        _ = adversarialRounds A hist (x :: xs) := by
                    simp [adversarialRounds]

theorem noFreeLunch_distinctSequence {α : Type} [DecidableEq α]
    (A : Learner α) :
    ∀ {xs : List α}, xs.Nodup →
      ∃ f : α → Bool, mistakeCount A (roundsFromFunction f xs) = xs.length := by
  intro xs hxs
  refine ⟨adversarialLabeling A [] xs, ?_⟩
  rw [roundsFromFunction_adversarialLabeling (A := A) (hist := []) hxs]
  simpa [mistakeCount] using mistakeCountOn_adversarialRounds A [] xs
```

> **Remark** (Why this is stronger).
> The slide theorem is a corollary: if $\mathcal{X}$ is finite, choose $x_1, \ldots, x_T$ to be any ordering of all points in $\mathcal{X}$. The stronger theorem then produces a target function that defeats the learner on that full ordering. So the paper proof already gives more than the existential worst-case statement.

> **Example 3** (The adversary at work on $\mathcal{X} = \{a, b, c\}$).
> Consider any learner $A$. The adversary presents points in the order $a, b, c$ and constructs $f$ as follows:
>
> - **Round 1:** $x_1 = a$. Suppose $A$ predicts $\hat{y}_1 = 1$. Set $f(a) = 0$. Mistake.
> - **Round 2:** $x_2 = b$. The learner now knows $f(a) = 0$ and predicts, say, $\hat{y}_2 = 0$. Set $f(b) = 1$. Mistake.
> - **Round 3:** $x_3 = c$. The learner knows $f(a) = 0$ and $f(b) = 1$ and predicts, say, $\hat{y}_3 = 1$. Set $f(c) = 0$. Mistake.
>
> The resulting function $f = \{a \mapsto 0,\; b \mapsto 1,\; c \mapsto 0\}$ is a perfectly valid labeling of $\mathcal{X}$, but the learner was wrong every time. No matter how clever the learner is, a different adversarial $f$ will defeat it.

> **Remark.**
> The adversary's power comes from being *adaptive*: it sees the learner's prediction before choosing the label. If the labels were fixed in advance (i.e., the adversary is *oblivious*), the picture changes—this is one reason the statistical (batch) setting, where data is drawn i.i.d. from a fixed distribution, behaves very differently. We will study this starting in Week 2.

### 2.2 Lean proof of the stronger form

The Lean development separates the argument into three pieces: a core inductive theorem about adversarial transcripts, a bridge theorem that turns the adaptive adversary into a single global labeling function, and then a short wrapper theorem for the stronger statement. This keeps the formal proof close to the paper proof while making the bookkeeping explicit.

#### The core inductive theorem

The main technical lemma proves the adversarial mistake count from an *arbitrary* current history, not just from the empty history. That generalized statement is what makes induction possible after the history changes.

```lean
theorem mistakeCountOn_adversarialRounds {α : Type} (A : Learner α)
    (hist : History α) (xs : List α) :
    mistakeCountOn A hist (adversarialRounds A hist xs) = xs.length := by
  induction xs generalizing hist with
  | nil =>
      simp [adversarialRounds, mistakeCountOn]
  | cons x xs ih =>
      have ih' :
          mistakeCountOn A (hist ++ [(x, flip (A hist x))])
            (adversarialRounds A (hist ++ [(x, flip (A hist x))]) xs) = xs.length :=
        ih (hist ++ [(x, flip (A hist x))])
      calc
        mistakeCountOn A hist (adversarialRounds A hist (x :: xs))
            = 1 + mistakeCountOn A (hist ++ [(x, flip (A hist x))])
                (adversarialRounds A (hist ++ [(x, flip (A hist x))]) xs) := by
                  simp [adversarialRounds, mistakeCountOn]
        _ = 1 + xs.length := by
              rw [ih']
        _ = (x :: xs).length := by
              simp [Nat.add_comm]
```

The decisive phrase is `generalizing hist`. After the first round, the recursive call lives at the updated history `hist ++ [(x, flip (A hist x))]`, so the induction hypothesis must already be strong enough to handle any current history.

#### Bridge: From adaptive labels to one global function

The stronger theorem does not only talk about an adversarial transcript; it asks for a single target function `f : α → Bool`. The bridge theorem says that on a duplicate-free list, the recursively defined function `adversarialLabeling` produces exactly the same transcript as the adaptive construction.

```lean
theorem roundsFromFunction_adversarialLabeling {α : Type} [DecidableEq α]
    (A : Learner α) (hist : History α) :
    ∀ {xs : List α}, xs.Nodup →
      roundsFromFunction (adversarialLabeling A hist xs) xs = adversarialRounds A hist xs := by
  intro xs hxs
  induction xs generalizing hist with
  | nil =>
      simp [roundsFromFunction, adversarialLabeling, adversarialRounds]
  | cons x xs ih =>
      rcases List.nodup_cons.mp hxs with ⟨hnotin, hxs⟩
      have htail :
          roundsFromFunction (adversarialLabeling A hist (x :: xs)) xs
            = roundsFromFunction (adversarialLabeling A (hist ++ [(x, flip (A hist x))]) xs) xs := by
        unfold roundsFromFunction
        apply List.map_congr_left
        intro z hz
        have hz_ne : z ≠ x := by
          intro hzx
          subst hzx
          exact hnotin hz
        simp [adversarialLabeling, hz_ne]
      calc
        roundsFromFunction (adversarialLabeling A hist (x :: xs)) (x :: xs)
            = (x, flip (A hist x))
                :: roundsFromFunction (adversarialLabeling A hist (x :: xs)) xs := by
                    simp [roundsFromFunction, adversarialLabeling]
        _ = (x, flip (A hist x))
                :: roundsFromFunction (adversarialLabeling A (hist ++ [(x, flip (A hist x))]) xs) xs := by
                    rw [htail]
        _ = (x, flip (A hist x))
                :: adversarialRounds A (hist ++ [(x, flip (A hist x))]) xs := by
                    rw [ih (hist := hist ++ [(x, flip (A hist x))]) hxs]
        _ = adversarialRounds A hist (x :: xs) := by
                    simp [adversarialRounds]
```

This is where `xs.Nodup` matters: if a point appeared twice, the adaptive adversary could want different labels at the two occurrences, and that would not come from a single global function.

#### Lean theorem for the stronger form (Lean 4)

```lean
theorem noFreeLunch_distinctSequence {α : Type} [DecidableEq α]
    (A : Learner α) :
    ∀ {xs : List α}, xs.Nodup →
      ∃ f : α → Bool, mistakeCount A (roundsFromFunction f xs) = xs.length := by
  intro xs hxs
  refine ⟨adversarialLabeling A [] xs, ?_⟩
  rw [roundsFromFunction_adversarialLabeling (A := A) (hist := []) hxs]
  simpa [mistakeCount] using mistakeCountOn_adversarialRounds A [] xs
```

Here `xs.Nodup` is exactly the paper assumption that the query points are all distinct. The theorem chooses the global target function `adversarialLabeling A [] xs`, rewrites the resulting transcript into the adversarial transcript using `roundsFromFunction_adversarialLabeling`, and then invokes the core theorem `mistakeCountOn_adversarialRounds`.

---

## 3. How Structure Helps

The no-free-lunch theorem tells us that without any assumptions about the labeling rule, learning is hopeless. But real-world problems have structure: spam emails look different from legitimate ones, medical images of tumors differ from healthy tissue, and so on. The labeling rules we encounter in practice are not arbitrary—they belong to some restricted family. This insight leads to the central concept of a *hypothesis class*.

### 3.1 Hypothesis classes and realizability

> **Definition 3** (Hypothesis Class).
> A *hypothesis class* $\mathcal{H} \subseteq \mathcal{Y}^{\mathcal{X}}$ is a set of candidate labeling functions.

> **Assumption** (Realizability).
> There exists some $h^* \in \mathcal{H}$ such that $y_t = h^*(x_t)$ for all $t$. The learner knows $\mathcal{H}$ but does not know which $h^* \in \mathcal{H}$ generates the labels.

> **Remark.**
> The hypothesis class $\mathcal{H}$ encodes our *prior knowledge* about the problem. A smaller $\mathcal{H}$ represents a stronger assumption and should make learning easier; a larger $\mathcal{H}$ is a weaker assumption and makes learning harder. The no-free-lunch theorem corresponds to $\mathcal{H} = \mathcal{Y}^{\mathcal{X}}$, the set of all possible labelings—the weakest possible assumption.

### 3.2 Threshold functions: a binary search strategy

To see the power of structural assumptions, consider the simplest non-trivial example. Let $\mathcal{X} = [0, 1]$ and suppose the labels are generated by a threshold $h_{\theta^*}(x) = \mathbf{1}[x > \theta^*]$ for some unknown $\theta^* \in [0, 1]$. Despite the fact that $\mathcal{X}$ is infinite, we can learn with very few mistakes using a binary search strategy.

> **Example 4** (Binary search for thresholds).
> Maintain an interval $[a, b]$ known to contain $\theta^*$, starting with $[a, b] = [0, 1]$. When a point $x$ arrives, predict using the midpoint: $\hat{y} = \mathbf{1}[x > (a + b)/2]$.
>
> If we make a mistake at $x$, we learn which half of $[a, b]$ contains $\theta^*$ and shrink the interval accordingly:
>
> - Predicted 1 but $y = 0$: we know $\theta^* > x$, so update $[a, b] \gets [x, b]$.
> - Predicted 0 but $y = 1$: we know $\theta^* < x$, so update $[a, b] \gets [a, x]$.
>
> Why does this give a halving guarantee? Let $m = (a+b)/2$ be the midpoint used for prediction. If we predict 1 and are wrong, then $x > m$ but the true label is 0, so $x \leq \theta^*$; hence $\theta^* \in [x, b]$, and the new interval has length $b - x \leq b - m = (b-a)/2$. Similarly, if we predict 0 and are wrong, then $x \leq m$ but the true label is 1, so $\theta^* < x$; hence $\theta^* \in [a, x]$, and the new interval has length $x - a \leq m - a = (b-a)/2$.
>
> After $k$ mistakes the interval has length $(b - a)/2^k$. To achieve precision $\varepsilon$, we need at most $\lceil \log_2(1/\varepsilon) \rceil$ mistakes.

This is a dramatic improvement over the no-free-lunch lower bound: structure (the assumption that labels come from a threshold) transforms learning from impossible to logarithmic.

---

## 4. Finite Hypothesis Classes and the Halving Algorithm

The binary search idea for thresholds generalizes beautifully to *any* finite hypothesis class. The key concept is the *version space*: the set of hypotheses still consistent with everything the learner has seen so far.

### 4.1 The Halving algorithm

> **Definition 4** (Version Space).
> The *version space* at round $t$ is $V_t = \{h \in \mathcal{H} : h(x_i) = y_i \text{ for all } i < t\}$, the set of hypotheses consistent with all observations so far.

> **Algorithm 1** (Halving).
>
> **Input:** Finite hypothesis class $\mathcal{H}$.
>
> 1. Initialize $V_1 = \mathcal{H}$.
> 2. At round $t$, predict $\hat{y}_t = \text{majority vote of } \{h(x_t) : h \in V_t\}$.
> 3. After observing $y_t$, update $V_{t+1} = \{h \in V_t : h(x_t) = y_t\}$.

The Halving algorithm predicts with the majority vote of all surviving hypotheses and then eliminates every hypothesis that disagrees with the revealed label. The true hypothesis $h^*$ is never eliminated, since it always predicts the correct label.

### 4.2 Mistake bound analysis

> **Theorem 2** (Halving Mistake Bound).
> Under the realizability assumption, the Halving algorithm makes at most $\lfloor \log_2 |\mathcal{H}| \rfloor$ mistakes.

*Proof.* We first verify that $h^*$ is never eliminated from the version space. Since $y_t = h^*(x_t)$ for all $t$ by the realizability assumption, $h^*$ always passes the consistency check, so $h^* \in V_t$ for all $t$. In particular, $|V_t| \geq 1$ always holds.

Now suppose the algorithm makes a mistake in round $t$: the majority of $V_t$ predicted the wrong label. This means at least half of the hypotheses in $V_t$ are eliminated, so $|V_{t+1}| \leq |V_t|/2$.

Starting from $|V_1| = |\mathcal{H}|$, after $k$ mistakes we have $|V| \leq |\mathcal{H}| / 2^k$. Since $|V| \geq 1$, we conclude $1 \leq |\mathcal{H}| / 2^k$, giving $k \leq \log_2 |\mathcal{H}|$. $\blacksquare$

### 4.3 Complexity of hypothesis classes

The Halving bound tells us that the number of mistakes scales with $\log_2 |\mathcal{H}|$. This quantity—the "size" of the hypothesis class—serves as a measure of learning difficulty. But what happens when $|\mathcal{H}|$ is infinite?

We already saw that threshold functions have $|\mathcal{H}| = \infty$ but can still be learned with $O(\log(1/\varepsilon))$ mistakes. So cardinality alone does not capture learning difficulty. We need a more refined notion of complexity—this will lead us to concepts like the VC dimension and Littlestone dimension in future weeks.

> **Remark** (The expressiveness–computation tradeoff).
> There is a tension between expressiveness and computational efficiency. Consider using $\mathcal{H}$ = all 100-line Python programs. The mistake bound would be $\log_2 128^{8000} \approx 56{,}000$, which is finite, but running Halving requires evaluating each surviving program on each example—a task that is not even computable in general (by the halting problem). Even for "nice" classes like decision trees with $k$ leaves over $|D|$ features, Halving achieves $O(k \log |D|)$ mistakes but requires $O(|D|^k)$ time per round. We want hypothesis classes that are both expressive *and* efficiently learnable.

---

## 5. Linear Predictors and the Perceptron

Linear predictors are the first example of a hypothesis class that is both highly expressive and efficiently learnable. They occupy a sweet spot that makes them one of the most important objects in learning theory.

### 5.1 Linear classifiers

> **Definition 5** (Linear Classifier / Halfspace).
> Given a feature map $\phi : \mathcal{X} \to \mathbb{R}^d$, a *linear classifier* is defined by a weight vector $w \in \mathbb{R}^d$ and a threshold $\theta \in \mathbb{R}$:
>
> $$h_{w,\theta}(x) \;=\; \mathbf{1}\bigl[\langle w, \phi(x) \rangle > \theta\bigr].$$
>
> The hypothesis class of all linear classifiers is $\mathcal{H} = \{h_{w,\theta} : w \in \mathbb{R}^d,\; \theta \in \mathbb{R}\}$.

Linear classifiers are far more expressive than they first appear. With the right choice of features, they can represent conjunctions ($[\phi_{i_1} + \phi_{i_2} + \phi_{i_3} > 2.5]$), disjunctions ($[\phi_{i_1} + \phi_{i_2} + \phi_{i_3} > 0.5]$), and weighted votes ($[3\phi_{\text{free}} + 2\phi_{\text{click}} - \phi_{\text{meeting}} > 1]$). The key question is: **can we learn linear classifiers online?**

### 5.2 The challenge of infinite hypothesis classes

The hypothesis class of linear classifiers is infinite—there are uncountably many choices of $(w, \theta)$. We cannot directly apply the Halving algorithm. In fact, for continuous threshold functions, an adversary can force infinite mistakes.

> **Theorem 3** (Continuous thresholds admit infinite mistakes).
> For the hypothesis class $\mathcal{H} = \{h_\theta(x) = \mathbf{1}[x \leq \theta] : \theta \in \mathbb{R}\}$, for any learner $A$ there exists a sequence realized by some $h_{\theta^*} \in \mathcal{H}$ on which $A$ makes a mistake on every round.

*Proof sketch.* For this construction it is convenient to switch temporarily to signed labels $z_t \in \{-1, +1\}$ and signed predictions $\hat{z}_t \in \{-1, +1\}$. Set $x_1 = 0.5$ and choose $z_t = -\hat{z}_t$, so the learner is wrong on every round. Then define

$$x_{t+1} = x_t + z_t \cdot 2^{-(t+1)}.$$

The resulting threshold

$$\theta^* = 0.5 + \sum_{t \geq 1} z_t \cdot 2^{-(t+1)}$$

is well-defined because the series converges. Moreover, $z_t = +1$ exactly when $x_t \leq \theta^*$, so the whole sequence is realized by the threshold classifier $h_{\theta^*}(x) = \mathbf{1}[x \leq \theta^*]$ after translating back to $0/1$ labels via $y_t = (z_t + 1)/2$.

The adversary exploits infinite precision: it pushes points arbitrarily close to the threshold, so the learner can never resolve where $\theta^*$ is. $\blacksquare$

One natural fix is *discretization*: restrict $\theta$ to a finite grid $G_r = \{-1, -\frac{r-1}{r}, \ldots, 0, \ldots, 1\}$. This gives $|\mathcal{H}| = 2r + 1$ in 1D, so Halving achieves $O(\log r)$ mistakes. In $d$ dimensions with $w \in G_r^d$, the mistake bound becomes $O(d \log r)$. But the runtime of Halving is $\Omega(|G_r|^d) = \Omega(r^d)$—**exponential in $d$**.

We arrive at a crossroads:

- **Approach 1 (continuous $\mathcal{H}$):** Adversary exploits infinite precision → infinite mistakes.
- **Approach 2 (discretize):** $O(d \log r)$ mistakes with Halving, but $\Omega(r^d)$ runtime → exponential.
- **Approach 3 (the Perceptron):** Works with continuous $\mathcal{H}$ directly, $O(1/\gamma^2)$ mistakes where $\gamma$ is the margin, $O(d)$ time per round → **efficient.**

The Perceptron sidesteps both problems by exploiting a geometric property of the data: the *margin*.

From this point on, it is convenient to use signed labels $y_t \in \{-1, +1\}$. We also absorb the threshold term into the feature map by augmenting $\phi(x)$ with one constant coordinate, so an affine classifier $h_{w,\theta}$ can be written in the form $\mathrm{sign}(\langle w, \phi(x) \rangle)$ without loss of generality.

### 5.3 Margin

> **Definition 6** (Margin).
> Given a labeled sequence $(x_t, y_t)_{t=1}^T$ with $y_t \in \{-1, +1\}$ and a unit-norm separator $w^*$ with $\|w^*\| = 1$, the *margin* is
>
> $$\gamma \;=\; \min_{t=1,\ldots,T} \; y_t \langle w^*,\, \phi(x_t) \rangle.$$

Geometrically, $\gamma$ is the minimum distance from any data point to the decision boundary $\{x : \langle w^*, \phi(x) \rangle = 0\}$.

A large margin means the two classes are well-separated—an "easy" problem. A small margin means points from opposite classes are nearly touching—a "hard" problem. The threshold counterexample above has $\gamma \to 0$: the adversary pushes points arbitrarily close to the decision boundary.

### 5.4 The Perceptron algorithm

> **Algorithm 2** (Perceptron, Rosenblatt 1958).
>
> **Input:** Feature map $\phi : \mathcal{X} \to \mathbb{R}^d$. Labels $y_t \in \{-1, +1\}$.
>
> 1. Initialize $w_1 = 0$.
> 2. Receive $x_t$, predict $\hat{y}_t = +1$ if $\langle w_t, \phi(x_t) \rangle \geq 0$, and predict $\hat{y}_t = -1$ otherwise.
> 3. Receive true label $y_t$.
> 4. If $\hat{y}_t \neq y_t$ (mistake): set $w_{t+1} = w_t + y_t \cdot \phi(x_t)$.
> 5. Else: set $w_{t+1} = w_t$.

The update rule has an intuitive interpretation: on a mistake, the weight vector $w_t$ is nudged in the direction of the correctly-labeled data point $y_t \phi(x_t)$. This moves $w$ toward a separator that classifies $x_t$ correctly. Note that the Perceptron does not need to enumerate hypotheses—it simply updates a weight vector, taking $O(d)$ time per round.

### 5.5 Mistake bound analysis

> **Theorem 4** (Perceptron Mistake Bound, Novikoff 1962).
> If the data is linearly separable with margin $\gamma > 0$ and $\|\phi(x_t)\| \leq R$ for all $t$, then the Perceptron algorithm makes at most
>
> $$M \;\leq\; \frac{R^2}{\gamma^2}$$
>
> mistakes.

The proof proceeds via two lemmas that track the weight vector from complementary perspectives: how aligned it becomes with the true separator $w^*$, and how large its norm grows.

> **Lemma 1** (Alignment grows with each mistake).
> After $M_t$ mistakes, $\langle w^*,\, w_{t+1} \rangle \geq \gamma \cdot M_t$.

*Proof.* Since $w_1 = 0$ and the update $w_{t+1} = w_t + y_t \phi(x_t)$ happens only on mistakes, after all mistakes we have

$$w_{t+1} \;=\; \sum_{i \leq t:\; \text{mistake}} y_i\, \phi(x_i).$$

Taking the inner product with $w^*$:

$$\langle w^*, w_{t+1} \rangle \;=\; \sum_{i:\;\text{mistake}} y_i \langle w^*, \phi(x_i) \rangle.$$

By the margin assumption, each term satisfies $y_i \langle w^*, \phi(x_i) \rangle \geq \gamma$, so the sum is at least $\gamma \cdot M_t$. $\blacksquare$

> **Lemma 2** (Norm grows slowly).
> After $M_t$ mistakes, $\|w_{t+1}\|^2 \leq R^2 \cdot M_t$.

*Proof.* On a mistake in round $t$, we have $y_t \langle w_t, \phi(x_t) \rangle \leq 0$ (the prediction was wrong). Expanding the squared norm of the updated weight:

$$\|w_{t+1}\|^2 \;=\; \|w_t + y_t \phi(x_t)\|^2 \;=\; \|w_t\|^2 + 2\underbrace{y_t \langle w_t, \phi(x_t) \rangle}_{\leq\, 0} + \underbrace{\|\phi(x_t)\|^2}_{\leq\, R^2} \;\leq\; \|w_t\|^2 + R^2.$$

Telescoping from $\|w_1\|^2 = 0$: each mistake adds at most $R^2$ to the squared norm, giving $\|w_{t+1}\|^2 \leq R^2 \cdot M_t$. $\blacksquare$

With both lemmas in hand, the main theorem follows from a short calculation.

*Proof of Theorem 4.* Combining the two lemmas with the Cauchy–Schwarz inequality and $\|w^*\| = 1$:

$$\gamma\, M_t \;\leq\; \langle w^*, w_{t+1} \rangle \;\leq\; \|w^*\| \cdot \|w_{t+1}\| \;=\; \|w_{t+1}\| \;\leq\; R\sqrt{M_t}.$$

Dividing both sides by $\sqrt{M_t}$ (assuming $M_t > 0$):

$$\gamma \sqrt{M_t} \;\leq\; R \qquad\Longrightarrow\qquad M_t \;\leq\; \frac{R^2}{\gamma^2}. \qquad\blacksquare$$

> **Remark** (Why the bound is dimension-independent).
> The Perceptron mistake bound $R^2/\gamma^2$ depends on the geometry of the data (the radius $R$ and the margin $\gamma$) but **not on the dimension $d$**. A problem in $d = 1{,}000{,}000$ dimensions with a large margin is easier than a problem in $d = 2$ with a tiny margin. This is a recurring theme in learning theory: the "effective" complexity of a problem is determined by its geometric or combinatorial structure, not by the raw number of parameters.

> **Remark** (Connecting back to the counterexample).
> The threshold counterexample from Theorem 3 now makes sense through the lens of margin. The adversary constructs a sequence where the margin $\gamma$ tends to zero—points are pushed arbitrarily close to the decision boundary. The Perceptron bound $R^2/\gamma^2 \to \infty$ as $\gamma \to 0$, which is consistent with the adversary achieving unbounded mistakes.

---

## 6. Looking Ahead

Everything in this lecture assumed a worst-case adversary choosing both the data points and the labeling rule. The no-free-lunch theorem and the threshold counterexample both rely on an adversary that carefully crafts the input sequence to defeat the learner. But in many real-world settings, data arrives in no particular adversarial order—it is better modeled as random draws from a fixed distribution. This motivates the *statistical learning* model, where data is sampled i.i.d. and the learner's goal is to find a hypothesis with low population error. We begin this study next week.
