# Summary of changes for run 4002c9ff-fae1-4cff-a677-dc13ce1d280f
I formalized the Perceptron Mistake Bound (Theorem 4 from the lecture notes) in Lean 4, along with both supporting lemmas, in `FormalizationPerceptronAristotle/Basic.lean`.

## What was formalized

**Definition — `perceptronWeight`**: The weight vector of the Perceptron algorithm after `k` mistake rounds, defined recursively as `w₀ = 0` and `w_{k+1} = w_k + y_k • x_k`. The sequences `x` and `y` are indexed over mistake rounds only (abstracting away non-mistake rounds where the weight doesn't change).

**Lemma 1 — `perceptron_alignment_lower_bound`**: After `M` mistakes, the alignment `⟪w*, w_M⟫ ≥ M * γ`. Proved by induction on `M`, using the margin assumption at each step.

**Lemma 2 — `perceptron_norm_upper_bound`**: After `M` mistakes, the squared norm `‖w_M‖² ≤ R² * M`. Proved by induction on `M`, expanding `‖w + y•x‖²` via `norm_add_sq_real`, using the mistake condition (cross term ≤ 0) and the label condition `y ∈ {-1, +1}` (so `‖y•x‖ = ‖x‖ ≤ R`).

**Theorem 4 — `perceptron_mistake_bound`**: If the data is linearly separable with margin `γ > 0` by a unit-norm separator `w*`, and `‖x_t‖ ≤ R` for all data points, then `M ≤ R²/γ²`. The proof combines both lemmas with the Cauchy–Schwarz inequality (`abs_real_inner_le_norm`).

## Design choices

- The formalization works over a general real inner product space `E` (not just `ℝ^d`), making it maximally general.
- The code follows Mathlib conventions: doc comments on all declarations, structured `induction ... with` syntax, lines under 100 characters, and no trailing semicolons.
- All proofs compile without `sorry` and use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).