/-
Copyright (c) 2026 Formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization
-/
import Mathlib

/-!
# The Perceptron Mistake Bound

This file formalizes the Perceptron algorithm's mistake bound (Novikoff 1962),
following the presentation in Week 1 lecture notes on online learning theory.

## Main results

* `perceptron_alignment_lower_bound` — **Lemma 1**: After `M` mistakes, the
  alignment `⟪w*, w_M⟫` grows at least as `γ * M`.
* `perceptron_norm_upper_bound` — **Lemma 2**: After `M` mistakes, the squared
  norm `‖w_M‖²` grows at most as `R² * M`.
* `perceptron_mistake_bound` — **Theorem 4**: The total number of mistakes
  satisfies `M ≤ R² / γ²`.

## Setup

We model the Perceptron algorithm by recording only the mistake rounds. The
sequences `x` and `y` are indexed by mistake round number: `x i` is the data
point and `y i ∈ {-1, +1}` is the label at the `i`-th mistake. The weight
vector `perceptronWeight x y k` is the cumulative sum `∑_{i<k} y i • x i`,
starting from `w₀ = 0`.
-/

noncomputable section

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Weight vector of the Perceptron algorithm after `k` mistake rounds.
The sequences `x` and `y` record the data point and label at each mistake
round. -/
def perceptronWeight (x : ℕ → E) (y : ℕ → ℝ) : ℕ → E
  | 0 => 0
  | k + 1 => perceptronWeight x y k + y k • x k

@[simp]
theorem perceptronWeight_zero (x : ℕ → E) (y : ℕ → ℝ) :
    perceptronWeight x y 0 = 0 :=
  rfl

@[simp]
theorem perceptronWeight_succ (x : ℕ → E) (y : ℕ → ℝ)
    (k : ℕ) :
    perceptronWeight x y (k + 1) =
      perceptronWeight x y k + y k • x k :=
  rfl

/-- **Lemma 1** (Alignment grows with each mistake).
After `M` mistake rounds, the inner product `⟪w*, w_M⟫_ℝ` is at least
`M * γ`. This follows because each mistake contributes at least `γ` to
the alignment, by the margin assumption. -/
theorem perceptron_alignment_lower_bound
    {wStar : E} {γ : ℝ} {x : ℕ → E} {y : ℕ → ℝ} {M : ℕ}
    (hMargin : ∀ i, i < M → γ ≤ y i * ⟪wStar, x i⟫_ℝ) :
    ↑M * γ ≤ ⟪wStar, perceptronWeight x y M⟫_ℝ := by
  induction M with
  | zero => simp
  | succ n ih =>
    simp only [perceptronWeight_succ, inner_add_right,
      inner_smul_right, Nat.cast_succ, add_mul]
    have := hMargin n (Nat.lt_succ_self n)
    linarith [ih fun i hi => hMargin i (by omega)]

/-- **Lemma 2** (Norm grows slowly).
After `M` mistake rounds, the squared norm `‖w_M‖²` is at most
`R² * M`. Each mistake adds at most `R²` to the squared norm, because
the cross term `2 * y * ⟪w, x⟫` is nonpositive on mistake rounds and
`|y|² * ‖x‖² ≤ R²`. -/
theorem perceptron_norm_upper_bound
    {R : ℝ} {x : ℕ → E} {y : ℕ → ℝ} {M : ℕ}
    (hBound : ∀ i, i < M → ‖x i‖ ≤ R)
    (hLabel : ∀ i, i < M → y i = 1 ∨ y i = -1)
    (hMistake : ∀ i, i < M →
      y i * ⟪perceptronWeight x y i, x i⟫_ℝ ≤ 0) :
    ‖perceptronWeight x y M‖ ^ 2 ≤ R ^ 2 * ↑M := by
  induction M with
  | zero => simp
  | succ n ih =>
    rw [perceptronWeight_succ, norm_add_sq_real]
    have hIH := ih (fun i hi => hBound i (by omega))
      (fun i hi => hLabel i (by omega))
      (fun i hi => hMistake i (by omega))
    have hMis := hMistake n (Nat.lt_succ_self n)
    have hBnd := hBound n (Nat.lt_succ_self n)
    -- Since y n = ±1, we have ‖y n • x n‖ = ‖x n‖
    have hSmul : ‖y n • x n‖ = ‖x n‖ := by
      rw [norm_smul]
      obtain h | h := hLabel n (Nat.lt_succ_self n) <;>
        simp [h]
    rw [inner_smul_right, hSmul]
    push_cast [Nat.succ_eq_add_one]
    nlinarith [norm_nonneg (x n)]

/-- **Theorem 4** (Perceptron Mistake Bound, Novikoff 1962).
If the data is linearly separable with margin `γ > 0` by a unit-norm
separator `w*`, and all data points satisfy `‖x_t‖ ≤ R`, then the
Perceptron makes at most `R² / γ²` mistakes. The proof combines
Lemma 1, Lemma 2, and the Cauchy–Schwarz inequality. -/
theorem perceptron_mistake_bound
    {wStar : E} {γ R : ℝ} {x : ℕ → E} {y : ℕ → ℝ} {M : ℕ}
    (hγ : 0 < γ)
    (hwStar : ‖wStar‖ = 1)
    (hMargin : ∀ i, i < M →
      γ ≤ y i * ⟪wStar, x i⟫_ℝ)
    (hBound : ∀ i, i < M → ‖x i‖ ≤ R)
    (hLabel : ∀ i, i < M → y i = 1 ∨ y i = -1)
    (hMistake : ∀ i, i < M →
      y i * ⟪perceptronWeight x y i, x i⟫_ℝ ≤ 0) :
    (M : ℝ) ≤ R ^ 2 / γ ^ 2 := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < γ ^ 2)]
  by_cases hM : M = 0
  · subst hM; simp [sq_nonneg]
  · -- Lemma 1: alignment lower bound
    have h1 := perceptron_alignment_lower_bound hMargin
    -- Cauchy–Schwarz: ⟪w*, w_M⟫ ≤ ‖w*‖ * ‖w_M‖ = ‖w_M‖
    have hCS : ⟪wStar, perceptronWeight x y M⟫_ℝ ≤
        ‖perceptronWeight x y M‖ := by
      have := abs_real_inner_le_norm wStar
        (perceptronWeight x y M)
      rw [hwStar, one_mul] at this
      linarith [le_abs_self
        ⟪wStar, perceptronWeight x y M⟫_ℝ]
    -- Combined: M * γ ≤ ‖w_M‖
    have hAlign : ↑M * γ ≤
        ‖perceptronWeight x y M‖ :=
      le_trans h1 hCS
    -- Lemma 2: norm upper bound
    have hNorm :=
      perceptron_norm_upper_bound hBound hLabel hMistake
    -- (M * γ)² ≤ ‖w_M‖² ≤ R² * M, so M * γ² ≤ R²
    nlinarith [mul_self_le_mul_self
      (by positivity) hAlign]

end
