/-
Copyright (c) 2026 Johann Birnick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johann Birnick
-/
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The Perceptron Mistake Bound

This file formalizes the Perceptron mistake bound due to Novikoff (1962).

Only mistake rounds move the Perceptron's weight vector, so we track the
weight only along the (sub)sequence of mistake rounds and then bound the
number of such rounds.

## Main results

* `Perceptron.inner_wStar_w_ge` — **Lemma 1**: after `n` mistakes the
  alignment `⟪wStar, w n⟫` with the target separator is at least `γ * n`.
* `Perceptron.norm_w_sq_le` — **Lemma 2**: after `n` mistakes the squared
  norm `‖w n‖²` is at most `R² * n`.
* `Perceptron.mistake_bound` — **Theorem 4** (Novikoff 1962): the number of
  Perceptron mistakes is at most `R² / γ²`.
-/

open scoped InnerProductSpace

namespace Perceptron

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Perceptron weight vector after `n` mistake updates on examples `xs` with
labels `ys`, starting from `0`. The `i`-th mistake adds `ys i • xs i`. -/
def w (xs : ℕ → E) (ys : ℕ → ℝ) : ℕ → E
  | 0     => 0
  | n + 1 => w xs ys n + ys n • xs n

@[simp] lemma w_zero (xs : ℕ → E) (ys : ℕ → ℝ) : w xs ys 0 = 0 := rfl

@[simp] lemma w_succ (xs : ℕ → E) (ys : ℕ → ℝ) (n : ℕ) :
    w xs ys (n + 1) = w xs ys n + ys n • xs n := rfl

/-- **Lemma 1 (Alignment grows with each mistake).**
If every mistake example `(xs i, ys i)` lies on the correct side of the
unit-norm target `wStar` with margin at least `γ`, then after `n` mistakes
the inner product `⟪wStar, w n⟫` is at least `γ * n`. -/
lemma inner_wStar_w_ge {xs : ℕ → E} {ys : ℕ → ℝ} {wStar : E} {γ : ℝ}
    (hMargin : ∀ i, γ ≤ ys i * ⟪wStar, xs i⟫_ℝ) :
    ∀ n : ℕ, γ * n ≤ ⟪wStar, w xs ys n⟫_ℝ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : ⟪wStar, w xs ys (n + 1)⟫_ℝ
        = ⟪wStar, w xs ys n⟫_ℝ + ys n * ⟪wStar, xs n⟫_ℝ := by
      simp [w_succ, inner_add_right, real_inner_smul_right]
    have hmar := hMargin n
    rw [hstep]
    push_cast
    linarith

/-- **Lemma 2 (Norm grows slowly).**
If every mistake example has norm at most `R`, labels square to `1`, and the
update really is triggered by a mistake (so `ys i * ⟪w i, xs i⟫ ≤ 0`), then
after `n` mistakes the squared norm of the Perceptron weight is at most
`R² * n`. -/
lemma norm_w_sq_le {xs : ℕ → E} {ys : ℕ → ℝ} {R : ℝ}
    (hRadius : ∀ i, ‖xs i‖ ≤ R) (hSign : ∀ i, ys i ^ 2 = 1)
    (hMistake : ∀ i, ys i * ⟪w xs ys i, xs i⟫_ℝ ≤ 0) :
    ∀ n : ℕ, ‖w xs ys n‖ ^ 2 ≤ R ^ 2 * n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hxnn : (0 : ℝ) ≤ ‖xs n‖ := norm_nonneg _
    -- Expand the squared norm of the updated weight.
    have hexpand : ‖w xs ys (n + 1)‖ ^ 2
        = ‖w xs ys n‖ ^ 2 + 2 * ⟪w xs ys n, ys n • xs n⟫_ℝ
            + ‖ys n • xs n‖ ^ 2 := by
      rw [w_succ]; exact norm_add_sq_real _ _
    -- The cross term is nonpositive because the round is a mistake.
    have hcross : 2 * ⟪w xs ys n, ys n • xs n⟫_ℝ ≤ 0 := by
      rw [real_inner_smul_right]; linarith [hMistake n]
    -- The new-example term is bounded by `R²`.
    have hxsq : ‖xs n‖ ^ 2 ≤ R ^ 2 := by nlinarith [hRadius n, hxnn]
    have hsmul : ‖ys n • xs n‖ ^ 2 ≤ R ^ 2 := by
      rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hSign n, one_mul]
      exact hxsq
    -- Combine: `‖w (n+1)‖² ≤ ‖w n‖² + R² ≤ R² * n + R² = R² * (n+1)`.
    have hstep : ‖w xs ys (n + 1)‖ ^ 2 ≤ ‖w xs ys n‖ ^ 2 + R ^ 2 := by
      rw [hexpand]; linarith
    have hgoal : ‖w xs ys n‖ ^ 2 + R ^ 2 ≤ R ^ 2 * ((n : ℝ) + 1) := by
      nlinarith [ih]
    push_cast
    linarith

/-- **Theorem 4 (Perceptron Mistake Bound, Novikoff 1962).**
Assume the data is linearly separable by the unit-norm `wStar` with margin at
least `γ > 0` and that all examples have norm at most `R`. Then the number of
mistakes made by the Perceptron up to any point is at most `R² / γ²`. -/
theorem mistake_bound {xs : ℕ → E} {ys : ℕ → ℝ} {wStar : E} {γ R : ℝ}
    (hγpos : 0 < γ) (hwStar : ‖wStar‖ = 1)
    (hMargin : ∀ i, γ ≤ ys i * ⟪wStar, xs i⟫_ℝ)
    (hRadius : ∀ i, ‖xs i‖ ≤ R) (hSign : ∀ i, ys i ^ 2 = 1)
    (hMistake : ∀ i, ys i * ⟪w xs ys i, xs i⟫_ℝ ≤ 0) (n : ℕ) :
    (n : ℝ) ≤ R ^ 2 / γ ^ 2 := by
  have hγsq : (0 : ℝ) < γ ^ 2 := by positivity
  have hAlign := inner_wStar_w_ge hMargin n
  have hNorm := norm_w_sq_le hRadius hSign hMistake n
  -- Cauchy–Schwarz with `‖wStar‖ = 1` gives `⟪wStar, w n⟫ ≤ ‖w n‖`.
  have hCS : ⟪wStar, w xs ys n⟫_ℝ ≤ ‖w xs ys n‖ := by
    have h := real_inner_le_norm wStar (w xs ys n)
    rwa [hwStar, one_mul] at h
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hγnn : 0 ≤ γ * n := mul_nonneg hγpos.le hnn
  have hwnn : 0 ≤ ‖w xs ys n‖ := norm_nonneg _
  -- `(γ n)² ≤ ‖w n‖² ≤ R² n`.
  have hchain : γ * n ≤ ‖w xs ys n‖ := hAlign.trans hCS
  have hSquared : (γ * (n : ℝ)) ^ 2 ≤ R ^ 2 * n := by
    have hsq : (γ * (n : ℝ)) ^ 2 ≤ ‖w xs ys n‖ ^ 2 := by
      have := mul_self_le_mul_self hγnn hchain
      simpa [sq] using this
    linarith
  -- Conclude by cancelling an `n` (or handling `n = 0`).
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    simp only [Nat.cast_zero]
    positivity
  · have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hmul : (n : ℝ) * γ ^ 2 ≤ R ^ 2 := by
      have hh : ((n : ℝ) * γ ^ 2) * n ≤ R ^ 2 * n := by nlinarith [hSquared]
      exact le_of_mul_le_mul_right hh hnR
    exact (le_div_iff₀ hγsq).mpr hmul

end Perceptron
