import Mathlib.Analysis.InnerProductSpace.Basic

open Real InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- `z` represents the sequence of examples where mistakes are made: `y_i * \phi(x_i)`
def perceptronWeights (z : ℕ → E) : ℕ → E
  | 0 => 0
  | (n + 1) => perceptronWeights z n + z n

@[simp]
lemma perceptronWeights_zero (z : ℕ → E) : perceptronWeights z 0 = 0 := rfl

@[simp]
lemma perceptronWeights_succ (z : ℕ → E) (n : ℕ) :
  perceptronWeights z (n + 1) = perceptronWeights z n + z n := rfl

/-- Lemma 1 (Alignment grows with each mistake). -/
lemma perceptron_lemma1 (z : ℕ → E) (w_star : E) (gamma : ℝ) (M : ℕ)
    (hgamma : ∀ i < M, gamma ≤ ⟪w_star, z i⟫_ℝ) :
    (M : ℝ) * gamma ≤ ⟪w_star, perceptronWeights z M⟫_ℝ := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [perceptronWeights_succ, inner_add_right]
    have h1 : (M : ℝ) * gamma ≤ ⟪w_star, perceptronWeights z M⟫_ℝ := ih (fun i hi => hgamma i (by omega))
    have h2 : gamma ≤ ⟪w_star, z M⟫_ℝ := hgamma M (by omega)
    push_cast
    linarith

/-- Lemma 2 (Norm grows slowly). -/
lemma perceptron_lemma2 (z : ℕ → E) (R : ℝ) (M : ℕ)
    (hmistake : ∀ i < M, ⟪perceptronWeights z i, z i⟫_ℝ ≤ 0)
    (hbound : ∀ i < M, ‖z i‖ ≤ R) :
    ‖perceptronWeights z M‖ ^ 2 ≤ (M : ℝ) * R ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [perceptronWeights_succ, norm_add_sq_real]
    have h1 : ‖perceptronWeights z M‖ ^ 2 ≤ (M : ℝ) * R ^ 2 := ih (fun i hi => hmistake i (by omega)) (fun i hi => hbound i (by omega))
    have h2 : ⟪perceptronWeights z M, z M⟫_ℝ ≤ 0 := hmistake M (by omega)
    have h3 : ‖z M‖ ≤ R := hbound M (by omega)
    have h4 : ‖z M‖ ^ 2 ≤ R ^ 2 := by
      have hR : 0 ≤ R := le_trans (norm_nonneg _) h3
      have hz : 0 ≤ ‖z M‖ := norm_nonneg _
      nlinarith
    push_cast
    linarith

/-- Theorem 4 (Perceptron Mistake Bound). -/
theorem perceptron_mistake_bound (z : ℕ → E) (w_star : E) (gamma R : ℝ) (M : ℕ)
    (hw_star_norm : ‖w_star‖ = 1)
    (hgamma_pos : 0 < gamma)
    (hmistake : ∀ i < M, ⟪perceptronWeights z i, z i⟫_ℝ ≤ 0)
    (hgamma : ∀ i < M, gamma ≤ ⟪w_star, z i⟫_ℝ)
    (hbound : ∀ i < M, ‖z i‖ ≤ R) :
    (M : ℝ) ≤ R ^ 2 / gamma ^ 2 := by
  have hl1 : (M : ℝ) * gamma ≤ ⟪w_star, perceptronWeights z M⟫_ℝ :=
    perceptron_lemma1 z w_star gamma M hgamma
  have hl2 : ‖perceptronWeights z M‖ ^ 2 ≤ (M : ℝ) * R ^ 2 :=
    perceptron_lemma2 z R M hmistake hbound
  have hcs : ⟪w_star, perceptronWeights z M⟫_ℝ ≤ ‖perceptronWeights z M‖ := by
    calc
      ⟪w_star, perceptronWeights z M⟫_ℝ ≤ ‖w_star‖ * ‖perceptronWeights z M‖ := real_inner_le_norm w_star (perceptronWeights z M)
      _ = ‖perceptronWeights z M‖ := by rw [hw_star_norm, one_mul]
  have hl3 : (M : ℝ) * gamma ≤ ‖perceptronWeights z M‖ := le_trans hl1 hcs
  have hl4 : 0 ≤ (M : ℝ) * gamma := mul_nonneg (Nat.cast_nonneg M) (le_of_lt hgamma_pos)
  have hl5 : ((M : ℝ) * gamma) ^ 2 ≤ ‖perceptronWeights z M‖ ^ 2 := by
    nlinarith [hl3, hl4]
  have hl6 : ((M : ℝ) * gamma) ^ 2 ≤ (M : ℝ) * R ^ 2 := le_trans hl5 hl2
  rcases eq_or_lt_of_le (Nat.cast_nonneg M) with hM0 | hMpos
  · rw [←hM0]
    positivity
  · have hMpos_real : 0 < (M : ℝ) := hMpos
    have hl8 : (M : ℝ) * gamma ^ 2 ≤ R ^ 2 := by
      have h_mul : (M : ℝ) * ((M : ℝ) * gamma ^ 2) ≤ (M : ℝ) * R ^ 2 := by
        calc
          (M : ℝ) * ((M : ℝ) * gamma ^ 2) = ((M : ℝ) * gamma) ^ 2 := by ring
          _ ≤ (M : ℝ) * R ^ 2 := hl6
      nlinarith
    have hgamma2_pos : 0 < gamma ^ 2 := by positivity
    exact (le_div_iff₀ hgamma2_pos).mpr hl8
