import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

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

/-- Theorem 4 (Perceptron Mistake Bound). -/
theorem perceptron_mistake_bound {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z : ℕ → E) (w_star : E) (gamma R : ℝ) (M : ℕ)
    (hw_star_norm : ‖w_star‖ = 1)
    (hgamma_pos : 0 < gamma)
    (hmistake : ∀ i < M, ⟪perceptronWeights z i, z i⟫_ℝ ≤ 0)
    (hgamma : ∀ i < M, gamma ≤ ⟪w_star, z i⟫_ℝ)
    (hbound : ∀ i < M, ‖z i‖ ≤ R) :
    (M : ℝ) ≤ R ^ 2 / gamma ^ 2 := by
  have hl8 : (M : ℝ) * gamma ^ 2 ≤ R ^ 2 := sorry
  have hgamma2_pos : 0 < gamma ^ 2 := sq_pos_of_pos hgamma_pos
  have H : ((M : ℝ) ≤ R ^ 2 / gamma ^ 2) ↔ ((M : ℝ) * gamma ^ 2 ≤ R ^ 2) := le_div_iff₀ hgamma2_pos
  exact H.mpr hl8
