import Mathlib.Analysis.InnerProductSpace.Basic

open Real

theorem test_div (M : ℕ) (gamma R : ℝ) (hgamma_pos : 0 < gamma) (hl8 : (M : ℝ) * gamma ^ 2 ≤ R ^ 2) :
    (M : ℝ) ≤ R ^ 2 / gamma ^ 2 := by
  have hgamma2_pos : 0 < gamma ^ 2 := sq_pos_of_pos hgamma_pos
  have hl9 : (M : ℝ) * gamma ^ 2 * (gamma ^ 2)⁻¹ ≤ R ^ 2 * (gamma ^ 2)⁻¹ :=
    mul_le_mul_of_nonneg_right hl8 (inv_nonneg.mpr (le_of_lt hgamma2_pos))
  have hgamma2_ne_zero : gamma ^ 2 ≠ 0 := ne_of_gt hgamma2_pos
  rw [mul_inv_cancel_right₀ _ hgamma2_ne_zero] at hl9
  exact hl9
