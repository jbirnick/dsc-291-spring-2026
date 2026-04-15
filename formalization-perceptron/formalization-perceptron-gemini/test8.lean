import Mathlib.Analysis.InnerProductSpace.Basic

open Real

theorem test_div (M : ℕ) (gamma R : ℝ) (hgamma_pos : 0 < gamma) (hl8 : (M : ℝ) * gamma ^ 2 ≤ R ^ 2) :
    (M : ℝ) ≤ R ^ 2 / gamma ^ 2 := by
  have hM_nonneg : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  rcases eq_or_lt_of_le hM_nonneg with hM0 | hMpos
  · rw [←hM0]
    have h_zero : (0 : ℝ) ≤ R ^ 2 / gamma ^ 2 := by positivity
    exact h_zero
  · have hgamma2_pos : 0 < gamma ^ 2 := sq_pos_of_pos hgamma_pos
    have H : ((M : ℝ) ≤ R ^ 2 / gamma ^ 2) ↔ ((M : ℝ) * gamma ^ 2 ≤ R ^ 2) := le_div_iff₀ hgamma2_pos
    exact H.mpr hl8
