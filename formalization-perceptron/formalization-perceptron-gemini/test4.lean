import Mathlib.Analysis.InnerProductSpace.Basic

open Real

theorem test_div (M : ℕ) (gamma R : ℝ) (hgamma_pos : 0 < gamma) (hl8 : (M : ℝ) * gamma ^ 2 ≤ R ^ 2) :
    (M : ℝ) ≤ R ^ 2 / gamma ^ 2 := by
  have hgamma2_pos : 0 < gamma ^ 2 := sq_pos_of_pos hgamma_pos
  rw [le_div_iff₀ hgamma2_pos]
  exact hl8
