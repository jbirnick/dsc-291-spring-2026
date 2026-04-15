import Mathlib.Analysis.InnerProductSpace.Basic

open Real

example (M gamma R : ℝ) (hgamma_pos : 0 < gamma) (hl8 : M * gamma ^ 2 ≤ R ^ 2) : M ≤ R ^ 2 / gamma ^ 2 := by
  have hgamma2_pos : 0 < gamma ^ 2 := sq_pos_of_pos hgamma_pos
  exact (le_div_iff₀ hgamma2_pos).mpr hl8
