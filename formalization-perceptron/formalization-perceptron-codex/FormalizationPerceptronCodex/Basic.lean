import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

open scoped RealInnerProductSpace

namespace FormalizationPerceptronCodex

/-- Signed labels for the Perceptron algorithm. -/
inductive Label where
  | pos
  | neg
deriving DecidableEq, Repr

namespace Label

/-- The scalar associated to a signed label. -/
def toReal : Label → ℝ
  | pos => 1
  | neg => -1

@[simp] lemma toReal_pos : Label.toReal .pos = 1 := rfl

@[simp] lemma toReal_neg : Label.toReal .neg = -1 := rfl

@[simp] lemma sq_toReal (y : Label) : y.toReal ^ 2 = 1 := by
  cases y <;> norm_num [toReal]

@[simp] lemma norm_smul_toReal {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (y : Label) (v : V) :
    ‖y.toReal • v‖ = ‖v‖ := by
  cases y <;> simp

@[simp] lemma norm_smul_toReal_sq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (y : Label) (v : V) :
    ‖y.toReal • v‖ ^ 2 = ‖v‖ ^ 2 := by
  rw [norm_smul_toReal]

end Label

/-- A single labeled example. -/
structure Example (α : Type*) where
  input : α
  label : Label
deriving Repr

/-- The current weight vector together with the cumulative mistake count. -/
structure State (V : Type*) where
  weight : V
  mistakes : ℕ

namespace State

variable {V : Type*} [Zero V]

/-- The initial state of the Perceptron algorithm. -/
def init : State V :=
  { weight := 0
    mistakes := 0 }

@[simp] lemma init_weight : (init : State V).weight = 0 := rfl

@[simp] lemma init_mistakes : (init : State V).mistakes = 0 := rfl

end State

namespace Perceptron

variable {α V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Perceptron's prediction on a single instance. -/
noncomputable def predict (ϕ : α → V) (w : V) (x : α) : Label :=
  if 0 ≤ ⟪w, ϕ x⟫ then .pos else .neg

/-- An example is misclassified when the current prediction disagrees with its label. -/
def misclassified (ϕ : α → V) (w : V) (e : Example α) : Prop :=
  predict ϕ w e.input ≠ e.label

/-- One Perceptron step: update on a mistake, otherwise keep the current state. -/
noncomputable def step (ϕ : α → V) (s : State V) (e : Example α) : State V :=
  by
    classical
    exact
      if h : misclassified ϕ s.weight e then
        { weight := s.weight + e.label.toReal • ϕ e.input
          mistakes := s.mistakes + 1 }
      else
        s

/-- Run the Perceptron from an arbitrary initial state on a finite data sequence. -/
noncomputable def runFrom (ϕ : α → V) (s : State V) : List (Example α) → State V
  | [] => s
  | e :: data => runFrom ϕ (step ϕ s e) data

/-- Run the Perceptron from the zero initial state. -/
noncomputable def run (ϕ : α → V) (data : List (Example α)) : State V :=
  runFrom ϕ State.init data

lemma label_mul_inner_le_zero_of_misclassified {ϕ : α → V} {w : V} {e : Example α}
    (h : misclassified ϕ w e) :
    e.label.toReal * ⟪w, ϕ e.input⟫ ≤ 0 := by
  rcases e with ⟨x, y⟩
  cases y <;> simp [misclassified, predict] at h ⊢ <;> linarith

theorem alignment_grows_from_state {ϕ : α → V} {γ : ℝ} {wStar : V} {s : State V}
    {data : List (Example α)}
    (hs : γ * (s.mistakes : ℝ) ≤ ⟪wStar, s.weight⟫)
    (hsep : ∀ e ∈ data, γ ≤ e.label.toReal * ⟪wStar, ϕ e.input⟫) :
    γ * ((runFrom ϕ s data).mistakes : ℝ) ≤ ⟪wStar, (runFrom ϕ s data).weight⟫ := by
  induction data generalizing s with
  | nil =>
      simpa [runFrom] using hs
  | cons e data ih =>
      have hs' : γ * ((step ϕ s e).mistakes : ℝ) ≤ ⟪wStar, (step ϕ s e).weight⟫ := by
        by_cases hmis : misclassified ϕ s.weight e
        · have hmargin : γ ≤ e.label.toReal * ⟪wStar, ϕ e.input⟫ := hsep e (by simp)
          have hmistakes : ((step ϕ s e).mistakes : ℝ) = (s.mistakes : ℝ) + 1 := by
            simp [step, hmis]
          calc
            γ * ((step ϕ s e).mistakes : ℝ)
                = γ * ((s.mistakes : ℝ) + 1) := by
                    rw [hmistakes]
            _ = γ * (s.mistakes : ℝ) + γ := by
                  ring
            _ ≤ ⟪wStar, s.weight⟫ + e.label.toReal * ⟪wStar, ϕ e.input⟫ := by
              linarith
            _ = ⟪wStar, (step ϕ s e).weight⟫ := by
              simp [step, hmis, inner_add_right, real_inner_smul_right]
        · simpa [step, hmis] using hs
      have htail : ∀ e' ∈ data, γ ≤ e'.label.toReal * ⟪wStar, ϕ e'.input⟫ := by
        intro e' he'
        exact hsep e' (by simp [he'])
      simpa [runFrom] using ih hs' htail

/-- Lemma 1 from the notes: the alignment with a separating direction grows by at least
`γ` on every Perceptron mistake. -/
theorem lemma1_alignment_grows_with_each_mistake {ϕ : α → V} {γ : ℝ} {wStar : V}
    {data : List (Example α)}
    (hsep : ∀ e ∈ data, γ ≤ e.label.toReal * ⟪wStar, ϕ e.input⟫) :
    γ * ((run ϕ data).mistakes : ℝ) ≤ ⟪wStar, (run ϕ data).weight⟫ := by
  simpa [run, State.init] using
    alignment_grows_from_state (ϕ := ϕ) (γ := γ) (wStar := wStar) (s := State.init)
      (data := data) (hs := by simp) hsep

theorem norm_sq_grows_from_state {ϕ : α → V} {R : ℝ} (hR_nonneg : 0 ≤ R) {s : State V}
    {data : List (Example α)}
    (hs : ‖s.weight‖ ^ 2 ≤ R ^ 2 * (s.mistakes : ℝ))
    (hR : ∀ e ∈ data, ‖ϕ e.input‖ ≤ R) :
    ‖(runFrom ϕ s data).weight‖ ^ 2 ≤ R ^ 2 * ((runFrom ϕ s data).mistakes : ℝ) := by
  induction data generalizing s with
  | nil =>
      simpa [runFrom] using hs
  | cons e data ih =>
      have hs' : ‖(step ϕ s e).weight‖ ^ 2 ≤ R ^ 2 * ((step ϕ s e).mistakes : ℝ) := by
        by_cases hmis : misclassified ϕ s.weight e
        · have hinner : e.label.toReal * ⟪s.weight, ϕ e.input⟫ ≤ 0 :=
            label_mul_inner_le_zero_of_misclassified hmis
          have hmistakes : ((step ϕ s e).mistakes : ℝ) = (s.mistakes : ℝ) + 1 := by
            simp [step, hmis]
          have hnorm : ‖ϕ e.input‖ ^ 2 ≤ R ^ 2 := by
            have : ‖ϕ e.input‖ ≤ R := hR e (by simp)
            nlinarith [norm_nonneg (ϕ e.input), hR_nonneg]
          calc
            ‖(step ϕ s e).weight‖ ^ 2 = ‖s.weight + e.label.toReal • ϕ e.input‖ ^ 2 := by
              simp [step, hmis]
            _ = ‖s.weight‖ ^ 2 + 2 * ⟪s.weight, e.label.toReal • ϕ e.input⟫ +
                  ‖e.label.toReal • ϕ e.input‖ ^ 2 := by
                simpa using norm_add_sq_real s.weight (e.label.toReal • ϕ e.input)
            _ = ‖s.weight‖ ^ 2 + 2 * (e.label.toReal * ⟪s.weight, ϕ e.input⟫) +
                  ‖ϕ e.input‖ ^ 2 := by
                simp [real_inner_smul_right]
            _ ≤ ‖s.weight‖ ^ 2 + R ^ 2 := by
                nlinarith
            _ ≤ R ^ 2 * (s.mistakes : ℝ) + R ^ 2 := by
                nlinarith
            _ = R ^ 2 * ((step ϕ s e).mistakes : ℝ) := by
                rw [hmistakes]
                ring
        · simpa [step, hmis] using hs
      have htail : ∀ e' ∈ data, ‖ϕ e'.input‖ ≤ R := by
        intro e' he'
        exact hR e' (by simp [he'])
      simpa [runFrom] using ih hs' htail

/-- Lemma 2 from the notes: the squared norm of the Perceptron weight grows by at most
`R²` on every mistake. -/
theorem lemma2_norm_grows_slowly {ϕ : α → V} {R : ℝ} (hR_nonneg : 0 ≤ R)
    {data : List (Example α)}
    (hR : ∀ e ∈ data, ‖ϕ e.input‖ ≤ R) :
    ‖(run ϕ data).weight‖ ^ 2 ≤ R ^ 2 * ((run ϕ data).mistakes : ℝ) := by
  simpa [run, State.init] using
    norm_sq_grows_from_state (ϕ := ϕ) (R := R) hR_nonneg (s := State.init) (data := data)
      (hs := by simp) hR

/-- Theorem 4 from the notes: Novikoff's mistake bound for the Perceptron algorithm. -/
theorem perceptron_mistake_bound {ϕ : α → V} {data : List (Example α)} {γ R : ℝ} {wStar : V}
    (hγ : 0 < γ) (hR_nonneg : 0 ≤ R) (hwStar : ‖wStar‖ = 1)
    (hsep : ∀ e ∈ data, γ ≤ e.label.toReal * ⟪wStar, ϕ e.input⟫)
    (hR : ∀ e ∈ data, ‖ϕ e.input‖ ≤ R) :
    ((run ϕ data).mistakes : ℝ) ≤ R ^ 2 / γ ^ 2 := by
  let final := run ϕ data
  let m : ℕ := final.mistakes
  let w : V := final.weight
  have halign : γ * (m : ℝ) ≤ ⟪wStar, w⟫ := by
    simpa [final, m, w] using
      lemma1_alignment_grows_with_each_mistake (ϕ := ϕ) (γ := γ) (wStar := wStar)
        (data := data) hsep
  have hnorm : ‖w‖ ^ 2 ≤ R ^ 2 * (m : ℝ) := by
    simpa [final, m, w] using
      lemma2_norm_grows_slowly (ϕ := ϕ) (R := R) hR_nonneg (data := data) hR
  have halign' : γ * (m : ℝ) ≤ ‖w‖ := by
    calc
      γ * (m : ℝ) ≤ ⟪wStar, w⟫ := halign
      _ ≤ ‖wStar‖ * ‖w‖ := real_inner_le_norm _ _
      _ = ‖w‖ := by simp [hwStar]
  by_cases hm : m = 0
  · have hbound : 0 ≤ R ^ 2 / γ ^ 2 := by positivity
    have hm_zero : ((run ϕ data).mistakes : ℝ) = 0 := by
      simp [final, m, hm]
    exact hm_zero.le.trans hbound
  · have hm_pos : 0 < (m : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hm
    have hγ_sq_pos : 0 < γ ^ 2 := by positivity
    have hγm_nonneg : 0 ≤ γ * (m : ℝ) := by positivity
    have hsq_lower : γ ^ 2 * (m : ℝ) ^ 2 ≤ ‖w‖ ^ 2 := by
      have hsq : (γ * (m : ℝ)) ^ 2 ≤ ‖w‖ ^ 2 := by
        exact (sq_le_sq₀ hγm_nonneg (norm_nonneg _)).2 halign'
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
    have hγm_le_R : γ ^ 2 * (m : ℝ) ≤ R ^ 2 := by
      have : γ ^ 2 * (m : ℝ) ^ 2 ≤ R ^ 2 * (m : ℝ) := le_trans hsq_lower hnorm
      nlinarith
    exact (_root_.le_div_iff₀ hγ_sq_pos).2 <| by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hγm_le_R

end Perceptron
end FormalizationPerceptronCodex
