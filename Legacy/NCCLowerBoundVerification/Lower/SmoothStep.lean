import NCCLowerBoundVerification.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The smooth-step family

This module formalizes Definition `def:Lambda-family` from
`Upper+Lower_unified_lower.tex`.  It proves the denominator certificate,
the endpoint and range identities, the symmetry of the master step, and the
threshold identities of the oppositely oriented detector.
-/

namespace NCCLowerBoundVerification

noncomputable section

/-- The one-sided flat exponential used in Definition `def:Lambda-family`. -/
def rho (t : ℝ) : ℝ :=
  if 0 < t then Real.exp (-1 / t) else 0

/-- The increasing master step `Λ₁` from Definition `def:Lambda-family`. -/
def Lambda1 (t : ℝ) : ℝ :=
  rho t / (rho t + rho (1 - t))

/-- The oppositely oriented detector `Λ₂`, with transition width `θ`. -/
def Lambda2 (theta t : ℝ) : ℝ :=
  1 - Lambda1 ((t - 1) / theta)

/-- The paper's one-sided flat exponential is exactly mathlib's canonical
`expNegInvGlue`.  This bridge lets all smoothness facts below be inherited
from the proved analytic construction rather than postulated. -/
theorem rho_eq_expNegInvGlue (t : ℝ) : rho t = expNegInvGlue t := by
  by_cases ht : 0 < t
  · simp [rho, expNegInvGlue, ht, not_le.mpr ht, div_eq_mul_inv]
  · have hnonpos : t ≤ 0 := le_of_not_gt ht
    simp [rho, expNegInvGlue, ht, hnonpos]

/-- `Λ₁` is definitionally the standard infinitely smooth transition after
identifying the paper's notation for the flat exponential. -/
theorem Lambda1_eq_smoothTransition : Lambda1 = Real.smoothTransition := by
  funext t
  simp only [Lambda1, Real.smoothTransition, rho_eq_expNegInvGlue]

/-- The master step is smooth to every finite or infinite order. -/
theorem Lambda1_contDiff {k : ℕ∞} : ContDiff ℝ k Lambda1 := by
  rw [Lambda1_eq_smoothTransition]
  exact Real.smoothTransition.contDiff

theorem Lambda1_continuous : Continuous Lambda1 :=
  (@Lambda1_contDiff 0).continuous

/-- The detector is also smooth to every order, for every fixed width. -/
theorem Lambda2_contDiff (theta : ℝ) {k : ℕ∞} :
    ContDiff ℝ k (Lambda2 theta) := by
  unfold Lambda2
  exact contDiff_const.sub
    (Lambda1_contDiff.comp ((contDiff_id.sub contDiff_const).div_const theta))

theorem Lambda2_continuous (theta : ℝ) : Continuous (Lambda2 theta) :=
  (@Lambda2_contDiff theta 0).continuous

/-- Monotonicity of the master step, inherited from its concrete formula. -/
theorem Lambda1_monotone : Monotone Lambda1 := by
  rw [Lambda1_eq_smoothTransition]
  exact Real.smoothTransition.monotone

/-- A positive transition width reverses the orientation, as required for
the low-memory detector in the hard instance. -/
theorem Lambda2_antitone {theta : ℝ} (htheta : 0 < theta) :
    Antitone (Lambda2 theta) := by
  intro a b hab
  have harg : (a - 1) / theta ≤ (b - 1) / theta := by
    exact div_le_div_of_nonneg_right (by linarith) htheta.le
  have hmono := Lambda1_monotone harg
  simp only [Lambda2]
  linarith

theorem rho_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : rho t = 0 := by
  simp [rho, not_lt.mpr ht]

theorem rho_pos_of_pos {t : ℝ} (ht : 0 < t) : 0 < rho t := by
  simp [rho, ht, Real.exp_pos]

theorem rho_nonneg (t : ℝ) : 0 ≤ rho t := by
  by_cases ht : 0 < t
  · exact (rho_pos_of_pos ht).le
  · simp [rho, ht]

theorem rho_pos_iff {t : ℝ} : 0 < rho t ↔ 0 < t := by
  constructor
  · intro h
    by_contra ht
    have : t ≤ 0 := le_of_not_gt ht
    rw [rho_eq_zero_of_nonpos this] at h
    exact (lt_irrefl 0) h
  · exact rho_pos_of_pos

theorem rho_zero : rho 0 = 0 := by
  exact rho_eq_zero_of_nonpos le_rfl

/-- The two terms in the denominator of `Λ₁` never vanish simultaneously. -/
theorem lambda1_denominator_pos (t : ℝ) :
    0 < rho t + rho (1 - t) := by
  by_cases ht : 0 < t
  · exact add_pos_of_pos_of_nonneg (rho_pos_of_pos ht) (rho_nonneg (1 - t))
  · have hcomp : 0 < 1 - t := by
      have ht' : t ≤ 0 := le_of_not_gt ht
      linarith
    exact add_pos_of_nonneg_of_pos (rho_nonneg t) (rho_pos_of_pos hcomp)

theorem lambda1_denominator_ne (t : ℝ) :
    rho t + rho (1 - t) ≠ 0 :=
  ne_of_gt (lambda1_denominator_pos t)

theorem Lambda1_nonneg (t : ℝ) : 0 ≤ Lambda1 t := by
  unfold Lambda1
  exact div_nonneg (rho_nonneg t) (lambda1_denominator_pos t).le

theorem Lambda1_le_one (t : ℝ) : Lambda1 t ≤ 1 := by
  unfold Lambda1
  apply (div_le_one (lambda1_denominator_pos t)).2
  exact le_add_of_nonneg_right (rho_nonneg (1 - t))

theorem Lambda1_mem_unitInterval (t : ℝ) : Lambda1 t ∈ Set.Icc (0 : ℝ) 1 := by
  exact ⟨Lambda1_nonneg t, Lambda1_le_one t⟩

theorem Lambda1_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : Lambda1 t = 0 := by
  unfold Lambda1
  rw [rho_eq_zero_of_nonpos ht]
  simp

theorem Lambda1_eq_one_of_one_le {t : ℝ} (ht : 1 ≤ t) : Lambda1 t = 1 := by
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hcomp : 1 - t ≤ 0 := sub_nonpos.mpr ht
  unfold Lambda1
  rw [rho_eq_zero_of_nonpos hcomp]
  simp [ne_of_gt (rho_pos_of_pos htpos)]

theorem Lambda1_zero : Lambda1 0 = 0 := by
  exact Lambda1_eq_zero_of_nonpos le_rfl

theorem Lambda1_one : Lambda1 1 = 1 := by
  exact Lambda1_eq_one_of_one_le le_rfl

/-- Equation `eq:Lambda-symmetry` in the paper. -/
theorem Lambda1_symmetry (t : ℝ) : Lambda1 t + Lambda1 (1 - t) = 1 := by
  unfold Lambda1
  rw [show 1 - (1 - t) = t by ring]
  have h₁ : rho t + rho (1 - t) ≠ 0 := lambda1_denominator_ne t
  have h₂ : rho (1 - t) + rho t ≠ 0 := by
    rw [add_comm]
    exact h₁
  field_simp [h₁, h₂]
  ring

theorem Lambda1_one_sub (t : ℝ) : Lambda1 (1 - t) = 1 - Lambda1 t := by
  linarith [Lambda1_symmetry t]

theorem Lambda2_mem_unitInterval (theta t : ℝ) :
    Lambda2 theta t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold Lambda2
  constructor
  · linarith [Lambda1_le_one ((t - 1) / theta)]
  · linarith [Lambda1_nonneg ((t - 1) / theta)]

/-- Below the lower threshold, the detector is identically one. -/
theorem Lambda2_eq_one_of_le_one {theta t : ℝ} (htheta : 0 < theta)
    (ht : t ≤ 1) : Lambda2 theta t = 1 := by
  have harg : (t - 1) / theta ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) htheta.le
  simp [Lambda2, Lambda1_eq_zero_of_nonpos harg]

/-- Above the upper threshold, the detector is identically zero. -/
theorem Lambda2_eq_zero_of_one_add_le {theta t : ℝ} (htheta : 0 < theta)
    (ht : 1 + theta ≤ t) : Lambda2 theta t = 0 := by
  have hnum : theta ≤ t - 1 := by linarith
  have harg : 1 ≤ (t - 1) / theta := by
    exact (le_div_iff₀ htheta).2 (by simpa using hnum)
  simp [Lambda2, Lambda1_eq_one_of_one_le harg]

theorem Lambda2_one (theta : ℝ) (htheta : 0 < theta) :
    Lambda2 theta 1 = 1 := by
  exact Lambda2_eq_one_of_le_one htheta le_rfl

theorem Lambda2_one_add (theta : ℝ) (htheta : 0 < theta) :
    Lambda2 theta (1 + theta) = 0 := by
  exact Lambda2_eq_zero_of_one_add_le htheta le_rfl

/-- Every positive-order derivative of the master step vanishes away from
the closed transition interval.  Endpoint flatness is already included in
`Lambda1_contDiff`; for the global boundedness proof it is enough to record
the strict exterior here. -/
theorem Lambda1_iteratedDeriv_eq_zero_of_not_mem_Icc
    {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : t ∉ Set.Icc (0 : ℝ) 1) :
    iteratedDeriv k Lambda1 t = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · have heq : Set.EqOn Lambda1 (fun _ : ℝ => 0) (Set.Iio 0) := by
      intro x hx
      exact Lambda1_eq_zero_of_nonpos hx.le
    have hder := (heq.iteratedDeriv_of_isOpen isOpen_Iio k) ht
    simpa using hder
  · have heq : Set.EqOn Lambda1 (fun _ : ℝ => 1) (Set.Ioi 1) := by
      intro x hx
      exact Lambda1_eq_one_of_one_le hx.le
    have hder := (heq.iteratedDeriv_of_isOpen isOpen_Ioi k) ht
    simpa [iteratedDeriv_const, hk.ne'] using hder

/-- The precise global bounded-derivative assertion in
`lem:Lambda-family-properties`: for each derivative order there is a finite
real bound valid on the whole line. -/
theorem Lambda1_iteratedDeriv_bounded (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |iteratedDeriv k Lambda1 t| ≤ C := by
  cases k with
  | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro t
      rw [iteratedDeriv_zero, abs_of_nonneg (Lambda1_nonneg t)]
      exact Lambda1_le_one t
  | succ k =>
      have hcont : Continuous (fun t : ℝ => |iteratedDeriv (k + 1) Lambda1 t|) := by
        exact ((@Lambda1_contDiff ((k + 1 : ℕ) : ℕ∞)).continuous_iteratedDeriv'
          (k + 1)).abs
      obtain ⟨C, hC⟩ := bddAbove_def.mp
        (isCompact_Icc.bddAbove_image hcont.continuousOn)
      refine ⟨max C 0, le_max_right _ _, ?_⟩
      intro t
      by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
      · exact (hC _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
      · rw [Lambda1_iteratedDeriv_eq_zero_of_not_mem_Icc (Nat.succ_pos k) ht, abs_zero]
        exact le_max_right _ _

/-- The detector derivative is zero throughout its constant low regime,
including the gluing endpoint `t = 1`. -/
theorem Lambda2_deriv_eq_zero_of_le_one {theta t : ℝ} (htheta : 0 < theta)
    (ht : t ≤ 1) : deriv (Lambda2 theta) t = 0 := by
  refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic 1 t ht)
  refine (hasDerivWithinAt_const t (Set.Iic 1) 1).congr_of_mem (fun x hx => ?_) ht
  exact Lambda2_eq_one_of_le_one htheta hx

theorem Lambda2_iteratedDeriv_eq_zero_of_not_mem_Icc
    {theta : ℝ} (htheta : 0 < theta) {k : ℕ} (hk : 0 < k) {t : ℝ}
    (ht : t ∉ Set.Icc (1 : ℝ) (1 + theta)) :
    iteratedDeriv k (Lambda2 theta) t = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · have heq : Set.EqOn (Lambda2 theta) (fun _ : ℝ => 1) (Set.Iio 1) := by
      intro x hx
      exact Lambda2_eq_one_of_le_one htheta hx.le
    have hder := (heq.iteratedDeriv_of_isOpen isOpen_Iio k) ht
    simpa [iteratedDeriv_const, hk.ne'] using hder
  · have heq : Set.EqOn (Lambda2 theta) (fun _ : ℝ => 0) (Set.Ioi (1 + theta)) := by
      intro x hx
      exact Lambda2_eq_zero_of_one_add_le htheta hx.le
    have hder := (heq.iteratedDeriv_of_isOpen isOpen_Ioi k) ht
    simpa using hder

/-- Once `theta` is fixed and positive, every derivative of the detector is
globally bounded.  In particular this supplies the first- and second-order
bounds used later in the hard-instance regularity estimates. -/
theorem Lambda2_iteratedDeriv_bounded {theta : ℝ} (htheta : 0 < theta) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |iteratedDeriv k (Lambda2 theta) t| ≤ C := by
  cases k with
  | zero =>
      refine ⟨1, zero_le_one, ?_⟩
      intro t
      rw [iteratedDeriv_zero, abs_of_nonneg (Lambda2_mem_unitInterval theta t).1]
      exact (Lambda2_mem_unitInterval theta t).2
  | succ k =>
      have hcont : Continuous (fun t : ℝ => |iteratedDeriv (k + 1) (Lambda2 theta) t|) := by
        exact ((@Lambda2_contDiff theta ((k + 1 : ℕ) : ℕ∞)).continuous_iteratedDeriv'
          (k + 1)).abs
      obtain ⟨C, hC⟩ := bddAbove_def.mp
        (isCompact_Icc.bddAbove_image hcont.continuousOn)
      refine ⟨max C 0, le_max_right _ _, ?_⟩
      intro t
      by_cases ht : t ∈ Set.Icc (1 : ℝ) (1 + theta)
      · exact (hC _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
      · rw [Lambda2_iteratedDeriv_eq_zero_of_not_mem_Icc htheta
            (Nat.succ_pos k) ht, abs_zero]
        exact le_max_right _ _

theorem Lambda2_first_two_derivatives_bounded {theta : ℝ} (htheta : 0 < theta) :
    ∃ C₁ C₂ : ℝ,
      0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ t : ℝ, |deriv (Lambda2 theta) t| ≤ C₁) ∧
      (∀ t : ℝ, |iteratedDeriv 2 (Lambda2 theta) t| ≤ C₂) := by
  obtain ⟨C₁, hC₁, h₁⟩ := Lambda2_iteratedDeriv_bounded htheta 1
  obtain ⟨C₂, hC₂, h₂⟩ := Lambda2_iteratedDeriv_bounded htheta 2
  refine ⟨C₁, C₂, hC₁, hC₂, ?_, h₂⟩
  intro t
  simpa using h₁ t

end

end NCCLowerBoundVerification
