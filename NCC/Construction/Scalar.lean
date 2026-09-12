import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Exact scalar functions in the current NC-C manuscript

The primitive `p` is the integral of mathlib's proved smooth transition.
The lemmas below identify it with all three branches of `eq:base-ramp`.
`q`, `e_s`, `e_nu`, and `R` then use precisely the current displayed formulas.
The parameter of `R` stands for the manuscript's numerical constant `c_R`.
In particular, this file does not identify `R` with the older phase potential.
-/

namespace NCC.Construction

noncomputable section

open Set MeasureTheory
open scoped Interval

/-- The smooth step occurring as the derivative of the current ramp. -/
abbrev step : ℝ → ℝ := Real.smoothTransition

theorem step_contDiff {k : ℕ∞} : ContDiff ℝ k step :=
  Real.smoothTransition.contDiff

theorem step_continuous : Continuous step := Real.smoothTransition.continuous

theorem step_nonneg (t : ℝ) : 0 ≤ step t := Real.smoothTransition.nonneg t

theorem step_le_one (t : ℝ) : step t ≤ 1 := Real.smoothTransition.le_one t

theorem step_monotone : Monotone step := Real.smoothTransition.monotone

theorem step_eq_zero {t : ℝ} (ht : t ≤ 0) : step t = 0 :=
  Real.smoothTransition.zero_of_nonpos ht

theorem step_eq_one {t : ℝ} (ht : 1 ≤ t) : step t = 1 :=
  Real.smoothTransition.one_of_one_le ht

theorem step_symmetry (t : ℝ) : step t + step (1 - t) = 1 := by
  unfold step Real.smoothTransition
  rw [show 1 - (1 - t) = t by ring]
  have h : expNegInvGlue t + expNegInvGlue (1 - t) ≠ 0 :=
    (Real.smoothTransition.pos_denom t).ne'
  rw [add_comm (expNegInvGlue (1 - t)) (expNegInvGlue t)]
  rw [← add_div, div_self h]

theorem step_eq_exp_ratio {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    step t = Real.exp (-1 / t) /
      (Real.exp (-1 / t) + Real.exp (-1 / (1 - t))) := by
  simp [step, Real.smoothTransition, expNegInvGlue, not_le.mpr h0,
    not_le.mpr (sub_pos.mpr h1), div_eq_mul_inv]

/-- The integral definition agrees with every branch of `eq:base-ramp`. -/
def p (t : ℝ) : ℝ := ∫ u in 0..t, step u

theorem hasDerivAt_p (t : ℝ) : HasDerivAt p (step t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    (step_continuous.intervalIntegrable 0 t)
    step_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
    step_continuous.continuousAt

theorem deriv_p (t : ℝ) : deriv p t = step t := (hasDerivAt_p t).deriv

theorem p_contDiff : ContDiff ℝ (⊤ : ℕ∞) p := by
  apply contDiff_infty_iff_deriv.2
  refine ⟨fun t ↦ (hasDerivAt_p t).differentiableAt, ?_⟩
  have h : deriv p = step := funext deriv_p
  rw [h]
  exact step_contDiff

theorem p_eq_zero {t : ℝ} (ht : t ≤ 0) : p t = 0 := by
  unfold p
  calc
    (∫ u in 0..t, step u) = ∫ _ in 0..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_ge ht] at hu
      exact step_eq_zero hu.2
    _ = 0 := by simp

theorem p_zero : p 0 = 0 := p_eq_zero le_rfl

theorem step_integral_unit : (∫ u in (0 : ℝ)..1, step u) = 1 / 2 := by
  have hreflect : (∫ u in (0 : ℝ)..1, step (1 - u)) =
      ∫ u in (0 : ℝ)..1, step u := by
    simpa only [sub_self, sub_zero] using
      (intervalIntegral.integral_comp_sub_left step (a := 0) (b := 1) 1)
  have hsum : (∫ u in (0 : ℝ)..1, step u) +
      (∫ u in (0 : ℝ)..1, step (1 - u)) = 1 := by
    have hreflect_cont : Continuous (fun u : ℝ ↦ step (1 - u)) :=
      step_continuous.comp (continuous_const.sub continuous_id)
    rw [← intervalIntegral.integral_add
      (step_continuous.intervalIntegrable 0 1)
      (hreflect_cont.intervalIntegrable 0 1)]
    simp only [step_symmetry]
    norm_num
  rw [hreflect] at hsum
  linarith

theorem p_eq_affine {t : ℝ} (ht : 1 ≤ t) : p t = t - 1 / 2 := by
  have htail : (∫ u in (1 : ℝ)..t, step u) = t - 1 := by
    calc
      (∫ u in (1 : ℝ)..t, step u) = ∫ _ in (1 : ℝ)..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le ht] at hu
        exact step_eq_one hu.1
      _ = t - 1 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (step_continuous.intervalIntegrable (μ := volume) 0 1)
    (step_continuous.intervalIntegrable (μ := volume) 1 t)
  change _ = p t at hadd
  rw [step_integral_unit, htail] at hadd
  linarith

/-- Exact correspondence to the integral middle branch, including the raw
exponential expression used by the manuscript. -/
theorem p_eq_integral_exp {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    p t = ∫ u in 0..t, Real.exp (-1 / u) /
      (Real.exp (-1 / u) + Real.exp (-1 / (1 - u))) := by
  apply intervalIntegral.integral_congr_Ioo_of_le h0.le
  intro u hu
  exact step_eq_exp_ratio hu.1 (hu.2.trans h1)

theorem p_piecewise (t : ℝ) :
    p t = if t ≤ 0 then 0 else if t < 1 then
      (∫ u in 0..t, Real.exp (-1 / u) /
        (Real.exp (-1 / u) + Real.exp (-1 / (1 - u)))) else t - 1 / 2 := by
  split_ifs with h0 h1
  · exact p_eq_zero h0
  · exact p_eq_integral_exp (lt_of_not_ge h0) h1
  · exact p_eq_affine (le_of_not_gt h1)

theorem deriv_p_mem (t : ℝ) : deriv p t ∈ Icc (0 : ℝ) 1 := by
  rw [deriv_p]
  exact ⟨step_nonneg t, step_le_one t⟩

theorem p_monotone : Monotone p :=
  monotone_of_deriv_nonneg (fun t ↦ (hasDerivAt_p t).differentiableAt)
    (fun t ↦ (deriv_p_mem t).1)

theorem p_nonneg (t : ℝ) : 0 ≤ p t := by
  by_cases ht : t ≤ 0
  · rw [p_eq_zero ht]
  · simpa only [p_zero] using p_monotone (le_of_not_ge ht)

theorem deriv_deriv_p_nonneg (t : ℝ) : 0 ≤ deriv (deriv p) t := by
  have h : deriv p = step := funext deriv_p
  rw [h]
  exact step_monotone.deriv_nonneg

/-- The current activation function `q`. -/
def q (t : ℝ) : ℝ := deriv p ((5 * t - 1) / 4)

theorem q_eq_step (t : ℝ) : q t = step ((5 * t - 1) / 4) :=
  deriv_p _

theorem q_contDiff {k : ℕ∞} : ContDiff ℝ k q := by
  have h : q = fun t ↦ step ((5 * t - 1) / 4) := funext q_eq_step
  rw [h]
  exact step_contDiff.comp
    (((contDiff_const.mul contDiff_id).sub contDiff_const).div_const 4)

theorem q_mem (t : ℝ) : q t ∈ Icc (0 : ℝ) 1 := by
  rw [q_eq_step]
  exact ⟨step_nonneg _, step_le_one _⟩

theorem q_eq_zero {t : ℝ} (ht : t ≤ 1 / 5) : q t = 0 := by
  rw [q_eq_step]
  apply step_eq_zero
  linarith

theorem q_eq_one {t : ℝ} (ht : 1 ≤ t) : q t = 1 := by
  rw [q_eq_step]
  apply step_eq_one
  linarith

theorem q_monotone : Monotone q := by
  intro a b hab
  rw [q_eq_step, q_eq_step]
  apply step_monotone
  linarith

theorem deriv_q_nonneg (t : ℝ) : 0 ≤ deriv q t := q_monotone.deriv_nonneg

/-- A common expression for the two exact bounded identity extensions. -/
def identityExtension (radius t : ℝ) : ℝ :=
  p (t + (radius + 1)) - p (t - radius) - (radius + 1 / 2)

def e_s (t : ℝ) : ℝ := p (t + 3) - p (t - 2) - 5 / 2

def e_nu (t : ℝ) : ℝ := p (t + 22) - p (t - 21) - 43 / 2

theorem e_s_eq_identityExtension : e_s = identityExtension 2 := by
  funext t
  norm_num [e_s, identityExtension]

theorem e_nu_eq_identityExtension : e_nu = identityExtension 21 := by
  funext t
  norm_num [e_nu, identityExtension]

theorem identityExtension_eq_self {radius t : ℝ}
    (hlo : -radius ≤ t) (hhi : t ≤ radius) : identityExtension radius t = t := by
  rw [identityExtension, p_eq_affine (by linarith), p_eq_zero (by linarith)]
  ring

theorem identityExtension_eq_left {radius t : ℝ} (hr : 0 ≤ radius)
    (ht : t ≤ -(radius + 1)) : identityExtension radius t = -(radius + 1 / 2) := by
  rw [identityExtension, p_eq_zero (by linarith), p_eq_zero (by linarith)]
  ring

theorem identityExtension_eq_right {radius t : ℝ} (hr : 0 ≤ radius)
    (ht : radius + 1 ≤ t) : identityExtension radius t = radius + 1 / 2 := by
  rw [identityExtension, p_eq_affine (by linarith), p_eq_affine (by linarith)]
  ring

theorem e_s_eq_self {t : ℝ} (ht : |t| ≤ 2) : e_s t = t := by
  rw [e_s_eq_identityExtension]
  exact identityExtension_eq_self (abs_le.mp ht).1 (abs_le.mp ht).2

theorem e_nu_eq_self {t : ℝ} (ht : |t| ≤ 21) : e_nu t = t := by
  rw [e_nu_eq_identityExtension]
  exact identityExtension_eq_self (abs_le.mp ht).1 (abs_le.mp ht).2

theorem identityExtension_contDiff (radius : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (identityExtension radius) := by
  unfold identityExtension
  exact ((p_contDiff.comp (contDiff_id.add contDiff_const)).sub
    (p_contDiff.comp (contDiff_id.sub contDiff_const))).sub contDiff_const

theorem hasDerivAt_identityExtension (radius t : ℝ) :
    HasDerivAt (identityExtension radius)
      (step (t + (radius + 1)) - step (t - radius)) t := by
  have hplus := (hasDerivAt_p (t + (radius + 1))).comp t
    ((hasDerivAt_id t).add_const (radius + 1))
  have hminus := (hasDerivAt_p (t - radius)).comp t
    ((hasDerivAt_id t).sub_const radius)
  convert! (hplus.sub hminus).sub_const (radius + 1 / 2) using 1
  ring

theorem deriv_identityExtension (radius t : ℝ) :
    deriv (identityExtension radius) t =
      step (t + (radius + 1)) - step (t - radius) :=
  (hasDerivAt_identityExtension radius t).deriv

theorem deriv_identityExtension_mem {radius : ℝ} (hr : 0 ≤ radius) (t : ℝ) :
    deriv (identityExtension radius) t ∈ Icc (0 : ℝ) 1 := by
  rw [deriv_identityExtension]
  have hm : step (t - radius) ≤ step (t + (radius + 1)) :=
    step_monotone (by linarith)
  constructor
  · linarith
  · linarith [step_le_one (t + (radius + 1)), step_nonneg (t - radius)]

/-- The current regularizer, with `c` representing `c_R`. -/
def R (c t : ℝ) : ℝ :=
  (12 / 5) * p (-10 * t) -
    ((c + 1) / 10) * (p (10 * t - 1) - p (10 * t - 10))

theorem hasDerivAt_R (c t : ℝ) : HasDerivAt (R c)
    (-24 * step (-10 * t) -
      (c + 1) * (step (10 * t - 1) - step (10 * t - 10))) t := by
  have hleft := ((hasDerivAt_p (-10 * t)).comp t
    ((hasDerivAt_id t).const_mul (-10))).const_mul (12 / 5)
  have hright := (((hasDerivAt_p (10 * t - 1)).comp t
    (((hasDerivAt_id t).const_mul 10).sub_const 1)).sub
    ((hasDerivAt_p (10 * t - 10)).comp t
      (((hasDerivAt_id t).const_mul 10).sub_const 10))).const_mul ((c + 1) / 10)
  convert! hleft.sub hright using 1
  ring

theorem deriv_R (c t : ℝ) : deriv (R c) t =
    -24 * step (-10 * t) -
      (c + 1) * (step (10 * t - 1) - step (10 * t - 10)) :=
  (hasDerivAt_R c t).deriv

theorem R_contDiff (c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (R c) := by
  unfold R
  exact (contDiff_const.mul (p_contDiff.comp (contDiff_const.mul contDiff_id))).sub
    (contDiff_const.mul
      ((p_contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)).sub
        (p_contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))))

theorem R_zero (c : ℝ) : R c 0 = 0 := by
  norm_num [R, p_zero, p_eq_zero (by norm_num : (-1 : ℝ) ≤ 0),
    p_eq_zero (by norm_num : (-10 : ℝ) ≤ 0)]

theorem deriv_R_nonpos {c : ℝ} (hc : -1 ≤ c) (t : ℝ) : deriv (R c) t ≤ 0 := by
  rw [deriv_R]
  have hm : step (10 * t - 10) ≤ step (10 * t - 1) := step_monotone (by linarith)
  have hp := mul_nonneg (show 0 ≤ c + 1 by linarith) (sub_nonneg.mpr hm)
  linarith [step_nonneg (-10 * t)]

theorem deriv_R_left {c t : ℝ} (ht : t ≤ -(1 / 10)) : deriv (R c) t = -24 := by
  rw [deriv_R, step_eq_one (by linarith : 1 ≤ -10 * t),
    step_eq_zero (by linarith : 10 * t - 1 ≤ 0),
    step_eq_zero (by linarith : 10 * t - 10 ≤ 0)]
  ring

theorem deriv_R_transition {c t : ℝ} (hlo : 1 / 5 ≤ t) (hhi : t ≤ 1) :
    deriv (R c) t = -(c + 1) := by
  rw [deriv_R, step_eq_zero (by linarith : -10 * t ≤ 0),
    step_eq_one (by linarith : 1 ≤ 10 * t - 1),
    step_eq_zero (by linarith : 10 * t - 10 ≤ 0)]
  ring

theorem deriv_R_near_zero {c t : ℝ} (hlo : 0 ≤ t) (hhi : t ≤ 1 / 10) :
    deriv (R c) t = 0 := by
  rw [deriv_R, step_eq_zero (by linarith : -10 * t ≤ 0),
    step_eq_zero (by linarith : 10 * t - 1 ≤ 0),
    step_eq_zero (by linarith : 10 * t - 10 ≤ 0)]
  ring

theorem deriv_R_right {c t : ℝ} (ht : 11 / 10 ≤ t) : deriv (R c) t = 0 := by
  rw [deriv_R, step_eq_zero (by linarith : -10 * t ≤ 0),
    step_eq_one (by linarith : 1 ≤ 10 * t - 1),
    step_eq_one (by linarith : 1 ≤ 10 * t - 10)]
  ring

theorem R_eq_right {c t : ℝ} (ht : 11 / 10 ≤ t) : R c t = -(9 / 10) * (c + 1) := by
  rw [R, p_eq_zero (by linarith : -10 * t ≤ 0),
    p_eq_affine (by linarith : 1 ≤ 10 * t - 1),
    p_eq_affine (by linarith : 1 ≤ 10 * t - 10)]
  ring

theorem R_antitone {c : ℝ} (hc : -1 ≤ c) : Antitone (R c) :=
  antitone_of_deriv_nonpos (fun t ↦ (hasDerivAt_R c t).differentiableAt)
    (deriv_R_nonpos hc)

theorem R_lower_bound {c : ℝ} (hc : -1 ≤ c) (t : ℝ) :
    -(9 / 10) * (c + 1) ≤ R c t := by
  by_cases ht : t ≤ 11 / 10
  · simpa only [R_eq_right (le_refl (11 / 10 : ℝ))] using R_antitone hc ht
  · rw [R_eq_right (le_of_not_ge ht)]

end

end NCC.Construction
