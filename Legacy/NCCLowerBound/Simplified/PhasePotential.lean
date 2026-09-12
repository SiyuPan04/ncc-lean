import NCCLowerBound.Simplified.OuterInterfaces

/-!
# The phase potential of the simplified memory--pulse chain

This file formalises lines 1726--1821 of
`NC_C_Lower_Bound_simplified.tex`.  The constant called `K` below is the
abstract parameter `K_out` from the manuscript.  Its concrete estimate in
terms of the other outer interfaces belongs to the later composite-objective
module; none of the analytic properties of `U` needs that estimate, only
`0 < K`.
-/

namespace NCCLowerBound
namespace Simplified

noncomputable section

open Set MeasureTheory
open scoped Interval
open NCCLowerBoundVerification

/-- The left endpoint `-1/10` of the phase ramp. -/
def phaseLeftEndpoint : ℝ := -(1 / 10 : ℝ)

/-! ## The general soft left ramp `R_{r_-,r_+}` -/

/--
The manuscript's
`R_{r_-,r_+}(t) = integral_t^{r_+} (1 - theta ((u-r_-)/(r_+-r_-))) du`.
-/
def softLeftRamp (rMinus rPlus t : ℝ) : ℝ :=
  leftHinge rMinus rPlus t

theorem softLeftRamp_eq_integral (rMinus rPlus t : ℝ) :
    softLeftRamp rMinus rPlus t =
      ∫ u in t..rPlus,
        (1 - theta ((u - rMinus) / (rPlus - rMinus))) := by
  rfl

theorem softLeftRamp_contDiff (rMinus rPlus : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (softLeftRamp rMinus rPlus) := by
  change ContDiff ℝ (⊤ : ℕ∞) (leftHinge rMinus rPlus)
  exact leftHinge_contDiff rMinus rPlus

theorem deriv_softLeftRamp (rMinus rPlus t : ℝ) :
    deriv (softLeftRamp rMinus rPlus) t =
      -1 + theta ((t - rMinus) / (rPlus - rMinus)) := by
  change deriv (leftHinge rMinus rPlus) t =
    -1 + Lambda1 ((t - rMinus) / (rPlus - rMinus))
  exact deriv_leftHinge rMinus rPlus t

theorem softLeftRamp_deriv_mem (rMinus rPlus t : ℝ) :
    deriv (softLeftRamp rMinus rPlus) t ∈ Set.Icc (-1 : ℝ) 0 := by
  rw [deriv_softLeftRamp]
  exact leftHingeDeriv_mem rMinus rPlus t

theorem softLeftRamp_deriv_eq_neg_one {rMinus rPlus t : ℝ}
    (hr : rMinus < rPlus) (ht : t ≤ rMinus) :
    deriv (softLeftRamp rMinus rPlus) t = -1 := by
  rw [deriv_softLeftRamp]
  exact leftHingeDeriv_eq_neg_one hr ht

theorem softLeftRamp_deriv_eq_zero {rMinus rPlus t : ℝ}
    (hr : rMinus < rPlus) (ht : rPlus ≤ t) :
    deriv (softLeftRamp rMinus rPlus) t = 0 := by
  rw [deriv_softLeftRamp]
  exact leftHingeDeriv_eq_zero hr ht

theorem softLeftRamp_nonneg {rMinus rPlus : ℝ}
    (hr : rMinus < rPlus) (t : ℝ) :
    0 ≤ softLeftRamp rMinus rPlus t := by
  simpa [softLeftRamp] using leftHinge_nonneg hr t

/-! ## The compact phase pulse and its primitive -/

/-- The integrand in the second term of `U`. -/
def phasePulse (t : ℝ) : ℝ :=
  theta (10 * t - 1) * (1 - theta (t - 1))

theorem phasePulse_contDiff {k : ℕ∞} : ContDiff ℝ k phasePulse := by
  unfold phasePulse theta
  exact (Lambda1_contDiff.comp
      (contDiff_const.mul contDiff_id |>.sub contDiff_const)).mul
    (contDiff_const.sub
      (Lambda1_contDiff.comp (contDiff_id.sub contDiff_const)))

theorem phasePulse_continuous : Continuous phasePulse :=
  (phasePulse_contDiff (k := (0 : ℕ∞))).continuous

theorem phasePulse_mem_unitInterval (t : ℝ) :
    phasePulse t ∈ Set.Icc (0 : ℝ) 1 := by
  have h₁ := Lambda1_mem_unitInterval (10 * t - 1)
  have h₂ := Lambda1_mem_unitInterval (t - 1)
  have hcomp0 : 0 ≤ 1 - theta (t - 1) := by
    simpa [theta] using sub_nonneg.mpr h₂.2
  have hcomp1 : 1 - theta (t - 1) ≤ 1 := by
    simpa [theta] using sub_le_self 1 h₂.1
  constructor
  · exact mul_nonneg h₁.1 hcomp0
  · calc
      phasePulse t ≤ 1 * (1 - theta (t - 1)) := by
        exact mul_le_mul_of_nonneg_right h₁.2 hcomp0
      _ ≤ 1 * 1 := by
        exact mul_le_mul_of_nonneg_left hcomp1 zero_le_one
      _ = 1 := by ring

theorem phasePulse_nonneg (t : ℝ) : 0 ≤ phasePulse t :=
  (phasePulse_mem_unitInterval t).1

theorem phasePulse_le_one (t : ℝ) : phasePulse t ≤ 1 :=
  (phasePulse_mem_unitInterval t).2

theorem phasePulse_eq_zero_of_le_tenth {t : ℝ}
    (ht : t ≤ (1 / 10 : ℝ)) : phasePulse t = 0 := by
  have harg : 10 * t - 1 ≤ 0 := by linarith
  simp [phasePulse, theta, Lambda1_eq_zero_of_nonpos harg]

theorem phasePulse_eq_one {t : ℝ}
    (hlow : (1 / 5 : ℝ) ≤ t) (hhigh : t ≤ 1) :
    phasePulse t = 1 := by
  have hleft : (1 : ℝ) ≤ 10 * t - 1 := by linarith
  have hright : t - 1 ≤ 0 := by linarith
  simp [phasePulse, theta, Lambda1_eq_one_of_one_le hleft,
    Lambda1_eq_zero_of_nonpos hright]

theorem phasePulse_eq_zero_of_two_le {t : ℝ}
    (ht : (2 : ℝ) ≤ t) : phasePulse t = 0 := by
  have harg : (1 : ℝ) ≤ t - 1 := by linarith
  simp [phasePulse, theta, Lambda1_eq_one_of_one_le harg]

/-- The variable-upper-limit integral in the definition of `U`. -/
def phasePulseIntegral (t : ℝ) : ℝ :=
  ∫ u in 0..t, phasePulse u

theorem hasDerivAt_phasePulseIntegral (t : ℝ) :
    HasDerivAt phasePulseIntegral (phasePulse t) t := by
  exact intervalIntegral.integral_hasDerivAt_right
    (phasePulse_continuous.intervalIntegrable 0 t)
    phasePulse_continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      phasePulse_continuous.continuousAt

theorem deriv_phasePulseIntegral (t : ℝ) :
    deriv phasePulseIntegral t = phasePulse t :=
  (hasDerivAt_phasePulseIntegral t).deriv

theorem phasePulseIntegral_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) phasePulseIntegral := by
  apply contDiff_infty_iff_deriv.2
  refine ⟨fun t ↦ (hasDerivAt_phasePulseIntegral t).differentiableAt, ?_⟩
  have heq : deriv phasePulseIntegral = phasePulse := by
    funext t
    exact deriv_phasePulseIntegral t
  rw [heq]
  exact phasePulse_contDiff

/-! ## The phase potential `U` -/

/--
The phase potential, with the manuscript's `K_out` supplied as the abstract
parameter `K`.
-/
def phasePotential (K t : ℝ) : ℝ :=
  24 * softLeftRamp phaseLeftEndpoint 0 t -
    (K + 1) * phasePulseIntegral t

/-- The explicit derivative displayed by differentiating the two integrals. -/
def phasePotentialDeriv (K t : ℝ) : ℝ :=
  24 * leftHingeDeriv phaseLeftEndpoint 0 t -
    (K + 1) * phasePulse t

theorem hasDerivAt_phasePotential (K t : ℝ) :
    HasDerivAt (phasePotential K) (phasePotentialDeriv K t) t := by
  change HasDerivAt
    (fun u ↦ 24 * leftHinge phaseLeftEndpoint 0 u -
      (K + 1) * phasePulseIntegral u)
    (24 * leftHingeDeriv phaseLeftEndpoint 0 t -
      (K + 1) * phasePulse t) t
  exact ((hasDerivAt_leftHinge phaseLeftEndpoint 0 t).const_mul 24).sub
    ((hasDerivAt_phasePulseIntegral t).const_mul (K + 1))

theorem deriv_phasePotential (K t : ℝ) :
    deriv (phasePotential K) t = phasePotentialDeriv K t :=
  (hasDerivAt_phasePotential K t).deriv

theorem phasePotential_contDiff (K : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (phasePotential K) := by
  unfold phasePotential
  exact (contDiff_const.mul
      (softLeftRamp_contDiff phaseLeftEndpoint 0)).sub
    (contDiff_const.mul phasePulseIntegral_contDiff)

theorem phasePotential_zero (K : ℝ) : phasePotential K 0 = 0 := by
  simp [phasePotential, softLeftRamp, leftHinge_self, phasePulseIntegral]

theorem phasePotential_deriv_zero (K : ℝ) :
    deriv (phasePotential K) 0 = 0 := by
  rw [deriv_phasePotential]
  have hhinge :
      leftHingeDeriv phaseLeftEndpoint 0 0 = 0 :=
    leftHingeDeriv_eq_zero (by norm_num [phaseLeftEndpoint]) le_rfl
  have hpulse : phasePulse 0 = 0 :=
    phasePulse_eq_zero_of_le_tenth (by norm_num)
  simp [phasePotentialDeriv, hhinge, hpulse]

theorem phasePotential_deriv_nonpos {K : ℝ} (hK : 0 < K) (t : ℝ) :
    deriv (phasePotential K) t ≤ 0 := by
  rw [deriv_phasePotential]
  have hhinge := (leftHingeDeriv_mem
    phaseLeftEndpoint 0 t).2
  have hcoef : 0 ≤ K + 1 := by linarith
  have hpulse := phasePulse_nonneg t
  unfold phasePotentialDeriv
  nlinarith [mul_nonneg hcoef hpulse]

theorem phasePotential_deriv_eq_neg_twentyFour {K t : ℝ}
    (ht : t ≤ -(1 / 10 : ℝ)) :
    deriv (phasePotential K) t = -24 := by
  rw [deriv_phasePotential]
  have hhinge : leftHingeDeriv phaseLeftEndpoint 0 t = -1 :=
    leftHingeDeriv_eq_neg_one (by norm_num [phaseLeftEndpoint])
      (by simpa [phaseLeftEndpoint] using ht)
  have hpulse : phasePulse t = 0 :=
    phasePulse_eq_zero_of_le_tenth (by linarith)
  simp [phasePotentialDeriv, hhinge, hpulse]

theorem phasePotential_deriv_eq_neg_K_add_one {K t : ℝ}
    (hlow : (1 / 5 : ℝ) < t) (hhigh : t < 1) :
    deriv (phasePotential K) t = -(K + 1) := by
  rw [deriv_phasePotential]
  have hhinge : leftHingeDeriv phaseLeftEndpoint 0 t = 0 :=
    leftHingeDeriv_eq_zero (by norm_num [phaseLeftEndpoint]) (by linarith)
  have hpulse : phasePulse t = 1 :=
    phasePulse_eq_one (le_of_lt hlow) (le_of_lt hhigh)
  simp [phasePotentialDeriv, hhinge, hpulse]

theorem phasePotential_deriv_eq_zero_of_two_le {K t : ℝ}
    (ht : (2 : ℝ) ≤ t) :
    deriv (phasePotential K) t = 0 := by
  rw [deriv_phasePotential]
  have hhinge : leftHingeDeriv phaseLeftEndpoint 0 t = 0 :=
    leftHingeDeriv_eq_zero (by norm_num [phaseLeftEndpoint]) (by linarith)
  have hpulse : phasePulse t = 0 := phasePulse_eq_zero_of_two_le ht
  simp [phasePotentialDeriv, hhinge, hpulse]

theorem phasePotential_deriv_mem {K : ℝ} (hK : 0 < K) (t : ℝ) :
    deriv (phasePotential K) t ∈ Set.Icc (-(K + 25)) 0 := by
  rw [deriv_phasePotential]
  rcases leftHingeDeriv_mem phaseLeftEndpoint 0 t with
    ⟨hhingeLow, hhingeHigh⟩
  rcases phasePulse_mem_unitInterval t with ⟨hpulseLow, hpulseHigh⟩
  have hcoef : 0 ≤ K + 1 := by linarith
  have hmul : (K + 1) * phasePulse t ≤ K + 1 :=
    mul_le_of_le_one_right hcoef hpulseHigh
  have hmul0 : 0 ≤ (K + 1) * phasePulse t :=
    mul_nonneg hcoef hpulseLow
  unfold phasePotentialDeriv
  constructor
  · nlinarith
  · nlinarith

theorem phasePotential_first_deriv_bounded {K : ℝ} (hK : 0 < K) :
    ∀ t : ℝ, |deriv (phasePotential K) t| ≤ K + 25 := by
  intro t
  rcases phasePotential_deriv_mem hK t with ⟨hlow, hhigh⟩
  rw [abs_of_nonpos hhigh]
  linarith

/-! ## Second derivative and its global bound -/

def phasePotentialSecond (K t : ℝ) : ℝ :=
  deriv (phasePotentialDeriv K) t

theorem phasePotentialDeriv_contDiff (K : ℝ) {k : ℕ∞} :
    ContDiff ℝ k (phasePotentialDeriv K) := by
  unfold phasePotentialDeriv leftHingeDeriv
  exact (contDiff_const.mul
      (contDiff_const.add
        (Lambda1_contDiff.comp
          ((contDiff_id.sub contDiff_const).div_const
            (0 - phaseLeftEndpoint))))).sub
    (contDiff_const.mul phasePulse_contDiff)

theorem hasDerivAt_phasePotentialDeriv (K t : ℝ) :
    HasDerivAt (phasePotentialDeriv K) (phasePotentialSecond K t) t := by
  unfold phasePotentialSecond
  exact (phasePotentialDeriv_contDiff K (k := (1 : ℕ∞))).differentiable
    (by norm_num) t |>.hasDerivAt

theorem phasePotential_second_deriv_eq (K t : ℝ) :
    deriv (deriv (phasePotential K)) t = phasePotentialSecond K t := by
  have heq : deriv (phasePotential K) = phasePotentialDeriv K := by
    funext u
    exact deriv_phasePotential K u
  rw [heq]
  rfl

theorem phasePotentialSecond_eq_zero_of_not_mem {K t : ℝ}
    (ht : t ∉ Set.Icc (-(1 / 10 : ℝ)) 2) :
    phasePotentialSecond K t = 0 := by
  change t ∉ Set.Icc phaseLeftEndpoint 2 at ht
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  unfold phasePotentialSecond
  rcases ht with ht | ht
  · have heq : Set.EqOn (phasePotentialDeriv K) (fun _ : ℝ ↦ -24)
        (Set.Iio (-(1 / 10 : ℝ))) := by
      intro x hx
      rw [← deriv_phasePotential]
      exact phasePotential_deriv_eq_neg_twentyFour hx.le
    simpa using heq.deriv isOpen_Iio ht
  · have heq : Set.EqOn (phasePotentialDeriv K) (fun _ : ℝ ↦ 0)
        (Set.Ioi (2 : ℝ)) := by
      intro x hx
      rw [← deriv_phasePotential]
      exact phasePotential_deriv_eq_zero_of_two_le hx.le
    simpa using heq.deriv isOpen_Ioi ht

theorem phasePotential_second_bounded (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |phasePotentialSecond K t| ≤ C := by
  have hcont : Continuous (fun t : ℝ ↦ |phasePotentialSecond K t|) := by
    unfold phasePotentialSecond
    exact ((phasePotentialDeriv_contDiff K (k := (2 : ℕ∞))).continuous_deriv
      (by norm_num)).abs
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.continuousOn)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (-(1 / 10 : ℝ)) 2
  · exact (hC _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  · rw [phasePotentialSecond_eq_zero_of_not_mem ht, abs_zero]
    exact le_max_right _ _

theorem phasePotential_first_two_derivatives_bounded {K : ℝ} (hK : 0 < K) :
    ∃ C₁ C₂ : ℝ,
      0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      (∀ t : ℝ, |deriv (phasePotential K) t| ≤ C₁) ∧
      (∀ t : ℝ, |deriv (deriv (phasePotential K)) t| ≤ C₂) := by
  obtain ⟨C₂, hC₂, hsecond⟩ := phasePotential_second_bounded K
  refine ⟨K + 25, C₂, by linarith, hC₂,
    phasePotential_first_deriv_bounded hK, ?_⟩
  intro t
  rw [phasePotential_second_deriv_eq]
  exact hsecond t

/-! ## Monotonicity, flat right tail, and a lower bound -/

theorem phasePotential_antitone {K : ℝ} (hK : 0 < K) :
    Antitone (phasePotential K) := by
  apply antitone_of_deriv_nonpos
  · exact fun t ↦ (hasDerivAt_phasePotential K t).differentiableAt
  · exact phasePotential_deriv_nonpos hK

theorem phasePotential_eq_at_two_of_two_le {K t : ℝ}
    (ht : (2 : ℝ) ≤ t) :
    phasePotential K t = phasePotential K 2 := by
  rcases ht.eq_or_lt with rfl | ht
  · rfl
  have hdiff : DifferentiableOn ℝ (phasePotential K) (Set.Icc 2 t) :=
    fun x _ ↦ (hasDerivAt_phasePotential K x).differentiableAt.differentiableWithinAt
  have hzero : ∀ x ∈ Set.Ico (2 : ℝ) t,
      derivWithin (phasePotential K) (Set.Icc 2 t) x = 0 := by
    intro x hx
    have hz : phasePotentialDeriv K x = 0 := by
      rw [← deriv_phasePotential]
      exact phasePotential_deriv_eq_zero_of_two_le hx.1
    have hder : HasDerivAt (phasePotential K) 0 x := by
      simpa only [hz] using hasDerivAt_phasePotential K x
    exact hder.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc ht x ⟨hx.1, le_of_lt hx.2⟩)
  exact constant_of_derivWithin_zero hdiff hzero t ⟨ht.le, le_rfl⟩

theorem phasePotential_lower_bound {K : ℝ} (hK : 0 < K) :
    ∀ t : ℝ, phasePotential K 2 ≤ phasePotential K t := by
  intro t
  by_cases ht : t ≤ 2
  · exact phasePotential_antitone hK ht
  · rw [phasePotential_eq_at_two_of_two_le (le_of_not_ge ht)]

theorem phasePotential_bddBelow {K : ℝ} (hK : 0 < K) :
    BddBelow (Set.range (phasePotential K)) := by
  refine ⟨phasePotential K 2, ?_⟩
  rintro _ ⟨t, rfl⟩
  exact phasePotential_lower_bound hK t

/-! ## Abstract phase-margin consequences -/

/-- `K` is a uniform absolute bound for the derivative of the outer remainder. -/
def IsOuterRemainderBound (K : ℝ) (remainderDeriv : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, |remainderDeriv t| ≤ K

theorem IsOuterRemainderBound.upper {K : ℝ} {remainderDeriv : ℝ → ℝ}
    (h : IsOuterRemainderBound K remainderDeriv) (t : ℝ) :
    remainderDeriv t ≤ K := by
  exact (le_abs_self (remainderDeriv t)).trans (h t)

/-- Phase-margin case (i): `-24` plus at most `22` is at most `-2`. -/
theorem phaseMargin_farLeft {K t outerDerivative totalDerivative : ℝ}
    (ht : t ≤ -(1 / 10 : ℝ))
    (houter : outerDerivative ≤ 22)
    (htotal : totalDerivative =
      deriv (phasePotential K) t + outerDerivative) :
    totalDerivative ≤ -2 := by
  rw [htotal, phasePotential_deriv_eq_neg_twentyFour ht]
  linarith

/--
Phase-margin case (ii): the exact phase slope `-(K+1)` strictly dominates
an outer remainder whose absolute value is bounded by `K`.
-/
theorem phaseMargin_transition {K t : ℝ} {remainderDeriv : ℝ → ℝ}
    {totalDerivative : ℝ} (hK : 0 < K)
    (hbound : IsOuterRemainderBound K remainderDeriv)
    (hlow : (1 / 5 : ℝ) < t) (hhigh : t < 1)
    (htotal : totalDerivative =
      deriv (phasePotential K) t + remainderDeriv t) :
    totalDerivative ≤ -1 := by
  rw [htotal, phasePotential_deriv_eq_neg_K_add_one hlow hhigh]
  have hrem := hbound.upper t
  have hKnonneg : 0 ≤ K := hK.le
  linarith

/--
Phase-margin case (iii), after the sign analysis of the ordering terms has
isolated a contribution `-24` and a possibly positive remainder at most `22`.
-/
theorem phaseMargin_predecessor {K t positiveRemainder totalDerivative : ℝ}
    (hK : 0 < K) (hpositive : positiveRemainder ≤ 22)
    (htotal : totalDerivative =
      deriv (phasePotential K) t - 24 + positiveRemainder) :
    totalDerivative ≤ -2 := by
  rw [htotal]
  have hU := phasePotential_deriv_nonpos hK t
  linarith

/-- A single abstract packaging of the three margins used in the manuscript. -/
theorem phaseMargins_abstract
    {K sLeft sMiddle sPrevious : ℝ}
    {remainderDeriv : ℝ → ℝ}
    {leftPositive previousPositive leftTotal middleTotal previousTotal : ℝ}
    (hK : 0 < K)
    (hleftState : sLeft ≤ -(1 / 10 : ℝ))
    (hmiddleLow : (1 / 5 : ℝ) < sMiddle) (hmiddleHigh : sMiddle < 1)
    (hbound : IsOuterRemainderBound K remainderDeriv)
    (hleftPositive : leftPositive ≤ 22)
    (hpreviousPositive : previousPositive ≤ 22)
    (hleftTotal : leftTotal =
      deriv (phasePotential K) sLeft + leftPositive)
    (hmiddleTotal : middleTotal =
      deriv (phasePotential K) sMiddle + remainderDeriv sMiddle)
    (hpreviousTotal : previousTotal =
      deriv (phasePotential K) sPrevious - 24 + previousPositive) :
    leftTotal ≤ -2 ∧ middleTotal ≤ -1 ∧ previousTotal ≤ -2 := by
  exact ⟨phaseMargin_farLeft hleftState hleftPositive hleftTotal,
    phaseMargin_transition hK hbound hmiddleLow hmiddleHigh hmiddleTotal,
    phaseMargin_predecessor hK hpreviousPositive hpreviousTotal⟩

end

end Simplified
end NCCLowerBound
