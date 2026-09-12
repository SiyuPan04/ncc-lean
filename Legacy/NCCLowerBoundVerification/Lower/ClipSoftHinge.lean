import NCCLowerBoundVerification.Lower.SmoothStep
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Concrete clips and soft hinges

This module formalizes the concrete integral templates in Definitions
`def:pi-family` and `def:Sigma-family` of `Upper+Lower_unified_lower.tex`.
-/

namespace NCCLowerBoundVerification

noncomputable section

open Set MeasureTheory
open scoped Interval

/-! ## The symmetric saturation template and the two clips -/

def clipIntegrand (R width t : ℝ) : ℝ :=
  1 - Lambda1 ((|t| - R) / width)

/-- A manifestly smooth formula equal to the absolute-value formula when
`R ≥ 0` and `width > 0`. -/
def smoothClipIntegrand (R width t : ℝ) : ℝ :=
  1 - Lambda1 ((t - R) / width) - Lambda1 ((-t - R) / width)

theorem clipIntegrand_eq_smooth {R width : ℝ} (hR : 0 ≤ R) (hwidth : 0 < width) :
    clipIntegrand R width = smoothClipIntegrand R width := by
  funext t
  by_cases ht : 0 ≤ t
  · have hneg : (-t - R) / width ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hwidth.le
    simp [clipIntegrand, smoothClipIntegrand, abs_of_nonneg ht,
      Lambda1_eq_zero_of_nonpos hneg]
  · have ht' : t ≤ 0 := le_of_not_ge ht
    have hpos : (t - R) / width ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hwidth.le
    simp [clipIntegrand, smoothClipIntegrand, abs_of_nonpos ht',
      Lambda1_eq_zero_of_nonpos hpos]

theorem clipIntegrand_contDiff {R width : ℝ} (hR : 0 ≤ R) (hwidth : 0 < width)
    {k : ℕ∞} : ContDiff ℝ k (clipIntegrand R width) := by
  rw [clipIntegrand_eq_smooth hR hwidth]
  unfold smoothClipIntegrand
  exact (contDiff_const.sub
    (Lambda1_contDiff.comp ((contDiff_id.sub contDiff_const).div_const width))).sub
      (Lambda1_contDiff.comp ((contDiff_id.neg.sub contDiff_const).div_const width))

/-- Equation `eq:clip-template`. -/
def saturationTemplate (R width t : ℝ) : ℝ :=
  ∫ u in 0..t, clipIntegrand R width u

theorem clipIntegrand_continuous (R width : ℝ) :
    Continuous (clipIntegrand R width) := by
  unfold clipIntegrand
  exact continuous_const.sub
    (Lambda1_continuous.comp ((continuous_abs.sub continuous_const).div_const width))

theorem clipIntegrand_nonneg (R width t : ℝ) :
    0 ≤ clipIntegrand R width t := by
  unfold clipIntegrand
  linarith [Lambda1_le_one ((|t| - R) / width)]

theorem clipIntegrand_le_one (R width t : ℝ) :
    clipIntegrand R width t ≤ 1 := by
  unfold clipIntegrand
  linarith [Lambda1_nonneg ((|t| - R) / width)]

theorem hasDerivAt_saturationTemplate (R width t : ℝ) :
    HasDerivAt (saturationTemplate R width) (clipIntegrand R width t) t := by
  have hc := clipIntegrand_continuous R width
  exact intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem deriv_saturationTemplate (R width t : ℝ) :
    deriv (saturationTemplate R width) t = clipIntegrand R width t :=
  (hasDerivAt_saturationTemplate R width t).deriv

theorem differentiable_saturationTemplate (R width : ℝ) :
    Differentiable ℝ (saturationTemplate R width) :=
  fun t ↦ (hasDerivAt_saturationTemplate R width t).differentiableAt

theorem saturationTemplate_contDiff_one (R width : ℝ) :
    ContDiff ℝ 1 (saturationTemplate R width) := by
  apply contDiff_one_iff_deriv.2
  refine ⟨differentiable_saturationTemplate R width, ?_⟩
  have heq : deriv (saturationTemplate R width) = clipIntegrand R width := by
    funext t
    exact deriv_saturationTemplate R width t
  rw [heq]
  exact clipIntegrand_continuous R width

theorem saturationTemplate_contDiff {R width : ℝ} (hR : 0 ≤ R) (hwidth : 0 < width) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (saturationTemplate R width) := by
  apply contDiff_infty_iff_deriv.2
  refine ⟨differentiable_saturationTemplate R width, ?_⟩
  have heq : deriv (saturationTemplate R width) = clipIntegrand R width := by
    funext t
    exact deriv_saturationTemplate R width t
  rw [heq]
  exact clipIntegrand_contDiff hR hwidth

/-! The transition symmetry fixes its area exactly. -/

theorem integral_Lambda1_zero_one : (∫ u in (0 : ℝ)..1, Lambda1 u) = 1 / 2 := by
  have hi : IntervalIntegrable Lambda1 volume 0 1 :=
    Lambda1_continuous.intervalIntegrable 0 1
  have hirev : IntervalIntegrable (fun u : ℝ ↦ Lambda1 (1 - u)) volume 0 1 :=
    (Lambda1_continuous.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 1
  have hrev : (∫ u in (0 : ℝ)..1, Lambda1 (1 - u)) =
      ∫ u in (0 : ℝ)..1, Lambda1 u := by
    simpa only [sub_self, sub_zero] using
      intervalIntegral.integral_comp_sub_left
        (a := (0 : ℝ)) (b := 1) Lambda1 (1 : ℝ)
  have hadd := intervalIntegral.integral_add hi hirev
  have hpoint : (fun u : ℝ ↦ Lambda1 u + Lambda1 (1 - u)) = fun _ ↦ (1 : ℝ) := by
    funext u
    exact Lambda1_symmetry u
  calc
    (∫ u in (0 : ℝ)..1, Lambda1 u) =
        1 / 2 * ((∫ u in (0 : ℝ)..1, Lambda1 u) +
          ∫ u in (0 : ℝ)..1, Lambda1 (1 - u)) := by rw [hrev]; ring
    _ = 1 / 2 * ∫ u in (0 : ℝ)..1, (Lambda1 u + Lambda1 (1 - u)) := by rw [hadd]
    _ = 1 / 2 * ∫ _u in (0 : ℝ)..1, (1 : ℝ) := by rw [hpoint]
    _ = 1 / 2 := by norm_num

theorem integral_clip_transition {R width : ℝ} (hR : 0 ≤ R) (hwidth : 0 < width) :
    (∫ u in R..R + width, clipIntegrand R width u) = width / 2 := by
  have hchange := intervalIntegral.smul_integral_comp_mul_add
    (f := clipIntegrand R width) (a := (0 : ℝ)) (b := 1) width R
  have hunit : (∫ x in (0 : ℝ)..1, clipIntegrand R width (width * x + R)) = 1 / 2 := by
    calc
      (∫ x in (0 : ℝ)..1, clipIntegrand R width (width * x + R)) =
          ∫ x in (0 : ℝ)..1, (1 - Lambda1 x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
          simpa [uIcc_of_le zero_le_one] using hx
        have hu : 0 ≤ width * x + R := add_nonneg (mul_nonneg hwidth.le hx'.1) hR
        have harg : (|width * x + R| - R) / width = x := by
          rw [abs_of_nonneg hu]
          field_simp [hwidth.ne']
          ring
        simp [clipIntegrand, harg]
      _ = 1 / 2 := by
        rw [intervalIntegral.integral_sub]
        · norm_num [integral_Lambda1_zero_one]
        · exact intervalIntegrable_const
        · exact Lambda1_continuous.intervalIntegrable _ _
  calc
    (∫ u in R..R + width, clipIntegrand R width u) =
        width * ∫ x in (0 : ℝ)..1, clipIntegrand R width (width * x + R) := by
      symm
      simpa only [smul_eq_mul, mul_zero, zero_add, add_zero, mul_one, add_comm] using hchange
    _ = width * (1 / 2) := by rw [hunit]
    _ = width / 2 := by ring

theorem saturationTemplate_monotone (R width : ℝ) :
    Monotone (saturationTemplate R width) := by
  apply monotone_of_deriv_nonneg (differentiable_saturationTemplate R width)
  intro t
  rw [deriv_saturationTemplate]
  exact clipIntegrand_nonneg R width t

theorem saturationTemplate_zero (R width : ℝ) :
    saturationTemplate R width 0 = 0 := by
  simp [saturationTemplate]

theorem clipIntegrand_even (R width t : ℝ) :
    clipIntegrand R width (-t) = clipIntegrand R width t := by
  simp [clipIntegrand]

theorem saturationTemplate_odd (R width t : ℝ) :
    saturationTemplate R width (-t) = -saturationTemplate R width t := by
  unfold saturationTemplate
  calc
    (∫ u in 0..-t, clipIntegrand R width u) =
        -(∫ u in -t..0, clipIntegrand R width u) := by
          rw [intervalIntegral.integral_symm]
    _ = -(∫ u in 0..t, clipIntegrand R width u) := by
      congr 1
      calc
        (∫ u in -t..0, clipIntegrand R width u) =
            ∫ u in 0..t, clipIntegrand R width (-u) := by
              have hneg :
                  (∫ u in (0 : ℝ)..t, clipIntegrand R width (-u)) =
                    ∫ u in -t..-(0 : ℝ), clipIntegrand R width u :=
                intervalIntegral.integral_comp_neg (clipIntegrand R width)
              simpa only [neg_zero] using hneg.symm
        _ = ∫ u in 0..t, clipIntegrand R width u := by
          apply intervalIntegral.integral_congr
          intro u _
          exact clipIntegrand_even R width u

theorem saturationTemplate_eq_self {R width t : ℝ} (_hR : 0 ≤ R)
    (hwidth : 0 < width) (ht : |t| ≤ R) : saturationTemplate R width t = t := by
  unfold saturationTemplate
  calc
    (∫ u in 0..t, clipIntegrand R width u) = ∫ _u in 0..t, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hut : |u| ≤ |t| := by
        simpa using abs_sub_left_of_mem_uIcc hu
      have harg : (|u| - R) / width ≤ 0 := by
        apply div_nonpos_of_nonpos_of_nonneg
        · linarith
        · exact hwidth.le
      simp [clipIntegrand, Lambda1_eq_zero_of_nonpos harg]
    _ = t := by simp

theorem saturationTemplate_at_right_edge {R width : ℝ} (hR : 0 ≤ R)
    (hwidth : 0 < width) :
    saturationTemplate R width (R + width) = R + width / 2 := by
  have hc := clipIntegrand_continuous R width
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 R) (hc.intervalIntegrable R (R + width))
  unfold saturationTemplate
  rw [← hadd]
  rw [show (∫ u in (0 : ℝ)..R, clipIntegrand R width u) = R by
    simpa [saturationTemplate] using
      saturationTemplate_eq_self hR hwidth (t := R) (abs_of_nonneg hR).le]
  rw [integral_clip_transition hR hwidth]

theorem saturationTemplate_eq_right_plateau {R width t : ℝ} (hR : 0 ≤ R)
    (hwidth : 0 < width) (ht : R + width ≤ t) :
    saturationTemplate R width t = R + width / 2 := by
  have hc := clipIntegrand_continuous R width
  have htail : (∫ u in R + width..t, clipIntegrand R width u) = 0 := by
    calc
      (∫ u in R + width..t, clipIntegrand R width u) =
          ∫ _u in R + width..t, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu' : u ∈ Set.Icc (R + width) t := by
          simpa [uIcc_of_le ht] using hu
        have hbound := hu'.1
        have hu0 : 0 ≤ u := by linarith
        have harg : 1 ≤ (|u| - R) / width := by
          rw [abs_of_nonneg hu0]
          exact (le_div_iff₀ hwidth).2 (by linarith)
        simp [clipIntegrand, Lambda1_eq_one_of_one_le harg]
      _ = 0 := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (R + width)) (hc.intervalIntegrable (R + width) t)
  unfold saturationTemplate
  rw [← hadd, htail, add_zero]
  exact saturationTemplate_at_right_edge hR hwidth

theorem saturationTemplate_eq_left_plateau {R width t : ℝ} (hR : 0 ≤ R)
    (hwidth : 0 < width) (ht : t ≤ -(R + width)) :
    saturationTemplate R width t = -(R + width / 2) := by
  rw [show t = -(-t) by ring, saturationTemplate_odd]
  rw [saturationTemplate_eq_right_plateau hR hwidth (by linarith)]

theorem saturationTemplate_range_bounds {R width t : ℝ} (hR : 0 ≤ R)
    (hwidth : 0 < width) :
    -(R + width / 2) ≤ saturationTemplate R width t ∧
      saturationTemplate R width t ≤ R + width / 2 := by
  have hmono := saturationTemplate_monotone R width
  constructor
  · by_cases ht : t ≤ -(R + width)
    · rw [saturationTemplate_eq_left_plateau hR hwidth ht]
    · have hle : -(R + width) ≤ t := le_of_not_ge ht
      have hm := hmono hle
      rw [saturationTemplate_eq_left_plateau hR hwidth le_rfl] at hm
      exact hm
  · by_cases ht : R + width ≤ t
    · rw [saturationTemplate_eq_right_plateau hR hwidth ht]
    · have hle : t ≤ R + width := le_of_not_ge ht
      have hm := hmono hle
      rw [saturationTemplate_eq_right_plateau hR hwidth le_rfl] at hm
      exact hm

theorem saturationTemplate_range {R width : ℝ} (hR : 0 ≤ R) (hwidth : 0 < width) :
    Set.range (saturationTemplate R width) =
      Set.Icc (-(R + width / 2)) (R + width / 2) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact saturationTemplate_range_bounds hR hwidth
  · intro y hy
    have hS : -(R + width) ≤ R + width := by linarith
    have hy' : y ∈ Set.Icc
        (saturationTemplate R width (-(R + width)))
        (saturationTemplate R width (R + width)) := by
      rw [saturationTemplate_eq_left_plateau hR hwidth le_rfl,
        saturationTemplate_eq_right_plateau hR hwidth le_rfl]
      exact hy
    have himage := intermediate_value_Icc hS
      (differentiable_saturationTemplate R width).continuous.continuousOn hy'
    rcases himage with ⟨t, _ht, rfl⟩
    exact ⟨t, rfl⟩

theorem clipIntegrand_eq_one {R width t : ℝ} (hwidth : 0 < width)
    (ht : |t| ≤ R) : clipIntegrand R width t = 1 := by
  have harg : (|t| - R) / width ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hwidth.le
  simp [clipIntegrand, Lambda1_eq_zero_of_nonpos harg]

theorem clipIntegrand_eq_zero {R width t : ℝ} (hwidth : 0 < width)
    (ht : R + width ≤ |t|) : clipIntegrand R width t = 0 := by
  have harg : 1 ≤ (|t| - R) / width := by
    apply (le_div_iff₀ hwidth).2
    linarith
  simp [clipIntegrand, Lambda1_eq_one_of_one_le harg]

def clipIntegrandDeriv (R width t : ℝ) : ℝ :=
  deriv (clipIntegrand R width) t

def saturationTemplateSecond (R width t : ℝ) : ℝ :=
  clipIntegrandDeriv R width t

theorem hasDerivAt_clipIntegrand {R width t : ℝ} (hR : 0 ≤ R) (hwidth : 0 < width) :
    HasDerivAt (clipIntegrand R width) (clipIntegrandDeriv R width t) t := by
  unfold clipIntegrandDeriv
  exact ((clipIntegrand_contDiff hR hwidth (k := (1 : ℕ∞))).differentiable
    (by norm_num) t).hasDerivAt

theorem secondDeriv_saturationTemplate {R width t : ℝ} :
    deriv (deriv (saturationTemplate R width)) t = saturationTemplateSecond R width t := by
  have heq : deriv (saturationTemplate R width) = clipIntegrand R width := by
    funext s
    exact deriv_saturationTemplate R width s
  rw [heq]
  rfl

theorem clipIntegrandDeriv_eq_zero_of_not_mem {R width t : ℝ}
    (hR : 0 ≤ R) (hwidth : 0 < width)
    (ht : t ∉ Set.Icc (-(R + width)) (R + width)) :
    clipIntegrandDeriv R width t = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  unfold clipIntegrandDeriv
  rcases ht with ht | ht
  · have heq : Set.EqOn (clipIntegrand R width) (fun _ : ℝ ↦ 0)
        (Set.Iio (-(R + width))) := by
      intro x hx
      have hxl : x < -(R + width) := hx
      apply clipIntegrand_eq_zero hwidth
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hd := heq.deriv isOpen_Iio ht
    simpa using hd
  · have heq : Set.EqOn (clipIntegrand R width) (fun _ : ℝ ↦ 0)
        (Set.Ioi (R + width)) := by
      intro x hx
      have hxl : R + width < x := hx
      apply clipIntegrand_eq_zero hwidth
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hd := heq.deriv isOpen_Ioi ht
    simpa using hd

theorem clipIntegrandDeriv_bounded {R width : ℝ} (hR : 0 ≤ R) (hwidth : 0 < width) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |clipIntegrandDeriv R width t| ≤ C := by
  let S := R + width + 1
  have hcontDeriv : Continuous (clipIntegrandDeriv R width) := by
    unfold clipIntegrandDeriv
    exact (clipIntegrand_contDiff hR hwidth (k := (2 : ℕ∞))).continuous_deriv (by norm_num)
  have hcont : Continuous (fun t : ℝ ↦ |clipIntegrandDeriv R width t|) := hcontDeriv.abs
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.continuousOn)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (-S) S
  · exact (hC _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  · have hout : t ∉ Set.Icc (-(R + width)) (R + width) := by
      intro hin
      apply ht
      exact ⟨by dsimp [S]; linarith [hin.1], by dsimp [S]; linarith [hin.2]⟩
    rw [clipIntegrandDeriv_eq_zero_of_not_mem hR hwidth hout, abs_zero]
    exact le_max_right _ _

theorem saturationTemplate_deriv_mem_unitInterval (R width t : ℝ) :
    deriv (saturationTemplate R width) t ∈ Set.Icc (0 : ℝ) 1 := by
  rw [deriv_saturationTemplate]
  exact ⟨clipIntegrand_nonneg R width t, clipIntegrand_le_one R width t⟩

/-- The pulse radius `R_p = P₀ + 2`. -/
def pulseRadius (P0 : ℝ) : ℝ := P0 + 2

/-- Equation `eq:pi-two`. -/
def pi2 (P0 t : ℝ) : ℝ := saturationTemplate (pulseRadius P0) 1 t

def pi2Deriv (P0 t : ℝ) : ℝ := clipIntegrand (pulseRadius P0) 1 t
def pi2Second (P0 t : ℝ) : ℝ := clipIntegrandDeriv (pulseRadius P0) 1 t

theorem hasDerivAt_pi2 (P0 t : ℝ) : HasDerivAt (pi2 P0) (pi2Deriv P0 t) t := by
  exact hasDerivAt_saturationTemplate (pulseRadius P0) 1 t

theorem pi2_contDiff {P0 : ℝ} (hP0 : 1 < P0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (pi2 P0) := by
  exact saturationTemplate_contDiff (by unfold pulseRadius; linarith) zero_lt_one

theorem deriv_pi2 (P0 t : ℝ) : deriv (pi2 P0) t = pi2Deriv P0 t :=
  (hasDerivAt_pi2 P0 t).deriv

theorem hasDerivAt_pi2Deriv {P0 t : ℝ} (hP0 : 1 < P0) :
    HasDerivAt (pi2Deriv P0) (pi2Second P0 t) t := by
  have hdiff : DifferentiableAt ℝ (clipIntegrand (pulseRadius P0) 1) t :=
    (clipIntegrand_contDiff (by unfold pulseRadius; linarith) zero_lt_one
      (k := (1 : ℕ∞))).differentiable (by norm_num) t
  unfold pi2Deriv pi2Second clipIntegrandDeriv
  convert hdiff.hasDerivAt using 1

theorem deriv_pi2Deriv {P0 t : ℝ} (hP0 : 1 < P0) :
    deriv (pi2Deriv P0) t = pi2Second P0 t :=
  (hasDerivAt_pi2Deriv hP0).deriv

theorem pi2Second_bounded {P0 : ℝ} (hP0 : 1 < P0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |pi2Second P0 t| ≤ C := by
  simpa only [pi2Second] using clipIntegrandDeriv_bounded
    (R := pulseRadius P0) (width := 1) (by unfold pulseRadius; linarith) zero_lt_one

theorem pi2_eq_self {P0 t : ℝ} (hP0 : 1 < P0)
    (ht : |t| ≤ P0 + 2) : pi2 P0 t = t := by
  exact saturationTemplate_eq_self (by unfold pulseRadius; linarith) zero_lt_one ht

theorem pi2Deriv_eq_one {P0 t : ℝ} (ht : |t| ≤ P0 + 2) :
    pi2Deriv P0 t = 1 := by
  exact clipIntegrand_eq_one zero_lt_one ht

theorem pi2Deriv_eq_zero {P0 t : ℝ} (ht : P0 + 3 ≤ |t|) :
    pi2Deriv P0 t = 0 := by
  apply clipIntegrand_eq_zero zero_lt_one
  unfold pulseRadius
  linarith

theorem pi2_zero (P0 : ℝ) : pi2 P0 0 = 0 := saturationTemplate_zero _ _

theorem pi2_odd (P0 t : ℝ) : pi2 P0 (-t) = -pi2 P0 t :=
  saturationTemplate_odd _ _ _

theorem pi2Deriv_zero {P0 : ℝ} (hP0 : 1 < P0) : pi2Deriv P0 0 = 1 := by
  apply pi2Deriv_eq_one
  simp only [abs_zero]
  linarith

theorem pi2_monotone (P0 : ℝ) : Monotone (pi2 P0) :=
  saturationTemplate_monotone _ _

theorem pi2_deriv_mem_unitInterval (P0 t : ℝ) :
    deriv (pi2 P0) t ∈ Set.Icc (0 : ℝ) 1 := by
  exact saturationTemplate_deriv_mem_unitInterval _ _ _

theorem pi2_range {P0 : ℝ} (hP0 : 1 < P0) :
    Set.range (pi2 P0) = Set.Icc (-(P0 + 5 / 2)) (P0 + 5 / 2) := by
  have heq : P0 + 5 / 2 = (P0 + 2) + 1 / 2 := by ring
  rw [heq]
  unfold pi2 pulseRadius
  simpa using saturationTemplate_range (R := P0 + 2) (width := 1) (by linarith) zero_lt_one

theorem pi2_abs_le {P0 t : ℝ} (hP0 : 1 < P0) : |pi2 P0 t| ≤ P0 + 5 / 2 := by
  have hmem : pi2 P0 t ∈ Set.Icc (-(P0 + 5 / 2)) (P0 + 5 / 2) := by
    rw [← pi2_range hP0]
    exact ⟨t, rfl⟩
  rw [abs_le]
  exact hmem

theorem pi2_uniform_bound {P0 : ℝ} (hP0 : 1 < P0) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      |pi2 P0 t| + |pi2Deriv P0 t| + |pi2Second P0 t| ≤ C := by
  obtain ⟨C₂, hC₂, hsecond⟩ := pi2Second_bounded hP0
  refine ⟨P0 + 7 / 2 + C₂, by linarith, ?_⟩
  intro t
  have hvalue := pi2_abs_le (t := t) hP0
  have hderivMem := pi2_deriv_mem_unitInterval P0 t
  rw [deriv_pi2] at hderivMem
  have hderiv : |pi2Deriv P0 t| ≤ 1 := by
    rw [abs_of_nonneg hderivMem.1]
    exact hderivMem.2
  linarith [hsecond t]

/-- The lower, upper, midpoint, and half-width parameters of the state clip. -/
def stateLower (delta : ℝ) : ℝ := -delta / 2
def stateUpper : ℝ := 3
def stateMidpoint (delta : ℝ) : ℝ := (stateLower delta + stateUpper) / 2
def stateHalfWidth (delta : ℝ) : ℝ := (stateUpper - stateLower delta) / 2
def tauS (delta : ℝ) : ℝ := delta / 4
def stateExcess (delta P0 : ℝ) : ℝ :=
  stateHalfWidth delta / (2 * pulseRadius P0)

/-- Equation `eq:pi-one`. -/
def pi1 (delta P0 t : ℝ) : ℝ :=
  stateMidpoint delta + stateHalfWidth delta / pulseRadius P0 *
    pi2 P0 (pulseRadius P0 / stateHalfWidth delta * (t - stateMidpoint delta))

def pi1Deriv (delta P0 t : ℝ) : ℝ :=
  pi2Deriv P0
    (pulseRadius P0 / stateHalfWidth delta * (t - stateMidpoint delta))

def pi1Second (delta P0 t : ℝ) : ℝ :=
  pulseRadius P0 / stateHalfWidth delta *
    pi2Second P0
      (pulseRadius P0 / stateHalfWidth delta * (t - stateMidpoint delta))

theorem hasDerivAt_pi1 {delta P0 t : ℝ} (hdelta : 0 < delta) (hP0 : 1 < P0) :
    HasDerivAt (pi1 delta P0) (pi1Deriv delta P0 t) t := by
  have hh : 0 < stateHalfWidth delta := by
    unfold stateHalfWidth stateUpper stateLower
    linarith
  have hR : 0 < pulseRadius P0 := by unfold pulseRadius; linarith
  have hinner : HasDerivAt
      (fun s : ℝ ↦ pulseRadius P0 / stateHalfWidth delta * (s - stateMidpoint delta))
      (pulseRadius P0 / stateHalfWidth delta) t := by
    convert ((hasDerivAt_id t).sub_const (stateMidpoint delta)).const_mul
      (pulseRadius P0 / stateHalfWidth delta) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext s
      rfl
    · ring
  have hcomp := (hasDerivAt_pi2 P0
    (pulseRadius P0 / stateHalfWidth delta * (t - stateMidpoint delta))).comp t hinner
  have hscaled := hcomp.const_mul (stateHalfWidth delta / pulseRadius P0)
  have hsum := (hasDerivAt_const t (stateMidpoint delta)).add hscaled
  convert hsum using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · unfold pi1Deriv
    field_simp [hh.ne', hR.ne']
    simp

theorem deriv_pi1 {delta P0 t : ℝ} (hdelta : 0 < delta) (hP0 : 1 < P0) :
    deriv (pi1 delta P0) t = pi1Deriv delta P0 t :=
  (hasDerivAt_pi1 hdelta hP0).deriv

theorem hasDerivAt_pi1Deriv {delta P0 t : ℝ} (hdelta : 0 < delta) (hP0 : 1 < P0) :
    HasDerivAt (pi1Deriv delta P0) (pi1Second delta P0 t) t := by
  have hh : 0 < stateHalfWidth delta := by
    unfold stateHalfWidth stateUpper stateLower
    linarith
  have hinner : HasDerivAt
      (fun s : ℝ ↦ pulseRadius P0 / stateHalfWidth delta * (s - stateMidpoint delta))
      (pulseRadius P0 / stateHalfWidth delta) t := by
    convert ((hasDerivAt_id t).sub_const (stateMidpoint delta)).const_mul
      (pulseRadius P0 / stateHalfWidth delta) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext s
      rfl
    · ring
  have hcomp := (hasDerivAt_pi2Deriv (P0 := P0)
    (t := pulseRadius P0 / stateHalfWidth delta * (t - stateMidpoint delta)) hP0).comp t hinner
  unfold pi1Deriv pi1Second
  convert hcomp using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · ring

theorem deriv_pi1Deriv {delta P0 t : ℝ} (hdelta : 0 < delta) (hP0 : 1 < P0) :
    deriv (pi1Deriv delta P0) t = pi1Second delta P0 t :=
  (hasDerivAt_pi1Deriv hdelta hP0).deriv

theorem pi1Second_bounded {delta P0 : ℝ} (hdelta : 0 < delta) (hP0 : 1 < P0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |pi1Second delta P0 t| ≤ C := by
  obtain ⟨C₂, hC₂, hbound⟩ := pi2Second_bounded hP0
  have hh : 0 < stateHalfWidth delta := by
    unfold stateHalfWidth stateUpper stateLower
    linarith
  refine ⟨|pulseRadius P0 / stateHalfWidth delta| * C₂,
    mul_nonneg (abs_nonneg _) hC₂, ?_⟩
  intro t
  unfold pi1Second
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg _)

theorem pi1_contDiff {delta P0 : ℝ} (hdelta : 0 < delta) (hP0 : 1 < P0) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (pi1 delta P0) := by
  have hh : 0 < stateHalfWidth delta := by
    unfold stateHalfWidth stateUpper stateLower
    linarith
  unfold pi1
  exact contDiff_const.add
    (contDiff_const.mul ((pi2_contDiff hP0).comp
      (((contDiff_const.div_const (stateHalfWidth delta)).mul
        (contDiff_id.sub contDiff_const)))))

theorem pi1_monotone {delta P0 : ℝ} (hdelta : 0 < delta) (hP0 : 1 < P0) :
    Monotone (pi1 delta P0) := by
  apply monotone_of_deriv_nonneg
  · exact fun t ↦ (hasDerivAt_pi1 hdelta hP0).differentiableAt
  · intro t
    rw [deriv_pi1 hdelta hP0]
    unfold pi1Deriv pi2Deriv
    exact clipIntegrand_nonneg _ _ _

theorem pi1Deriv_mem_unitInterval (delta P0 t : ℝ) :
    pi1Deriv delta P0 t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold pi1Deriv pi2Deriv
  exact ⟨clipIntegrand_nonneg _ _ _, clipIntegrand_le_one _ _ _⟩

theorem pi1_eq_self {delta P0 t : ℝ} (hdelta : 0 < delta)
    (hP0 : 1 < P0) (htlow : stateLower delta ≤ t) (hthigh : t ≤ stateUpper) :
    pi1 delta P0 t = t := by
  have hh : 0 < stateHalfWidth delta := by
    unfold stateHalfWidth stateUpper stateLower
    linarith
  have hR : 0 < pulseRadius P0 := by unfold pulseRadius; linarith
  have harg :
      |pulseRadius P0 / stateHalfWidth delta * (t - stateMidpoint delta)| ≤
        P0 + 2 := by
    rw [abs_mul, abs_of_pos (div_pos hR hh)]
    have hm : |t - stateMidpoint delta| ≤ stateHalfWidth delta := by
      rw [abs_le]
      unfold stateMidpoint stateHalfWidth
      constructor <;> linarith
    unfold pulseRadius
    calc
      (P0 + 2) / stateHalfWidth delta * |t - stateMidpoint delta| ≤
          (P0 + 2) / stateHalfWidth delta * stateHalfWidth delta := by gcongr
      _ = P0 + 2 := by field_simp
  unfold pi1
  rw [pi2_eq_self hP0 harg]
  field_simp
  ring

theorem pi1Deriv_eq_one {delta P0 t : ℝ} (hdelta : 0 < delta)
    (hP0 : 1 < P0) (htlow : stateLower delta ≤ t) (hthigh : t ≤ stateUpper) :
    pi1Deriv delta P0 t = 1 := by
  have hh : 0 < stateHalfWidth delta := by
    unfold stateHalfWidth stateUpper stateLower
    linarith
  have hR : 0 < pulseRadius P0 := by unfold pulseRadius; linarith
  have harg :
      |pulseRadius P0 / stateHalfWidth delta * (t - stateMidpoint delta)| ≤
        P0 + 2 := by
    rw [abs_mul, abs_of_pos (div_pos hR hh)]
    have hm : |t - stateMidpoint delta| ≤ stateHalfWidth delta := by
      rw [abs_le]
      unfold stateMidpoint stateHalfWidth
      constructor <;> linarith
    unfold pulseRadius
    calc
      (P0 + 2) / stateHalfWidth delta * |t - stateMidpoint delta| ≤
          (P0 + 2) / stateHalfWidth delta * stateHalfWidth delta := by gcongr
      _ = P0 + 2 := by field_simp
  exact pi2Deriv_eq_one harg

theorem pi1_range_bounds {delta P0 t : ℝ} (hdelta : 0 < delta) (hP0 : 1 < P0) :
    stateLower delta - stateExcess delta P0 ≤ pi1 delta P0 t ∧
      pi1 delta P0 t ≤ stateUpper + stateExcess delta P0 := by
  have hh : 0 < stateHalfWidth delta := by
    unfold stateHalfWidth stateUpper stateLower
    linarith
  have hR : 0 < pulseRadius P0 := by unfold pulseRadius; linarith
  have hp := pi2_abs_le (t := pulseRadius P0 / stateHalfWidth delta *
    (t - stateMidpoint delta)) hP0
  rw [abs_le] at hp
  have hmL : stateMidpoint delta = stateLower delta + stateHalfWidth delta := by
    unfold stateMidpoint stateHalfWidth
    ring
  have hmU : stateMidpoint delta = stateUpper - stateHalfWidth delta := by
    unfold stateMidpoint stateHalfWidth
    ring
  have hscale : stateHalfWidth delta / pulseRadius P0 * (P0 + 5 / 2) =
      stateHalfWidth delta + stateExcess delta P0 := by
    unfold stateExcess
    simp only [pulseRadius]
    field_simp [hR.ne']
    ring
  unfold pi1
  constructor
  · have hm := mul_le_mul_of_nonneg_left hp.1 (div_nonneg hh.le hR.le)
    nlinarith
  · have hm := mul_le_mul_of_nonneg_left hp.2 (div_nonneg hh.le hR.le)
    nlinarith

theorem pi1_range {delta P0 : ℝ} (hdelta : 0 < delta) (hP0 : 1 < P0) :
    Set.range (pi1 delta P0) =
      Set.Icc (stateLower delta - stateExcess delta P0)
        (stateUpper + stateExcess delta P0) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨t, rfl⟩
    exact pi1_range_bounds hdelta hP0
  · intro z hz
    have hh : 0 < stateHalfWidth delta := by
      unfold stateHalfWidth stateUpper stateLower
      linarith
    have hR : 0 < pulseRadius P0 := by unfold pulseRadius; linarith
    let y := pulseRadius P0 / stateHalfWidth delta * (z - stateMidpoint delta)
    have hy : y ∈ Set.Icc (-(P0 + 5 / 2)) (P0 + 5 / 2) := by
      rcases hz with ⟨hzl, hzu⟩
      unfold stateExcess at hzl hzu
      dsimp [y]
      have hmL : stateMidpoint delta = stateLower delta + stateHalfWidth delta := by
        unfold stateMidpoint stateHalfWidth
        ring
      have hmU : stateMidpoint delta = stateUpper - stateHalfWidth delta := by
        unfold stateMidpoint stateHalfWidth
        ring
      have he : pulseRadius P0 *
          (stateHalfWidth delta / (2 * pulseRadius P0)) = stateHalfWidth delta / 2 := by
        field_simp [hR.ne']
      constructor
      · rw [div_mul_eq_mul_div]
        change -(P0 + 5 / 2) ≤
          pulseRadius P0 * (z - stateMidpoint delta) / stateHalfWidth delta
        apply (le_div_iff₀ hh).2
        have hzscaled := mul_le_mul_of_nonneg_left hzl hR.le
        have hB : (P0 + 5 / 2) * stateHalfWidth delta =
            pulseRadius P0 * stateHalfWidth delta + stateHalfWidth delta / 2 := by
          simp only [pulseRadius]
          ring
        nlinarith
      · rw [div_mul_eq_mul_div]
        change pulseRadius P0 * (z - stateMidpoint delta) / stateHalfWidth delta ≤
          P0 + 5 / 2
        apply (div_le_iff₀ hh).2
        have hzscaled := mul_le_mul_of_nonneg_left hzu hR.le
        have hB : (P0 + 5 / 2) * stateHalfWidth delta =
            pulseRadius P0 * stateHalfWidth delta + stateHalfWidth delta / 2 := by
          simp only [pulseRadius]
          ring
        nlinarith
    rw [← pi2_range hP0] at hy
    rcases hy with ⟨x, hx⟩
    refine ⟨stateMidpoint delta + stateHalfWidth delta / pulseRadius P0 * x, ?_⟩
    unfold pi1
    have harg : pulseRadius P0 / stateHalfWidth delta *
        (stateMidpoint delta + stateHalfWidth delta / pulseRadius P0 * x -
          stateMidpoint delta) = x := by
      field_simp [hh.ne', hR.ne']
      ring
    rw [harg, hx]
    unfold y
    field_simp [hh.ne', hR.ne']
    ring

theorem pi1_range_subset {delta P0 B : ℝ} (hdelta : 0 < delta) (hP0 : 1 < P0)
    (hexcess : stateExcess delta P0 ≤ min (delta / 2) (B - 3)) :
    Set.range (pi1 delta P0) ⊆ Set.Icc (-delta) B := by
  rw [pi1_range hdelta hP0]
  rintro z ⟨hzl, hzu⟩
  change -delta / 2 - stateExcess delta P0 ≤ z at hzl
  change z ≤ 3 + stateExcess delta P0 at hzu
  have heleft : stateExcess delta P0 ≤ delta / 2 :=
    le_trans hexcess (min_le_left _ _)
  have heright : stateExcess delta P0 ≤ B - 3 :=
    le_trans hexcess (min_le_right _ _)
  exact ⟨by linarith, by linarith⟩

theorem stateLower_eq_neg_two_tauS (delta : ℝ) :
    stateLower delta = -2 * tauS delta := by
  unfold stateLower tauS
  ring

/-! ## Integrated soft-hinge templates -/

def leftHingeIntegrand (a b u : ℝ) : ℝ :=
  1 - Lambda1 ((u - a) / (b - a))

def rightHingeIntegrand (a b u : ℝ) : ℝ :=
  Lambda1 ((u - a) / (b - a))

/-- Equation `eq:left-hinge-template`. -/
def leftHinge (a b t : ℝ) : ℝ :=
  ∫ u in t..b, leftHingeIntegrand a b u

/-- Equation `eq:right-hinge-template`. -/
def rightHinge (a b t : ℝ) : ℝ :=
  ∫ u in a..t, rightHingeIntegrand a b u

def leftHingeDeriv (a b t : ℝ) : ℝ :=
  -1 + Lambda1 ((t - a) / (b - a))

def rightHingeDeriv (a b t : ℝ) : ℝ :=
  Lambda1 ((t - a) / (b - a))

def leftHingeSecond (a b t : ℝ) : ℝ := deriv (leftHingeDeriv a b) t
def rightHingeSecond (a b t : ℝ) : ℝ := deriv (rightHingeDeriv a b) t

theorem leftHingeDeriv_contDiff (a b : ℝ) {k : ℕ∞} :
    ContDiff ℝ k (leftHingeDeriv a b) := by
  unfold leftHingeDeriv
  exact contDiff_const.add
    (Lambda1_contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b - a)))

theorem rightHingeDeriv_contDiff (a b : ℝ) {k : ℕ∞} :
    ContDiff ℝ k (rightHingeDeriv a b) := by
  unfold rightHingeDeriv
  exact Lambda1_contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b - a))

theorem hasDerivAt_leftHingeDeriv (a b t : ℝ) :
    HasDerivAt (leftHingeDeriv a b) (leftHingeSecond a b t) t := by
  unfold leftHingeSecond
  exact ((leftHingeDeriv_contDiff a b (k := (1 : ℕ∞))).differentiable
    (by norm_num) t).hasDerivAt

theorem hasDerivAt_rightHingeDeriv (a b t : ℝ) :
    HasDerivAt (rightHingeDeriv a b) (rightHingeSecond a b t) t := by
  unfold rightHingeSecond
  exact ((rightHingeDeriv_contDiff a b (k := (1 : ℕ∞))).differentiable
    (by norm_num) t).hasDerivAt

theorem leftHingeIntegrand_continuous (a b : ℝ) :
    Continuous (leftHingeIntegrand a b) := by
  unfold leftHingeIntegrand
  exact continuous_const.sub
    (Lambda1_continuous.comp ((continuous_id.sub continuous_const).div_const (b - a)))

theorem rightHingeIntegrand_continuous (a b : ℝ) :
    Continuous (rightHingeIntegrand a b) := by
  unfold rightHingeIntegrand
  exact Lambda1_continuous.comp
    ((continuous_id.sub continuous_const).div_const (b - a))

theorem hasDerivAt_leftHinge (a b t : ℝ) :
    HasDerivAt (leftHinge a b) (leftHingeDeriv a b t) t := by
  have hc := leftHingeIntegrand_continuous a b
  have h := intervalIntegral.integral_hasDerivAt_left
    (hc.intervalIntegrable t b)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · unfold leftHingeDeriv leftHingeIntegrand
    ring

theorem hasDerivAt_rightHinge (a b t : ℝ) :
    HasDerivAt (rightHinge a b) (rightHingeDeriv a b t) t := by
  have hc := rightHingeIntegrand_continuous a b
  have h := intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable a t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · rfl

theorem deriv_leftHinge (a b t : ℝ) :
    deriv (leftHinge a b) t = leftHingeDeriv a b t :=
  (hasDerivAt_leftHinge a b t).deriv

theorem deriv_rightHinge (a b t : ℝ) :
    deriv (rightHinge a b) t = rightHingeDeriv a b t :=
  (hasDerivAt_rightHinge a b t).deriv

theorem leftHinge_contDiff_one (a b : ℝ) : ContDiff ℝ 1 (leftHinge a b) := by
  apply contDiff_one_iff_deriv.2
  refine ⟨(fun t ↦ (hasDerivAt_leftHinge a b t).differentiableAt), ?_⟩
  have heq : deriv (leftHinge a b) = leftHingeDeriv a b := by
    funext t
    exact deriv_leftHinge a b t
  rw [heq]
  unfold leftHingeDeriv
  exact continuous_const.add
    (Lambda1_continuous.comp ((continuous_id.sub continuous_const).div_const (b - a)))

theorem rightHinge_contDiff_one (a b : ℝ) : ContDiff ℝ 1 (rightHinge a b) := by
  apply contDiff_one_iff_deriv.2
  refine ⟨(fun t ↦ (hasDerivAt_rightHinge a b t).differentiableAt), ?_⟩
  have heq : deriv (rightHinge a b) = rightHingeDeriv a b := by
    funext t
    exact deriv_rightHinge a b t
  rw [heq]
  unfold rightHingeDeriv
  exact Lambda1_continuous.comp
    ((continuous_id.sub continuous_const).div_const (b - a))

theorem leftHinge_contDiff (a b : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (leftHinge a b) := by
  apply contDiff_infty_iff_deriv.2
  refine ⟨(fun t ↦ (hasDerivAt_leftHinge a b t).differentiableAt), ?_⟩
  have heq : deriv (leftHinge a b) = leftHingeDeriv a b := by
    funext t
    exact deriv_leftHinge a b t
  rw [heq]
  unfold leftHingeDeriv
  exact contDiff_const.add
    (Lambda1_contDiff.comp ((contDiff_id.sub contDiff_const).div_const (b - a)))

theorem rightHinge_contDiff (a b : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (rightHinge a b) := by
  apply contDiff_infty_iff_deriv.2
  refine ⟨(fun t ↦ (hasDerivAt_rightHinge a b t).differentiableAt), ?_⟩
  have heq : deriv (rightHinge a b) = rightHingeDeriv a b := by
    funext t
    exact deriv_rightHinge a b t
  rw [heq]
  unfold rightHingeDeriv
  exact Lambda1_contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const (b - a))

theorem leftHingeDeriv_mem (a b t : ℝ) :
    leftHingeDeriv a b t ∈ Set.Icc (-1 : ℝ) 0 := by
  unfold leftHingeDeriv
  constructor <;> linarith [Lambda1_nonneg ((t-a)/(b-a)), Lambda1_le_one ((t-a)/(b-a))]

theorem rightHingeDeriv_mem (a b t : ℝ) :
    rightHingeDeriv a b t ∈ Set.Icc (0 : ℝ) 1 := by
  exact Lambda1_mem_unitInterval _

theorem leftHinge_antitone (a b : ℝ) : Antitone (leftHinge a b) := by
  apply antitone_of_deriv_nonpos
  · exact fun t ↦ (hasDerivAt_leftHinge a b t).differentiableAt
  · intro t
    rw [deriv_leftHinge]
    exact (leftHingeDeriv_mem a b t).2

theorem rightHinge_monotone (a b : ℝ) : Monotone (rightHinge a b) := by
  apply monotone_of_deriv_nonneg
  · exact fun t ↦ (hasDerivAt_rightHinge a b t).differentiableAt
  · intro t
    rw [deriv_rightHinge]
    exact (rightHingeDeriv_mem a b t).1

theorem leftHingeDeriv_eq_neg_one {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    leftHingeDeriv a b t = -1 := by
  have harg : (t - a) / (b - a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hab).le
  simp [leftHingeDeriv, Lambda1_eq_zero_of_nonpos harg]

theorem leftHingeDeriv_eq_zero {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    leftHingeDeriv a b t = 0 := by
  have harg : 1 ≤ (t - a) / (b - a) := by
    apply (le_div_iff₀ (sub_pos.mpr hab)).2
    linarith
  simp [leftHingeDeriv, Lambda1_eq_one_of_one_le harg]

theorem rightHingeDeriv_eq_zero {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    rightHingeDeriv a b t = 0 := by
  have harg : (t - a) / (b - a) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hab).le
  exact Lambda1_eq_zero_of_nonpos harg

theorem rightHingeDeriv_eq_one {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    rightHingeDeriv a b t = 1 := by
  have harg : 1 ≤ (t - a) / (b - a) := by
    apply (le_div_iff₀ (sub_pos.mpr hab)).2
    linarith
  exact Lambda1_eq_one_of_one_le harg

theorem leftHingeSecond_eq_zero_of_not_mem {a b t : ℝ} (hab : a < b)
    (ht : t ∉ Set.Icc a b) : leftHingeSecond a b t = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  unfold leftHingeSecond
  rcases ht with ht | ht
  · have heq : Set.EqOn (leftHingeDeriv a b) (fun _ : ℝ ↦ -1) (Set.Iio a) := by
      intro x hx
      exact leftHingeDeriv_eq_neg_one hab hx.le
    simpa using heq.deriv isOpen_Iio ht
  · have heq : Set.EqOn (leftHingeDeriv a b) (fun _ : ℝ ↦ 0) (Set.Ioi b) := by
      intro x hx
      exact leftHingeDeriv_eq_zero hab hx.le
    simpa using heq.deriv isOpen_Ioi ht

theorem rightHingeSecond_eq_zero_of_not_mem {a b t : ℝ} (hab : a < b)
    (ht : t ∉ Set.Icc a b) : rightHingeSecond a b t = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  unfold rightHingeSecond
  rcases ht with ht | ht
  · have heq : Set.EqOn (rightHingeDeriv a b) (fun _ : ℝ ↦ 0) (Set.Iio a) := by
      intro x hx
      exact rightHingeDeriv_eq_zero hab hx.le
    simpa using heq.deriv isOpen_Iio ht
  · have heq : Set.EqOn (rightHingeDeriv a b) (fun _ : ℝ ↦ 1) (Set.Ioi b) := by
      intro x hx
      exact rightHingeDeriv_eq_one hab hx.le
    simpa using heq.deriv isOpen_Ioi ht

theorem leftHingeSecond_bounded {a b : ℝ} (hab : a < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |leftHingeSecond a b t| ≤ C := by
  have hcont : Continuous (fun t : ℝ ↦ |leftHingeSecond a b t|) := by
    unfold leftHingeSecond
    exact ((leftHingeDeriv_contDiff a b (k := (2 : ℕ∞))).continuous_deriv
      (by norm_num)).abs
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.continuousOn)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc a b
  · exact (hC _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  · rw [leftHingeSecond_eq_zero_of_not_mem hab ht, abs_zero]
    exact le_max_right _ _

theorem rightHingeSecond_bounded {a b : ℝ} (hab : a < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |rightHingeSecond a b t| ≤ C := by
  have hcont : Continuous (fun t : ℝ ↦ |rightHingeSecond a b t|) := by
    unfold rightHingeSecond
    exact ((rightHingeDeriv_contDiff a b (k := (2 : ℕ∞))).continuous_deriv
      (by norm_num)).abs
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.continuousOn)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc a b
  · exact (hC _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  · rw [rightHingeSecond_eq_zero_of_not_mem hab ht, abs_zero]
    exact le_max_right _ _

theorem leftHinge_self (a b : ℝ) : leftHinge a b b = 0 := by simp [leftHinge]
theorem rightHinge_self (a b : ℝ) : rightHinge a b a = 0 := by simp [rightHinge]

theorem leftHinge_eq_zero_of_right {a b t : ℝ} (hab : a < b) (ht : b ≤ t) :
    leftHinge a b t = 0 := by
  unfold leftHinge
  calc
    (∫ u in t..b, leftHingeIntegrand a b u) = ∫ _u in t..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hbu : b ≤ u := by
        rw [uIcc_comm, uIcc_of_le ht] at hu
        exact hu.1
      have harg : 1 ≤ (u - a) / (b - a) := by
        apply (le_div_iff₀ (sub_pos.mpr hab)).2
        linarith
      simp [leftHingeIntegrand, Lambda1_eq_one_of_one_le harg]
    _ = 0 := by simp

theorem rightHinge_eq_zero_of_left {a b t : ℝ} (hab : a < b) (ht : t ≤ a) :
    rightHinge a b t = 0 := by
  unfold rightHinge
  calc
    (∫ u in a..t, rightHingeIntegrand a b u) = ∫ _u in a..t, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hua : u ≤ a := by
        rw [uIcc_comm, uIcc_of_le ht] at hu
        exact hu.2
      have harg : (u - a) / (b - a) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hua) (sub_pos.mpr hab).le
      exact Lambda1_eq_zero_of_nonpos harg
    _ = 0 := by simp

theorem leftHinge_nonneg {a b : ℝ} (hab : a < b) (t : ℝ) :
    0 ≤ leftHinge a b t := by
  by_cases ht : b ≤ t
  · rw [leftHinge_eq_zero_of_right hab ht]
  · have hmono := leftHinge_antitone a b (le_of_not_ge ht)
    simpa [leftHinge_self] using hmono

theorem rightHinge_nonneg {a b : ℝ} (hab : a < b) (t : ℝ) :
    0 ≤ rightHinge a b t := by
  by_cases ht : t ≤ a
  · rw [rightHinge_eq_zero_of_left hab ht]
  · have hmono := rightHinge_monotone a b (le_of_not_ge ht)
    simpa [rightHinge_self] using hmono

/-- The three concrete members in Equation `eq:Sigma-family`. -/
def Sigma1 (theta t : ℝ) : ℝ := leftHinge 1 (1 + theta) t
def Sigma2 (tau t : ℝ) : ℝ := leftHinge (-tau) 0 t
def Sigma3 (P0 P1 K r : ℝ) : ℝ := K * rightHinge (P0 ^ 2) (P1 ^ 2) r

def Sigma1Deriv (theta t : ℝ) : ℝ := leftHingeDeriv 1 (1 + theta) t
def Sigma2Deriv (tau t : ℝ) : ℝ := leftHingeDeriv (-tau) 0 t
def Sigma3Deriv (P0 P1 K r : ℝ) : ℝ := K * rightHingeDeriv (P0 ^ 2) (P1 ^ 2) r
def Sigma1Second (theta t : ℝ) : ℝ := leftHingeSecond 1 (1 + theta) t
def Sigma2Second (tau t : ℝ) : ℝ := leftHingeSecond (-tau) 0 t
def Sigma3Second (P0 P1 K r : ℝ) : ℝ := K * rightHingeSecond (P0 ^ 2) (P1 ^ 2) r

theorem hasDerivAt_Sigma1 (theta t : ℝ) :
    HasDerivAt (Sigma1 theta) (Sigma1Deriv theta t) t :=
  hasDerivAt_leftHinge 1 (1 + theta) t

theorem hasDerivAt_Sigma2 (tau t : ℝ) :
    HasDerivAt (Sigma2 tau) (Sigma2Deriv tau t) t :=
  hasDerivAt_leftHinge (-tau) 0 t

theorem hasDerivAt_Sigma3 (P0 P1 K r : ℝ) :
    HasDerivAt (Sigma3 P0 P1 K) (Sigma3Deriv P0 P1 K r) r := by
  exact (hasDerivAt_rightHinge (P0 ^ 2) (P1 ^ 2) r).const_mul K

theorem hasDerivAt_Sigma1Deriv (theta t : ℝ) :
    HasDerivAt (Sigma1Deriv theta) (Sigma1Second theta t) t :=
  hasDerivAt_leftHingeDeriv _ _ _

theorem hasDerivAt_Sigma2Deriv (tau t : ℝ) :
    HasDerivAt (Sigma2Deriv tau) (Sigma2Second tau t) t :=
  hasDerivAt_leftHingeDeriv _ _ _

theorem hasDerivAt_Sigma3Deriv (P0 P1 K r : ℝ) :
    HasDerivAt (Sigma3Deriv P0 P1 K) (Sigma3Second P0 P1 K r) r := by
  exact (hasDerivAt_rightHingeDeriv (P0 ^ 2) (P1 ^ 2) r).const_mul K

theorem Sigma1_contDiff_one (theta : ℝ) : ContDiff ℝ 1 (Sigma1 theta) :=
  leftHinge_contDiff_one _ _

theorem Sigma2_contDiff_one (tau : ℝ) : ContDiff ℝ 1 (Sigma2 tau) :=
  leftHinge_contDiff_one _ _

theorem Sigma3_contDiff_one (P0 P1 K : ℝ) : ContDiff ℝ 1 (Sigma3 P0 P1 K) := by
  apply contDiff_one_iff_deriv.2
  refine ⟨(fun r ↦ (hasDerivAt_Sigma3 P0 P1 K r).differentiableAt), ?_⟩
  have heq : deriv (Sigma3 P0 P1 K) = Sigma3Deriv P0 P1 K := by
    funext r
    exact (hasDerivAt_Sigma3 P0 P1 K r).deriv
  rw [heq]
  unfold Sigma3Deriv rightHingeDeriv
  exact continuous_const.mul
    (Lambda1_continuous.comp
      ((continuous_id.sub continuous_const).div_const (P1 ^ 2 - P0 ^ 2)))

theorem Sigma1_contDiff (theta : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (Sigma1 theta) := leftHinge_contDiff _ _

theorem Sigma2_contDiff (tau : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (Sigma2 tau) := leftHinge_contDiff _ _

theorem Sigma3_contDiff (P0 P1 K : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (Sigma3 P0 P1 K) := by
  exact contDiff_const.mul (rightHinge_contDiff _ _)

theorem Sigma1_antitone (theta : ℝ) : Antitone (Sigma1 theta) :=
  leftHinge_antitone _ _

theorem Sigma2_antitone (tau : ℝ) : Antitone (Sigma2 tau) :=
  leftHinge_antitone _ _

theorem Sigma3_monotone {P0 P1 K : ℝ} (hK : 0 ≤ K) :
    Monotone (Sigma3 P0 P1 K) := by
  intro s t hst
  unfold Sigma3
  exact mul_le_mul_of_nonneg_left (rightHinge_monotone _ _ hst) hK

theorem Sigma1_nonneg {theta : ℝ} (htheta : 0 < theta) (t : ℝ) :
    0 ≤ Sigma1 theta t := leftHinge_nonneg (by linarith) t

theorem Sigma2_nonneg {tau : ℝ} (htau : 0 < tau) (t : ℝ) :
    0 ≤ Sigma2 tau t := leftHinge_nonneg (by linarith) t

theorem Sigma3_nonneg {P0 P1 K : ℝ} (hP : P0 ^ 2 < P1 ^ 2)
    (hK : 0 ≤ K) (r : ℝ) : 0 ≤ Sigma3 P0 P1 K r := by
  exact mul_nonneg hK (rightHinge_nonneg hP r)

theorem Sigma1_eq_zero {theta t : ℝ} (htheta : 0 < theta)
    (ht : 1 + theta ≤ t) : Sigma1 theta t = 0 :=
  leftHinge_eq_zero_of_right (by linarith) ht

theorem Sigma2_eq_zero {tau t : ℝ} (htau : 0 < tau) (ht : 0 ≤ t) :
    Sigma2 tau t = 0 := leftHinge_eq_zero_of_right (by linarith) ht

theorem Sigma3_eq_zero {P0 P1 K r : ℝ} (hP : P0 ^ 2 < P1 ^ 2)
    (hr : r ≤ P0 ^ 2) : Sigma3 P0 P1 K r = 0 := by
  simp [Sigma3, rightHinge_eq_zero_of_left hP hr]

theorem Sigma1Deriv_eq_neg_one {theta t : ℝ} (htheta : 0 < theta) (ht : t ≤ 1) :
    Sigma1Deriv theta t = -1 := leftHingeDeriv_eq_neg_one (by linarith) ht

theorem Sigma1Deriv_eq_zero {theta t : ℝ} (htheta : 0 < theta)
    (ht : 1 + theta ≤ t) : Sigma1Deriv theta t = 0 :=
  leftHingeDeriv_eq_zero (by linarith) ht

theorem Sigma2Deriv_eq_neg_one {tau t : ℝ} (htau : 0 < tau) (ht : t ≤ -tau) :
    Sigma2Deriv tau t = -1 := leftHingeDeriv_eq_neg_one (by linarith) ht

theorem Sigma2Deriv_zero {tau : ℝ} (htau : 0 < tau) : Sigma2Deriv tau 0 = 0 :=
  leftHingeDeriv_eq_zero (by linarith) le_rfl

theorem Sigma3Deriv_eq_zero {P0 P1 K r : ℝ} (hP : P0 ^ 2 < P1 ^ 2)
    (hr : r ≤ P0 ^ 2) : Sigma3Deriv P0 P1 K r = 0 := by
  simp [Sigma3Deriv, rightHingeDeriv_eq_zero hP hr]

theorem Sigma3Deriv_eq_K {P0 P1 K r : ℝ} (hP : P0 ^ 2 < P1 ^ 2)
    (hr : P1 ^ 2 ≤ r) : Sigma3Deriv P0 P1 K r = K := by
  simp [Sigma3Deriv, rightHingeDeriv_eq_one hP hr]

theorem Sigma3Deriv_mem {P0 P1 K r : ℝ} (hK : 0 ≤ K) :
    Sigma3Deriv P0 P1 K r ∈ Set.Icc (0 : ℝ) K := by
  unfold Sigma3Deriv
  rcases rightHingeDeriv_mem (P0 ^ 2) (P1 ^ 2) r with ⟨h0, h1⟩
  exact ⟨mul_nonneg hK h0, mul_le_of_le_one_right hK h1⟩

theorem Sigma1Second_bounded {theta : ℝ} (htheta : 0 < theta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |Sigma1Second theta t| ≤ C := by
  exact leftHingeSecond_bounded (by linarith)

theorem Sigma2Second_bounded {tau : ℝ} (htau : 0 < tau) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |Sigma2Second tau t| ≤ C := by
  exact leftHingeSecond_bounded (by linarith)

theorem Sigma3Second_eq_zero_of_not_mem {P0 P1 K r : ℝ}
    (hP : P0 ^ 2 < P1 ^ 2) (hr : r ∉ Set.Icc (P0 ^ 2) (P1 ^ 2)) :
    Sigma3Second P0 P1 K r = 0 := by
  simp [Sigma3Second, rightHingeSecond_eq_zero_of_not_mem hP hr]

theorem Sigma3Second_bounded {P0 P1 K : ℝ} (hP : P0 ^ 2 < P1 ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |Sigma3Second P0 P1 K r| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := rightHingeSecond_bounded hP
  refine ⟨|K| * C, mul_nonneg (abs_nonneg K) hC, ?_⟩
  intro r
  unfold Sigma3Second
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hbound r) (abs_nonneg K)

theorem Sigma3_weightedSecond_bounded {P0 P1 K : ℝ} (hP : P0 ^ 2 < P1 ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |r * Sigma3Second P0 P1 K r| ≤ C := by
  have hcontSecond : Continuous (Sigma3Second P0 P1 K) := by
    unfold Sigma3Second rightHingeSecond
    exact continuous_const.mul
      ((rightHingeDeriv_contDiff (P0 ^ 2) (P1 ^ 2) (k := (2 : ℕ∞))).continuous_deriv
        (by norm_num))
  have hcont : Continuous (fun r : ℝ ↦ |r * Sigma3Second P0 P1 K r|) :=
    (continuous_id.mul hcontSecond).abs
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.continuousOn)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro r
  by_cases hr : r ∈ Set.Icc (P0 ^ 2) (P1 ^ 2)
  · exact (hC _ ⟨r, hr, rfl⟩).trans (le_max_left _ _)
  · rw [Sigma3Second_eq_zero_of_not_mem hP hr, mul_zero, abs_zero]
    exact le_max_right _ _

end

end NCCLowerBoundVerification
