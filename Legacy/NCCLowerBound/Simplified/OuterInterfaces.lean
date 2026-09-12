import NCCLowerBoundVerification.Lower.ClipSoftHinge

/-!
# Scalar interfaces for the simplified memory--pulse chain

This is the literal construction in Appendix `app:scalar-interfaces` of
`NC_C_Lower_Bound_simplified.tex`.  The manuscript's `vartheta` is the
already verified `Lambda1`; its odd saturation is the already verified
`saturationTemplate`.
-/

namespace NCCLowerBound
namespace Simplified

noncomputable section

open Set MeasureTheory
open scoped Interval
open NCCLowerBoundVerification

/-- The flat step `vartheta`. -/
abbrev theta : ℝ → ℝ := Lambda1

/-- State saturation `C = S_{2,1}`. -/
def stateClip : ℝ → ℝ := saturationTemplate 2 1

/-- Frontier switch `A(t) = vartheta ((5 C(t)-1)/4)`. -/
def frontierSwitch (t : ℝ) : ℝ :=
  theta ((5 * stateClip t - 1) / 4)

/-- Pulse saturation `P = S_{21,1}`. -/
def pulseClip : ℝ → ℝ := saturationTemplate 21 1

theorem stateClip_contDiff : ContDiff ℝ (⊤ : ℕ∞) stateClip := by
  simpa [stateClip] using
    (saturationTemplate_contDiff (R := (2 : ℝ)) (width := (1 : ℝ))
      (by norm_num) (by norm_num))

theorem pulseClip_contDiff : ContDiff ℝ (⊤ : ℕ∞) pulseClip := by
  simpa [pulseClip] using
    (saturationTemplate_contDiff (R := (21 : ℝ)) (width := (1 : ℝ))
      (by norm_num) (by norm_num))

theorem frontierSwitch_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) frontierSwitch := by
  unfold frontierSwitch theta
  exact Lambda1_contDiff.comp
    (((contDiff_const.mul stateClip_contDiff).sub contDiff_const).div_const 4)

theorem stateClip_monotone : Monotone stateClip := by
  simpa [stateClip] using saturationTemplate_monotone (2 : ℝ) 1

theorem pulseClip_monotone : Monotone pulseClip := by
  simpa [pulseClip] using saturationTemplate_monotone (21 : ℝ) 1

theorem stateClip_eq_self {t : ℝ} (ht : |t| ≤ 2) : stateClip t = t := by
  simpa [stateClip] using
    (saturationTemplate_eq_self (R := (2 : ℝ)) (width := (1 : ℝ))
      (t := t) (by norm_num) (by norm_num) ht)

theorem pulseClip_eq_self {t : ℝ} (ht : |t| ≤ 21) : pulseClip t = t := by
  simpa [pulseClip] using
    (saturationTemplate_eq_self (R := (21 : ℝ)) (width := (1 : ℝ))
      (t := t) (by norm_num) (by norm_num) ht)

theorem stateClip_abs_le_three (t : ℝ) : |stateClip t| ≤ 3 := by
  have h := saturationTemplate_range_bounds (R := (2 : ℝ)) (width := (1 : ℝ))
    (t := t) (by norm_num) (by norm_num)
  rw [abs_le]
  constructor <;> dsimp [stateClip] at h ⊢ <;> linarith

theorem pulseClip_abs_le_twentyTwo (t : ℝ) : |pulseClip t| ≤ 22 := by
  have h := saturationTemplate_range_bounds (R := (21 : ℝ)) (width := (1 : ℝ))
    (t := t) (by norm_num) (by norm_num)
  rw [abs_le]
  constructor <;> dsimp [pulseClip] at h ⊢ <;> linarith

theorem frontierSwitch_mem_unitInterval (t : ℝ) :
    frontierSwitch t ∈ Set.Icc (0 : ℝ) 1 := by
  exact Lambda1_mem_unitInterval _

theorem frontierSwitch_eq_zero_of_le_fifth {t : ℝ}
    (ht : t ≤ (1 / 5 : ℝ)) : frontierSwitch t = 0 := by
  have hmono : stateClip t ≤ stateClip (1 / 5 : ℝ) := stateClip_monotone ht
  have hedge : stateClip (1 / 5 : ℝ) = 1 / 5 :=
    stateClip_eq_self (by norm_num [abs_of_nonneg] : |(1 / 5 : ℝ)| ≤ 2)
  have harg : (5 * stateClip t - 1) / 4 ≤ 0 := by
    rw [hedge] at hmono
    linarith
  exact Lambda1_eq_zero_of_nonpos harg

theorem frontierSwitch_eq_one_of_one_le {t : ℝ}
    (ht : (1 : ℝ) ≤ t) : frontierSwitch t = 1 := by
  have hmono : stateClip (1 : ℝ) ≤ stateClip t := stateClip_monotone ht
  have hedge : stateClip (1 : ℝ) = 1 := stateClip_eq_self (by norm_num)
  have harg : (1 : ℝ) ≤ (5 * stateClip t - 1) / 4 := by
    rw [hedge] at hmono
    linarith
  exact Lambda1_eq_one_of_one_le harg

theorem frontierSwitch_zero : frontierSwitch 0 = 0 := by
  exact frontierSwitch_eq_zero_of_le_fifth (by norm_num)

theorem frontierSwitch_one : frontierSwitch 1 = 1 := by
  exact frontierSwitch_eq_one_of_one_le le_rfl

theorem stateClip_zero : stateClip 0 = 0 := by
  exact stateClip_eq_self (by norm_num)

theorem pulseClip_zero : pulseClip 0 = 0 := by
  exact pulseClip_eq_self (by norm_num)

/-- The derivative of either saturation lies in `[0,1]`. -/
theorem stateClip_deriv_mem_unitInterval (t : ℝ) :
    deriv stateClip t ∈ Set.Icc (0 : ℝ) 1 := by
  simpa [stateClip] using
    saturationTemplate_deriv_mem_unitInterval (2 : ℝ) 1 t

theorem pulseClip_deriv_mem_unitInterval (t : ℝ) :
    deriv pulseClip t ∈ Set.Icc (0 : ℝ) 1 := by
  simpa [pulseClip] using
    saturationTemplate_deriv_mem_unitInterval (21 : ℝ) 1 t

theorem stateClip_deriv_eq_one {t : ℝ} (ht : |t| ≤ 2) :
    deriv stateClip t = 1 := by
  simpa [stateClip, deriv_saturationTemplate] using
    (clipIntegrand_eq_one (R := (2 : ℝ)) (width := (1 : ℝ))
      (t := t) (by norm_num) ht)

theorem pulseClip_deriv_eq_one {t : ℝ} (ht : |t| ≤ 21) :
    deriv pulseClip t = 1 := by
  simpa [pulseClip, deriv_saturationTemplate] using
    (clipIntegrand_eq_one (R := (21 : ℝ)) (width := (1 : ℝ))
      (t := t) (by norm_num) ht)

/-- The switch is locally constant throughout its closed low region. -/
theorem frontierSwitch_deriv_eq_zero_of_le_fifth {t : ℝ}
    (ht : t ≤ (1 / 5 : ℝ)) : deriv frontierSwitch t = 0 := by
  refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic (1 / 5 : ℝ) t ht)
  refine (hasDerivWithinAt_const t (Set.Iic (1 / 5 : ℝ)) 0).congr_of_mem
    (fun x hx => ?_) ht
  exact frontierSwitch_eq_zero_of_le_fifth hx

/-- On the working low interval the state factor has derivative one. -/
theorem deriv_stateClip_mul_one_sub_switch_eq_one {t : ℝ}
    (hlow : -(1 / 10 : ℝ) ≤ t) (hhigh : t ≤ (1 / 5 : ℝ)) :
    deriv (fun u => stateClip u * (1 - frontierSwitch u)) t = 1 := by
  have hC : HasDerivAt stateClip 1 t := by
    have ht : |t| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    have hdifferentiable : DifferentiableAt ℝ stateClip t :=
      stateClip_contDiff.differentiable (by simp) t
    simpa only [stateClip_deriv_eq_one ht] using hdifferentiable.hasDerivAt
  have hA : HasDerivAt frontierSwitch 0 t := by
    have hdifferentiable : DifferentiableAt ℝ frontierSwitch t :=
      frontierSwitch_contDiff.differentiable (by simp) t
    simpa only [frontierSwitch_deriv_eq_zero_of_le_fifth hhigh] using
      hdifferentiable.hasDerivAt
  have hAval : frontierSwitch t = 0 := frontierSwitch_eq_zero_of_le_fifth hhigh
  have hCval : stateClip t = t := by
    apply stateClip_eq_self
    rw [abs_le]
    constructor <;> linarith
  have hprod := hC.mul ((hasDerivAt_const t 1).sub hA)
  change deriv (stateClip * ((fun _ : ℝ => 1) - frontierSwitch)) t = 1
  simpa [hAval, hCval] using hprod.deriv

end

end Simplified
end NCCLowerBound
