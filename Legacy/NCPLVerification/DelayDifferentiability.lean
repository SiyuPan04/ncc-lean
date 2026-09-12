import NCPLVerification.InnerDifferentiability
import NCPLVerification.DelayBlock

/-!
# Analytic derivatives of the delay block

This file proves that the fields used in the delay-block PL estimates are the
actual Frechet gradients, not merely algebraic coordinate formulas.
-/

namespace NCPLVerification

noncomputable section

theorem hasEVecFDerivAt_innerGamma {N : Nat} (z : EVec N) :
    HasEVecFDerivAt innerGamma (evecDot (innerGammaField N z)) z := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasEVecFDerivAt
  by_cases hN : 0 < N
  · let last : Fin N := ⟨N - 1, Nat.sub_lt hN (by omega)⟩
    have hcoord : HasFDerivAt (fun w : EVec N => w last) (evecProj last) z :=
      (evecProj last).hasFDerivAt
    have hsig := (hasDerivAt_sigma (z last)).hasFDerivAt.comp z hcoord
    convert hsig using 1
    · funext w
      simp [innerGamma, hN, last]
    · apply ContinuousLinearMap.ext
      intro h
      simp [evecDot, innerGammaField, hN, last]
      ring
  · have hconst : HasFDerivAt (fun _ : EVec N => (0 : ℝ)) 0 z :=
      hasFDerivAt_const (𝕜 := ℝ) 0 z
    convert hconst using 1
    · funext w
      simp [innerGamma, hN]
    · apply ContinuousLinearMap.ext
      intro h
      simp [evecDot, innerGammaField, hN]

theorem evecDot_linear_combination {N : Nat} (a b : ℝ) (g k : EVec N) :
    evecDot (fun i => a * g i - b * k i) =
      a • evecDot g - b • evecDot k := by
  apply ContinuousLinearMap.ext
  intro h
  simp only [evecDot_apply, sub_apply, smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- `delayGradient` is the actual gradient of `delayG`. -/
theorem hasEVecFDerivAt_delayG (N : Nat) (lambdaWall eta a : ℝ)
    (z : EVec N) :
    HasEVecFDerivAt (delayG N lambdaWall eta a)
      (evecDot (delayGradient N lambdaWall eta a z)) z := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasEVecFDerivAt
  have hgamma : HasFDerivAt innerGamma (evecDot (innerGammaField N z)) z := by
    simpa only [HasEVecFDerivAt] using hasEVecFDerivAt_innerGamma z
  have hinner : HasFDerivAt (innerH N lambdaWall)
      (evecDot (innerGradient N lambdaWall z)) z := by
    simpa only [HasEVecFDerivAt] using
      hasEVecFDerivAt_innerH_gradient N lambdaWall z
  have h := hgamma.const_mul a |>.sub (hinner.const_mul eta)
  have heq : evecDot (delayGradient N lambdaWall eta a z) =
      a • evecDot (innerGammaField N z) -
        eta • evecDot (innerGradient N lambdaWall z) := by
    change evecDot (fun i => a * innerGammaField N z i -
      eta * innerGradient N lambdaWall z i) = _
    exact evecDot_linear_combination a eta _ _
  rw [heq]
  convert h using 1
  funext w
  rfl

end

end NCPLVerification
