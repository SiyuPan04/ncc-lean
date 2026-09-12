import NCPLVerification.DelayDifferentiability
import NCPLVerification.Perspective

/-!
# Actual dual derivatives of the perspective block
-/

namespace NCPLVerification

noncomputable section

def rescaleCLM {N : Nat} (rho : ℝ) : EVec N →L[ℝ] EVec N := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact LinearMap.toContinuousLinearMap
    ({ toFun := rescaleEVec rho
       map_add' := by
         intro x y
         funext i
         simp [rescaleEVec, add_div]
       map_smul' := by
         intro c x
         funext i
         simp [rescaleEVec]
         ring } : EVec N →ₗ[ℝ] EVec N)

@[simp] theorem rescaleCLM_apply {N : Nat} (rho : ℝ) (h : EVec N) :
    rescaleCLM rho h = rescaleEVec rho h := by
  unfold rescaleCLM
  rfl

theorem perspective_positive_derivative_map {N : Nat} {rho : ℝ}
    (hrho : 0 < rho) (g : EVec N) :
    rho ^ 2 • (evecDot g ∘L rescaleCLM rho) =
      evecDot (fun i => rho * g i) := by
  apply ContinuousLinearMap.ext
  intro h
  change rho ^ 2 * evecDot g (rescaleCLM rho h) =
    ∑ i : Fin N, rho * g i * h i
  rw [evecDot_apply, rescaleCLM_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [rescaleEVec]
  field_simp

theorem hasEVecFDerivAt_perspectiveDelay_pos {N : Nat} {rho : ℝ}
    (hrho : 0 < rho) (lambdaWall eta A : ℝ) (u : EVec N) :
    HasEVecFDerivAt (perspectiveDelay N lambdaWall eta rho A)
      (evecDot (perspectiveGradient N lambdaWall eta rho A u)) u := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasEVecFDerivAt
  have hscale : HasFDerivAt (rescaleEVec rho) (rescaleCLM rho) u := by
    refine (rescaleCLM (N := N) rho).hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun h => ?_)
    exact (rescaleCLM_apply rho h).symm
  have hdelay : HasFDerivAt
      (delayG N lambdaWall eta (A / rho ^ 2))
      (evecDot (delayGradient N lambdaWall eta (A / rho ^ 2)
        (rescaleEVec rho u))) (rescaleEVec rho u) := by
    simpa only [HasEVecFDerivAt] using
      hasEVecFDerivAt_delayG N lambdaWall eta (A / rho ^ 2)
        (rescaleEVec rho u)
  have hcomp := hdelay.comp u hscale
  have hmul := hcomp.const_mul (rho ^ 2)
  have hmap := perspective_positive_derivative_map hrho
    (delayGradient N lambdaWall eta (A / rho ^ 2) (rescaleEVec rho u))
  rw [hmap] at hmul
  have hfun (w : EVec N) :
      perspectiveDelay N lambdaWall eta rho A w =
        rho ^ 2 * (delayG N lambdaWall eta (A / rho ^ 2) ∘
          rescaleEVec rho) w := by
    simpa [Function.comp_def] using
      perspectiveDelay_pos hrho lambdaWall eta A w
  have hmul' := hmul.congr_of_eventuallyEq
    (Filter.Eventually.of_forall hfun)
  have hgrad :
      evecDot (fun i => rho * delayGradient N lambdaWall eta
        (A / rho ^ 2) (rescaleEVec rho u) i) =
        evecDot (perspectiveGradient N lambdaWall eta rho A u) := by
    apply ContinuousLinearMap.ext
    intro h
    simp [perspectiveGradient, hrho]
  exact hmul'.congr_fderiv hgrad

def innerWallEnergyFDeriv (N : Nat) (z : EVec N) : EVec N →L[ℝ] ℝ :=
  evecDot (fun i => -2 * innerD N i * negPart (z i))

theorem hasEVecFDerivAt_innerWallEnergy (N : Nat) (z : EVec N) :
    HasEVecFDerivAt (innerWallEnergy N) (innerWallEnergyFDeriv N z) z := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasEVecFDerivAt
  have hsum : HasFDerivAt
      (fun w : EVec N => ∑ i : Fin N, innerD N i * negPart (w i) ^ 2)
      (∑ i : Fin N, (innerD N i) • innerWallSqFDeriv z i) z := by
    apply HasFDerivAt.fun_sum
    intro i _
    have hi : HasFDerivAt (fun w : EVec N => negPart (w i) ^ 2)
        (innerWallSqFDeriv z i) z := by
      simpa only [HasEVecFDerivAt] using hasEVecFDerivAt_innerWall_sq z i
    simpa only using hi.const_mul (innerD N i)
  have hfun (w : EVec N) : innerWallEnergy N w =
      ∑ i : Fin N, innerD N i * negPart (w i) ^ 2 := by rfl
  have hsum' := hsum.congr_of_eventuallyEq
    (Filter.Eventually.of_forall hfun)
  have hmap : (∑ i : Fin N, (innerD N i) • innerWallSqFDeriv z i) =
      innerWallEnergyFDeriv N z := by
    apply ContinuousLinearMap.ext
    intro h
    rw [continuousLinearMap_sum_apply]
    simp only [smul_apply, smul_eq_mul, innerWallSqFDeriv_apply,
      innerWallEnergyFDeriv, evecDot_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact hsum'.congr_fderiv hmap

theorem hasEVecFDerivAt_perspectiveDelay_zero (N : Nat)
    (lambdaWall eta A : ℝ) (u : EVec N) :
    HasEVecFDerivAt (perspectiveDelay N lambdaWall eta 0 A)
      (evecDot (perspectiveGradient N lambdaWall eta 0 A u)) u := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasEVecFDerivAt
  have hwall : HasFDerivAt (innerWallEnergy N) (innerWallEnergyFDeriv N u) u := by
    simpa only [HasEVecFDerivAt] using hasEVecFDerivAt_innerWallEnergy N u
  have h := hwall.const_mul (-eta * lambdaWall)
  have hfun (w : EVec N) :
      perspectiveDelay N lambdaWall eta 0 A w =
        -eta * lambdaWall * innerWallEnergy N w := by
    simp [perspectiveDelay]
  have h' := h.congr_of_eventuallyEq
    (Filter.Eventually.of_forall hfun)
  have hmap : (-eta * lambdaWall) • innerWallEnergyFDeriv N u =
      evecDot (perspectiveGradient N lambdaWall eta 0 A u) := by
    apply ContinuousLinearMap.ext
    intro k
    simp [perspectiveGradient, innerWallEnergyFDeriv, evecDot]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  exact h'.congr_fderiv hmap

theorem hasEVecFDerivAt_perspectiveDelay {N : Nat} {rho : ℝ}
    (hrho : 0 ≤ rho) (lambdaWall eta A : ℝ) (u : EVec N) :
    HasEVecFDerivAt (perspectiveDelay N lambdaWall eta rho A)
      (evecDot (perspectiveGradient N lambdaWall eta rho A u)) u := by
  rcases hrho.eq_or_lt with rfl | hpos
  · exact hasEVecFDerivAt_perspectiveDelay_zero N lambdaWall eta A u
  · exact hasEVecFDerivAt_perspectiveDelay_pos hpos lambdaWall eta A u

end

end NCPLVerification
