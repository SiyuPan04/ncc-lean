import NCPLVerification.HardPrimalDifferentiability

/-!
# Joint differentiability and actual joint gradient
-/

namespace NCPLVerification

noncomputable section

theorem differentiableAt_hardWeightedBlock_joint {T N : Nat}
    (x : EVec T) (y : EVec (T * N)) (i : Fin T) :
    DifferentiableAt ℝ
      (fun p : EVec T × EVec (T * N) ↦
        hardDualWeightedBlock p.1 p.2 i) (x, y) := by
  have hsnd : DifferentiableAt ℝ
      (fun p : EVec T × EVec (T * N) ↦ p.2) (x, y) := differentiableAt_snd
  apply differentiableAt_pi.2
  intro j
  have hcoord : DifferentiableAt ℝ
      (fun p : EVec T × EVec (T * N) ↦
        p.2 (finProdFinEquiv (i, j))) (x, y) := by fun_prop
  have h := hcoord.const_mul (1 / Real.sqrt (innerD N j))
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  · funext p
    simp [hardDualWeightedBlock, toWeightedCoordinates, dualBlock]
    ring

theorem hasFDerivAt_carmonRhoSq_joint_zero {T M : Nat}
    (x : EVec T) (y : EVec M) (i : Fin T)
    (hrho : carmonRho x i = 0) :
    HasFDerivAt
      (fun p : EVec T × EVec M ↦ carmonRhoSq p.1 i)
      (0 : (EVec T × EVec M) →L[ℝ] ℝ) (x, y) := by
  have hbase := hasEVecFDerivAt_carmonRhoSq_zero x i hrho
  unfold HasEVecFDerivAt at hbase
  have hfst : HasFDerivAt
      (fun p : EVec T × EVec M ↦ p.1)
      (ContinuousLinearMap.fst ℝ (EVec T) (EVec M)) (x, y) :=
    hasFDerivAt_fst
  have hc := hbase.comp (x, y) hfst
  change HasFDerivAt
    (fun p : EVec T × EVec M ↦ carmonRhoSq p.1 i) _ (x, y) at hc
  convert hc using 1
  all_goals try { apply Module.ext <;> rfl }
  · apply ContinuousLinearMap.ext
    intro p
    simp

theorem differentiableAt_hardBlockValue_joint {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N))
    (i : Fin T) :
    DifferentiableAt ℝ
      (fun p : EVec T × EVec (T * N) ↦
        hardBlockValue N lambdaWall eta p.1 p.2 i) (x, y) := by
  have hfst : DifferentiableAt ℝ
      (fun p : EVec T × EVec (T * N) ↦ p.1) (x, y) := by fun_prop
  have hrhoComp := (differentiableAt_carmonRho_standard x i).comp (x, y) hfst
  have hrhoDiff : DifferentiableAt ℝ
      (fun p : EVec T × EVec (T * N) ↦ carmonRho p.1 i) (x, y) := by
    change DifferentiableAt ℝ
      (fun p : EVec T × EVec (T * N) ↦ carmonRho p.1 i) (x, y) at hrhoComp
    exact hrhoComp
  have hAComp := (differentiableAt_carmonOuterA_standard x i).comp (x, y) hfst
  have hADiff : DifferentiableAt ℝ
      (fun p : EVec T × EVec (T * N) ↦ carmonOuterA p.1 i) (x, y) := by
    change DifferentiableAt ℝ
      (fun p : EVec T × EVec (T * N) ↦ carmonOuterA p.1 i) (x, y) at hAComp
    exact hAComp
  have huDiff := differentiableAt_hardWeightedBlock_joint x y i
  by_cases hrho : carmonRho x i = 0
  · have hr2zero := hasFDerivAt_carmonRhoSq_joint_zero
      (M := T * N) x y i hrho
    have hp := differentiableAt_perspectiveDelay_comp_zero_variable hN
      lambdaWall eta carmonAmax
      (fun p : EVec T × EVec (T * N) ↦ carmonRho p.1 i)
      (fun p : EVec T × EVec (T * N) ↦ carmonRhoSq p.1 i)
      (fun p : EVec T × EVec (T * N) ↦ carmonOuterA p.1 i)
      (fun p : EVec T × EVec (T * N) ↦
        hardDualWeightedBlock p.1 p.2 i) (x, y)
      (fun p ↦ carmonRho_nonneg p.1 i)
      (fun p ↦ carmonOuterA_nonneg p.1 i)
      carmonAmax_nonneg (fun p ↦ carmonOuterA_le p.1 i)
      (fun p ↦ carmonRho_sq p.1 i) hrho hr2zero huDiff
    have hbase := hr2zero.differentiableAt.const_mul (-carmonPhiCap)
    change DifferentiableAt ℝ (fun p : EVec T × EVec (T * N) ↦
      -carmonPhiCap * carmonRhoSq p.1 i +
        perspectiveDelay N lambdaWall eta (carmonRho p.1 i)
          (carmonOuterA p.1 i) (hardDualWeightedBlock p.1 p.2 i)) (x, y)
    have hd := hbase.add hp
    change DifferentiableAt ℝ (fun p : EVec T × EVec (T * N) ↦
      -carmonPhiCap * carmonRhoSq p.1 i +
        perspectiveDelay N lambdaWall eta (carmonRho p.1 i)
          (carmonOuterA p.1 i) (hardDualWeightedBlock p.1 p.2 i)) (x, y) at hd
    exact hd
  · have hrhopos : 0 < carmonRho x i :=
      lt_of_le_of_ne (carmonRho_nonneg x i) (Ne.symm hrho)
    have hp := differentiableAt_perspectiveDelay_comp_pos_variable
      lambdaWall eta
      (fun p : EVec T × EVec (T * N) ↦ carmonRho p.1 i)
      (fun p : EVec T × EVec (T * N) ↦ carmonOuterA p.1 i)
      (fun p : EVec T × EVec (T * N) ↦
        hardDualWeightedBlock p.1 p.2 i) (x, y)
      hrhoDiff hADiff huDiff hrhopos
    have hr2Comp :=
      (differentiableAt_carmonRhoSq_standard x i).comp (x, y) hfst
    have hr2Diff : DifferentiableAt ℝ
        (fun p : EVec T × EVec (T * N) ↦ carmonRhoSq p.1 i) (x, y) := by
      change DifferentiableAt ℝ
        (fun p : EVec T × EVec (T * N) ↦ carmonRhoSq p.1 i) (x, y)
        at hr2Comp
      exact hr2Comp
    have hbase := hr2Diff.const_mul (-carmonPhiCap)
    change DifferentiableAt ℝ (fun p : EVec T × EVec (T * N) ↦
      -carmonPhiCap * carmonRhoSq p.1 i +
        perspectiveDelay N lambdaWall eta (carmonRho p.1 i)
          (carmonOuterA p.1 i) (hardDualWeightedBlock p.1 p.2 i)) (x, y)
    have hd := hbase.add hp
    change DifferentiableAt ℝ (fun p : EVec T × EVec (T * N) ↦
      -carmonPhiCap * carmonRhoSq p.1 i +
        perspectiveDelay N lambdaWall eta (carmonRho p.1 i)
          (carmonOuterA p.1 i) (hardDualWeightedBlock p.1 p.2 i)) (x, y) at hd
    exact hd

theorem differentiableAt_hardF_joint {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N)) :
    DifferentiableAt ℝ (Function.uncurry (hardF T N lambdaWall eta)) (x, y) := by
  unfold hardF Function.uncurry
  exact DifferentiableAt.fun_sum fun i _ ↦
    differentiableAt_hardBlockValue_joint hN lambdaWall eta x y i

theorem differentiable_hardF_joint {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) :
    Differentiable ℝ (Function.uncurry (hardF T N lambdaWall eta)) := by
  rintro ⟨x, y⟩
  exact differentiableAt_hardF_joint hN lambdaWall eta x y

/-- The two coordinate fields used by the hard-instance certificates jointly
represent the actual Fréchet derivative, as required by Definition 1.1. -/
theorem hardF_representsJointGradient {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) :
    RepresentsJointGradient (hardF T N lambdaWall eta)
      (hardGradX T N lambdaWall eta) (hardGradY T N lambdaWall eta) := by
  constructor
  · exact differentiable_hardF_joint hN lambdaWall eta
  · intro x y hx hy
    let J := Function.uncurry (hardF T N lambdaWall eta)
    have hJ : HasFDerivAt J (fderiv ℝ J (x, y)) (x, y) :=
      (differentiableAt_hardF_joint hN lambdaWall eta x y).hasFDerivAt
    have hinX : HasFDerivAt
        (fun w : EVec T ↦ (w, y))
        (ContinuousLinearMap.inl ℝ (EVec T) (EVec (T * N))) x :=
      hasFDerivAt_prodMk_left x y
    have hcompX := hJ.comp x hinX
    change HasFDerivAt
      (fun w : EVec T ↦ hardF T N lambdaWall eta w y)
      ((fderiv ℝ J (x, y)).comp
        (ContinuousLinearMap.inl ℝ (EVec T) (EVec (T * N)))) x at hcompX
    have hpartialX := hasEVecFDerivAt_hardF_x_gradient hN lambdaWall eta x y
    unfold HasEVecFDerivAt at hpartialX
    have hxmap :
        (fderiv ℝ J (x, y)).comp
            (ContinuousLinearMap.inl ℝ (EVec T) (EVec (T * N))) =
          evecDot (hardGradX T N lambdaWall eta x y) :=
      hcompX.unique hpartialX
    have hinY : HasFDerivAt
        (fun v : EVec (T * N) ↦ (x, v))
        (ContinuousLinearMap.inr ℝ (EVec T) (EVec (T * N))) y :=
      hasFDerivAt_prodMk_right x y
    have hcompY := hJ.comp y hinY
    change HasFDerivAt
      (fun v : EVec (T * N) ↦ hardF T N lambdaWall eta x v)
      ((fderiv ℝ J (x, y)).comp
        (ContinuousLinearMap.inr ℝ (EVec T) (EVec (T * N)))) y at hcompY
    have hpartialY := hasEVecFDerivAt_hardF_y_gradient
      T N hN lambdaWall eta x y
    unfold HasEVecFDerivAt at hpartialY
    have hymap :
        (fderiv ℝ J (x, y)).comp
            (ContinuousLinearMap.inr ℝ (EVec T) (EVec (T * N))) =
          evecDot (hardGradY T N lambdaWall eta x y) :=
      hcompY.unique hpartialY
    have hxapply := congrArg (fun q : EVec T →L[ℝ] ℝ ↦ q hx) hxmap
    have hyapply := congrArg (fun q : EVec (T * N) →L[ℝ] ℝ ↦ q hy) hymap
    simp only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply] at hxapply hyapply
    change (fderiv ℝ J (x, y)) (hx, hy) = _
    rw [show (hx, hy) = (hx, 0) + (0, hy) by ext <;> simp, map_add,
      hxapply, hyapply, evecDot_apply, evecDot_apply]

end

end NCPLVerification
