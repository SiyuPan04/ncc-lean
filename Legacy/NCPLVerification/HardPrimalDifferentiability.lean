import NCPLVerification.HardDifferentiability
import NCPLVerification.OuterActivation
import NCPLVerification.PerspectivePrimalDifferentiability

/-!
# Actual primal derivatives of the hard blocks
-/

namespace NCPLVerification

noncomputable section

theorem differentiableAt_carmonRho_standard {T : Nat}
    (x : EVec T) (i : Fin T) :
    DifferentiableAt ℝ (fun w : EVec T ↦ carmonRho w i) x := by
  have h := (hasCarmonFDerivAt_carmonRho x i).differentiableAt
  convert h using 1

theorem differentiableAt_carmonRhoSq_standard {T : Nat}
    (x : EVec T) (i : Fin T) :
    DifferentiableAt ℝ (fun w : EVec T ↦ carmonRhoSq w i) x := by
  have h := (hasCarmonFDerivAt_carmonRhoSq x i).differentiableAt
  convert h using 1

theorem differentiableAt_carmonOuterA_standard {T : Nat}
    (x : EVec T) (i : Fin T) :
    DifferentiableAt ℝ (fun w : EVec T ↦ carmonOuterA w i) x := by
  have h := (hasCarmonFDerivAt_carmonOuterA x i).differentiableAt
  convert h using 1

theorem carmonRhoSqFDeriv_eq_zero_of_rho_eq_zero {T : Nat}
    (x : EVec T) (i : Fin T) (hrho : carmonRho x i = 0) :
    carmonRhoSqFDeriv x i = 0 := by
  have hi : i.1 ≠ 0 := by
    intro hi
    have hone : carmonRho x i = 1 := by
      rw [carmonRho_eq_profile]
      simp [hi]
    linarith
  have hc := abs_carmonRhoSqPrevDeriv_le x i
  rw [hrho, mul_zero] at hc
  have hcoeff : carmonRhoSqPrevDeriv x i = 0 :=
    abs_eq_zero.mp (le_antisymm hc (abs_nonneg _))
  simp [carmonRhoSqFDeriv, hi, hcoeff]

theorem hasEVecFDerivAt_carmonRhoSq_zero {T : Nat}
    (x : EVec T) (i : Fin T) (hrho : carmonRho x i = 0) :
    HasEVecFDerivAt (fun w : EVec T ↦ carmonRhoSq w i) 0 x := by
  have h := hasCarmonFDerivAt_carmonRhoSq x i
  rw [carmonRhoSqFDeriv_eq_zero_of_rho_eq_zero x i hrho] at h
  unfold HasEVecFDerivAt
  unfold HasCarmonFDerivAt at h
  convert h using 1

theorem differentiableAt_hardBlockValue_x {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N))
    (i : Fin T) :
    EVecDifferentiableAt
      (fun w : EVec T ↦ hardBlockValue N lambdaWall eta w y i) x := by
  unfold EVecDifferentiableAt
  by_cases hrho : carmonRho x i = 0
  · have hp := hasEVecFDerivAt_perspectiveDelay_comp_zero hN
        lambdaWall eta carmonAmax (hardDualWeightedBlock x y i)
        (fun w : EVec T ↦ carmonRho w i)
        (fun w : EVec T ↦ carmonRhoSq w i)
        (fun w : EVec T ↦ carmonOuterA w i) x
        (fun w ↦ carmonRho_nonneg w i)
        (fun w ↦ carmonOuterA_nonneg w i)
        carmonAmax_nonneg
        (fun w ↦ carmonOuterA_le w i)
        (fun w ↦ carmonRho_sq w i) hrho
        (hasEVecFDerivAt_carmonRhoSq_zero x i hrho)
    have hr2 := hasEVecFDerivAt_carmonRhoSq_zero x i hrho
    have hbase := hr2.const_mul (-carmonPhiCap)
    have hsum := hbase.add hp
    change DifferentiableAt ℝ (fun w : EVec T ↦
      -carmonPhiCap * carmonRhoSq w i +
        perspectiveDelay N lambdaWall eta (carmonRho w i)
          (carmonOuterA w i) (hardDualWeightedBlock x y i)) x
    have hd := hsum.differentiableAt
    change DifferentiableAt ℝ (fun w : EVec T ↦
      -carmonPhiCap * carmonRhoSq w i +
        perspectiveDelay N lambdaWall eta (carmonRho w i)
          (carmonOuterA w i) (hardDualWeightedBlock x y i)) x at hd
    exact hd
  · have hrhopos : 0 < carmonRho x i :=
      lt_of_le_of_ne (carmonRho_nonneg x i) (Ne.symm hrho)
    have hp := differentiableAt_perspectiveDelay_comp_pos
      lambdaWall eta (hardDualWeightedBlock x y i)
      (fun w : EVec T ↦ carmonRho w i)
      (fun w : EVec T ↦ carmonOuterA w i) x
      (differentiableAt_carmonRho_standard x i)
      (differentiableAt_carmonOuterA_standard x i) hrhopos
    have hbase : DifferentiableAt ℝ
        (fun w : EVec T ↦ -carmonPhiCap * carmonRhoSq w i) x :=
      (differentiableAt_const (c := -carmonPhiCap)).mul
        (differentiableAt_carmonRhoSq_standard x i)
    change DifferentiableAt ℝ (fun w : EVec T ↦
      -carmonPhiCap * carmonRhoSq w i +
        perspectiveDelay N lambdaWall eta (carmonRho w i)
          (carmonOuterA w i) (hardDualWeightedBlock x y i)) x
    have hd := hbase.add hp
    change DifferentiableAt ℝ (fun w : EVec T ↦
      -carmonPhiCap * carmonRhoSq w i +
        perspectiveDelay N lambdaWall eta (carmonRho w i)
          (carmonOuterA w i) (hardDualWeightedBlock x y i)) x at hd
    exact hd

def hardBlockXFDeriv {T N : Nat} (lambdaWall eta : ℝ)
    (x : EVec T) (y : EVec (T * N)) (i : Fin T) : EVec T →L[ℝ] ℝ :=
  evecFderiv (fun w : EVec T ↦ hardBlockValue N lambdaWall eta w y i) x

theorem hasEVecFDerivAt_hardBlockValue_x {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N))
    (i : Fin T) :
    HasEVecFDerivAt
      (fun w : EVec T ↦ hardBlockValue N lambdaWall eta w y i)
      (hardBlockXFDeriv lambdaWall eta x y i) x := by
  exact (differentiableAt_hardBlockValue_x hN lambdaWall eta x y i).hasEVecFDerivAt

def hardXFDeriv (T N : Nat) (lambdaWall eta : ℝ)
    (x : EVec T) (y : EVec (T * N)) : EVec T →L[ℝ] ℝ :=
  ∑ i : Fin T, hardBlockXFDeriv lambdaWall eta x y i

def hardGradX (T N : Nat) (lambdaWall eta : ℝ)
    (x : EVec T) (y : EVec (T * N)) : EVec T :=
  continuousLinearMapCoordinates (hardXFDeriv T N lambdaWall eta x y)

theorem hardXFDeriv_apply_eq_hardGradX (T N : Nat) (lambdaWall eta : ℝ)
    (x h : EVec T) (y : EVec (T * N)) :
    hardXFDeriv T N lambdaWall eta x y h =
      ∑ i : Fin T, hardGradX T N lambdaWall eta x y i * h i := by
  exact continuousLinearMap_apply_eq_coordinates _ h

theorem hasEVecFDerivAt_hardF_x {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N)) :
    HasEVecFDerivAt (fun w : EVec T ↦ hardF T N lambdaWall eta w y)
      (hardXFDeriv T N lambdaWall eta x y) x := by
  unfold HasEVecFDerivAt hardXFDeriv hardF
  exact HasFDerivAt.fun_sum fun i _ ↦ by
    simpa only [HasEVecFDerivAt] using
      hasEVecFDerivAt_hardBlockValue_x hN lambdaWall eta x y i

theorem hasEVecFDerivAt_hardF_x_gradient {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N)) :
    HasEVecFDerivAt (fun w : EVec T ↦ hardF T N lambdaWall eta w y)
      (evecDot (hardGradX T N lambdaWall eta x y)) x := by
  have h := hasEVecFDerivAt_hardF_x hN lambdaWall eta x y
  apply h.congr_fderiv
  apply ContinuousLinearMap.ext
  intro k
  rw [hardXFDeriv_apply_eq_hardGradX, evecDot_apply]

end

end NCPLVerification
