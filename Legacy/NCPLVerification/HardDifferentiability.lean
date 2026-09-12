import NCPLVerification.HardInstance
import NCPLVerification.PerspectiveDifferentiability

/-!
# Actual Euclidean dual derivative of the hard instance

The dual field used in the PL certificate is not merely a formal vector:
this file proves that it represents the genuine Frechet derivative of the
assembled objective with the primal variable fixed.
-/

namespace NCPLVerification

noncomputable section

/-- The block extraction followed by the article's diagonal inverse scaling,
as a continuous linear map on Euclidean dual coordinates. -/
def hardWeightedBlockCLM {T N : Nat} (i : Fin T) :
    EVec (T * N) →L[ℝ] EVec N := by
  letI : AddCommGroup (EVec (T * N)) :=
    Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec (T * N)) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec (T * N)) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact LinearMap.toContinuousLinearMap
    ({ toFun := fun y : EVec (T * N) ↦
          toWeightedCoordinates (dualBlock y i)
       map_add' := by
         intro y y'
         funext j
         simp [toWeightedCoordinates, dualBlock, add_div]
       map_smul' := by
         intro c y
         funext j
         simp [toWeightedCoordinates, dualBlock]
         ring } : EVec (T * N) →ₗ[ℝ] EVec N)

@[simp] theorem hardWeightedBlockCLM_apply {T N : Nat} (i : Fin T)
    (x : EVec T) (y : EVec (T * N)) :
    hardWeightedBlockCLM i y = hardDualWeightedBlock x y i := by
  unfold hardWeightedBlockCLM hardDualWeightedBlock
  rfl

theorem hasFDerivAt_hardDualWeightedBlock {T N : Nat}
    (x : EVec T) (y : EVec (T * N)) (i : Fin T) :
    HasFDerivAt (fun v : EVec (T * N) ↦ hardDualWeightedBlock x v i)
      (hardWeightedBlockCLM i) y := by
  letI : AddCommGroup (EVec (T * N)) :=
    Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec (T * N)) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec (T * N)) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  refine (hardWeightedBlockCLM (N := N) i).hasFDerivAt.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun v ↦ ?_)
  unfold hardDualWeightedBlock hardWeightedBlockCLM
  rfl

/-- Derivative of one assembled hard block with respect to all Euclidean
dual coordinates. -/
def hardBlockYFDeriv {T N : Nat} (lambdaWall eta : ℝ)
    (x : EVec T) (y : EVec (T * N)) (i : Fin T) :
    EVec (T * N) →L[ℝ] ℝ :=
  evecDot
      (perspectiveGradient N lambdaWall eta (carmonRho x i)
        (carmonOuterA x i) (hardDualWeightedBlock x y i)) ∘L
    hardWeightedBlockCLM i

theorem hasEVecFDerivAt_hardBlockValue_y {T N : Nat}
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N)) (i : Fin T) :
    HasEVecFDerivAt
      (fun v : EVec (T * N) ↦ hardBlockValue N lambdaWall eta x v i)
      (hardBlockYFDeriv lambdaWall eta x y i) y := by
  letI : AddCommGroup (EVec (T * N)) :=
    Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec (T * N)) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec (T * N)) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasEVecFDerivAt
  have hu := hasEVecFDerivAt_perspectiveDelay
    (carmonRho_nonneg x i) lambdaWall eta (carmonOuterA x i)
      (hardDualWeightedBlock x y i)
  have hblock := hasFDerivAt_hardDualWeightedBlock x y i
  have hu' : HasFDerivAt
      (perspectiveDelay N lambdaWall eta (carmonRho x i) (carmonOuterA x i))
      (evecDot (perspectiveGradient N lambdaWall eta (carmonRho x i)
        (carmonOuterA x i) (hardDualWeightedBlock x y i)))
      (hardDualWeightedBlock x y i) := by
    simpa only [HasEVecFDerivAt] using hu
  have hcomp : HasEVecFDerivAt
      (fun v : EVec (T * N) ↦
        perspectiveDelay N lambdaWall eta (carmonRho x i)
          (carmonOuterA x i) (hardDualWeightedBlock x v i))
      (hardBlockYFDeriv lambdaWall eta x y i) y := by
    unfold HasEVecFDerivAt
    have hc := hu'.comp y hblock
    change HasFDerivAt
      (fun v : EVec (T * N) ↦
        perspectiveDelay N lambdaWall eta (carmonRho x i)
          (carmonOuterA x i) (hardDualWeightedBlock x v i)) _ y at hc
    simpa only [hardBlockYFDeriv] using hc
  unfold HasEVecFDerivAt at hcomp
  have hconst : HasFDerivAt
      (fun _ : EVec (T * N) ↦ -carmonPhiCap * carmonRhoSq x i)
      0 y := hasFDerivAt_const (𝕜 := ℝ)
        (-carmonPhiCap * carmonRhoSq x i) y
  convert hconst.add hcomp using 1
  · funext v
    simp only [Pi.add_apply]
    rfl
  · simp

def hardYFDeriv (T N : Nat) (lambdaWall eta : ℝ)
    (x : EVec T) (y : EVec (T * N)) : EVec (T * N) →L[ℝ] ℝ :=
  ∑ i : Fin T, hardBlockYFDeriv lambdaWall eta x y i

theorem hasEVecFDerivAt_hardF_y (T N : Nat) (lambdaWall eta : ℝ)
    (x : EVec T) (y : EVec (T * N)) :
    HasEVecFDerivAt (fun v ↦ hardF T N lambdaWall eta x v)
      (hardYFDeriv T N lambdaWall eta x y) y := by
  letI : AddCommGroup (EVec (T * N)) :=
    Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec (T * N)) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec (T * N)) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasEVecFDerivAt hardYFDeriv hardF
  exact HasFDerivAt.fun_sum fun i _ ↦ by
    simpa only [HasEVecFDerivAt] using
      hasEVecFDerivAt_hardBlockValue_y lambdaWall eta x y i

theorem hardBlockYFDeriv_apply {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y h : EVec (T * N))
    (i : Fin T) :
    hardBlockYFDeriv lambdaWall eta x y i h =
      ∑ j : Fin N,
        toEuclideanGradient
            (perspectiveGradient N lambdaWall eta (carmonRho x i)
              (carmonOuterA x i) (hardDualWeightedBlock x y i)) j *
          h (finProdFinEquiv (i, j)) := by
  unfold hardBlockYFDeriv
  rw [ContinuousLinearMap.comp_apply, evecDot_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [hardWeightedBlockCLM_apply i x h]
  simp only [hardDualWeightedBlock, toWeightedCoordinates,
    dualBlock, toEuclideanGradient]
  ring

theorem hardYFDeriv_eq_hardGradY (T N : Nat) (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N)) :
    hardYFDeriv T N lambdaWall eta x y =
      evecDot (hardGradY T N lambdaWall eta x y) := by
  apply ContinuousLinearMap.ext
  intro h
  unfold hardYFDeriv
  rw [continuousLinearMap_sum_apply, evecDot_apply]
  simp_rw [hardBlockYFDeriv_apply hN]
  calc
    (∑ i : Fin T, ∑ j : Fin N,
        toEuclideanGradient
            (perspectiveGradient N lambdaWall eta (carmonRho x i)
              (carmonOuterA x i) (hardDualWeightedBlock x y i)) j *
          h (finProdFinEquiv (i, j))) =
        ∑ p : Fin T × Fin N,
          toEuclideanGradient
              (perspectiveGradient N lambdaWall eta (carmonRho x p.1)
                (carmonOuterA x p.1) (hardDualWeightedBlock x y p.1)) p.2 *
            h (finProdFinEquiv p) := by rw [Fintype.sum_prod_type]
    _ = ∑ p : Fin T × Fin N,
        hardGradY T N lambdaWall eta x y (finProdFinEquiv p) *
          h (finProdFinEquiv p) := by
        apply Finset.sum_congr rfl
        intro p _
        simp [hardGradY, assembleDualBlocks]
    _ = ∑ k : Fin (T * N), hardGradY T N lambdaWall eta x y k * h k :=
      Equiv.sum_comp finProdFinEquiv
        (fun k : Fin (T * N) ↦ hardGradY T N lambdaWall eta x y k * h k)

/-- The vector `hardGradY` in the PL theorem is the actual Euclidean
gradient with respect to `y`. -/
theorem hasEVecFDerivAt_hardF_y_gradient (T N : Nat) (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N)) :
    HasEVecFDerivAt (fun v ↦ hardF T N lambdaWall eta x v)
      (evecDot (hardGradY T N lambdaWall eta x y)) y := by
  exact (hasEVecFDerivAt_hardF_y T N lambdaWall eta x y).congr_fderiv
    (hardYFDeriv_eq_hardGradY T N hN lambdaWall eta x y)

end

end NCPLVerification
