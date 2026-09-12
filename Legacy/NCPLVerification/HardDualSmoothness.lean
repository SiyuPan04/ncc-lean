import NCPLVerification.PerspectiveDualSmoothness
import NCPLVerification.HardInstance

/-!
# Uniform smoothness in the complete Euclidean dual variable

The dual blocks are orthogonal coordinate blocks.  Summing the one-block
estimate therefore introduces no factor depending on either chain length.
-/

namespace NCPLVerification

noncomputable section

@[simp] theorem assembleDualBlocks_dualBlock {T N : Nat}
    (y : EVec (T * N)) :
    assembleDualBlocks (fun i ↦ dualBlock y i) = y := by
  funext k
  let p := finProdFinEquiv.symm k
  have hpk : finProdFinEquiv p = k := finProdFinEquiv.apply_symm_apply k
  simp only [assembleDualBlocks, dualBlock]
  rw [hpk]

theorem vecSq_eq_sum_dualBlock {T N : Nat} (y : EVec (T * N)) :
    vecSq y = ∑ i : Fin T, vecSq (dualBlock y i) := by
  calc
    vecSq y = vecSq (assembleDualBlocks (fun i ↦ dualBlock y i)) := by
      rw [assembleDualBlocks_dualBlock]
    _ = ∑ i : Fin T, vecSq (dualBlock y i) := by
      unfold vecSq
      exact sum_assembleDualBlocks_sq _

theorem vecSq_assembleDualBlocks {T N : Nat} (b : Fin T → EVec N) :
    vecSq (assembleDualBlocks b) = ∑ i : Fin T, vecSq (b i) := by
  unfold vecSq
  exact sum_assembleDualBlocks_sq b

theorem dualBlock_sub {T N : Nat} (y y' : EVec (T * N)) (i : Fin T) :
    dualBlock (y - y') i = dualBlock y i - dualBlock y' i := by
  rfl

def hardBlockGradY (T N : Nat) (lambdaWall eta : ℝ)
    (x : EVec T) (y : EVec (T * N)) (i : Fin T) : EVec N :=
  toEuclideanGradient
    (perspectiveGradient N lambdaWall eta (carmonRho x i)
      (carmonOuterA x i) (hardDualWeightedBlock x y i))

theorem hardGradY_eq_assemble (T N : Nat) (lambdaWall eta : ℝ)
    (x : EVec T) (y : EVec (T * N)) :
    hardGradY T N lambdaWall eta x y =
      assembleDualBlocks (fun i ↦ hardBlockGradY T N lambdaWall eta x y i) := by
  rfl

theorem hardBlockGradY_lipschitz_in_y {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y y' : EVec (T * N))
    (i : Fin T) :
    vecSq
        (hardBlockGradY T N lambdaWall eta x y i -
          hardBlockGradY T N lambdaWall eta x y' i) ≤
      perspectiveDualSmoothCoeff lambdaWall eta carmonAmax *
        vecSq (dualBlock y i - dualBlock y' i) := by
  exact perspectiveEuclideanGradient_lipschitz hN
    (carmonRho_nonneg x i) (carmonOuterA_nonneg x i)
    carmonAmax_nonneg (carmonOuterA_le x i)
    (dualBlock y i) (dualBlock y' i)

/-- The `y → y` block of the hard-instance Hessian is bounded by a numerical
constant independent of both `T` and `N`. -/
theorem hardGradY_lipschitz_in_y {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y y' : EVec (T * N)) :
    vecSq
        (hardGradY T N lambdaWall eta x y -
          hardGradY T N lambdaWall eta x y') ≤
      perspectiveDualSmoothCoeff lambdaWall eta carmonAmax *
        vecSq (y - y') := by
  rw [hardGradY_eq_assemble, hardGradY_eq_assemble]
  have hdiff :
      assembleDualBlocks (fun i ↦ hardBlockGradY T N lambdaWall eta x y i) -
          assembleDualBlocks (fun i ↦ hardBlockGradY T N lambdaWall eta x y' i) =
        assembleDualBlocks (fun i ↦
          hardBlockGradY T N lambdaWall eta x y i -
            hardBlockGradY T N lambdaWall eta x y' i) := by
    funext k
    let p := finProdFinEquiv.symm k
    simp [assembleDualBlocks]
  rw [hdiff]
  rw [vecSq_assembleDualBlocks]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
    hardBlockGradY_lipschitz_in_y hN lambdaWall eta x y y' i
  calc
    (∑ i : Fin T, vecSq
        (hardBlockGradY T N lambdaWall eta x y i -
          hardBlockGradY T N lambdaWall eta x y' i)) ≤
        ∑ i : Fin T,
          perspectiveDualSmoothCoeff lambdaWall eta carmonAmax *
            vecSq (dualBlock y i - dualBlock y' i) := hsum
    _ = perspectiveDualSmoothCoeff lambdaWall eta carmonAmax *
        ∑ i : Fin T, vecSq (dualBlock y i - dualBlock y' i) := by
      rw [Finset.mul_sum]
    _ = perspectiveDualSmoothCoeff lambdaWall eta carmonAmax *
        vecSq (y - y') := by
      congr 1
      rw [vecSq_eq_sum_dualBlock]
      apply Finset.sum_congr rfl
      intro i _
      rw [dualBlock_sub]

end

end NCPLVerification
