import NCPLVerification.HardBlockExplicit
import NCPLVerification.HardDualSmoothness

/-!
# Dimension-free joint smoothness of the hard instance
-/

namespace NCPLVerification

noncomputable section

theorem carmonBlockPrev_sq_sub_eq {T : Nat} (x x' : EVec T) (i : Fin T) :
    (carmonBlockPrev x i - carmonBlockPrev x' i) ^ 2 =
      carmonPrevDiff x x' i ^ 2 := by
  by_cases hi : i.1 = 0
  · simp [carmonBlockPrev, carmonPrevDiff, hi]
  · simp [carmonBlockPrev, carmonPrevDiff, hi, sq_abs]

theorem perspectiveGradient_outer_param_weighted_le {T N : Nat}
    (hN : 0 < N) (lambdaWall eta : ℝ) (heta : |eta| ≤ 1)
    (x x' : EVec T) (y : EVec (T * N)) (i : Fin T) :
    innerDualSq N
        (perspectiveGradient N lambdaWall eta (carmonRho x i)
            (carmonOuterA x i) (hardDualWeightedBlock x y i) -
          perspectiveGradient N lambdaWall eta (carmonRho x' i)
            (carmonOuterA x' i) (hardDualWeightedBlock x' y i)) ≤
      8 * hardBlockDualParamC ^ 2 *
        (carmonPrevDiff x x' i ^ 2 + (x i - x' i) ^ 2) := by
  have heqU : hardDualWeightedBlock x y i = hardDualWeightedBlock x' y i := rfl
  rw [heqU]
  rw [← hardBlockExplicitGradU_eq hN lambdaWall eta x i,
    ← hardBlockExplicitGradU_eq hN lambdaWall eta x' i]
  have h := hardBlockExplicitGradU_param_weighted_le hN lambdaWall eta
    (carmonBlockPrev x i) (x i) (carmonBlockPrev x' i) (x' i)
    (hardDualWeightedBlock x' y i) heta
  rwa [carmonBlockPrev_sq_sub_eq] at h

theorem hardBlockGradY_param_lipschitz {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (heta : |eta| ≤ 1)
    (x x' : EVec T) (y : EVec (T * N)) (i : Fin T) :
    vecSq (hardBlockGradY T N lambdaWall eta x y i -
        hardBlockGradY T N lambdaWall eta x' y i) ≤
      8 * hardBlockDualParamC ^ 2 *
        (carmonPrevDiff x x' i ^ 2 + (x i - x' i) ^ 2) := by
  unfold hardBlockGradY
  rw [vecSq_toEuclideanGradient_sub hN]
  exact perspectiveGradient_outer_param_weighted_le hN lambdaWall eta heta x x' y i

theorem vecSq_add_le_two {m : Nat} (a b : EVec m) :
    vecSq (a + b) ≤ 2 * vecSq a + 2 * vecSq b := by
  unfold vecSq
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (a i - b i)]

theorem hardGradY_param_lipschitz {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (heta : |eta| ≤ 1)
    (x x' : EVec T) (y : EVec (T * N)) :
    vecSq (hardGradY T N lambdaWall eta x y -
        hardGradY T N lambdaWall eta x' y) ≤
      16 * hardBlockDualParamC ^ 2 * vecSq (x - x') := by
  rw [hardGradY_eq_assemble, hardGradY_eq_assemble]
  have heq :
      assembleDualBlocks (fun i ↦ hardBlockGradY T N lambdaWall eta x y i) -
        assembleDualBlocks (fun i ↦ hardBlockGradY T N lambdaWall eta x' y i) =
      assembleDualBlocks (fun i ↦
        hardBlockGradY T N lambdaWall eta x y i -
          hardBlockGradY T N lambdaWall eta x' y i) := by
    funext k
    let p := finProdFinEquiv.symm k
    simp [assembleDualBlocks]
  rw [heq, vecSq_assembleDualBlocks]
  have hblocks :
      (∑ i : Fin T,
        vecSq (hardBlockGradY T N lambdaWall eta x y i -
          hardBlockGradY T N lambdaWall eta x' y i)) ≤
      ∑ i : Fin T, 8 * hardBlockDualParamC ^ 2 *
        (carmonPrevDiff x x' i ^ 2 + (x i - x' i) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    exact hardBlockGradY_param_lipschitz hN lambdaWall eta heta x x' y i
  have hprev := sum_carmonPrevDiff_sq_le x x'
  have hcurr : (∑ i : Fin T, (x i - x' i) ^ 2) = vecSq (x - x') := by
    rfl
  calc
    _ ≤ ∑ i : Fin T, 8 * hardBlockDualParamC ^ 2 *
        (carmonPrevDiff x x' i ^ 2 + (x i - x' i) ^ 2) := hblocks
    _ = 8 * hardBlockDualParamC ^ 2 *
        ((∑ i : Fin T, carmonPrevDiff x x' i ^ 2) +
          ∑ i : Fin T, (x i - x' i) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 8 * hardBlockDualParamC ^ 2 *
        (vecSq (x - x') + vecSq (x - x')) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add hprev (le_of_eq hcurr)) (by positivity)
    _ = 16 * hardBlockDualParamC ^ 2 * vecSq (x - x') := by ring

theorem hardGradY_joint_lipschitz {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (heta : |eta| ≤ 1)
    (x x' : EVec T) (y y' : EVec (T * N)) :
    vecSq (hardGradY T N lambdaWall eta x y -
        hardGradY T N lambdaWall eta x' y') ≤
      32 * hardBlockDualParamC ^ 2 * vecSq (x - x') +
        2 * perspectiveDualSmoothCoeff lambdaWall eta carmonAmax *
          vecSq (y - y') := by
  let a := hardGradY T N lambdaWall eta x y -
    hardGradY T N lambdaWall eta x' y
  let b := hardGradY T N lambdaWall eta x' y -
    hardGradY T N lambdaWall eta x' y'
  have heq : hardGradY T N lambdaWall eta x y -
      hardGradY T N lambdaWall eta x' y' = a + b := by
    funext k
    simp [a, b]
  rw [heq]
  have hab := vecSq_add_le_two a b
  have ha := hardGradY_param_lipschitz hN lambdaWall eta heta x x' y
  have hb := hardGradY_lipschitz_in_y hN lambdaWall eta x' y y'
  dsimp [a, b] at hab ha hb
  nlinarith

end

end NCPLVerification
