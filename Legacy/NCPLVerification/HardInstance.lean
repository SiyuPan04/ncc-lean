import NCPLVerification.CarmonChain
import NCPLVerification.Perspective

/-!
# The unscaled NC--PL hard instance

This file assembles one perspective delay block per outer Carmon coordinate,
using the article's Euclidean diagonal dual scaling.
-/

namespace NCPLVerification

noncomputable section

def dualBlock {T N : Nat} (y : EVec (T * N)) (i : Fin T) : EVec N :=
  fun j ↦ y (finProdFinEquiv (i, j))

def assembleDualBlocks {T N : Nat} (b : Fin T → EVec N) : EVec (T * N) :=
  fun k ↦
    let p := finProdFinEquiv.symm k
    b p.1 p.2

@[simp] theorem dualBlock_assemble {T N : Nat} (b : Fin T → EVec N)
    (i : Fin T) :
    dualBlock (assembleDualBlocks b) i = b i := by
  funext j
  simp [dualBlock, assembleDualBlocks]

theorem sum_assembleDualBlocks_sq {T N : Nat} (b : Fin T → EVec N) :
    (∑ k : Fin (T * N), assembleDualBlocks b k ^ 2) =
      ∑ i : Fin T, ∑ j : Fin N, b i j ^ 2 := by
  calc
    (∑ k : Fin (T * N), assembleDualBlocks b k ^ 2) =
        ∑ p : Fin T × Fin N,
          assembleDualBlocks b (finProdFinEquiv p) ^ 2 := by
            symm
            exact Equiv.sum_comp finProdFinEquiv
              (fun k : Fin (T * N) ↦ assembleDualBlocks b k ^ 2)
    _ = ∑ p : Fin T × Fin N, b p.1 p.2 ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      simp [assembleDualBlocks]
    _ = ∑ i : Fin T, ∑ j : Fin N, b i j ^ 2 := by
      rw [Fintype.sum_prod_type]

def hardDualWeightedBlock {T N : Nat} (x : EVec T) (y : EVec (T * N))
    (i : Fin T) : EVec N :=
  toWeightedCoordinates (dualBlock y i)

def hardBlockValue (N : Nat) (lambdaWall eta : ℝ)
    {T : Nat} (x : EVec T) (y : EVec (T * N)) (i : Fin T) : ℝ :=
  -carmonPhiCap * carmonRhoSq x i +
    perspectiveDelay N lambdaWall eta (carmonRho x i) (carmonOuterA x i)
      (hardDualWeightedBlock x y i)

/-- Euclidean-coordinate unscaled saddle objective `bar F_{T,N}`. -/
def hardF (T N : Nat) (lambdaWall eta : ℝ)
    (x : EVec T) (y : EVec (T * N)) : ℝ :=
  ∑ i : Fin T, hardBlockValue N lambdaWall eta x y i

def hardGradY (T N : Nat) (lambdaWall eta : ℝ)
    (x : EVec T) (y : EVec (T * N)) : EVec (T * N) :=
  assembleDualBlocks fun i ↦
    toEuclideanGradient
      (perspectiveGradient N lambdaWall eta (carmonRho x i)
        (carmonOuterA x i) (hardDualWeightedBlock x y i))

theorem hard_block_le_outerA {T N : Nat} (hN : 0 < N)
    {lambdaWall eta : ℝ} (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (x : EVec T) (y : EVec (T * N)) (i : Fin T) :
    perspectiveDelay N lambdaWall eta (carmonRho x i) (carmonOuterA x i)
        (hardDualWeightedBlock x y i) ≤ carmonOuterA x i := by
  exact perspective_le_A hN (carmonRho_nonneg x i) hlambda heta
    (carmonOuterA_nonneg x i) (carmonOuterA_le x i) _

theorem hardF_le_carmonF {T N : Nat} (hN : 0 < N)
    {lambdaWall eta : ℝ} (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (x : EVec T) (y : EVec (T * N)) :
    hardF T N lambdaWall eta x y ≤ carmonF T x := by
  unfold hardF carmonF hardBlockValue
  apply Finset.sum_le_sum
  intro i _
  have h := hard_block_le_outerA hN hlambda heta x y i
  unfold carmonOuterA at h
  calc
    -carmonPhiCap * carmonRhoSq x i +
        perspectiveDelay N lambdaWall eta (carmonRho x i)
          (carmonPhiCap * carmonRhoSq x i + carmonTerm x i)
          (hardDualWeightedBlock x y i) ≤
        -carmonPhiCap * carmonRhoSq x i +
          (carmonPhiCap * carmonRhoSq x i + carmonTerm x i) :=
      by
        simpa [add_comm] using
          add_le_add_right h (-carmonPhiCap * carmonRhoSq x i)
    _ = carmonTerm x i := by ring

theorem hardF_attains_carmonF {T N : Nat} (hN : 0 < N)
    {lambdaWall eta : ℝ} (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (x : EVec T) :
    ∃ y : EVec (T * N), hardF T N lambdaWall eta x y = carmonF T x := by
  have hmax (i : Fin T) : ∃ u : EVec N,
      perspectiveDelay N lambdaWall eta (carmonRho x i) (carmonOuterA x i) u =
        carmonOuterA x i :=
    perspective_attains_max hN (carmonRho_nonneg x i) hlambda heta
      (carmonOuterA_nonneg x i) (carmonOuterA_le x i)
  let ustar : Fin T → EVec N := fun i ↦ Classical.choose (hmax i)
  let ystar : EVec (T * N) := assembleDualBlocks fun i ↦
    fromWeightedCoordinates (ustar i)
  refine ⟨ystar, ?_⟩
  unfold hardF carmonF hardBlockValue
  apply Finset.sum_congr rfl
  intro i _
  have hblock : hardDualWeightedBlock x ystar i = ustar i := by
    unfold hardDualWeightedBlock ystar
    rw [dualBlock_assemble]
    exact toWeightedCoordinates_fromWeighted hN (ustar i)
  rw [hblock, Classical.choose_spec (hmax i)]
  unfold carmonOuterA
  ring

theorem hardF_isMaximizer {T N : Nat} (hN : 0 < N)
    {lambdaWall eta : ℝ} (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (x : EVec T) :
    ∃ y : EVec (T * N),
      IsMaximizer (hardF T N lambdaWall eta) x y := by
  obtain ⟨y, hy⟩ := hardF_attains_carmonF hN hlambda heta x
  refine ⟨y, fun v ↦ ?_⟩
  rw [hy]
  exact hardF_le_carmonF hN hlambda heta x v

/-- Proposition 7.1: the envelope is exactly the outer Carmon chain. -/
theorem hardF_envelope_eq_carmonF {T N : Nat} (hN : 0 < N)
    {lambdaWall eta : ℝ} (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (x : EVec T) :
    Envelope (hardF T N lambdaWall eta) x = carmonF T x := by
  obtain ⟨y, hymax⟩ := hardF_isMaximizer hN hlambda heta x
  rw [envelope_eq_of_isMaximizer hymax]
  exact le_antisymm (hardF_le_carmonF hN hlambda heta x y)
    (by obtain ⟨v, hv⟩ := hardF_attains_carmonF hN hlambda heta x
        rw [← hv]
        exact hymax v)

theorem vecSq_hardGradY {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N)) :
    vecSq (hardGradY T N lambdaWall eta x y) =
      ∑ i : Fin T,
        innerDualSq N
          (perspectiveGradient N lambdaWall eta (carmonRho x i)
            (carmonOuterA x i) (hardDualWeightedBlock x y i)) := by
  unfold vecSq hardGradY
  rw [sum_assembleDualBlocks_sq]
  apply Finset.sum_congr rfl
  intro i _
  exact euclideanSq_toEuclideanGradient hN _

theorem hardF_gap_eq_sum {T N : Nat} (hN : 0 < N)
    {lambdaWall eta : ℝ} (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (x : EVec T) (y : EVec (T * N)) :
    Envelope (hardF T N lambdaWall eta) x - hardF T N lambdaWall eta x y =
      ∑ i : Fin T,
        (carmonOuterA x i -
          perspectiveDelay N lambdaWall eta (carmonRho x i) (carmonOuterA x i)
            (hardDualWeightedBlock x y i)) := by
  rw [hardF_envelope_eq_carmonF hN hlambda heta]
  unfold carmonF hardF hardBlockValue carmonOuterA
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Proposition 7.2, dual-PL part, in exact Euclidean dual coordinates. -/
theorem hardF_dual_PL {T N : Nat} (hN2 : 2 ≤ N)
    {lambdaWall eta : ℝ} (hlambda : 12 ≤ lambdaWall) (heta : 0 < eta)
    (x : EVec T) (y : EVec (T * N)) :
    (1 : ℝ) / 2 * vecSq (hardGradY T N lambdaWall eta x y) ≥
      perspectivePLConstant lambdaWall eta carmonAmax / (N : ℝ) *
        (Envelope (hardF T N lambdaWall eta) x - hardF T N lambdaWall eta x y) := by
  have hN : 0 < N := by omega
  have hblocks :
      (∑ i : Fin T,
        perspectivePLConstant lambdaWall eta carmonAmax / (N : ℝ) *
          (carmonOuterA x i -
            perspectiveDelay N lambdaWall eta (carmonRho x i) (carmonOuterA x i)
              (hardDualWeightedBlock x y i))) ≤
      ∑ i : Fin T, (1 : ℝ) / 2 *
        innerDualSq N
          (perspectiveGradient N lambdaWall eta (carmonRho x i)
            (carmonOuterA x i) (hardDualWeightedBlock x y i)) := by
    apply Finset.sum_le_sum
    intro i _
    exact perspective_delay_PL_field hN2 (carmonRho_nonneg x i) hlambda heta
      (carmonOuterA_nonneg x i) carmonAmax_nonneg (carmonOuterA_le x i) _
  rw [vecSq_hardGradY hN, hardF_gap_eq_sum hN (by linarith) heta.le]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact hblocks

end

end NCPLVerification
