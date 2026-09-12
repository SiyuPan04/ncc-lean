import NCCLowerBound.Simplified.CurrentHardData
import NCCLowerBound.Simplified.CompositeSmoothnessAssembly

/-!
# Joint-smoothness transport for the current hard instance

This module transports the actual flat gradients through the fixed primal
and dual coordinate permutations used by `CurrentHardData`.  Both
permutations preserve the exact squared Euclidean form, so the smoothness
constant is unchanged and remains independent of `M` and `N`.
-/

namespace NCCLowerBound
namespace Simplified
namespace CurrentSmoothnessTransport

noncomputable section

open NCCLowerBoundVerification
open RestrictedBall CompositeSmoothness CompositeSmoothnessAssembly
open CurrentHardData

def flatStateIndex {M : Nat} (i : Fin M) : Fin (M * 3) :=
  finProdFinEquiv (i, (0 : Fin 3))

def flatEntranceIndex {M : Nat} (i : Fin M) : Fin (M * 3) :=
  finProdFinEquiv (i, (1 : Fin 3))

def flatExitIndex {M : Nat} (i : Fin M) : Fin (M * 3) :=
  finProdFinEquiv (i, (2 : Fin 3))

theorem toFlatPrimal_basis_state {M : Nat} (i : Fin M) :
    toFlatPrimal
        (NCPLVerification.evecBasis (primalStateIndex i) :
          CurrentHardData.Primal M) =
      NCPLVerification.evecBasis (flatStateIndex i) := by
  funext j
  unfold toFlatPrimal flatStateIndex primalState primalA primalB
    NCPLVerification.evecBasis
  rcases hij : finProdFinEquiv.symm j with ⟨k, c⟩
  have hj := Equiv.apply_symm_apply finProdFinEquiv j
  rw [hij] at hj
  rw [← hj]
  fin_cases c <;> simp [primalStateIndex, primalAIndex, primalBIndex,
    finProdFinEquiv] <;> split <;> split <;> simp_all <;> omega

theorem toFlatPrimal_basis_A {M : Nat} (i : Fin M) :
    toFlatPrimal
        (NCPLVerification.evecBasis (primalAIndex i) :
          CurrentHardData.Primal M) =
      NCPLVerification.evecBasis (flatEntranceIndex i) := by
  funext j
  unfold toFlatPrimal flatEntranceIndex primalState primalA primalB
    NCPLVerification.evecBasis
  rcases hij : finProdFinEquiv.symm j with ⟨k, c⟩
  have hj := Equiv.apply_symm_apply finProdFinEquiv j
  rw [hij] at hj
  rw [← hj]
  fin_cases c <;> simp [primalStateIndex, primalAIndex, primalBIndex,
    finProdFinEquiv] <;> split <;> split <;> simp_all <;> omega

theorem toFlatPrimal_basis_B {M : Nat} (i : Fin M) :
    toFlatPrimal
        (NCPLVerification.evecBasis (primalBIndex i) :
          CurrentHardData.Primal M) =
      NCPLVerification.evecBasis (flatExitIndex i) := by
  funext j
  unfold toFlatPrimal flatExitIndex primalState primalA primalB
    NCPLVerification.evecBasis
  rcases hij : finProdFinEquiv.symm j with ⟨k, c⟩
  have hj := Equiv.apply_symm_apply finProdFinEquiv j
  rw [hij] at hj
  rw [← hj]
  fin_cases c <;> simp [primalStateIndex, primalAIndex, primalBIndex,
    finProdFinEquiv] <;> split <;> split <;> simp_all <;> omega

theorem toFlatDual_basis {M N : Nat} (j : Fin (M * N)) :
    toFlatDual
        (NCPLVerification.evecBasis (dualIndexEquiv M N j) :
          CurrentHardData.Dual M N) =
      NCPLVerification.evecBasis j := by
  funext k
  simp [toFlatDual, NCPLVerification.evecBasis]

@[simp] theorem toFlatDual_zero {M N : Nat} :
    toFlatDual (0 : CurrentHardData.Dual M N) = 0 := rfl

def toFlatPrimalCLM {M : Nat} :
    CurrentHardData.Primal M →L[ℝ] RestrictedBall.FlatPrimal M :=
  LinearMap.toContinuousLinearMap
    ({ toFun := toFlatPrimal
       map_add' := by
         intro x r
         funext j
         simp only [toFlatPrimal, Pi.add_apply]
         split
         · rfl
         · split <;> rfl
       map_smul' := by
         intro c x
         funext j
         simp only [toFlatPrimal, Pi.smul_apply, smul_eq_mul]
         split
         · rfl
         · split <;> rfl } :
      CurrentHardData.Primal M →ₗ[ℝ] RestrictedBall.FlatPrimal M)

@[simp] theorem toFlatPrimalCLM_apply {M : Nat}
    (x : CurrentHardData.Primal M) :
    toFlatPrimalCLM x = toFlatPrimal x := rfl

def toFlatDualCLM {M N : Nat} :
    CurrentHardData.Dual M N →L[ℝ] RestrictedBall.FlatDual M N :=
  LinearMap.toContinuousLinearMap
    ({ toFun := toFlatDual
       map_add' := by
         intro y v
         rfl
       map_smul' := by
         intro c y
         rfl } :
      CurrentHardData.Dual M N →ₗ[ℝ] RestrictedBall.FlatDual M N)

@[simp] theorem toFlatDualCLM_apply {M N : Nat}
    (y : CurrentHardData.Dual M N) :
    toFlatDualCLM y = toFlatDual y := rfl

def toFlatJointCLM {M N : Nat} :
    (CurrentHardData.Primal M × CurrentHardData.Dual M N) →L[ℝ]
      (RestrictedBall.FlatPrimal M × RestrictedBall.FlatDual M N) :=
  (toFlatPrimalCLM.comp
    (ContinuousLinearMap.fst ℝ (CurrentHardData.Primal M)
      (CurrentHardData.Dual M N))).prod
    (toFlatDualCLM.comp
      (ContinuousLinearMap.snd ℝ (CurrentHardData.Primal M)
        (CurrentHardData.Dual M N)))

@[simp] theorem toFlatJointCLM_apply {M N : Nat}
    (z : CurrentHardData.Primal M × CurrentHardData.Dual M N) :
    toFlatJointCLM z = (toFlatPrimal z.1, toFlatDual z.2) := rfl

theorem objective_hasFDerivAt_via_flat {M N : Nat} (hN : 0 < N)
    (K : ℝ) (x : CurrentHardData.Primal M)
    (y : CurrentHardData.Dual M N) :
    HasFDerivAt (Function.uncurry (objective hN K))
      ((fderiv ℝ (flatJointObjective hN K)
        (toFlatPrimal x, toFlatDual y)).comp toFlatJointCLM) (x, y) := by
  have hf : HasFDerivAt (flatJointObjective (M := M) hN K)
      (fderiv ℝ (flatJointObjective hN K)
        (toFlatPrimal x, toFlatDual y))
      (toFlatPrimal x, toFlatDual y) :=
    ((CompositeSmoothness.flatJointObjective_contDiff
      (M := M) hN K).differentiable (by simp) _).hasFDerivAt
  have hc := hf.comp (x, y) (toFlatJointCLM (M := M) (N := N)).hasFDerivAt
  have heq : Function.uncurry (objective (M := M) hN K) =
      flatJointObjective hN K ∘ toFlatJointCLM := by
    funext z
    exact objective_eq_flatHardObjective hN K z.1 z.2
  rw [heq]
  exact hc

theorem fderiv_objective_apply_eq_flat {M N : Nat} (hN : 0 < N)
    (K : ℝ) (x : CurrentHardData.Primal M)
    (y : CurrentHardData.Dual M N) (dx : CurrentHardData.Primal M)
    (dy : CurrentHardData.Dual M N) :
    fderiv ℝ (Function.uncurry (objective hN K)) (x, y) (dx, dy) =
      fderiv ℝ (flatJointObjective hN K)
        (toFlatPrimal x, toFlatDual y)
        (toFlatPrimal dx, toFlatDual dy) := by
  rw [(objective_hasFDerivAt_via_flat hN K x y).fderiv]
  rfl

theorem primalState_gradX_eq_flat {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : CurrentHardData.Primal M) (y : CurrentHardData.Dual M N)
    (i : Fin M) :
    primalState (gradX hN K x y) i =
      flatState (flatPrimalGradient hN K (toFlatPrimal x) (toFlatDual y)) i := by
  have ht := fderiv_objective_apply_eq_flat hN K x y
    (NCPLVerification.evecBasis (primalStateIndex i))
    (0 : CurrentHardData.Dual M N)
  rw [toFlatPrimal_basis_state] at ht
  simp only [toFlatDual_zero] at ht
  have hframework := (gradient_representation (M := M) hN K).2 x y
    (NCPLVerification.evecBasis (primalStateIndex i))
    (0 : CurrentHardData.Dual M N)
  have hflat := (CompositeSmoothness.flatGradient_represents_fderiv
    (M := M) hN K).2 (toFlatPrimal x) (toFlatDual y)
      (NCPLVerification.evecBasis (flatStateIndex i))
      (0 : RestrictedBall.FlatDual M N)
  change (fderiv ℝ (flatJointObjective hN K)
    (toFlatPrimal x, toFlatDual y))
      (NCPLVerification.evecBasis (flatStateIndex i), 0) = _ at hflat
  rw [hframework, hflat] at ht
  simpa [primalState, flatState, flatStateIndex,
    NCPLVerification.evecBasis] using ht

theorem primalA_gradX_eq_flat {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : CurrentHardData.Primal M) (y : CurrentHardData.Dual M N)
    (i : Fin M) :
    primalA (gradX hN K x y) i =
      flatEntrance
        (flatPrimalGradient hN K (toFlatPrimal x) (toFlatDual y)) i := by
  have ht := fderiv_objective_apply_eq_flat hN K x y
    (NCPLVerification.evecBasis (primalAIndex i))
    (0 : CurrentHardData.Dual M N)
  rw [toFlatPrimal_basis_A] at ht
  simp only [toFlatDual_zero] at ht
  have hframework := (gradient_representation (M := M) hN K).2 x y
    (NCPLVerification.evecBasis (primalAIndex i))
    (0 : CurrentHardData.Dual M N)
  have hflat := (CompositeSmoothness.flatGradient_represents_fderiv
    (M := M) hN K).2 (toFlatPrimal x) (toFlatDual y)
      (NCPLVerification.evecBasis (flatEntranceIndex i))
      (0 : RestrictedBall.FlatDual M N)
  change (fderiv ℝ (flatJointObjective hN K)
    (toFlatPrimal x, toFlatDual y))
      (NCPLVerification.evecBasis (flatEntranceIndex i), 0) = _ at hflat
  rw [hframework, hflat] at ht
  simpa [primalA, flatEntrance, flatEntranceIndex,
    NCPLVerification.evecBasis] using ht

theorem primalB_gradX_eq_flat {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : CurrentHardData.Primal M) (y : CurrentHardData.Dual M N)
    (i : Fin M) :
    primalB (gradX hN K x y) i =
      flatExit
        (flatPrimalGradient hN K (toFlatPrimal x) (toFlatDual y)) i := by
  have ht := fderiv_objective_apply_eq_flat hN K x y
    (NCPLVerification.evecBasis (primalBIndex i))
    (0 : CurrentHardData.Dual M N)
  rw [toFlatPrimal_basis_B] at ht
  simp only [toFlatDual_zero] at ht
  have hframework := (gradient_representation (M := M) hN K).2 x y
    (NCPLVerification.evecBasis (primalBIndex i))
    (0 : CurrentHardData.Dual M N)
  have hflat := (CompositeSmoothness.flatGradient_represents_fderiv
    (M := M) hN K).2 (toFlatPrimal x) (toFlatDual y)
      (NCPLVerification.evecBasis (flatExitIndex i))
      (0 : RestrictedBall.FlatDual M N)
  change (fderiv ℝ (flatJointObjective hN K)
    (toFlatPrimal x, toFlatDual y))
      (NCPLVerification.evecBasis (flatExitIndex i), 0) = _ at hflat
  rw [hframework, hflat] at ht
  simpa [primalB, flatExit, flatExitIndex,
    NCPLVerification.evecBasis] using ht

private theorem flatPrimal_ext {M : Nat}
    (p q : RestrictedBall.FlatPrimal M)
    (hs : flatState p = flatState q)
    (ha : flatEntrance p = flatEntrance q)
    (hb : flatExit p = flatExit q) : p = q := by
  funext j
  rcases hij : finProdFinEquiv.symm j with ⟨i, k⟩
  have hj := Equiv.apply_symm_apply finProdFinEquiv j
  rw [hij] at hj
  rw [← hj]
  fin_cases k
  · simpa [flatState] using congrFun hs i
  · simpa [flatEntrance] using congrFun ha i
  · simpa [flatExit] using congrFun hb i

theorem toFlatPrimal_gradX {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : CurrentHardData.Primal M) (y : CurrentHardData.Dual M N) :
    toFlatPrimal (gradX hN K x y) =
      flatPrimalGradient hN K (toFlatPrimal x) (toFlatDual y) := by
  apply flatPrimal_ext
  · funext i
    rw [flatState_toFlatPrimal]
    exact primalState_gradX_eq_flat hN K x y i
  · funext i
    rw [flatEntrance_toFlatPrimal]
    exact primalA_gradX_eq_flat hN K x y i
  · funext i
    rw [flatExit_toFlatPrimal]
    exact primalB_gradX_eq_flat hN K x y i

theorem toFlatDual_gradY {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : CurrentHardData.Primal M) (y : CurrentHardData.Dual M N) :
    toFlatDual (gradY hN K x y) =
      flatDualGradient hN K (toFlatPrimal x) (toFlatDual y) := by
  funext j
  have ht := fderiv_objective_apply_eq_flat hN K x y
    (0 : CurrentHardData.Primal M)
    (NCPLVerification.evecBasis (dualIndexEquiv M N j))
  rw [toFlatDual_basis] at ht
  simp only [toFlatPrimal_zero] at ht
  have hframework := (gradient_representation (M := M) hN K).2 x y
    (0 : CurrentHardData.Primal M)
    (NCPLVerification.evecBasis (dualIndexEquiv M N j))
  have hflat := (CompositeSmoothness.flatGradient_represents_fderiv
    (M := M) hN K).2 (toFlatPrimal x) (toFlatDual y)
      (0 : RestrictedBall.FlatPrimal M)
      (NCPLVerification.evecBasis j)
  change (fderiv ℝ (flatJointObjective hN K)
    (toFlatPrimal x, toFlatDual y))
      (0, NCPLVerification.evecBasis j) = _ at hflat
  rw [hframework, hflat] at ht
  simpa [toFlatDual, NCPLVerification.evecBasis] using ht

/-- The actual framework-coordinate gradients inherit the fixed,
dimension-independent joint smoothness constant of the flat construction. -/
theorem current_gradients_jointlySmooth {M N : Nat}
    (hN10 : 10 ≤ N) (K : ℝ) (hK : 0 < K) :
    NCPLVerification.IsJointlySmooth
      (CompositeSmoothnessAssembly.compositeEll0 K hK)
      (gradX (M := M) (by omega : 0 < N) K)
      (gradY (M := M) (by omega : 0 < N) K) := by
  let hN : 0 < N := by omega
  intro x y r v
  calc
    NCPLVerification.jointSq
        (gradX hN K x y - gradX hN K r v)
        (gradY hN K x y - gradY hN K r v) =
      NCPLVerification.jointSq
        (flatPrimalGradient hN K (toFlatPrimal x) (toFlatDual y) -
          flatPrimalGradient hN K (toFlatPrimal r) (toFlatDual v))
        (flatDualGradient hN K (toFlatPrimal x) (toFlatDual y) -
          flatDualGradient hN K (toFlatPrimal r) (toFlatDual v)) := by
            rw [← jointSq_toFlat,
              toFlatPrimal_gradX, toFlatPrimal_gradX,
              toFlatDual_gradY, toFlatDual_gradY]
    _ ≤ (CompositeSmoothnessAssembly.compositeEll0 K hK) ^ 2 *
        NCPLVerification.jointSq
          (toFlatPrimal x - toFlatPrimal r)
          (toFlatDual y - toFlatDual v) :=
      CompositeSmoothnessAssembly.flatActualGradients_jointlySmooth
        hN10 K hK (toFlatPrimal x) (toFlatDual y)
          (toFlatPrimal r) (toFlatDual v)
    _ = (CompositeSmoothnessAssembly.compositeEll0 K hK) ^ 2 *
        NCPLVerification.jointSq (x - r) (y - v) := by
      rw [jointSq_toFlat]

end

end CurrentSmoothnessTransport
end Simplified
end NCCLowerBound
