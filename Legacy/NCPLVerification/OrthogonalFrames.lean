import NCPLVerification.ZeroRespectingLowerBound
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite Euclidean frames

The project uses plain finite functions together with the explicit squared
Euclidean norm `vecSq`.  This file therefore develops column-orthogonal
embeddings directly from finite sums, without relying on the ambient Banach
norm chosen for function spaces.
-/

namespace NCPLVerification

noncomputable section

def evecDotValue {m : Nat} (x y : EVec m) : ℝ :=
  ∑ k : Fin m, x k * y k

theorem evecDotValue_self {m : Nat} (x : EVec m) :
    evecDotValue x x = vecSq x := by
  unfold evecDotValue vecSq
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem evecDotValue_comm {m : Nat} (x y : EVec m) :
    evecDotValue x y = evecDotValue y x := by
  unfold evecDotValue
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem evecDotValue_add_left {m : Nat} (x y z : EVec m) :
    evecDotValue (x + y) z = evecDotValue x z + evecDotValue y z := by
  unfold evecDotValue
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

theorem evecDotValue_smul_left {m : Nat} (c : ℝ) (x y : EVec m) :
    evecDotValue (c • x) y = c * evecDotValue x y := by
  unfold evecDotValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

def IsOrthonormalFrame {m D : Nat} (U : Fin m → EVec D) : Prop :=
  ∀ i j, evecDotValue (U i) (U j) = if i = j then 1 else 0

def frameEmbed {m D : Nat} (U : Fin m → EVec D) (x : EVec m) : EVec D :=
  fun k ↦ ∑ i : Fin m, x i * U i k

def frameProject {m D : Nat} (U : Fin m → EVec D) (X : EVec D) : EVec m :=
  fun i ↦ evecDotValue (U i) X

@[simp] theorem frameProject_zero {m D : Nat} (U : Fin m → EVec D) :
    frameProject U (0 : EVec D) = 0 := by
  funext i
  unfold frameProject evecDotValue
  simp

@[simp] theorem frameEmbed_zero {m D : Nat} (U : Fin m → EVec D) :
    frameEmbed U (0 : EVec m) = 0 := by
  funext k
  unfold frameEmbed
  simp

theorem evecDotValue_frameEmbed_left {m D : Nat}
    (U : Fin m → EVec D) (x : EVec m) (X : EVec D) :
    evecDotValue (frameEmbed U x) X =
      ∑ i : Fin m, x i * evecDotValue (U i) X := by
  unfold evecDotValue frameEmbed
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem frameProject_frameEmbed {m D : Nat}
    {U : Fin m → EVec D} (hU : IsOrthonormalFrame U) (x : EVec m) :
    frameProject U (frameEmbed U x) = x := by
  funext i
  change evecDotValue (U i) (frameEmbed U x) = x i
  rw [← evecDotValue_comm]
  rw [evecDotValue_frameEmbed_left]
  calc
    (∑ j : Fin m, x j * evecDotValue (U j) (U i)) =
        ∑ j : Fin m, if j = i then x j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hU]
      by_cases hji : j = i
      · simp [hji]
      · simp [hji]
    _ = x i := by simp

theorem vecSq_frameEmbed {m D : Nat}
    {U : Fin m → EVec D} (hU : IsOrthonormalFrame U) (x : EVec m) :
    vecSq (frameEmbed U x) = vecSq x := by
  rw [← evecDotValue_self, evecDotValue_frameEmbed_left]
  change (∑ i : Fin m, x i * frameProject U (frameEmbed U x) i) = vecSq x
  rw [frameProject_frameEmbed hU]
  unfold vecSq
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem evecDotValue_frameEmbed_project {m D : Nat}
    {U : Fin m → EVec D} (hU : IsOrthonormalFrame U) (X : EVec D) :
    evecDotValue (frameEmbed U (frameProject U X)) X =
      vecSq (frameProject U X) := by
  rw [evecDotValue_frameEmbed_left]
  unfold frameProject vecSq
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem vecSq_sub_expand {m : Nat} (x y : EVec m) :
    vecSq (x - y) = vecSq x - 2 * evecDotValue x y + vecSq y := by
  unfold vecSq evecDotValue
  simp only [Pi.sub_apply]
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [mul_assoc]

theorem vecSq_frameProject_le {m D : Nat}
    {U : Fin m → EVec D} (hU : IsOrthonormalFrame U) (X : EVec D) :
    vecSq (frameProject U X) ≤ vecSq X := by
  have hres : 0 ≤ vecSq (X - frameEmbed U (frameProject U X)) := by
    unfold vecSq
    positivity
  rw [vecSq_sub_expand, evecDotValue_comm,
    evecDotValue_frameEmbed_project hU,
    vecSq_frameEmbed hU] at hres
  linarith

theorem frameProject_sub {m D : Nat} (U : Fin m → EVec D)
    (X X' : EVec D) :
    frameProject U X - frameProject U X' = frameProject U (X - X') := by
  funext i
  unfold frameProject evecDotValue
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem frameEmbed_sub {m D : Nat} (U : Fin m → EVec D)
    (x x' : EVec m) :
    frameEmbed U x - frameEmbed U x' = frameEmbed U (x - x') := by
  funext k
  unfold frameEmbed
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

def frameProjectCLM {m D : Nat} (U : Fin m → EVec D) :
    EVec D →L[ℝ] EVec m :=
  ContinuousLinearMap.pi (fun i ↦ evecDot (U i))

@[simp] theorem frameProjectCLM_apply {m D : Nat}
    (U : Fin m → EVec D) (X : EVec D) :
    frameProjectCLM U X = frameProject U X := by
  rfl

def frameEmbedLM {m D : Nat} (U : Fin m → EVec D) :
    EVec m →ₗ[ℝ] EVec D where
  toFun := frameEmbed U
  map_add' := by
    intro x y
    funext k
    unfold frameEmbed
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  map_smul' := by
    intro c x
    funext k
    unfold frameEmbed
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def frameEmbedCLM {m D : Nat} (U : Fin m → EVec D) :
    EVec m →L[ℝ] EVec D :=
  LinearMap.toContinuousLinearMap (frameEmbedLM U)

@[simp] theorem frameEmbedCLM_apply {m D : Nat}
    (U : Fin m → EVec D) (x : EVec m) :
    frameEmbedCLM U x = frameEmbed U x := rfl

end

end NCPLVerification
