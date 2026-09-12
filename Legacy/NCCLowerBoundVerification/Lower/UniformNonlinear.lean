import NCCLowerBoundVerification.Lower.UnscaledRegularity

open scoped BigOperators
open Finset
open NCCLowerBoundVerification

private theorem vecSq_sum_single_of_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Nat}
    (idx : ι → Fin m) (hidx : Function.Injective idx) (f : ι → ℝ) :
    vecSq (∑ i, Pi.single (idx i) (f i) : EVec m) = ∑ i, (f i) ^ 2 := by
  classical
  unfold vecSq NCPLVerification.vecSq
  let s : Finset (Fin m) := Finset.univ.image idx
  rw [← Finset.sum_subset (Finset.subset_univ s)]
  · rw [Finset.sum_image hidx.injOn]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.sum_apply, Pi.single_apply]
    simp [hidx.eq_iff]
  · intro j hj hjs
    simp only [Finset.sum_apply, Pi.single_apply]
    have hne : ∀ i, idx i ≠ j := by
      intro i hij
      apply hjs
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hij⟩
    have hne' : ∀ i, j ≠ idx i := fun i ↦ (hne i).symm
    simp [hne']

private theorem sum_sq_comp_injective_le_vecSq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Nat}
    (idx : ι → Fin m) (hidx : Function.Injective idx) (x : EVec m) :
    (∑ i, (x (idx i)) ^ 2) ≤ vecSq x := by
  classical
  unfold vecSq NCPLVerification.vecSq
  calc
    (∑ i, (x (idx i)) ^ 2) =
        (∑ j ∈ Finset.univ.image idx, (x j) ^ 2) := by
          rw [Finset.sum_image hidx.injOn]
    _ ≤ ∑ j, (x j) ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun j ↦ sq_nonneg (x j))

private theorem sum_single_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : Nat} (idx : ι → Fin m) (f g : ι → ℝ) :
    (∑ i, Pi.single (idx i) (f i) : EVec m) -
        (∑ i, Pi.single (idx i) (g i) : EVec m) =
      ∑ i, Pi.single (idx i) (f i - g i) := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ext j
  by_cases h : j = idx i <;> simp [Pi.single_apply, h]

namespace NCCLowerBoundVerification

noncomputable def serializedGateAField {T n : Nat} (q : SerializedSpace T n) :
    SerializedSpace T n :=
  ∑ i : Fin (T - 1), Pi.single (serializedAIndex (n := n) i)
    (localGateA (localGateInput q i))

noncomputable def serializedGateBField {T n : Nat} (q : SerializedSpace T n) :
    SerializedSpace T n :=
  ∑ i : Fin (T - 1), Pi.single (serializedBIndex (n := n) i)
    (localGateB (localGateInput q i))

noncomputable def serializedGateNextField {T n : Nat} (q : SerializedSpace T n) :
    SerializedSpace T n :=
  ∑ i : Fin (T - 1), Pi.single (serializedStateIndex (n := n) i)
    (localGateNext (localGateInput q i))

noncomputable def serializedGateCurrentField {T n : Nat}
    (q : SerializedSpace T n) : SerializedSpace T n :=
  ∑ j : Fin (T - 2),
    Pi.single
      (serializedStateIndex (n := n) (⟨j.val, by omega⟩ : Fin (T - 1)))
      (localGateCurrent
        (localGateInput q (⟨j.val + 1, by omega⟩ : Fin (T - 1))))

noncomputable def serializedNonlinearGateField {T n : Nat}
    (q : SerializedSpace T n) : SerializedSpace T n :=
  serializedGateAField q + serializedGateBField q +
    serializedGateNextField q + serializedGateCurrentField q

private theorem vecSq_gateA_sub {T n : Nat} (q r : SerializedSpace T n) :
    vecSq (serializedGateAField q - serializedGateAField r) =
      ∑ i : Fin (T - 1),
        (localGateA (localGateInput q i) -
          localGateA (localGateInput r i)) ^ 2 := by
  have heq : serializedGateAField q - serializedGateAField r =
      ∑ i : Fin (T - 1), Pi.single (serializedAIndex (n := n) i)
        (localGateA (localGateInput q i) -
          localGateA (localGateInput r i)) := by
    unfold serializedGateAField
    exact sum_single_sub _ _ _
  rw [heq]
  exact vecSq_sum_single_of_injective _ serializedAIndex_injective _

private theorem vecSq_gateB_sub {T n : Nat} (q r : SerializedSpace T n) :
    vecSq (serializedGateBField q - serializedGateBField r) =
      ∑ i : Fin (T - 1),
        (localGateB (localGateInput q i) -
          localGateB (localGateInput r i)) ^ 2 := by
  have heq : serializedGateBField q - serializedGateBField r =
      ∑ i : Fin (T - 1), Pi.single (serializedBIndex (n := n) i)
        (localGateB (localGateInput q i) -
          localGateB (localGateInput r i)) := by
    unfold serializedGateBField
    exact sum_single_sub _ _ _
  rw [heq]
  exact vecSq_sum_single_of_injective _ serializedBIndex_injective _

private theorem vecSq_gateNext_sub {T n : Nat} (q r : SerializedSpace T n) :
    vecSq (serializedGateNextField q - serializedGateNextField r) =
      ∑ i : Fin (T - 1),
        (localGateNext (localGateInput q i) -
          localGateNext (localGateInput r i)) ^ 2 := by
  have heq : serializedGateNextField q - serializedGateNextField r =
      ∑ i : Fin (T - 1), Pi.single (serializedStateIndex (n := n) i)
        (localGateNext (localGateInput q i) -
          localGateNext (localGateInput r i)) := by
    unfold serializedGateNextField
    exact sum_single_sub _ _ _
  rw [heq]
  exact vecSq_sum_single_of_injective _ serializedStateIndex_injective _

private theorem gateCurrentIndex_injective {T n : Nat} :
    Function.Injective (fun j : Fin (T - 2) ↦
      serializedStateIndex (n := n) (⟨j.val, by omega⟩ : Fin (T - 1))) := by
  intro j k h
  have h' := serializedStateIndex_injective h
  apply Fin.ext
  simpa using congrArg Fin.val h'

private theorem vecSq_gateCurrent_sub {T n : Nat} (q r : SerializedSpace T n) :
    vecSq (serializedGateCurrentField q - serializedGateCurrentField r) =
      ∑ j : Fin (T - 2),
        (localGateCurrent
            (localGateInput q (⟨j.val + 1, by omega⟩ : Fin (T - 1))) -
          localGateCurrent
            (localGateInput r (⟨j.val + 1, by omega⟩ : Fin (T - 1)))) ^ 2 := by
  have heq : serializedGateCurrentField q - serializedGateCurrentField r =
      ∑ j : Fin (T - 2),
        Pi.single
          (serializedStateIndex (n := n) (⟨j.val, by omega⟩ : Fin (T - 1)))
          (localGateCurrent
              (localGateInput q (⟨j.val + 1, by omega⟩ : Fin (T - 1))) -
            localGateCurrent
              (localGateInput r (⟨j.val + 1, by omega⟩ : Fin (T - 1)))) := by
    unfold serializedGateCurrentField
    exact sum_single_sub _ _ _
  rw [heq]
  exact vecSq_sum_single_of_injective _ gateCurrentIndex_injective _

private theorem sum_serializedA_sub_sq_le {T n : Nat}
    (q r : SerializedSpace T n) :
    (∑ i : Fin (T - 1), (serializedA q i - serializedA r i) ^ 2) ≤
      vecSq (q - r) := by
  simpa [serializedA] using
    (sum_sq_comp_injective_le_vecSq
      (serializedAIndex (T := T) (n := n)) serializedAIndex_injective (q - r))

private theorem sum_serializedB_sub_sq_le {T n : Nat}
    (q r : SerializedSpace T n) :
    (∑ i : Fin (T - 1), (serializedB q i - serializedB r i) ^ 2) ≤
      vecSq (q - r) := by
  simpa [serializedB] using
    (sum_sq_comp_injective_le_vecSq
      (serializedBIndex (T := T) (n := n)) serializedBIndex_injective (q - r))

private theorem sum_serializedState_sub_sq_le {T n : Nat}
    (q r : SerializedSpace T n) :
    (∑ i : Fin (T - 1), (serializedState q i - serializedState r i) ^ 2) ≤
      vecSq (q - r) := by
  simpa [serializedState] using
    (sum_sq_comp_injective_le_vecSq
      (serializedStateIndex (T := T) (n := n)) serializedStateIndex_injective (q - r))

private abbrev NonzeroBlock (T : Nat) := {i : Fin (T - 1) // i.val ≠ 0}

private def predecessorStateIndex {T n : Nat} (i : NonzeroBlock T) :
    Fin ((T - 1) * (n + 3)) :=
  serializedStateIndex (n := n) (⟨i.val.val - 1, by omega⟩ : Fin (T - 1))

private theorem predecessorStateIndex_injective {T n : Nat} :
    Function.Injective (predecessorStateIndex (T := T) (n := n)) := by
  intro i j h
  have h' := serializedStateIndex_injective h
  apply Subtype.ext
  apply Fin.ext
  have hv := congrArg Fin.val h'
  dsimp [predecessorStateIndex] at hv
  omega

private theorem sum_serializedCurrentState_sub_sq_le {T n : Nat}
    (q r : SerializedSpace T n) :
    (∑ i : Fin (T - 1),
      (serializedCurrentState q i - serializedCurrentState r i) ^ 2) ≤
        vecSq (q - r) := by
  let F : Fin (T - 1) → ℝ := fun i ↦
    (serializedCurrentState q i - serializedCurrentState r i) ^ 2
  have hpart := Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin (T - 1) ↦ i.val ≠ 0) F
  have hzero : (∑ i : {i : Fin (T - 1) // ¬ i.val ≠ 0}, F i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi0 : i.val.val = 0 := by omega
    simp [F, serializedCurrentState, hi0]
  have hall : (∑ i : Fin (T - 1), F i) =
      ∑ i : NonzeroBlock T, F i := by
    rw [hzero, add_zero] at hpart
    exact hpart.symm
  rw [show (∑ i : Fin (T - 1),
      (serializedCurrentState q i - serializedCurrentState r i) ^ 2) =
      ∑ i : Fin (T - 1), F i by rfl, hall]
  have hcoord : (∑ i : NonzeroBlock T, F i) =
      ∑ i : NonzeroBlock T, ((q - r) (predecessorStateIndex (n := n) i)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [F, serializedCurrentState, i.property, serializedState,
      predecessorStateIndex]
  rw [hcoord]
  exact sum_sq_comp_injective_le_vecSq _ predecessorStateIndex_injective (q - r)

private theorem localGateInput_vecSq_expansion {T n : Nat}
    (q r : SerializedSpace T n) (i : Fin (T - 1)) :
    vecSq (localGateInput q i - localGateInput r i) =
      (serializedA q i - serializedA r i) ^ 2 +
      (serializedB q i - serializedB r i) ^ 2 +
      (serializedCurrentState q i - serializedCurrentState r i) ^ 2 +
      (serializedState q i - serializedState r i) ^ 2 := by
  unfold vecSq NCPLVerification.vecSq
  simp [Fin.sum_univ_succ, localGateInput]
  ring

theorem sum_localGateInput_vecSq_le {T n : Nat}
    (q r : SerializedSpace T n) :
    (∑ i : Fin (T - 1), vecSq (localGateInput q i - localGateInput r i)) ≤
      4 * vecSq (q - r) := by
  have hA := sum_serializedA_sub_sq_le q r
  have hB := sum_serializedB_sub_sq_le q r
  have hC := sum_serializedCurrentState_sub_sq_le q r
  have hS := sum_serializedState_sub_sq_le q r
  simp_rw [localGateInput_vecSq_expansion]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  nlinarith

private theorem localGateGradient_vecSq_expansion (z w : LocalGateSpace) :
    vecSq (localGateGradient z - localGateGradient w) =
      (localGateA z - localGateA w) ^ 2 +
      (localGateB z - localGateB w) ^ 2 +
      (localGateCurrent z - localGateCurrent w) ^ 2 +
      (localGateNext z - localGateNext w) ^ 2 := by
  unfold vecSq NCPLVerification.vecSq
  simp [Fin.sum_univ_succ, localGateGradient]
  ring

private theorem sum_localGateGradient_vecSq_le {T n : Nat}
    (q r : SerializedSpace T n) :
    (∑ i : Fin (T - 1),
      vecSq (localGateGradient (localGateInput q i) -
        localGateGradient (localGateInput r i))) ≤
      4 * (2 * concreteLocalGateC) ^ 2 * vecSq (q - r) := by
  have hsum : (∑ i : Fin (T - 1),
      vecSq (localGateGradient (localGateInput q i) -
        localGateGradient (localGateInput r i))) ≤
      ∑ i : Fin (T - 1),
        (2 * concreteLocalGateC) ^ 2 *
          vecSq (localGateInput q i - localGateInput r i) := by
    exact Finset.sum_le_sum (fun i _ ↦
      localGateGradient_vecSq_sub_le (localGateInput q i) (localGateInput r i))
  rw [← Finset.mul_sum] at hsum
  have hin := sum_localGateInput_vecSq_le q r
  have hc : 0 ≤ (2 * concreteLocalGateC) ^ 2 := sq_nonneg _
  nlinarith

private theorem sum_comp_injective_le_sum_of_nonneg
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (idx : ι → κ) (hidx : Function.Injective idx)
    (f : κ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    (∑ i, f (idx i)) ≤ ∑ k, f k := by
  classical
  calc
    (∑ i, f (idx i)) = ∑ k ∈ Finset.univ.image idx, f k := by
      rw [Finset.sum_image hidx.injOn]
    _ ≤ ∑ k, f k := Finset.sum_le_univ_sum_of_nonneg hf

private theorem successorBlock_injective {T : Nat} :
    Function.Injective (fun j : Fin (T - 2) ↦
      (⟨j.val + 1, by omega⟩ : Fin (T - 1))) := by
  intro j k h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp at hv
  omega

private theorem gateCurrent_energy_le_all {T n : Nat}
    (q r : SerializedSpace T n) :
    vecSq (serializedGateCurrentField q - serializedGateCurrentField r) ≤
      ∑ i : Fin (T - 1),
        (localGateCurrent (localGateInput q i) -
          localGateCurrent (localGateInput r i)) ^ 2 := by
  rw [vecSq_gateCurrent_sub]
  exact sum_comp_injective_le_sum_of_nonneg
    (idx := fun j : Fin (T - 2) ↦
      (⟨j.val + 1, by omega⟩ : Fin (T - 1)))
    successorBlock_injective
    (fun i : Fin (T - 1) ↦
      (localGateCurrent (localGateInput q i) -
        localGateCurrent (localGateInput r i)) ^ 2)
    (fun i ↦ sq_nonneg _)

private theorem vecSq_add_le_two_gate {d : Nat} (u v : EVec d) :
    vecSq (u + v) ≤ 2 * vecSq u + 2 * vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (u i - v i)]

noncomputable def concreteNonlinearGateL0 : ℝ := 12 * concreteLocalGateC

theorem concreteNonlinearGateL0_nonneg : 0 ≤ concreteNonlinearGateL0 := by
  unfold concreteNonlinearGateL0
  exact mul_nonneg (by norm_num) concreteLocalGateC_nonneg

theorem serializedNonlinearGateField_vecSq_sub_le {T n : Nat}
    (q r : SerializedSpace T n) :
    vecSq (serializedNonlinearGateField q - serializedNonlinearGateField r) ≤
      concreteNonlinearGateL0 ^ 2 * vecSq (q - r) := by
  let A := serializedGateAField q - serializedGateAField r
  let B := serializedGateBField q - serializedGateBField r
  let N := serializedGateNextField q - serializedGateNextField r
  let C := serializedGateCurrentField q - serializedGateCurrentField r
  have hfield : serializedNonlinearGateField q - serializedNonlinearGateField r =
      ((A + B) + N) + C := by
    ext j
    simp [serializedNonlinearGateField, A, B, N, C]
    ring
  rw [hfield]
  have htop := vecSq_add_le_two_gate ((A + B) + N) C
  have hmid := vecSq_add_le_two_gate (A + B) N
  have hab := vecSq_add_le_two_gate A B
  have hA := vecSq_gateA_sub q r
  have hB := vecSq_gateB_sub q r
  have hN := vecSq_gateNext_sub q r
  have hC := gateCurrent_energy_le_all q r
  have hlocal := sum_localGateGradient_vecSq_le q r
  simp_rw [localGateGradient_vecSq_expansion] at hlocal
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib] at hlocal
  dsimp [A, B, N, C] at htop hmid hab
  change vecSq A = _ at hA
  change vecSq B = _ at hB
  change vecSq N = _ at hN
  change vecSq C ≤ _ at hC
  unfold concreteNonlinearGateL0
  nlinarith [vecSq_nonneg A, vecSq_nonneg B, vecSq_nonneg N, vecSq_nonneg C]

@[simp] theorem serializedNonlinearGateField_A {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedNonlinearGateField q (serializedAIndex (n := n) i) =
      localGateA (localGateInput q i) := by
  classical
  unfold serializedNonlinearGateField serializedGateAField serializedGateBField
    serializedGateNextField serializedGateCurrentField
  simp [serializedAIndex_ne_BIndex, serializedAIndex_ne_stateIndex]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : serializedAIndex (n := n) j ≠ serializedAIndex i :=
      fun h ↦ hji (serializedAIndex_injective h)
    simp [hne]
  · simp

@[simp] theorem serializedNonlinearGateField_B {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedNonlinearGateField q (serializedBIndex (n := n) i) =
      localGateB (localGateInput q i) := by
  classical
  unfold serializedNonlinearGateField serializedGateAField serializedGateBField
    serializedGateNextField serializedGateCurrentField
  simp [serializedAIndex_ne_BIndex, serializedBIndex_ne_stateIndex]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hne : serializedBIndex (n := n) j ≠ serializedBIndex i :=
      fun h ↦ hji (serializedBIndex_injective h)
    simp [hne]
  · simp

@[simp] theorem serializedNonlinearGateField_Y {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) (k : Fin n) :
    serializedNonlinearGateField q (serializedDualIndex i k) = 0 := by
  classical
  unfold serializedNonlinearGateField serializedGateAField serializedGateBField
    serializedGateNextField serializedGateCurrentField
  simp [serializedAIndex_ne_dualIndex, serializedBIndex_ne_dualIndex,
    serializedStateIndex_ne_dualIndex]

@[simp] theorem serializedNonlinearGateField_state {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedNonlinearGateField q (serializedStateIndex (n := n) i) =
      localGateNext (localGateInput q i) +
        if h : i.val + 1 < T - 1 then
          localGateCurrent
            (localGateInput q (⟨i.val + 1, h⟩ : Fin (T - 1)))
        else 0 := by
  classical
  unfold serializedNonlinearGateField serializedGateAField serializedGateBField
    serializedGateNextField serializedGateCurrentField
  simp [serializedAIndex_ne_stateIndex, serializedBIndex_ne_stateIndex]
  rw [Finset.sum_eq_single i]
  · simp only [Pi.single_eq_same, add_zero]
    split_ifs with h
    · let j : Fin (T - 2) := ⟨i.val, by omega⟩
      rw [Finset.sum_eq_single j]
      · simp [j]
      · intro c _ hcj
        have hne : serializedStateIndex (n := n)
            (⟨c.val, by omega⟩ : Fin (T - 1)) ≠ serializedStateIndex i := by
          intro heq
          have hi := serializedStateIndex_injective heq
          apply hcj
          apply Fin.ext
          have hv := congrArg Fin.val hi
          simpa [j] using hv
        simp [hne]
      · simp
    · congr 1
      apply Finset.sum_eq_zero
      intro c _
      have hne : serializedStateIndex (n := n)
          (⟨c.val, by omega⟩ : Fin (T - 1)) ≠ serializedStateIndex i := by
        intro heq
        have hi := serializedStateIndex_injective heq
        have hv := congrArg Fin.val hi
        simp at hv
        omega
      simp [hne]
  · intro j _ hji
    have hne : serializedStateIndex (n := n) j ≠ serializedStateIndex i :=
      fun h ↦ hji (serializedStateIndex_injective h)
    simp [hne]
  · simp

end NCCLowerBoundVerification
