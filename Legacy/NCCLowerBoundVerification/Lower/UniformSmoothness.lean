import NCCLowerBoundVerification.Lower.UniformInner
import NCCLowerBoundVerification.Lower.UniformNonlinear
import NCCLowerBoundVerification.Lower.TerminalConcrete

/-!
# Dimension-free smoothness of the literal unscaled construction

This file combines the independent linear inner field, the finitely
overlapping four-coordinate nonlinear gates, and the radial pulse field.
-/

namespace NCCLowerBoundVerification

noncomputable section

open scoped BigOperators
open Finset Set

/-- Orthogonal projection onto the serialized `A` and `B` pulse coordinates. -/
def serializedPulseMask {T n : Nat} (q : SerializedSpace T n) :
    SerializedSpace T n := fun j =>
  let ik := finProdFinEquiv.symm j
  if ik.2.val = 0 ∨ ik.2.val = n + 1 then q j else 0

@[simp] theorem serializedPulseMask_apply_prod {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) (k : Fin (n + 3)) :
    serializedPulseMask q (finProdFinEquiv (i, k)) =
      if k.val = 0 ∨ k.val = n + 1 then
        serializedInputBlock q i k else 0 := by
  simp [serializedPulseMask, serializedInputBlock]

private theorem uniform_sum_fin_add_three {n : Nat}
    (f : Fin (n + 3) → ℝ) :
    (∑ k : Fin (n + 3), f k) =
      f ⟨0, by omega⟩ +
        (∑ k : Fin n, f ⟨k.val + 1, by omega⟩) +
        f ⟨n + 1, by omega⟩ + f ⟨n + 2, by omega⟩ := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hsum : (∑ i : Fin n, f i.castSucc.castSucc.succ) =
      ∑ i : Fin n, f ⟨i.val + 1, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    congr
  have hlastB : f (Fin.last n).castSucc.succ =
      f ⟨n + 1, by omega⟩ := by congr
  have hlastState : f (Fin.last (n + 1)).succ =
      f ⟨n + 2, by omega⟩ := by congr
  rw [hsum, hlastB, hlastState]
  have hsumComm : (∑ i : Fin n, f ⟨i.val + 1, by omega⟩) =
      ∑ i : Fin n, f ⟨1 + i.val, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg f
    apply Fin.ext
    simp [Nat.add_comm]
  rw [hsumComm]
  have hzero : f (0 : Fin (n + 3)) = f ⟨0, by omega⟩ := by congr
  rw [hzero]
  abel_nf

theorem serializedPulseMask_vecSq_sub_le {T n : Nat}
    (q r : SerializedSpace T n) :
    vecSq (serializedPulseMask q - serializedPulseMask r) ≤ vecSq (q - r) := by
  unfold vecSq NCPLVerification.vecSq
  apply Finset.sum_le_sum
  intro j _
  simp only [Pi.sub_apply]
  unfold serializedPulseMask
  dsimp only
  split_ifs <;> nlinarith

theorem vecSq_serializedPulseMask {T n : Nat} (q : SerializedSpace T n) :
    vecSq (serializedPulseMask q) = serializedPulseSq q := by
  unfold vecSq NCPLVerification.vecSq serializedPulseSq
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [uniform_sum_fin_add_three]
  have hmid : (∑ k : Fin n,
      serializedPulseMask q
        (finProdFinEquiv (i, (⟨k.val + 1, by omega⟩ :
          Fin (n + 3)))) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    rw [serializedPulseMask_apply_prod]
    have hk : ¬ (k.val + 1 = 0 ∨ k.val + 1 = n + 1) := by omega
    rw [if_neg hk]
    norm_num
  rw [hmid]
  simp only [serializedPulseMask_apply_prod]
  rw [serializedInputBlock_A, serializedInputBlock_B]
  simp only [true_or, or_true, if_true]
  have hstate : ¬ (n + 2 = 0 ∨ n + 2 = n + 1) := by omega
  rw [if_neg hstate]
  norm_num

/-- The radial gradient, with zeros on all non-pulse coordinates. -/
def serializedRadialField {T n : Nat} (q : SerializedSpace T n) :
    SerializedSpace T n :=
  radialGradient concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
    concreteUnscaledParameters.K (serializedPulseMask q)

theorem serializedRadialField_vecSq_sub_le {T n : Nat}
    (q r : SerializedSpace T n) :
    vecSq (serializedRadialField q - serializedRadialField r) ≤
      concreteRadialEuclideanL0 ^ 2 * vecSq (q - r) := by
  have hrad := concreteRadialGradient_vecSq_sub_le
    (serializedPulseMask q) (serializedPulseMask r)
  have hmask := serializedPulseMask_vecSq_sub_le q r
  unfold serializedRadialField
  exact hrad.trans (mul_le_mul_of_nonneg_left hmask (sq_nonneg _))

/-- Flip the serialized dual coordinates and leave primal coordinates fixed. -/
def serializedTrueSign {T n : Nat} (v : SerializedSpace T n) :
    SerializedSpace T n := fun j =>
  let ik := finProdFinEquiv.symm j
  if 1 ≤ ik.2.val ∧ ik.2.val ≤ n then -v j else v j

theorem vecSq_serializedTrueSign {T n : Nat} (v : SerializedSpace T n) :
    vecSq (serializedTrueSign v) = vecSq v := by
  unfold vecSq NCPLVerification.vecSq serializedTrueSign
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  split_ifs <;> ring

theorem serializedTrueSign_sub {T n : Nat} (v w : SerializedSpace T n) :
    serializedTrueSign (v - w) =
      serializedTrueSign v - serializedTrueSign w := by
  funext j
  simp only [serializedTrueSign, Pi.sub_apply]
  by_cases h : 1 ≤ (finProdFinEquiv.symm j).2.val ∧
      (finProdFinEquiv.symm j).2.val ≤ n
  · rw [if_pos h, if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h, if_neg h]

def serializedLinearTrueField {T n : Nat} (hn : 0 < n)
    (q : SerializedSpace T n) : SerializedSpace T n :=
  serializedTrueSign
    (totalLinearSerializedField hn concreteUnscaledParameters.gamma q)

theorem serializedLinearTrueField_vecSq_sub_le {T n : Nat} (hn : 10 ≤ n)
    (q r : SerializedSpace T n) :
    vecSq (serializedLinearTrueField (by omega) q -
        serializedLinearTrueField (by omega) r) ≤
      50000200 * vecSq (q - r) := by
  unfold serializedLinearTrueField
  rw [← serializedTrueSign_sub, vecSq_serializedTrueSign]
  exact totalLinearSerializedField_sub_vecSq_le hn
    concreteGateThreshold.gamma_pos.le concreteGateThreshold.gamma_le_half q r

private theorem uniform_serializedAIndex_prod {T n : Nat}
    (i : Fin (T - 1)) :
    serializedAIndex (n := n) i =
      finProdFinEquiv (i, (⟨0, by omega⟩ : Fin (n + 3))) := by
  apply Fin.ext
  simp [serializedAIndex, finProdFinEquiv, Nat.mul_comm]

private theorem uniform_serializedDualIndex_prod {T n : Nat}
    (i : Fin (T - 1)) (k : Fin n) :
    serializedDualIndex i k =
      finProdFinEquiv (i, (⟨k.val + 1, by omega⟩ : Fin (n + 3))) := by
  apply Fin.ext
  simp [serializedDualIndex, finProdFinEquiv, Nat.mul_comm]
  omega

private theorem uniform_serializedBIndex_prod {T n : Nat}
    (i : Fin (T - 1)) :
    serializedBIndex (n := n) i =
      finProdFinEquiv (i, (⟨n + 1, by omega⟩ : Fin (n + 3))) := by
  apply Fin.ext
  simp [serializedBIndex, finProdFinEquiv, Nat.mul_comm]
  omega

private theorem uniform_serializedStateIndex_prod {T n : Nat}
    (i : Fin (T - 1)) :
    serializedStateIndex (n := n) i =
      finProdFinEquiv (i, (⟨n + 2, by omega⟩ : Fin (n + 3))) := by
  apply Fin.ext
  simp [serializedStateIndex, finProdFinEquiv, Nat.mul_comm]
  omega

@[simp] theorem serializedPulseMask_A {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) :
    serializedPulseMask q (serializedAIndex (n := n) i) = serializedA q i := by
  rw [uniform_serializedAIndex_prod, serializedPulseMask_apply_prod]
  simp only [if_pos (Or.inl rfl)]
  exact serializedInputBlock_A q i

@[simp] theorem serializedPulseMask_B {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) :
    serializedPulseMask q (serializedBIndex (n := n) i) = serializedB q i := by
  rw [uniform_serializedBIndex_prod, serializedPulseMask_apply_prod]
  simp

@[simp] theorem serializedPulseMask_Y {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) (k : Fin n) :
    serializedPulseMask q (serializedDualIndex i k) = 0 := by
  rw [uniform_serializedDualIndex_prod, serializedPulseMask_apply_prod]
  have hk : ¬ (k.val + 1 = 0 ∨ k.val + 1 = n + 1) := by omega
  rw [if_neg hk]

@[simp] theorem serializedPulseMask_state {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedPulseMask q (serializedStateIndex (n := n) i) = 0 := by
  rw [uniform_serializedStateIndex_prod, serializedPulseMask_apply_prod]
  have hs : ¬ (n + 2 = 0 ∨ n + 2 = n + 1) := by omega
  rw [if_neg hs]

@[simp] theorem serializedRadialField_A {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) :
    serializedRadialField q (serializedAIndex (n := n) i) =
      2 * Sigma3Deriv concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
        concreteUnscaledParameters.K (serializedPulseSq q) * serializedA q i := by
  unfold serializedRadialField radialGradient
  rw [vecSq_serializedPulseMask, serializedPulseMask_A]

@[simp] theorem serializedRadialField_B {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) :
    serializedRadialField q (serializedBIndex (n := n) i) =
      2 * Sigma3Deriv concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
        concreteUnscaledParameters.K (serializedPulseSq q) * serializedB q i := by
  unfold serializedRadialField radialGradient
  rw [vecSq_serializedPulseMask, serializedPulseMask_B]

@[simp] theorem serializedRadialField_Y {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) (k : Fin n) :
    serializedRadialField q (serializedDualIndex i k) = 0 := by
  unfold serializedRadialField radialGradient
  simp

@[simp] theorem serializedRadialField_state {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedRadialField q (serializedStateIndex (n := n) i) = 0 := by
  unfold serializedRadialField radialGradient
  simp

@[simp] theorem serializedLinearTrueField_A {T n : Nat} (hn : 0 < n)
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedLinearTrueField hn q (serializedAIndex (n := n) i) =
      innerGradA hn (innerC hn) (serializedDualBlock q i) +
        2 * (innerC1 hn + concreteUnscaledParameters.gamma) * serializedA q i := by
  rw [uniform_serializedAIndex_prod]
  unfold serializedLinearTrueField serializedTrueSign totalLinearSerializedField
  simp [innerSerializedField_apply_prod, diagonalSerializedField_apply_prod]
  have hI : innerBlockField hn (serializedA q i) (serializedB q i)
      (serializedDualBlock q i) (0 : Fin (n + 3)) =
        innerGradA hn (innerC hn) (serializedDualBlock q i) := by
    simpa using innerBlockField_A hn (serializedA q i) (serializedB q i)
      (serializedDualBlock q i)
  have hD : diagonalBlockField hn concreteUnscaledParameters.gamma
      (serializedA q i) (serializedB q i) (0 : Fin (n + 3)) =
        2 * (innerC1 hn + concreteUnscaledParameters.gamma) * serializedA q i := by
    simpa using diagonalBlockField_A hn concreteUnscaledParameters.gamma
      (serializedA q i) (serializedB q i)
  rw [hI, hD]

@[simp] theorem serializedLinearTrueField_B {T n : Nat} (hn : 0 < n)
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedLinearTrueField hn q (serializedBIndex (n := n) i) =
      innerGradB hn (innerC hn) (serializedDualBlock q i) +
        2 * (innerC2 hn + concreteUnscaledParameters.gamma) * serializedB q i := by
  rw [uniform_serializedBIndex_prod]
  unfold serializedLinearTrueField serializedTrueSign totalLinearSerializedField
  simp [innerSerializedField_apply_prod, diagonalSerializedField_apply_prod]

@[simp] theorem serializedLinearTrueField_Y {T n : Nat} (hn : 0 < n)
    (q : SerializedSpace T n) (i : Fin (T - 1)) (k : Fin n) :
    serializedLinearTrueField hn q (serializedDualIndex i k) =
      -serializedSaddleGradY hn concreteUnscaledParameters q i k := by
  rw [uniform_serializedDualIndex_prod]
  unfold serializedLinearTrueField serializedTrueSign totalLinearSerializedField
    serializedSaddleGradY
  simp [innerSerializedField_apply_prod, diagonalSerializedField_apply_prod]

@[simp] theorem serializedLinearTrueField_state {T n : Nat} (hn : 0 < n)
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedLinearTrueField hn q (serializedStateIndex (n := n) i) = 0 := by
  rw [uniform_serializedStateIndex_prod]
  unfold serializedLinearTrueField serializedTrueSign totalLinearSerializedField
  simp [innerSerializedField_apply_prod, diagonalSerializedField_apply_prod]

theorem serializedNonlinearGateField_state_eq {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedNonlinearGateField q (serializedStateIndex (n := n) i) =
      serializedGradState concreteUnscaledParameters q i := by
  rw [serializedNonlinearGateField_state, localGateNext_input]
  split_ifs with h
  · have hcur : serializedCurrentState q
        (⟨i.val + 1, h⟩ : Fin (T - 1)) = serializedState q i := by
      unfold serializedCurrentState
      simp only [Nat.add_eq_zero, one_ne_zero, and_false, ↓reduceDIte]
      apply congrArg (serializedState q)
      apply Fin.ext
      simp
    rw [localGateCurrent_input]
    unfold serializedGradState serializedNextStateContribution
      serializedBlockNextGrad serializedBlockCurrentGrad
      serializedClippedCurrent serializedClippedNext
    simp only [h, ↓reduceDIte]
    rw [hcur]
  · unfold serializedGradState serializedNextStateContribution
      serializedBlockNextGrad serializedClippedCurrent serializedClippedNext
    simp only [h, ↓reduceDIte, add_zero]

def concreteUniformSerializedField {T n : Nat} (hn : 0 < n)
    (q : SerializedSpace T n) : SerializedSpace T n :=
  serializedLinearTrueField hn q + serializedNonlinearGateField q +
    serializedRadialField q

theorem concreteUniformSerializedField_eq_trueGradient {T n : Nat}
    (hn : 0 < n) (q : SerializedSpace T n) :
    concreteUniformSerializedField hn q =
      serializedTrueGradient hn concreteUnscaledParameters q := by
  apply SerializedSpace.ext_blocks
  · intro i
    unfold serializedA
    simp [concreteUniformSerializedField, serializedTrueGradient_A,
      serializedGradA, localGateA_input]
    ring
  · intro i k
    unfold serializedY
    simp [concreteUniformSerializedField, serializedTrueGradient_Y]
  · intro i
    unfold serializedB
    simp [concreteUniformSerializedField, serializedTrueGradient_B,
      serializedGradB, localGateB_input]
  · intro i
    unfold concreteUniformSerializedField serializedState
    simp only [Pi.add_apply]
    rw [serializedLinearTrueField_state,
      serializedNonlinearGateField_state_eq,
      serializedRadialField_state, serializedTrueGradient_state]
    ring

private theorem uniform_vecSq_add_le_two {d : Nat} (u v : EVec d) :
    vecSq (u + v) ≤ 2 * vecSq u + 2 * vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (u i - v i)]

noncomputable def concreteL0 : ℝ :=
  15000 + 2 * concreteNonlinearGateL0 + 2 * concreteRadialEuclideanL0

theorem concreteL0_pos : 0 < concreteL0 := by
  unfold concreteL0
  have hn := concreteNonlinearGateL0_nonneg
  have hr := concreteRadialEuclideanL0_nonneg
  linarith

theorem concreteUniformSerializedField_vecSq_sub_le {T n : Nat}
    (hn : 10 ≤ n) (q r : SerializedSpace T n) :
    vecSq (concreteUniformSerializedField (by omega) q -
        concreteUniformSerializedField (by omega) r) ≤
      concreteL0 ^ 2 * vecSq (q - r) := by
  let L := serializedLinearTrueField (T := T) (n := n) (by omega) q -
    serializedLinearTrueField (by omega) r
  let N := serializedNonlinearGateField q - serializedNonlinearGateField r
  let R := serializedRadialField q - serializedRadialField r
  have heq : concreteUniformSerializedField (by omega) q -
      concreteUniformSerializedField (by omega) r = (L + N) + R := by
    ext j
    simp [concreteUniformSerializedField, L, N, R]
    ring
  rw [heq]
  have htop := uniform_vecSq_add_le_two (L + N) R
  have hln := uniform_vecSq_add_le_two L N
  have hL := serializedLinearTrueField_vecSq_sub_le hn q r
  have hN := serializedNonlinearGateField_vecSq_sub_le q r
  have hR := serializedRadialField_vecSq_sub_le q r
  change vecSq L ≤ _ at hL
  change vecSq N ≤ _ at hN
  change vecSq R ≤ _ at hR
  have hq := vecSq_nonneg (q - r)
  have hn0 := concreteNonlinearGateL0_nonneg
  have hr0 := concreteRadialEuclideanL0_nonneg
  have hraw : vecSq ((L + N) + R) ≤
      (4 * 50000200 + 4 * concreteNonlinearGateL0 ^ 2 +
        2 * concreteRadialEuclideanL0 ^ 2) * vecSq (q - r) := by
    nlinarith [vecSq_nonneg L, vecSq_nonneg N, vecSq_nonneg R]
  have hcoef :
      4 * 50000200 + 4 * concreteNonlinearGateL0 ^ 2 +
          2 * concreteRadialEuclideanL0 ^ 2 ≤ concreteL0 ^ 2 := by
    unfold concreteL0
    nlinarith [mul_nonneg hn0 hr0]
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoef hq)

theorem concreteSerializedTrueGradient_vecSq_sub_le {T n : Nat}
    (hn : 10 ≤ n) (q r : SerializedSpace T n) :
    vecSq (serializedTrueGradient (by omega) concreteUnscaledParameters q -
        serializedTrueGradient (by omega) concreteUnscaledParameters r) ≤
      concreteL0 ^ 2 * vecSq (q - r) := by
  rw [← concreteUniformSerializedField_eq_trueGradient,
    ← concreteUniformSerializedField_eq_trueGradient]
  exact concreteUniformSerializedField_vecSq_sub_le hn q r

private def primalStorageEquiv (T : Nat) :
    Fin (T - 1) × Fin 3 ≃ Fin (3 * (T - 1)) where
  toFun p := Fin.cast (Nat.mul_comm (T - 1) 3) (finProdFinEquiv p)
  invFun j := finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 3 (T - 1)) j)
  left_inv p := by simp
  right_inv j := by
    apply Fin.ext
    exact Nat.mod_add_div j.val 3

private def primalStorageBlock {T : Nat} (x : UnscaledPrimal T)
    (i : Fin (T - 1)) : EVec 3 := fun k ↦ x (primalStorageEquiv T (i, k))

@[simp] private theorem primalStorageBlock_A {T : Nat} (x : UnscaledPrimal T)
    (i : Fin (T - 1)) : primalStorageBlock x i ⟨0, by omega⟩ = primalA x i := by
  unfold primalStorageBlock primalStorageEquiv primalA
  apply congrArg x
  apply Fin.ext
  simp [primalStorageEquiv, finProdFinEquiv, primalAIndex]

@[simp] private theorem primalStorageBlock_B {T : Nat} (x : UnscaledPrimal T)
    (i : Fin (T - 1)) : primalStorageBlock x i ⟨1, by omega⟩ = primalB x i := by
  unfold primalStorageBlock primalStorageEquiv primalB
  apply congrArg x
  apply Fin.ext
  simp [primalStorageEquiv, finProdFinEquiv, primalBIndex]
  omega

@[simp] private theorem primalStorageBlock_state {T : Nat}
    (x : UnscaledPrimal T) (i : Fin (T - 1)) :
    primalStorageBlock x i ⟨2, by omega⟩ = primalState x i := by
  unfold primalStorageBlock primalStorageEquiv primalState
  apply congrArg x
  apply Fin.ext
  simp [primalStorageEquiv, finProdFinEquiv, primalStateIndex]
  omega

private theorem vecSq_primalStorageBlock {T : Nat} (x : UnscaledPrimal T)
    (i : Fin (T - 1)) :
    vecSq (primalStorageBlock x i) =
      primalA x i ^ 2 + primalB x i ^ 2 + primalState x i ^ 2 := by
  unfold vecSq NCPLVerification.vecSq
  simp [Fin.sum_univ_succ]
  have hA : primalStorageBlock x i (0 : Fin 3) = primalA x i := by
    simpa using primalStorageBlock_A x i
  have hB : primalStorageBlock x i (1 : Fin 3) = primalB x i := by
    simpa using primalStorageBlock_B x i
  have hS : primalStorageBlock x i (2 : Fin 3) = primalState x i := by
    simpa using primalStorageBlock_state x i
  rw [hA, hB, hS]
  ring

theorem vecSq_unscaledPrimal_blocks {T : Nat} (x : UnscaledPrimal T) :
    vecSq x = ∑ i : Fin (T - 1),
      (primalA x i ^ 2 + primalB x i ^ 2 + primalState x i ^ 2) := by
  have hblocks : vecSq x = ∑ i : Fin (T - 1),
      vecSq (primalStorageBlock x i) := by
    unfold vecSq NCPLVerification.vecSq primalStorageBlock
    rw [← Equiv.sum_comp (primalStorageEquiv T), Fintype.sum_prod_type]
  rw [hblocks]
  apply Finset.sum_congr rfl
  intro i _
  rw [vecSq_primalStorageBlock]

private theorem vecSq_serializedInputBlock_serialize {T n : Nat}
    (x : UnscaledPrimal T) (y : UnscaledDual T n) (i : Fin (T - 1)) :
    vecSq (serializedInputBlock (serializeUnscaled x y) i) =
      primalA x i ^ 2 + vecSq (dualBlock y i) +
        primalB x i ^ 2 + primalState x i ^ 2 := by
  rw [vecSq_serializedInputBlock]
  simp

theorem vecSq_serializeUnscaled {T n : Nat}
    (x : UnscaledPrimal T) (y : UnscaledDual T n) :
    vecSq (serializeUnscaled x y) = jointSq x y := by
  have hser : vecSq (serializeUnscaled x y) =
      ∑ i : Fin (T - 1),
        vecSq (serializedInputBlock (serializeUnscaled x y) i) := by
    unfold vecSq NCPLVerification.vecSq serializedInputBlock
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  rw [hser]
  simp_rw [vecSq_serializedInputBlock_serialize]
  unfold jointSq
  rw [vecSq_unscaledPrimal_blocks, vecSq_eq_sum_dualBlock]
  simp only [Finset.sum_add_distrib]
  ring

theorem serializeUnscaled_sub {T n : Nat}
    (x x' : UnscaledPrimal T) (y y' : UnscaledDual T n) :
    serializeUnscaled (x - x') (y - y') =
      serializeUnscaled x y - serializeUnscaled x' y' := by
  have h := (serializeUnscaledLinear (T := T) (n := n)).map_sub (x, y) (x', y')
  exact h

private theorem uniform_dualBlockIndex_pair {T n : Nat}
    (i : Fin (T - 1)) (k : Fin n) :
    dualBlockIndexPair (dualBlockIndex i k) = (i, k) := by
  unfold dualBlockIndexPair
  have hcast : Fin.cast (Nat.mul_comm n (T - 1)) (dualBlockIndex i k) =
      finProdFinEquiv (i, k) := by
    apply Fin.ext
    simp [dualBlockIndex, finProdFinEquiv]
    omega
  rw [hcast, Equiv.symm_apply_apply]

private theorem uniform_serializeUnscaled_evecBasis_Y {T n : Nat}
    (i : Fin (T - 1)) (k : Fin n) :
    serializeUnscaled (0 : UnscaledPrimal T)
        (NCPLVerification.evecBasis (dualBlockIndex i k) : UnscaledDual T n) =
      (NCPLVerification.evecBasis (serializedDualIndex i k) :
        SerializedSpace T n) := by
  apply SerializedSpace.ext_blocks
  · intro j
    rw [serializedA_serializeUnscaled]
    simp [primalA, serializedA, NCPLVerification.evecBasis,
      serializedAIndex_ne_dualIndex]
  · intro j l
    rw [serializedY_serializeUnscaled]
    unfold dualBlock serializedY NCPLVerification.evecBasis
    by_cases hji : j = i
    · subst j
      by_cases hlk : l = k
      · subst l
        simp
      · have hdual : dualBlockIndex i l ≠ dualBlockIndex i k := by
          intro h
          have hp := congrArg dualBlockIndexPair h
          rw [uniform_dualBlockIndex_pair, uniform_dualBlockIndex_pair] at hp
          exact hlk (congrArg Prod.snd hp)
        have hserial : serializedDualIndex i l ≠ serializedDualIndex i k := by
          intro h
          have hp : (i, l) = (i, k) := serializedDualIndex_injective h
          exact hlk (congrArg Prod.snd hp)
        simp [hdual, hserial]
    · have hdual : dualBlockIndex j l ≠ dualBlockIndex i k := by
        intro h
        have hp := congrArg dualBlockIndexPair h
        rw [uniform_dualBlockIndex_pair, uniform_dualBlockIndex_pair] at hp
        exact hji (congrArg Prod.fst hp)
      have hserial : serializedDualIndex j l ≠ serializedDualIndex i k := by
        intro h
        have hp : (j, l) = (i, k) := serializedDualIndex_injective h
        exact hji (congrArg Prod.fst hp)
      simp [hdual, hserial]
  · intro j
    rw [serializedB_serializeUnscaled]
    simp [primalB, serializedB, NCPLVerification.evecBasis,
      serializedBIndex_ne_dualIndex]
  · intro j
    rw [serializedState_serializeUnscaled]
    simp [primalState, serializedState, NCPLVerification.evecBasis,
      serializedStateIndex_ne_dualIndex]

theorem dualBlock_unscaledTrueGradY_uniform {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (i : Fin (T - 1)) (k : Fin n) :
    dualBlock (unscaledTrueGradY hn P x y) i k =
      -serializedSaddleGradY hn P (serializeUnscaled x y) i k := by
  let h : UnscaledDual T n := NCPLVerification.evecBasis (dualBlockIndex i k)
  have hrep := (unscaledTrueGradient_representsJointGradient
    (T := T) hn P).2 x y (0 : UnscaledPrimal T) h
  rw [(unscaledObjective_hasFDerivAt (T := T) hn P x y).fderiv] at hrep
  simp only [ContinuousLinearMap.comp_apply, serializeUnscaledCLM_apply] at hrep
  rw [show serializeUnscaled (0 : UnscaledPrimal T) h =
      (NCPLVerification.evecBasis (serializedDualIndex i k) :
        SerializedSpace T n) by
        exact uniform_serializeUnscaled_evecBasis_Y i k] at hrep
  simp [h, NCPLVerification.evecDot_apply, NCPLVerification.evecBasis,
    serializedTrueGradient_Y] at hrep
  exact hrep.symm

theorem serializeUnscaled_trueGradient {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) (y : UnscaledDual T n) :
    serializeUnscaled (unscaledTrueGradX hn P x y)
        (unscaledTrueGradY hn P x y) =
      serializedTrueGradient hn P (serializeUnscaled x y) := by
  apply SerializedSpace.ext_blocks
  · intro i
    rw [serializedA_serializeUnscaled, primalA_unscaledTrueGradX]
    unfold serializedA
    rw [serializedTrueGradient_A]
  · intro i k
    rw [serializedY_serializeUnscaled, dualBlock_unscaledTrueGradY_uniform]
    unfold serializedY
    rw [serializedTrueGradient_Y]
  · intro i
    rw [serializedB_serializeUnscaled, primalB_unscaledTrueGradX]
    unfold serializedB
    rw [serializedTrueGradient_B]
  · intro i
    rw [serializedState_serializeUnscaled, primalState_unscaledTrueGradX]
    unfold serializedState
    rw [serializedTrueGradient_state]

/-- Literal separated primal/dual gradients satisfy the uniform joint
Euclidean estimate required by `ScalingSource`. -/
theorem concrete_unscaled_jointly_smooth {T n : Nat} (hn : 10 ≤ n)
    (x x' : UnscaledPrimal T) (y y' : UnscaledDual T n) :
    jointSq
        (unscaledTrueGradX (by omega) concreteUnscaledParameters x y -
          unscaledTrueGradX (by omega) concreteUnscaledParameters x' y')
        (unscaledTrueGradY (by omega) concreteUnscaledParameters x y -
          unscaledTrueGradY (by omega) concreteUnscaledParameters x' y') ≤
      concreteL0 ^ 2 * jointSq (x - x') (y - y') := by
  rw [← vecSq_serializeUnscaled]
  rw [serializeUnscaled_sub]
  rw [serializeUnscaled_trueGradient, serializeUnscaled_trueGradient]
  have hs := concreteSerializedTrueGradient_vecSq_sub_le hn
    (serializeUnscaled x y) (serializeUnscaled x' y')
  rw [← serializeUnscaled_sub, vecSq_serializeUnscaled] at hs
  exact hs

/-- Uniform source package for the literal unscaled lower-bound instance.
The smoothness constant is independent of `T`, `n`, and the dual diameter. -/
theorem concrete_unscaled_scalingSource {T n : Nat}
    (hT : 1 ≤ T) (hn : 10 ≤ n) {D0 Delta0 : ℝ}
    (hD0 : 0 < D0) (hgap : concreteDelta0 T ≤ Delta0) :
    ScalingSource concreteL0 D0 Delta0
      (unscaledNCCInstance (T := T) (n := n) (by omega)
        concreteUnscaledParameters D0) := by
  obtain ⟨hx0, hXne, hXcl, hXcv, hYne, hYcl, hYcv, hdiam⟩ :=
    unscaledNCCInstance_domain_data (T := T) (n := n) (by omega)
      concreteUnscaledParameters hD0.le
  refine
    { x0_mem := hx0
      X_nonempty := hXne
      X_closed := hXcl
      X_convex := hXcv
      Y_nonempty := hYne
      Y_closed := hYcl
      Y_convex := hYcv
      gradient_representation :=
        unscaledNCCInstance_gradient_representation (T := T) (n := n) (by omega)
          concreteUnscaledParameters D0
      jointly_smooth := ?_
      dual_concave := ?_
      maximum_attained := ?_
      value_bddBelow := concreteUnscaledValue_bddBelow (T := T) (n := n) hn hD0.le
      initial_gap :=
        (concreteUnscaled_initial_gap (T := T) (n := n) hn hD0.le).trans hgap
      dual_diameter := hdiam }
  · intro x _ y _ x' _ y' _
    exact concrete_unscaled_jointly_smooth hn x x' y y'
  · intro x _
    exact unscaledObjective_dual_concave (T := T) (n := n) (by omega)
      concreteUnscaledParameters x D0
  · intro x _
    exact unscaledObjective_maximum_attained (T := T) (n := n) (by omega)
      concreteUnscaledParameters hD0.le x

end

end NCCLowerBoundVerification
