import NCCLowerBoundVerification.Lower.GreenMatrix
import NCCLowerBoundVerification.Lower.UnscaledObjective

/-!
# Dimension-free Euclidean estimate for the inner path block

This module isolates the linear inner-chain gradient from the nonlinear
memory gates.  Its constants are numerical and independent of both chain
dimensions.
-/

namespace NCCLowerBoundVerification

noncomputable section

def pathLaplacianVector {n : Nat} (w : EVec n) : EVec n :=
  fun i => pathLaplacianCoord w i

private theorem sq_add_le_two (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem pathLaplacianVector_vecSq_le {n : Nat} (w : EVec n) :
    vecSq (pathLaplacianVector w) ≤ 4 * pathEnergy n w := by
  cases n with
  | zero => simp [vecSq, NCPLVerification.vecSq, pathLaplacianVector,
      pathEnergy]
  | succ n =>
      let prev : Fin (n + 1) → ℝ := fun i =>
        if h : 0 < i.val then w i - w ⟨i.val - 1, by omega⟩ else 0
      let next : Fin (n + 1) → ℝ := fun i =>
        if h : i.val + 1 < n + 1 then w i - w ⟨i.val + 1, h⟩ else 0
      have hcoord : ∀ i : Fin (n + 1),
          (pathLaplacianVector w i) ^ 2 ≤
            2 * (prev i) ^ 2 + 2 * (next i) ^ 2 := by
        intro i
        unfold pathLaplacianVector pathLaplacianCoord prev next
        exact sq_add_le_two _ _
      have hprev : (∑ i : Fin (n + 1), (prev i) ^ 2) = pathEnergy (n + 1) w := by
        rw [Fin.sum_univ_succ]
        simp only [prev, Fin.val_zero, lt_self_iff_false, ↓reduceDIte,
          pathEnergy]
        norm_num
        apply Finset.sum_congr rfl
        intro i _
        have hp : (⟨i.val, by omega⟩ : Fin (n + 1)) = i.castSucc := by
          apply Fin.ext
          rfl
        rw [hp]
        ring
      have hnext : (∑ i : Fin (n + 1), (next i) ^ 2) = pathEnergy (n + 1) w := by
        rw [Fin.sum_univ_castSucc]
        simp only [next, Fin.val_last, lt_self_iff_false, ↓reduceDIte,
          pathEnergy]
        norm_num
        apply Finset.sum_congr rfl
        intro i _
        rfl
      calc
        vecSq (pathLaplacianVector w) ≤
            ∑ i : Fin (n + 1),
              (2 * (prev i) ^ 2 + 2 * (next i) ^ 2) := by
          unfold vecSq NCPLVerification.vecSq
          exact Finset.sum_le_sum fun i _ => hcoord i
        _ = 2 * (∑ i : Fin (n + 1), (prev i) ^ 2) +
              2 * (∑ i : Fin (n + 1), (next i) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ = 4 * pathEnergy (n + 1) w := by rw [hprev, hnext]; ring

def regularizedPathVector {n : Nat} (w : EVec n) : EVec n :=
  fun i => regularizedPathCoord w i

theorem regularizedPathVector_vecSq_le_of_ten {n : Nat} (hn : 10 ≤ n)
    (w : EVec n) :
    vecSq (regularizedPathVector w) ≤ 33 * vecSq w := by
  let r := pathRegularization n
  have hr : 0 ≤ r := pathRegularization_nonneg n
  have hrle : r ≤ (1 / 100 : ℝ) := by
    dsimp [r, pathRegularization]
    have hnreal : (10 : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)]
    nlinarith [sq_nonneg ((n : ℝ) - 10)]
  have hcoord : regularizedPathVector w =
      r • w + pathLaplacianVector w := by
    funext i
    simp [regularizedPathVector, regularizedPathCoord, pathLaplacianVector, r]
  rw [hcoord]
  have hadd : vecSq (r • w + pathLaplacianVector w) ≤
      2 * vecSq (r • w) + 2 * vecSq (pathLaplacianVector w) := by
    unfold vecSq NCPLVerification.vecSq
    calc
      (∑ i, ((r • w + pathLaplacianVector w) i) ^ 2) ≤
          ∑ i, (2 * (r • w) i ^ 2 +
            2 * pathLaplacianVector w i ^ 2) := by
        exact Finset.sum_le_sum fun i _ => by
          simp only [Pi.add_apply]
          exact sq_add_le_two _ _
      _ = 2 * (∑ i, (r • w) i ^ 2) +
          2 * (∑ i, pathLaplacianVector w i ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hL := pathLaplacianVector_vecSq_le w
  have hE := pathEnergy_le_four_vecSq n w
  have hsmul : vecSq (r • w) = r ^ 2 * vecSq w := by
    unfold vecSq NCPLVerification.vecSq
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [hsmul] at hadd
  have hw : 0 ≤ vecSq w := by
    unfold vecSq NCPLVerification.vecSq
    positivity
  have hrsq : r ^ 2 ≤ (1 / 100 : ℝ) ^ 2 :=
    (sq_le_sq₀ hr (by norm_num)).2 hrle
  nlinarith

private theorem vecSq_single {n : Nat} (i : Fin n) (c : ℝ) :
    vecSq (Pi.single i c : EVec n) = c ^ 2 := by
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

private theorem vecSq_sub_le_two {n : Nat} (u v : EVec n) :
    vecSq (u - v) ≤ 2 * vecSq u + 2 * vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  calc
    (∑ i, (u - v) i ^ 2) ≤
        ∑ i, (2 * u i ^ 2 + 2 * v i ^ 2) := by
      exact Finset.sum_le_sum fun i _ => by
        simp only [Pi.sub_apply]
        nlinarith [sq_nonneg (u i + v i)]
    _ = 2 * (∑ i, u i ^ 2) + 2 * (∑ i, v i ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem innerSource_vecSq_le {n : Nat} (hn : 0 < n) (a b : ℝ) :
    vecSq (innerSource hn a b) ≤ 2 * (a ^ 2 + b ^ 2) := by
  have h := vecSq_sub_le_two
    (Pi.single (innerFirst hn) a : EVec n)
    (Pi.single (innerLast hn) (b / 2) : EVec n)
  rw [vecSq_single, vecSq_single] at h
  unfold innerSource
  nlinarith [sq_nonneg b]

private theorem coordinate_sq_le_vecSq {n : Nat} (w : EVec n) (i : Fin n) :
    w i ^ 2 ≤ vecSq w := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.single_le_sum (fun j _ => sq_nonneg (w j))
    (Finset.mem_univ i)

/-- Dimension-free Euclidean operator bound for one complete linear inner
block `(a,b,w) ↦ (∂ₐh, ∂ᵦh, -∇_w h)`. -/
theorem concrete_inner_block_gradient_sq_le {n : Nat} (hn : 10 ≤ n)
    (a b : ℝ) (w : EVec n) :
    innerGradA (by omega : 0 < n) (innerC (by omega : 0 < n)) w ^ 2 +
        innerGradB (by omega : 0 < n) (innerC (by omega : 0 < n)) w ^ 2 +
        vecSq (fun i => innerSaddleGradW (by omega : 0 < n)
          (innerC (by omega : 0 < n)) a b w i) ≤
      100 * (a ^ 2 + b ^ 2 + vecSq w) := by
  let hnpos : 0 < n := by omega
  let C := innerC hnpos
  let s := innerScale n C
  have hC := innerC_bounds hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hs0 : 0 ≤ s := by
    dsimp [s, innerScale]
    positivity
  have hsquare : s ^ 2 = C / (n : ℝ) := by
    dsimp [s, innerScale]
    rw [Real.sq_sqrt]
    exact div_nonneg (by linarith [hC.1]) hnreal.le
  have hsle : s ^ 2 ≤ 12 := by
    rw [hsquare, div_le_iff₀ hnreal]
    have hn10 : (10 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [C]
    nlinarith [hC.2]
  have hw0 : 0 ≤ vecSq w := by
    unfold vecSq NCPLVerification.vecSq
    positivity
  have hAcoord := coordinate_sq_le_vecSq w (innerFirst hnpos)
  have hBcoord := coordinate_sq_le_vecSq w (innerLast hnpos)
  have hA : innerGradA hnpos C w ^ 2 ≤ 12 * vecSq w := by
    have hprod : s ^ 2 * w (innerFirst hnpos) ^ 2 ≤
        12 * vecSq w :=
      mul_le_mul hsle hAcoord (sq_nonneg _) (by norm_num)
    dsimp [innerGradA]
    change (s * w (innerFirst hnpos)) ^ 2 ≤ 12 * vecSq w
    nlinarith
  have hB : innerGradB hnpos C w ^ 2 ≤ 3 * vecSq w := by
    have hprod : s ^ 2 * w (innerLast hnpos) ^ 2 ≤
        12 * vecSq w :=
      mul_le_mul hsle hBcoord (sq_nonneg _) (by norm_num)
    dsimp [innerGradB]
    change (-(1 / 2 : ℝ) * s * w (innerLast hnpos)) ^ 2 ≤ 3 * vecSq w
    nlinarith
  let src : EVec n := s • innerSource hnpos a b
  have hsrcEq : vecSq src = s ^ 2 * vecSq (innerSource hnpos a b) := by
    dsimp [src]
    unfold vecSq NCPLVerification.vecSq
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  have hsource0 : 0 ≤ vecSq (innerSource hnpos a b) := by
    unfold vecSq NCPLVerification.vecSq
    positivity
  have hsrc : vecSq src ≤ 24 * (a ^ 2 + b ^ 2) := by
    rw [hsrcEq]
    have hs := innerSource_vecSq_le hnpos a b
    have hab : 0 ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    nlinarith [mul_nonneg (sub_nonneg.mpr hsle) hsource0,
      mul_nonneg (sq_nonneg s) (sub_nonneg.mpr hs)]
  let path : EVec n := regularizedPathVector w
  have hpath : vecSq path ≤ 33 * vecSq w := by
    exact regularizedPathVector_vecSq_le_of_ten hn w
  let gw : EVec n := fun i => innerSaddleGradW hnpos C a b w i
  have hgwEq : gw = path - src := by
    funext i
    simp [gw, path, src, innerSaddleGradW, regularizedPathVector, s]
  have hgw : vecSq gw ≤ 66 * vecSq w + 48 * (a ^ 2 + b ^ 2) := by
    rw [hgwEq]
    exact (vecSq_sub_le_two path src).trans (by nlinarith)
  change innerGradA hnpos C w ^ 2 + innerGradB hnpos C w ^ 2 +
      vecSq gw ≤ 100 * (a ^ 2 + b ^ 2 + vecSq w)
  nlinarith [sq_nonneg a, sq_nonneg b]

/-! ## Global serialized assembly -/

/-- The linear inner saddle field on one serialized block.  Its coordinate
order is `A`, the `n` dual coordinates, `B`, and the (unused) state
coordinate. -/
def innerBlockField {n : Nat} (hn : 0 < n) (a b : ℝ) (w : EVec n) :
    EVec (n + 3) := fun k =>
  if hA : k.val = 0 then
    innerGradA hn (innerC hn) w
  else if hY : k.val ≤ n then
    innerSaddleGradW hn (innerC hn) a b w
      ⟨k.val - 1, by omega⟩
  else if hB : k.val = n + 1 then
    innerGradB hn (innerC hn) w
  else 0

@[simp] theorem innerBlockField_A {n : Nat} (hn : 0 < n)
    (a b : ℝ) (w : EVec n) :
    innerBlockField hn a b w ⟨0, by omega⟩ =
      innerGradA hn (innerC hn) w := by
  simp [innerBlockField]

@[simp] theorem innerBlockField_Y {n : Nat} (hn : 0 < n)
    (a b : ℝ) (w : EVec n) (k : Fin n) :
    innerBlockField hn a b w ⟨k.val + 1, by omega⟩ =
      innerSaddleGradW hn (innerC hn) a b w k := by
  simp only [innerBlockField]
  rw [dif_neg (by omega), dif_pos (by omega)]
  congr

@[simp] theorem innerBlockField_B {n : Nat} (hn : 0 < n)
    (a b : ℝ) (w : EVec n) :
    innerBlockField hn a b w ⟨n + 1, by omega⟩ =
      innerGradB hn (innerC hn) w := by
  simp [innerBlockField]

@[simp] theorem innerBlockField_state {n : Nat} (hn : 0 < n)
    (a b : ℝ) (w : EVec n) :
    innerBlockField hn a b w ⟨n + 2, by omega⟩ = 0 := by
  simp [innerBlockField]

theorem regularizedPathCoord_sub_eq {n : Nat} (u v : EVec n) (i : Fin n) :
    regularizedPathCoord (u - v) i =
      regularizedPathCoord u i - regularizedPathCoord v i := by
  unfold regularizedPathCoord pathLaplacianCoord
  split <;> split <;> simp [Pi.sub_apply] <;> ring

theorem innerSource_sub_eq {n : Nat} (hn : 0 < n)
    (a b c d : ℝ) :
    innerSource hn (a - c) (b - d) =
      innerSource hn a b - innerSource hn c d := by
  funext i
  simp [innerSource, Pi.single_apply, Pi.sub_apply]
  split_ifs <;> ring

theorem innerGradA_sub_eq {n : Nat} (hn : 0 < n) (C : ℝ)
    (u v : EVec n) :
    innerGradA hn C (u - v) = innerGradA hn C u - innerGradA hn C v := by
  simp [innerGradA, Pi.sub_apply]
  ring

theorem innerGradB_sub_eq {n : Nat} (hn : 0 < n) (C : ℝ)
    (u v : EVec n) :
    innerGradB hn C (u - v) = innerGradB hn C u - innerGradB hn C v := by
  simp [innerGradB, Pi.sub_apply]
  ring

theorem innerSaddleGradW_sub_eq {n : Nat} (hn : 0 < n) (C : ℝ)
    (a b c d : ℝ) (u v : EVec n) (i : Fin n) :
    innerSaddleGradW hn C (a - c) (b - d) (u - v) i =
      innerSaddleGradW hn C a b u i - innerSaddleGradW hn C c d v i := by
  unfold innerSaddleGradW
  rw [regularizedPathCoord_sub_eq, innerSource_sub_eq]
  simp only [Pi.sub_apply]
  ring

theorem innerBlockField_sub_apply {n : Nat} (hn : 0 < n)
    (a b c d : ℝ) (u v : EVec n) (k : Fin (n + 3)) :
    innerBlockField hn (a - c) (b - d) (u - v) k =
      innerBlockField hn a b u k - innerBlockField hn c d v k := by
  unfold innerBlockField
  split_ifs <;> simp_all [innerGradA_sub_eq, innerGradB_sub_eq,
    innerSaddleGradW_sub_eq]

private theorem sum_fin_add_three {n : Nat} (f : Fin (n + 3) → ℝ) :
    (∑ k : Fin (n + 3), f k) =
      f ⟨0, by omega⟩ +
        (∑ k : Fin n, f ⟨k.val + 1, by omega⟩) +
        f ⟨n + 1, by omega⟩ + f ⟨n + 2, by omega⟩ := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_castSucc]
  rw [Fin.sum_univ_castSucc]
  have hsum :
      (∑ i : Fin n, f i.castSucc.castSucc.succ) =
        ∑ i : Fin n, f ⟨i.val + 1, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    congr
  have hlastB : f (Fin.last n).castSucc.succ =
      f ⟨n + 1, by omega⟩ := by
    congr
  have hlastState : f (Fin.last (n + 1)).succ =
      f ⟨n + 2, by omega⟩ := by
    congr
  rw [hsum, hlastB, hlastState]
  have hsumComm :
      (∑ i : Fin n, f ⟨i.val + 1, by omega⟩) =
        ∑ i : Fin n, f ⟨1 + i.val, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    apply congrArg f
    apply Fin.ext
    simp [Nat.add_comm]
  rw [hsumComm]
  have hzero : f (0 : Fin (n + 3)) = f ⟨0, by omega⟩ := by
    congr
  rw [hzero]
  abel_nf

theorem innerBlockField_vecSq {n : Nat} (hn : 0 < n)
    (a b : ℝ) (w : EVec n) :
    vecSq (innerBlockField hn a b w) =
      innerGradA hn (innerC hn) w ^ 2 +
        innerGradB hn (innerC hn) w ^ 2 +
        vecSq (fun k => innerSaddleGradW hn (innerC hn) a b w k) := by
  unfold vecSq NCPLVerification.vecSq
  rw [sum_fin_add_three]
  simp only [innerBlockField_A, innerBlockField_Y, innerBlockField_B,
    innerBlockField_state, zero_pow, add_zero]
  ring

/-- The `i`th input block in the literal serialized storage order. -/
def serializedInputBlock {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) : EVec (n + 3) :=
  fun k => q (finProdFinEquiv (i, k))

@[simp] theorem serializedInputBlock_A {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedInputBlock q i ⟨0, by omega⟩ = serializedA q i := by
  unfold serializedInputBlock serializedA
  apply congrArg q
  apply Fin.ext
  simp [finProdFinEquiv, serializedAIndex, Nat.mul_comm]

@[simp] theorem serializedInputBlock_Y {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) (k : Fin n) :
    serializedInputBlock q i ⟨k.val + 1, by omega⟩ = serializedY q i k := by
  unfold serializedInputBlock serializedY
  apply congrArg q
  apply Fin.ext
  simp [finProdFinEquiv, serializedDualIndex, Nat.mul_comm]
  omega

@[simp] theorem serializedInputBlock_B {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedInputBlock q i ⟨n + 1, by omega⟩ = serializedB q i := by
  unfold serializedInputBlock serializedB
  apply congrArg q
  apply Fin.ext
  simp [finProdFinEquiv, serializedBIndex, Nat.mul_comm]
  omega

@[simp] theorem serializedInputBlock_state {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedInputBlock q i ⟨n + 2, by omega⟩ = serializedState q i := by
  unfold serializedInputBlock serializedState
  apply congrArg q
  apply Fin.ext
  simp [finProdFinEquiv, serializedStateIndex, Nat.mul_comm]
  omega

theorem vecSq_serializedInputBlock {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    vecSq (serializedInputBlock q i) =
      serializedA q i ^ 2 + vecSq (serializedDualBlock q i) +
        serializedB q i ^ 2 + serializedState q i ^ 2 := by
  unfold vecSq NCPLVerification.vecSq
  rw [sum_fin_add_three]
  simp only [serializedInputBlock_A, serializedInputBlock_Y,
    serializedInputBlock_B, serializedInputBlock_state]
  simp [serializedDualBlock, vecSq, NCPLVerification.vecSq]

/-- Assemble the independent linear inner fields in the literal serialized
storage order. -/
def innerSerializedField {T n : Nat} (hn : 0 < n)
    (q : SerializedSpace T n) : SerializedSpace T n := fun j =>
  let ik := finProdFinEquiv.symm j
  innerBlockField hn (serializedA q ik.1) (serializedB q ik.1)
    (serializedDualBlock q ik.1) ik.2

theorem innerSerializedField_apply_prod {T n : Nat} (hn : 0 < n)
    (q : SerializedSpace T n) (i : Fin (T - 1)) (k : Fin (n + 3)) :
    innerSerializedField hn q (finProdFinEquiv (i, k)) =
      innerBlockField hn (serializedA q i) (serializedB q i)
        (serializedDualBlock q i) k := by
  simp [innerSerializedField]

theorem vecSq_innerSerializedField {T n : Nat} (hn : 0 < n)
    (q : SerializedSpace T n) :
    vecSq (innerSerializedField hn q) =
      ∑ i : Fin (T - 1),
        vecSq (innerBlockField hn (serializedA q i) (serializedB q i)
          (serializedDualBlock q i)) := by
  unfold vecSq NCPLVerification.vecSq
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [innerSerializedField_apply_prod]

theorem innerSerializedField_sub {T n : Nat} (hn : 0 < n)
    (q r : SerializedSpace T n) :
    innerSerializedField hn (q - r) =
      innerSerializedField hn q - innerSerializedField hn r := by
  funext j
  let ik := finProdFinEquiv.symm j
  change innerBlockField hn
      (serializedA (q - r) ik.1) (serializedB (q - r) ik.1)
        (serializedDualBlock (q - r) ik.1) ik.2 =
    innerBlockField hn (serializedA q ik.1) (serializedB q ik.1)
        (serializedDualBlock q ik.1) ik.2 -
      innerBlockField hn (serializedA r ik.1) (serializedB r ik.1)
        (serializedDualBlock r ik.1) ik.2
  have hA : serializedA (q - r) ik.1 =
      serializedA q ik.1 - serializedA r ik.1 := by rfl
  have hB : serializedB (q - r) ik.1 =
      serializedB q ik.1 - serializedB r ik.1 := by rfl
  have hY : serializedDualBlock (q - r) ik.1 =
      serializedDualBlock q ik.1 - serializedDualBlock r ik.1 := by
    funext k
    rfl
  rw [hA, hB, hY]
  exact innerBlockField_sub_apply hn _ _ _ _ _ _ _

private theorem vecSq_eq_sum_serialized_blocks {T n : Nat}
    (q : SerializedSpace T n) :
    vecSq q = ∑ i : Fin (T - 1),
      vecSq (serializedInputBlock q i) := by
  unfold vecSq NCPLVerification.vecSq
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]
  simp [serializedInputBlock]

/-- Dimension-free global Euclidean estimate for all linear inner blocks.
The constant is independent of both `T` and `n`. -/
theorem innerSerializedField_sub_vecSq_le {T n : Nat} (hn : 10 ≤ n)
    (q r : SerializedSpace T n) :
    vecSq (innerSerializedField (by omega) q - innerSerializedField (by omega) r) ≤
      100 * vecSq (q - r) := by
  rw [← innerSerializedField_sub]
  rw [vecSq_innerSerializedField]
  rw [vecSq_eq_sum_serialized_blocks]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [innerBlockField_vecSq]
  have hblock := concrete_inner_block_gradient_sq_le hn
      (serializedA (q - r) i) (serializedB (q - r) i)
      (serializedDualBlock (q - r) i)
  calc
    _ ≤ 100 *
        (serializedA (q - r) i ^ 2 + serializedB (q - r) i ^ 2 +
          vecSq (serializedDualBlock (q - r) i)) := hblock
    _ ≤ 100 * vecSq
        (serializedInputBlock (q - r) i) := by
      rw [vecSq_serializedInputBlock]
      have hs : 0 ≤ serializedState (q - r) i ^ 2 := sq_nonneg _
      nlinarith

/-! ## Diagonal quadratic correction -/

/-- The `a,b` diagonal correction from
`innerC1 * a^2 + innerC2 * b^2 + gamma * (a^2+b^2)` on one block. -/
def diagonalBlockField {n : Nat} (hn : 0 < n) (gamma a b : ℝ) :
    EVec (n + 3) := fun k =>
  if hA : k.val = 0 then 2 * (innerC1 hn + gamma) * a
  else if hB : k.val = n + 1 then 2 * (innerC2 hn + gamma) * b
  else 0

@[simp] theorem diagonalBlockField_A {n : Nat} (hn : 0 < n)
    (gamma a b : ℝ) :
    diagonalBlockField hn gamma a b ⟨0, by omega⟩ =
      2 * (innerC1 hn + gamma) * a := by
  simp [diagonalBlockField]

@[simp] theorem diagonalBlockField_Y {n : Nat} (hn : 0 < n)
    (gamma a b : ℝ) (k : Fin n) :
    diagonalBlockField hn gamma a b ⟨k.val + 1, by omega⟩ = 0 := by
  simp [diagonalBlockField]
  omega

@[simp] theorem diagonalBlockField_B {n : Nat} (hn : 0 < n)
    (gamma a b : ℝ) :
    diagonalBlockField hn gamma a b ⟨n + 1, by omega⟩ =
      2 * (innerC2 hn + gamma) * b := by
  simp [diagonalBlockField]

@[simp] theorem diagonalBlockField_state {n : Nat} (hn : 0 < n)
    (gamma a b : ℝ) :
    diagonalBlockField hn gamma a b ⟨n + 2, by omega⟩ = 0 := by
  simp [diagonalBlockField]

theorem diagonalBlockField_sub_apply {n : Nat} (hn : 0 < n)
    (gamma a b c d : ℝ) (k : Fin (n + 3)) :
    diagonalBlockField hn gamma (a - c) (b - d) k =
      diagonalBlockField hn gamma a b k -
        diagonalBlockField hn gamma c d k := by
  unfold diagonalBlockField
  split_ifs <;> ring

theorem diagonalBlockField_vecSq {n : Nat} (hn : 0 < n)
    (gamma a b : ℝ) :
    vecSq (diagonalBlockField hn gamma a b) =
      (2 * (innerC1 hn + gamma) * a) ^ 2 +
        (2 * (innerC2 hn + gamma) * b) ^ 2 := by
  unfold vecSq NCPLVerification.vecSq
  rw [sum_fin_add_three]
  simp only [diagonalBlockField_A, diagonalBlockField_Y,
    diagonalBlockField_B, diagonalBlockField_state]
  simp

theorem diagonalBlockField_vecSq_le {n : Nat} (hn : 10 ≤ n)
    {gamma : ℝ} (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ 1 / 2)
    (a b : ℝ) :
    vecSq (diagonalBlockField (n := n) (by omega) gamma a b) ≤
      25000000 * (a ^ 2 + b ^ 2) := by
  let hnpos : 0 < n := by omega
  let cA : ℝ := 2 * (innerC1 hnpos + gamma)
  let cB : ℝ := 2 * (innerC2 hnpos + gamma)
  have habsgamma : |gamma| ≤ 1 / 2 := by
    rw [abs_of_nonneg hgamma0]
    exact hgamma
  have hcAabs : |cA| ≤ 5000 := by
    calc
      |cA| = 2 * |innerC1 hnpos + gamma| := by
        simp [cA, abs_mul]
      _ ≤ 2 * (|innerC1 hnpos| + |gamma|) := by
        gcongr
        exact abs_add_le _ _
      _ ≤ 5000 := by
        have h1 := innerC1_uniform_bound hn
        linarith
  have hcBabs : |cB| ≤ 5000 := by
    calc
      |cB| = 2 * |innerC2 hnpos + gamma| := by
        simp [cB, abs_mul]
      _ ≤ 2 * (|innerC2 hnpos| + |gamma|) := by
        gcongr
        exact abs_add_le _ _
      _ ≤ 5000 := by
        have h2 := innerC2_uniform_bound hn
        linarith
  have hcAsq : cA ^ 2 ≤ (25000000 : ℝ) := by
    have h := (abs_le.mp hcAabs)
    nlinarith [sq_nonneg (cA - 5000), sq_nonneg (cA + 5000)]
  have hcBsq : cB ^ 2 ≤ (25000000 : ℝ) := by
    have h := (abs_le.mp hcBabs)
    nlinarith [sq_nonneg (cB - 5000), sq_nonneg (cB + 5000)]
  rw [diagonalBlockField_vecSq]
  change (cA * a) ^ 2 + (cB * b) ^ 2 ≤
    25000000 * (a ^ 2 + b ^ 2)
  have hA := mul_le_mul_of_nonneg_right hcAsq (sq_nonneg a)
  have hB := mul_le_mul_of_nonneg_right hcBsq (sq_nonneg b)
  nlinarith

/-- Assemble all diagonal corrections in serialized storage order. -/
def diagonalSerializedField {T n : Nat} (hn : 0 < n) (gamma : ℝ)
    (q : SerializedSpace T n) : SerializedSpace T n := fun j =>
  let ik := finProdFinEquiv.symm j
  diagonalBlockField hn gamma (serializedA q ik.1) (serializedB q ik.1) ik.2

theorem diagonalSerializedField_apply_prod {T n : Nat} (hn : 0 < n)
    (gamma : ℝ) (q : SerializedSpace T n)
    (i : Fin (T - 1)) (k : Fin (n + 3)) :
    diagonalSerializedField hn gamma q (finProdFinEquiv (i, k)) =
      diagonalBlockField hn gamma (serializedA q i) (serializedB q i) k := by
  simp [diagonalSerializedField]

theorem vecSq_diagonalSerializedField {T n : Nat} (hn : 0 < n)
    (gamma : ℝ) (q : SerializedSpace T n) :
    vecSq (diagonalSerializedField hn gamma q) =
      ∑ i : Fin (T - 1),
        vecSq (diagonalBlockField hn gamma (serializedA q i) (serializedB q i)) := by
  unfold vecSq NCPLVerification.vecSq
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [diagonalSerializedField_apply_prod]

theorem diagonalSerializedField_sub {T n : Nat} (hn : 0 < n)
    (gamma : ℝ) (q r : SerializedSpace T n) :
    diagonalSerializedField hn gamma (q - r) =
      diagonalSerializedField hn gamma q - diagonalSerializedField hn gamma r := by
  funext j
  let ik := finProdFinEquiv.symm j
  change diagonalBlockField hn gamma
      (serializedA (q - r) ik.1) (serializedB (q - r) ik.1) ik.2 =
    diagonalBlockField hn gamma (serializedA q ik.1) (serializedB q ik.1) ik.2 -
      diagonalBlockField hn gamma (serializedA r ik.1) (serializedB r ik.1) ik.2
  have hA : serializedA (q - r) ik.1 =
      serializedA q ik.1 - serializedA r ik.1 := by rfl
  have hB : serializedB (q - r) ik.1 =
      serializedB q ik.1 - serializedB r ik.1 := by rfl
  rw [hA, hB]
  exact diagonalBlockField_sub_apply hn _ _ _ _ _ _

theorem diagonalSerializedField_sub_vecSq_le {T n : Nat} (hn : 10 ≤ n)
    {gamma : ℝ} (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ 1 / 2)
    (q r : SerializedSpace T n) :
    vecSq (diagonalSerializedField (by omega) gamma q -
        diagonalSerializedField (by omega) gamma r) ≤
      25000000 * vecSq (q - r) := by
  rw [← diagonalSerializedField_sub]
  rw [vecSq_diagonalSerializedField]
  rw [vecSq_eq_sum_serialized_blocks]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ 25000000 *
        (serializedA (q - r) i ^ 2 + serializedB (q - r) i ^ 2) :=
      diagonalBlockField_vecSq_le hn hgamma0 hgamma _ _
    _ ≤ 25000000 * vecSq (serializedInputBlock (q - r) i) := by
      rw [vecSq_serializedInputBlock]
      have hY : 0 ≤ vecSq (serializedDualBlock (q - r) i) := by
        unfold vecSq NCPLVerification.vecSq
        positivity
      have hs : 0 ≤ serializedState (q - r) i ^ 2 := sq_nonneg _
      nlinarith

/-- Linear part of the true field: inner path coupling plus the diagonal
quadratic correction. -/
def totalLinearSerializedField {T n : Nat} (hn : 0 < n) (gamma : ℝ)
    (q : SerializedSpace T n) : SerializedSpace T n :=
  innerSerializedField hn q + diagonalSerializedField hn gamma q

private theorem vecSq_add_le_two_global {m : Nat} (u v : EVec m) :
    vecSq (u + v) ≤ 2 * vecSq u + 2 * vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  calc
    (∑ i, (u + v) i ^ 2) ≤ ∑ i, (2 * u i ^ 2 + 2 * v i ^ 2) := by
      exact Finset.sum_le_sum fun i _ => by
        simp only [Pi.add_apply]
        exact sq_add_le_two _ _
    _ = 2 * (∑ i, u i ^ 2) + 2 * (∑ i, v i ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem totalLinearSerializedField_sub_vecSq_le {T n : Nat} (hn : 10 ≤ n)
    {gamma : ℝ} (hgamma0 : 0 ≤ gamma) (hgamma : gamma ≤ 1 / 2)
    (q r : SerializedSpace T n) :
    vecSq (totalLinearSerializedField (by omega) gamma q -
        totalLinearSerializedField (by omega) gamma r) ≤
      50000200 * vecSq (q - r) := by
  have heq :
      totalLinearSerializedField (by omega) gamma q -
          totalLinearSerializedField (by omega) gamma r =
        (innerSerializedField (by omega) q - innerSerializedField (by omega) r) +
        (diagonalSerializedField (by omega) gamma q -
          diagonalSerializedField (by omega) gamma r) := by
    funext j
    simp [totalLinearSerializedField, Pi.add_apply, Pi.sub_apply]
    ring
  rw [heq]
  have hadd := vecSq_add_le_two_global
    (innerSerializedField (by omega) q - innerSerializedField (by omega) r)
    (diagonalSerializedField (by omega) gamma q -
      diagonalSerializedField (by omega) gamma r)
  have hinner := innerSerializedField_sub_vecSq_le hn q r
  have hdiag := diagonalSerializedField_sub_vecSq_le hn hgamma0 hgamma q r
  have hsq : 0 ≤ vecSq (q - r) := by
    unfold vecSq NCPLVerification.vecSq
    positivity
  nlinarith

end

end NCCLowerBoundVerification
