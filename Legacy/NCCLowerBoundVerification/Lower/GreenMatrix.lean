import NCCLowerBoundVerification.Lower.InnerChain
import Mathlib.Data.Fin.Rev

/-!
# Green kernel of the regularized path matrix

This file derives the endpoint Green-kernel estimates used by the concrete
inner-chain construction directly from the regularized path operator.
-/

namespace NCCLowerBoundVerification

noncomputable section

private theorem regularizedPathBilinear_sum_right {n : Nat} (u : EVec n)
    (s : Finset (Fin n)) (f : Fin n → EVec n) :
    regularizedPathBilinear n u (∑ j ∈ s, f j) =
      ∑ j ∈ s, regularizedPathBilinear n u (f j) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using regularizedPathBilinear_smul_right n 0 u u
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [regularizedPathBilinear_add_right, ih]

private theorem basis_sum (n : Nat) (w : EVec n) :
    (∑ j : Fin n, w j • Pi.single j (1 : ℝ)) = w := by
  funext i
  classical
  simp [Pi.single_apply]

theorem innerM_mulVec_eq_bilinear {n : Nat} (w : EVec n) (i : Fin n) :
    (innerM n).mulVec w i =
      regularizedPathBilinear n (Pi.single i 1) w := by
  classical
  calc
    (innerM n).mulVec w i =
        ∑ j : Fin n, regularizedPathBilinear n (Pi.single i 1)
          (Pi.single j 1) * w j := by rfl
    _ = ∑ j : Fin n, regularizedPathBilinear n (Pi.single i 1)
          (w j • Pi.single j 1) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [regularizedPathBilinear_smul_right]
      ring
    _ = regularizedPathBilinear n (Pi.single i 1)
          (∑ j : Fin n, w j • Pi.single j 1) := by
      symm
      simpa using regularizedPathBilinear_sum_right
        (n := n) (Pi.single i 1) Finset.univ
        (fun j => w j • Pi.single j 1)
    _ = regularizedPathBilinear n (Pi.single i 1) w := by
      rw [basis_sum]

private theorem sum_castSucc_indicator {m : Nat} (i : Fin (m + 1))
    (h : i.val < m) (f : Fin m → ℝ) :
    (∑ j : Fin m, (if j.castSucc = i then 1 else 0) * f j) =
      f ⟨i.val, h⟩ := by
  classical
  let k : Fin m := ⟨i.val, h⟩
  calc
    _ = (if k.castSucc = i then 1 else 0) * f k := by
      apply Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
      intro j _ hj
      have hji : j.castSucc ≠ i := by
        intro heq
        apply hj
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change j.val = i.val at hv
        simpa [k] using hv
      simp [hji]
    _ = f ⟨i.val, h⟩ := by simp [k]

private theorem sum_castSucc_indicator_last {m : Nat} (i : Fin (m + 1))
    (h : ¬i.val < m) (f : Fin m → ℝ) :
    (∑ j : Fin m, (if j.castSucc = i then 1 else 0) * f j) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hji : j.castSucc ≠ i := by
    intro heq
    have hv := congrArg Fin.val heq
    change j.val = i.val at hv
    omega
  simp [hji]

private theorem sum_succ_indicator {m : Nat} (i : Fin (m + 1))
    (h : 0 < i.val) (f : Fin m → ℝ) :
    (∑ j : Fin m, (if j.succ = i then 1 else 0) * f j) =
      f ⟨i.val - 1, by omega⟩ := by
  classical
  let k : Fin m := ⟨i.val - 1, by omega⟩
  calc
    _ = (if k.succ = i then 1 else 0) * f k := by
      apply Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
      intro j _ hj
      have hji : j.succ ≠ i := by
        intro heq
        apply hj
        apply Fin.ext
        have hv := congrArg Fin.val heq
        change j.val + 1 = i.val at hv
        simp [k]
        omega
      simp [hji]
    _ = f ⟨i.val - 1, by omega⟩ := by
      have hk : k.succ = i := by
        apply Fin.ext
        simp [k]
        omega
      rw [if_pos hk, one_mul]

private theorem sum_succ_indicator_first {m : Nat} (i : Fin (m + 1))
    (h : ¬0 < i.val) (f : Fin m → ℝ) :
    (∑ j : Fin m, (if j.succ = i then 1 else 0) * f j) = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hji : j.succ ≠ i := by
    intro heq
    have := congrArg Fin.val heq
    simp at this
    omega
  simp [hji]

theorem regularizedPathBilinear_single_left_eq_coord {n : Nat}
    (w : EVec n) (i : Fin n) :
    regularizedPathBilinear n (Pi.single i 1) w =
      regularizedPathCoord w i := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ m =>
      unfold regularizedPathBilinear regularizedPathCoord pathLaplacianCoord
      classical
      change pathRegularization (m + 1) *
          (∑ j : Fin (m + 1), (Pi.single i (1 : ℝ) : EVec (m + 1)) j * w j) +
          (∑ j : Fin m,
            ((Pi.single i (1 : ℝ) : EVec (m + 1)) j.castSucc -
              (Pi.single i (1 : ℝ) : EVec (m + 1)) j.succ) *
              (w j.castSucc - w j.succ)) = _
      simp only [Pi.single_apply]
      split
      · rename_i hp
        split
        · rename_i hs
          have hedge :
              (∑ x : Fin m,
                ((if x.castSucc = i then 1 else 0) -
                  if x.succ = i then 1 else 0) *
                    (w x.castSucc - w x.succ)) =
                (∑ x : Fin m, (if x.castSucc = i then 1 else 0) *
                    (w x.castSucc - w x.succ)) -
                  ∑ x : Fin m, (if x.succ = i then 1 else 0) *
                    (w x.castSucc - w x.succ) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro x _
            ring
          rw [hedge, sum_castSucc_indicator i (by omega),
            sum_succ_indicator i hp]
          simp [ite_mul]
          have heq : (⟨i.val - 1 + 1, by omega⟩ : Fin (m + 1)) = i := by
            apply Fin.ext
            simp
            omega
          rw [heq]
          ring
        · rename_i hs
          have hedge :
              (∑ x : Fin m,
                ((if x.castSucc = i then 1 else 0) -
                  if x.succ = i then 1 else 0) *
                    (w x.castSucc - w x.succ)) =
                (∑ x : Fin m, (if x.castSucc = i then 1 else 0) *
                    (w x.castSucc - w x.succ)) -
                  ∑ x : Fin m, (if x.succ = i then 1 else 0) *
                    (w x.castSucc - w x.succ) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro x _
            ring
          rw [hedge, sum_castSucc_indicator_last i (by omega),
            sum_succ_indicator i hp]
          simp [ite_mul]
          have heq : (⟨i.val - 1 + 1, by omega⟩ : Fin (m + 1)) = i := by
            apply Fin.ext
            simp
            omega
          rw [heq]
      · rename_i hp
        split
        · rename_i hs
          have hedge :
              (∑ x : Fin m,
                ((if x.castSucc = i then 1 else 0) -
                  if x.succ = i then 1 else 0) *
                    (w x.castSucc - w x.succ)) =
                (∑ x : Fin m, (if x.castSucc = i then 1 else 0) *
                    (w x.castSucc - w x.succ)) -
                  ∑ x : Fin m, (if x.succ = i then 1 else 0) *
                    (w x.castSucc - w x.succ) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro x _
            ring
          rw [hedge, sum_castSucc_indicator i (by omega),
            sum_succ_indicator_first i hp]
          simp [ite_mul]
        · rename_i hs
          have hedge :
              (∑ x : Fin m,
                ((if x.castSucc = i then 1 else 0) -
                  if x.succ = i then 1 else 0) *
                    (w x.castSucc - w x.succ)) =
                (∑ x : Fin m, (if x.castSucc = i then 1 else 0) *
                    (w x.castSucc - w x.succ)) -
                  ∑ x : Fin m, (if x.succ = i then 1 else 0) *
                    (w x.castSucc - w x.succ) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro x _
            ring
          rw [hedge, sum_castSucc_indicator_last i (by omega),
            sum_succ_indicator_first i hp]
          simp_all [ite_mul]

theorem innerM_mulVec_eq_coord {n : Nat} (w : EVec n) (i : Fin n) :
    (innerM n).mulVec w i = regularizedPathCoord w i := by
  rw [innerM_mulVec_eq_bilinear,
    regularizedPathBilinear_single_left_eq_coord]

/-- Discrete maximum principle for the regularized path operator. -/
theorem regularizedPath_maximum_principle {n : Nat} (hn : 0 < n)
    {z : EVec n} (hz : ∀ i, 0 ≤ regularizedPathCoord z i) :
    ∀ i, 0 ≤ z i := by
  by_contra h
  push Not at h
  obtain ⟨i, hi⟩ := h
  letI : Nonempty (Fin n) := ⟨innerFirst hn⟩
  obtain ⟨m, hm⟩ := Finite.exists_min z
  have hmneg : z m < 0 := lt_of_le_of_lt (hm i) hi
  have hregneg : pathRegularization n * z m < 0 :=
    mul_neg_of_pos_of_neg (pathRegularization_pos hn) hmneg
  have hlap : pathLaplacianCoord z m ≤ 0 := by
    unfold pathLaplacianCoord
    split
    · rename_i hp
      have hpmin := hm (⟨m.val - 1, by omega⟩ : Fin n)
      split
      · rename_i hs
        have hsmin := hm (⟨m.val + 1, hs⟩ : Fin n)
        nlinarith
      · simp only [add_zero]
        nlinarith
    · split
      · rename_i hs
        have hsmin := hm (⟨m.val + 1, hs⟩ : Fin n)
        simp only [zero_add]
        nlinarith
      · simp
  have hcoordneg : regularizedPathCoord z m < 0 := by
    unfold regularizedPathCoord
    linarith
  exact (not_lt_of_ge (hz m)) hcoordneg

/-- Quadratic comparison profiles, parameterized by their constant and
curvature coefficients. -/
def quadraticGreenProfile (n : Nat) (c d : ℝ) : EVec n := fun i =>
  c * (n : ℝ) + d / (n : ℝ) *
    ((n : ℝ) - 1 - (i.val : ℝ)) ^ 2

/-- A positive lower comparison profile for the first Green column. -/
def greenLowerBarrier (n : Nat) : EVec n :=
  quadraticGreenProfile n (1 / 10) (2 / 5)

/-- A coarse upper comparison profile for the first Green column. -/
def greenUpperBarrier (n : Nat) : EVec n :=
  quadraticGreenProfile n 10 1

private theorem vecSq_eq_zero {n : Nat} {w : EVec n} (hw : vecSq w = 0) :
    w = 0 := by
  funext i
  have hi : w i ^ 2 ≤ vecSq w := by
    unfold vecSq NCPLVerification.vecSq
    exact Finset.single_le_sum (fun j _ => sq_nonneg (w j))
      (Finset.mem_univ i)
  have : w i ^ 2 = 0 := by nlinarith [sq_nonneg (w i)]
  exact sq_eq_zero_iff.mp this

private theorem bilinear_eq_dot_mulVec {n : Nat} (w : EVec n) :
    regularizedPathBilinear n w w =
      ∑ i : Fin n, w i * (innerM n).mulVec w i := by
  classical
  calc
    regularizedPathBilinear n w w =
        regularizedPathBilinear n w
          (∑ i : Fin n, w i • Pi.single i (1 : ℝ)) := by rw [basis_sum]
    _ = ∑ i : Fin n, regularizedPathBilinear n w
          (w i • Pi.single i (1 : ℝ)) := by
      simpa using regularizedPathBilinear_sum_right
        (n := n) w Finset.univ (fun i => w i • Pi.single i (1 : ℝ))
    _ = ∑ i : Fin n, w i * (innerM n).mulVec w i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [regularizedPathBilinear_smul_right,
        regularizedPathBilinear_comm,
        innerM_mulVec_eq_bilinear]

theorem innerM_isUnit {n : Nat} (hn : 0 < n) : IsUnit (innerM n) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro u v huv
  have hzero : (innerM n).mulVec (u - v) = 0 := by
    funext i
    unfold Matrix.mulVec dotProduct
    simp only [Pi.sub_apply, Pi.zero_apply,
      mul_sub, Finset.sum_sub_distrib]
    have hi := congrFun huv i
    unfold Matrix.mulVec dotProduct at hi
    linarith
  have hbil : regularizedPathBilinear n (u - v) (u - v) = 0 := by
    rw [bilinear_eq_dot_mulVec]
    simp [hzero]
  rw [regularizedPathBilinear_self] at hbil
  have hlower := regularizedPathQuad_lower n (u - v)
  have hreg := pathRegularization_pos hn
  have hsq : vecSq (u - v) = 0 := by
    have hsnonneg : 0 ≤ vecSq (u - v) := by
      unfold vecSq NCPLVerification.vecSq
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    nlinarith
  exact sub_eq_zero.mp (vecSq_eq_zero hsq)

theorem innerM_mul_innerB {n : Nat} (hn : 0 < n) :
    innerM n * innerB n = 1 := by
  unfold innerB
  exact Matrix.mul_nonsing_inv _
    ((innerM n).isUnit_iff_isUnit_det.mp (innerM_isUnit hn))

/-- The `j`th Green column. -/
def innerGreenColumn (n : Nat) (j : Fin n) : EVec n := fun i => innerB n i j

theorem innerGreenColumn_equation {n : Nat} (hn : 0 < n) (j i : Fin n) :
    regularizedPathCoord (innerGreenColumn n j) i =
      (Pi.single j (1 : ℝ) : EVec n) i := by
  rw [← innerM_mulVec_eq_coord]
  have hmul := congrFun (congrFun (innerM_mul_innerB hn) i) j
  simpa [innerGreenColumn, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.one_apply, Pi.single_apply, eq_comm] using hmul

private theorem quadraticGreenProfile_coord_interior {n : Nat} (hn : 0 < n)
    (c d : ℝ) (i : Fin n) (hp : 0 < i.val) (hs : i.val + 1 < n) :
    regularizedPathCoord (quadraticGreenProfile n c d) i =
      quadraticGreenProfile n c d i / (n : ℝ) ^ 2 - 2 * d / (n : ℝ) := by
  have hcast : ((i.val - 1 : Nat) : ℝ) = (i.val : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  unfold regularizedPathCoord pathLaplacianCoord pathRegularization
  simp only [hp, hs, ↓reduceDIte, quadraticGreenProfile]
  rw [hcast]
  push_cast
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hnreal]
  ring

private theorem quadraticGreenProfile_coord_first {n : Nat} (hn : 1 < n)
    (c d : ℝ) :
    regularizedPathCoord (quadraticGreenProfile n c d)
        (innerFirst (by omega : 0 < n)) =
      quadraticGreenProfile n c d (innerFirst (by omega : 0 < n)) /
          (n : ℝ) ^ 2 + d / (n : ℝ) * (2 * (n : ℝ) - 3) := by
  unfold regularizedPathCoord pathLaplacianCoord pathRegularization
  simp only [innerFirst, quadraticGreenProfile]
  norm_num
  have hs : 0 + 1 < n := by omega
  simp only [hs, if_true]
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  field_simp [hnreal]
  ring

private theorem quadraticGreenProfile_coord_last {n : Nat} (hn : 1 < n)
    (c d : ℝ) :
    regularizedPathCoord (quadraticGreenProfile n c d)
        (innerLast (by omega : 0 < n)) =
      quadraticGreenProfile n c d (innerLast (by omega : 0 < n)) /
          (n : ℝ) ^ 2 - d / (n : ℝ) := by
  have hp : 0 < (innerLast (by omega : 0 < n)).val := by
    simp [innerLast]
    omega
  have hs : ¬(innerLast (by omega : 0 < n)).val + 1 < n := by
    unfold innerLast
    simp only
    omega
  have hcast : ((((innerLast (by omega : 0 < n)).val - 1 : Nat)) : ℝ) =
      ((n : ℝ) - 1) - 1 := by
    unfold innerLast
    simp only
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  unfold regularizedPathCoord pathLaplacianCoord pathRegularization
  simp only [hp, hs, ↓reduceDIte, quadraticGreenProfile]
  rw [hcast]
  simp only [innerLast]
  have hncast : ((n - 1 : Nat) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hncast]
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  field_simp [hnreal]
  ring

private theorem greenLowerBarrier_bounds {n : Nat} (hn : 0 < n) (i : Fin n) :
    (n : ℝ) / 10 ≤ greenLowerBarrier n i ∧
      greenLowerBarrier n i ≤ (n : ℝ) / 2 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hiupper : (i.val : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast i.isLt
  have hdist0 : 0 ≤ (n : ℝ) - 1 - (i.val : ℝ) := by linarith
  have hsq : ((n : ℝ) - 1 - (i.val : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hdist0 (by linarith : 0 ≤ (n : ℝ) +
      ((n : ℝ) - 1 - (i.val : ℝ)))]
  unfold greenLowerBarrier quadraticGreenProfile
  constructor
  · field_simp
    nlinarith [sq_nonneg ((n : ℝ) - 1 - (i.val : ℝ))]
  · field_simp
    nlinarith

private theorem greenUpperBarrier_bounds {n : Nat} (hn : 0 < n) (i : Fin n) :
    10 * (n : ℝ) ≤ greenUpperBarrier n i ∧
      greenUpperBarrier n i ≤ 11 * (n : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hiupper : (i.val : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast i.isLt
  have hdist0 : 0 ≤ (n : ℝ) - 1 - (i.val : ℝ) := by linarith
  have hsq : ((n : ℝ) - 1 - (i.val : ℝ)) ^ 2 ≤ (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hdist0 (by linarith : 0 ≤ (n : ℝ) +
      ((n : ℝ) - 1 - (i.val : ℝ)))]
  unfold greenUpperBarrier quadraticGreenProfile
  constructor
  · field_simp
    nlinarith [sq_nonneg ((n : ℝ) - 1 - (i.val : ℝ))]
  · field_simp
    nlinarith

theorem greenLowerBarrier_coord_le_source {n : Nat} (hn : 10 ≤ n)
    (i : Fin n) :
    regularizedPathCoord (greenLowerBarrier n) i ≤
      (Pi.single (innerFirst (by omega : 0 < n)) (1 : ℝ) : EVec n) i := by
  have hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hb := greenLowerBarrier_bounds hnpos i
  simp only [greenLowerBarrier] at hb
  by_cases hp : 0 < i.val
  · have hne : i ≠ innerFirst hnpos := by
      intro heq
      have := congrArg Fin.val heq
      simp [innerFirst] at this
      omega
    simp [hne]
    by_cases hs : i.val + 1 < n
    · change regularizedPathCoord
          (quadraticGreenProfile n (1 / 10) (2 / 5)) i ≤ 0
      rw [quadraticGreenProfile_coord_interior hnpos (1 / 10) (2 / 5) i hp hs]
      field_simp
      nlinarith
    · have hilast : i = innerLast hnpos := by
        apply Fin.ext
        simp [innerLast]
        omega
      subst i
      change regularizedPathCoord
          (quadraticGreenProfile n (1 / 10) (2 / 5)) (innerLast hnpos) ≤ 0
      rw [quadraticGreenProfile_coord_last (n := n) (by omega) (1 / 10) (2 / 5)]
      have hncast : ((n - 1 : Nat) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]
        norm_num
      have hblast : quadraticGreenProfile n (1 / 10) (2 / 5)
          (innerLast hnpos) = (n : ℝ) / 10 := by
        unfold quadraticGreenProfile innerLast
        simp only
        rw [hncast]
        ring
      rw [hblast]
      field_simp
      nlinarith
  · have hizero : i = innerFirst hnpos := by
      apply Fin.ext
      simp [innerFirst]
      omega
    subst i
    simp
    change regularizedPathCoord
        (quadraticGreenProfile n (1 / 10) (2 / 5)) (innerFirst hnpos) ≤ 1
    rw [quadraticGreenProfile_coord_first (n := n) (by omega) (1 / 10) (2 / 5)]
    have hb' := greenLowerBarrier_bounds hnpos (innerFirst hnpos)
    simp only [greenLowerBarrier] at hb'
    field_simp
    nlinarith

theorem source_le_greenUpperBarrier_coord {n : Nat} (hn : 10 ≤ n)
    (i : Fin n) :
    (Pi.single (innerFirst (by omega : 0 < n)) (1 : ℝ) : EVec n) i ≤
      regularizedPathCoord (greenUpperBarrier n) i := by
  have hnpos : 0 < n := by omega
  have hb := greenUpperBarrier_bounds hnpos i
  simp only [greenUpperBarrier] at hb
  by_cases hp : 0 < i.val
  · have hne : i ≠ innerFirst hnpos := by
      intro heq
      have := congrArg Fin.val heq
      simp [innerFirst] at this
      omega
    simp [hne]
    by_cases hs : i.val + 1 < n
    · change 0 ≤ regularizedPathCoord (quadraticGreenProfile n 10 1) i
      rw [quadraticGreenProfile_coord_interior hnpos 10 1 i hp hs]
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
      field_simp
      nlinarith
    · have hilast : i = innerLast hnpos := by
        apply Fin.ext
        simp [innerLast]
        omega
      subst i
      change 0 ≤ regularizedPathCoord
          (quadraticGreenProfile n 10 1) (innerLast hnpos)
      rw [quadraticGreenProfile_coord_last (n := n) (by omega) 10 1]
      have hb' := greenUpperBarrier_bounds hnpos (innerLast hnpos)
      simp only [greenUpperBarrier] at hb'
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
      field_simp
      nlinarith
  · have hizero : i = innerFirst hnpos := by
      apply Fin.ext
      simp [innerFirst]
      omega
    subst i
    simp
    change 1 ≤ regularizedPathCoord
        (quadraticGreenProfile n 10 1) (innerFirst hnpos)
    rw [quadraticGreenProfile_coord_first (n := n) (by omega) 10 1]
    have hb' := greenUpperBarrier_bounds hnpos (innerFirst hnpos)
    simp only [greenUpperBarrier] at hb'
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    field_simp
    nlinarith

private theorem regularizedPathCoord_sub {n : Nat} (u v : EVec n) (i : Fin n) :
    regularizedPathCoord (u - v) i =
      regularizedPathCoord u i - regularizedPathCoord v i := by
  unfold regularizedPathCoord pathLaplacianCoord
  split <;> split <;> simp <;> ring

theorem greenLowerBarrier_le_firstColumn {n : Nat} (hn : 10 ≤ n)
    (i : Fin n) : greenLowerBarrier n i ≤
      innerB n i (innerFirst (by omega : 0 < n)) := by
  let hnpos : 0 < n := by omega
  let z : EVec n := innerGreenColumn n (innerFirst hnpos) - greenLowerBarrier n
  have hzcoord : ∀ j : Fin n, 0 ≤ regularizedPathCoord z j := by
    intro j
    unfold z
    rw [regularizedPathCoord_sub,
      innerGreenColumn_equation hnpos (innerFirst hnpos) j]
    exact sub_nonneg.mpr (greenLowerBarrier_coord_le_source hn j)
  have hz := regularizedPath_maximum_principle hnpos hzcoord i
  simpa [z, innerGreenColumn] using hz

theorem firstColumn_le_greenUpperBarrier {n : Nat} (hn : 10 ≤ n)
    (i : Fin n) : innerB n i (innerFirst (by omega : 0 < n)) ≤
      greenUpperBarrier n i := by
  let hnpos : 0 < n := by omega
  let z : EVec n := greenUpperBarrier n - innerGreenColumn n (innerFirst hnpos)
  have hzcoord : ∀ j : Fin n, 0 ≤ regularizedPathCoord z j := by
    intro j
    unfold z
    rw [regularizedPathCoord_sub,
      innerGreenColumn_equation hnpos (innerFirst hnpos) j]
    exact sub_nonneg.mpr (source_le_greenUpperBarrier_coord hn j)
  have hz := regularizedPath_maximum_principle hnpos hzcoord i
  simpa [z, innerGreenColumn] using hz

/-- The Green estimate quoted in the TeX, proved here with the sharper upper
constant `11` produced by the explicit comparison profile. -/
theorem innerB_first_column_bounds {n : Nat} (hn : 10 ≤ n) (i : Fin n) :
    (n : ℝ) / 10 ≤ innerB n i (innerFirst (by omega : 0 < n)) ∧
      innerB n i (innerFirst (by omega : 0 < n)) ≤ 20 * (n : ℝ) := by
  have hnpos : 0 < n := by omega
  have hlowerProfile := (greenLowerBarrier_bounds hnpos i).1
  have hlower := greenLowerBarrier_le_firstColumn hn i
  have hupper := firstColumn_le_greenUpperBarrier hn i
  have hupperProfile := (greenUpperBarrier_bounds hnpos i).2
  constructor <;> nlinarith

theorem innerB_cross_pos {n : Nat} (hn : 10 ≤ n) :
    0 < innerB n (innerLast (by omega : 0 < n))
      (innerFirst (by omega : 0 < n)) := by
  have h := (innerB_first_column_bounds hn
    (innerLast (by omega : 0 < n))).1
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  nlinarith

/-- Reversal of a path vector. -/
def reverseEVec {n : Nat} (w : EVec n) : EVec n := fun i => w i.rev

private theorem reverseEVec_involutive {n : Nat} (w : EVec n) :
    reverseEVec (reverseEVec w) = w := by
  funext i
  simp [reverseEVec]

private theorem reverseEVec_add {n : Nat} (u v : EVec n) :
    reverseEVec (u + v) = reverseEVec u + reverseEVec v := by
  rfl

private theorem reverseEVec_single {n : Nat} (i : Fin n) :
    reverseEVec (Pi.single i (1 : ℝ)) = Pi.single i.rev (1 : ℝ) := by
  funext j
  simp only [reverseEVec, Pi.single_apply]
  by_cases h : j.rev = i
  · have : j = i.rev := by
      rw [← Fin.rev_inj]
      simpa using h
    simp [this]
  · have : j ≠ i.rev := by
      intro heq
      apply h
      rw [heq, Fin.rev_rev]
    simp [h, this]

private theorem vecSq_reverse {n : Nat} (w : EVec n) :
    vecSq (reverseEVec w) = vecSq w := by
  unfold vecSq NCPLVerification.vecSq reverseEVec
  simpa [Fin.revPerm_apply] using
    (Equiv.sum_comp Fin.revPerm (fun i : Fin n => w i ^ 2))

private theorem pathEnergy_reverse {n : Nat} (w : EVec n) :
    pathEnergy n (reverseEVec w) = pathEnergy n w := by
  cases n with
  | zero => simp [pathEnergy]
  | succ m =>
      unfold pathEnergy reverseEVec
      calc
        (∑ j : Fin m, (w j.castSucc.rev - w j.succ.rev) ^ 2) =
            ∑ j : Fin m, (w j.rev.succ - w j.rev.castSucc) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Fin.rev_castSucc, Fin.rev_succ]
        _ = ∑ j : Fin m, (w j.rev.castSucc - w j.rev.succ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ = ∑ j : Fin m, (w j.castSucc - w j.succ) ^ 2 := by
          simpa [Fin.revPerm_apply] using
            (Equiv.sum_comp Fin.revPerm
              (fun j : Fin m => (w j.castSucc - w j.succ) ^ 2))

theorem regularizedPathQuad_reverse {n : Nat} (w : EVec n) :
    regularizedPathQuad n (reverseEVec w) = regularizedPathQuad n w := by
  unfold regularizedPathQuad
  rw [vecSq_reverse, pathEnergy_reverse]

private theorem bilinear_eq_polarization (n : Nat) (u v : EVec n) :
    regularizedPathBilinear n u v =
      (regularizedPathQuad n (u + v) - regularizedPathQuad n u -
        regularizedPathQuad n v) / 2 := by
  have h := regularizedPathQuad_add_expansion n u v
  linarith

theorem regularizedPathBilinear_reverse {n : Nat} (u v : EVec n) :
    regularizedPathBilinear n (reverseEVec u) (reverseEVec v) =
      regularizedPathBilinear n u v := by
  rw [bilinear_eq_polarization, ← reverseEVec_add,
    regularizedPathQuad_reverse, regularizedPathQuad_reverse,
    regularizedPathQuad_reverse, bilinear_eq_polarization]

theorem innerM_reverse (n : Nat) (i j : Fin n) :
    innerM n i.rev j.rev = innerM n i j := by
  unfold innerM
  rw [← reverseEVec_single i, ← reverseEVec_single j,
    regularizedPathBilinear_reverse]

theorem regularizedPathCoord_reverse {n : Nat} (w : EVec n) (i : Fin n) :
    regularizedPathCoord (reverseEVec w) i = regularizedPathCoord w i.rev := by
  rw [← regularizedPathBilinear_single_left_eq_coord,
    ← regularizedPathBilinear_single_left_eq_coord]
  calc
    regularizedPathBilinear n (Pi.single i 1) (reverseEVec w) =
        regularizedPathBilinear n
          (reverseEVec (Pi.single i.rev 1)) (reverseEVec w) := by
      rw [reverseEVec_single, Fin.rev_rev]
    _ = regularizedPathBilinear n (Pi.single i.rev 1) w :=
      regularizedPathBilinear_reverse _ _

private theorem single_reverse_apply {n : Nat} (j i : Fin n) :
    (Pi.single j (1 : ℝ) : EVec n) i.rev =
      (Pi.single j.rev (1 : ℝ) : EVec n) i := by
  simp only [Pi.single_apply]
  by_cases h : i.rev = j
  · have hr : i = j.rev := by
      rw [← Fin.rev_inj]
      simpa using h
    simp [hr]
  · have hr : i ≠ j.rev := by
      intro heq
      apply h
      rw [heq, Fin.rev_rev]
    simp [h, hr]

theorem innerGreenColumn_reverse {n : Nat} (hn : 0 < n) (j : Fin n) :
    reverseEVec (innerGreenColumn n j) = innerGreenColumn n j.rev := by
  apply (Matrix.mulVec_injective_iff_isUnit.mpr (innerM_isUnit hn))
  funext i
  rw [innerM_mulVec_eq_coord, innerM_mulVec_eq_coord,
    regularizedPathCoord_reverse,
    innerGreenColumn_equation hn j i.rev,
    innerGreenColumn_equation hn j.rev i,
    single_reverse_apply]

theorem innerB_reverse (n : Nat) (hn : 0 < n) (i j : Fin n) :
    innerB n i.rev j.rev = innerB n i j := by
  have h := congrFun (innerGreenColumn_reverse hn j) i.rev
  simpa [reverseEVec, innerGreenColumn] using h.symm

theorem innerFirst_rev {n : Nat} (hn : 0 < n) :
    (innerFirst hn).rev = innerLast hn := by
  apply Fin.ext
  simp [innerFirst, innerLast, Fin.rev]

theorem innerLast_rev {n : Nat} (hn : 0 < n) :
    (innerLast hn).rev = innerFirst hn := by
  rw [← innerFirst_rev hn, Fin.rev_rev]

theorem innerB_endpoint_diagonal_eq {n : Nat} (hn : 0 < n) :
    innerB n (innerLast hn) (innerLast hn) =
      innerB n (innerFirst hn) (innerFirst hn) := by
  rw [← innerFirst_rev hn]
  exact innerB_reverse n hn (innerFirst hn) (innerFirst hn)

theorem innerB_last_column_bounds {n : Nat} (hn : 10 ≤ n) (i : Fin n) :
    (n : ℝ) / 10 ≤ innerB n i (innerLast (by omega : 0 < n)) ∧
      innerB n i (innerLast (by omega : 0 < n)) ≤ 20 * (n : ℝ) := by
  let hnpos : 0 < n := by omega
  have h := innerB_first_column_bounds hn i.rev
  have href := innerB_reverse n hnpos i.rev (innerFirst hnpos)
  rw [Fin.rev_rev, innerFirst_rev hnpos] at href
  rw [href]
  exact h

private theorem bilinear_eq_weighted_action {n : Nat} (u v : EVec n) :
    regularizedPathBilinear n u v =
      ∑ i : Fin n, v i * (innerM n).mulVec u i := by
  classical
  calc
    regularizedPathBilinear n u v =
        regularizedPathBilinear n u
          (∑ i : Fin n, v i • Pi.single i (1 : ℝ)) := by rw [basis_sum]
    _ = ∑ i : Fin n, regularizedPathBilinear n u
          (v i • Pi.single i (1 : ℝ)) := by
      simpa using regularizedPathBilinear_sum_right
        (n := n) u Finset.univ (fun i => v i • Pi.single i (1 : ℝ))
    _ = ∑ i : Fin n, v i * (innerM n).mulVec u i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [regularizedPathBilinear_smul_right,
        regularizedPathBilinear_comm,
        innerM_mulVec_eq_bilinear]

private theorem bilinear_greenColumn {n : Nat} (hn : 0 < n)
    (j : Fin n) (d : EVec n) :
    regularizedPathBilinear n (innerGreenColumn n j) d = d j := by
  rw [bilinear_eq_weighted_action]
  have haction : (innerM n).mulVec (innerGreenColumn n j) =
      Pi.single j (1 : ℝ) := by
    funext i
    rw [innerM_mulVec_eq_coord, innerGreenColumn_equation hn]
  rw [haction]
  simp [Pi.single_apply]

theorem innerMaximizer_stationary {n : Nat} (hn : 10 ≤ n) (a b : ℝ) :
    IsInnerStationary (by omega : 0 < n) (innerC (by omega : 0 < n)) a b
      (innerMaximizer (by omega : 0 < n) a b) := by
  let hnpos : 0 < n := by omega
  intro d
  have hw : innerMaximizer hnpos a b =
      innerScale n (innerC hnpos) •
        (a • innerGreenColumn n (innerFirst hnpos) +
          (-(b / 2)) • innerGreenColumn n (innerLast hnpos)) := by
    funext i
    unfold innerMaximizer innerGreenColumn
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [hw, regularizedPathBilinear_smul_left,
    regularizedPathBilinear_add_left,
    regularizedPathBilinear_smul_left,
    regularizedPathBilinear_smul_left,
    bilinear_greenColumn hnpos, bilinear_greenColumn hnpos]
  unfold innerForcing
  ring

theorem innerC_bounds {n : Nat} (hn : 10 ≤ n) :
    (3 / 5 : ℝ) ≤ innerC (by omega : 0 < n) ∧
      innerC (by omega : 0 < n) ≤ 120 := by
  let hnpos : 0 < n := by omega
  have hcross := innerB_first_column_bounds hn (innerLast hnpos)
  exact innerC_bounds_of_endpoint_bounds hnpos hcross.1 hcross.2

theorem innerC_pos {n : Nat} (hn : 10 ≤ n) :
    0 < innerC (by omega : 0 < n) := by
  have h := (innerC_bounds hn).1
  norm_num at h ⊢
  linarith

theorem innerC1_uniform_bound {n : Nat} (hn : 10 ≤ n) :
    |innerC1 (by omega : 0 < n)| ≤ 2400 := by
  let hnpos : 0 < n := by omega
  let x := innerB n (innerLast hnpos) (innerFirst hnpos)
  let y := innerB n (innerFirst hnpos) (innerFirst hnpos)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hC := innerC_bounds hn
  have hx := innerB_first_column_bounds hn (innerLast hnpos)
  have hy := innerB_first_column_bounds hn (innerFirst hnpos)
  have hxabs : |x| ≤ 20 * (n : ℝ) := by
    rw [abs_of_nonneg (by dsimp [x]; linarith [hx.1])]
    exact hx.2
  have hyabs : |y| ≤ 20 * (n : ℝ) := by
    rw [abs_of_nonneg (by dsimp [y]; linarith [hy.1])]
    exact hy.2
  have hdiff : |x - y| ≤ 40 * (n : ℝ) := by
    calc
      |x - y| ≤ |x| + |y| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le x 0 y
      _ ≤ 40 * (n : ℝ) := by linarith
  have hprod : innerC hnpos * |x - y| ≤ 120 * (40 * (n : ℝ)) :=
    mul_le_mul hC.2 hdiff (abs_nonneg _) (by linarith [hC.1])
  unfold innerC1
  change |innerC hnpos * (x - y) / (2 * (n : ℝ))| ≤ 2400
  rw [abs_div, abs_mul, abs_of_nonneg (by linarith [hC.1]),
    abs_of_pos (by positivity : 0 < 2 * (n : ℝ)),
    div_le_iff₀ (by positivity : 0 < 2 * (n : ℝ))]
  nlinarith

theorem innerC2_uniform_bound {n : Nat} (hn : 10 ≤ n) :
    |innerC2 (by omega : 0 < n)| ≤ 600 := by
  let hnpos : 0 < n := by omega
  let x := innerB n (innerLast hnpos) (innerFirst hnpos)
  let y := innerB n (innerFirst hnpos) (innerFirst hnpos)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hC := innerC_bounds hn
  have hx := innerB_first_column_bounds hn (innerLast hnpos)
  have hy := innerB_first_column_bounds hn (innerFirst hnpos)
  have hxabs : |x| ≤ 20 * (n : ℝ) := by
    rw [abs_of_nonneg (by dsimp [x]; linarith [hx.1])]
    exact hx.2
  have hyabs : |y| ≤ 20 * (n : ℝ) := by
    rw [abs_of_nonneg (by dsimp [y]; linarith [hy.1])]
    exact hy.2
  have hdiff : |x - y| ≤ 40 * (n : ℝ) := by
    calc
      |x - y| ≤ |x| + |y| := by
        simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le x 0 y
      _ ≤ 40 * (n : ℝ) := by linarith
  have hprod : innerC hnpos * |x - y| ≤ 120 * (40 * (n : ℝ)) :=
    mul_le_mul hC.2 hdiff (abs_nonneg _) (by linarith [hC.1])
  unfold innerC2
  change |innerC hnpos * (x - y) / (8 * (n : ℝ))| ≤ 600
  rw [abs_div, abs_mul, abs_of_nonneg (by linarith [hC.1]),
    abs_of_pos (by positivity : 0 < 8 * (n : ℝ)),
    div_le_iff₀ (by positivity : 0 < 8 * (n : ℝ))]
  nlinarith

theorem innerChain_transfer_verified {n : Nat} (hn : 10 ≤ n) (a b : ℝ) :
    innerChain (by omega : 0 < n) (innerC (by omega : 0 < n)) a b
          (innerMaximizer (by omega : 0 < n) a b) +
        innerC1 (by omega : 0 < n) * a ^ 2 +
        innerC2 (by omega : 0 < n) * b ^ 2 =
      6 * (a - b / 2) ^ 2 := by
  let hnpos : 0 < n := by omega
  apply innerChain_explicit_transfer hnpos
  · exact (innerC_pos hn).le
  · exact fun q r => innerMaximizer_stationary hn q r
  · exact ne_of_gt (innerB_cross_pos hn)
  · exact innerB_endpoint_diagonal_eq hnpos

theorem innerMaximizer_size_verified {n : Nat} (hn : 10 ≤ n) (a b : ℝ) :
    vecSq (innerMaximizer (by omega : 0 < n) a b) ≤
      96000 * (n : ℝ) ^ 2 * (a ^ 2 + b ^ 2) := by
  let hnpos : 0 < n := by omega
  apply innerMaximizer_size_of_column_bounds hnpos
  · exact ⟨(innerC_pos hn).le, (innerC_bounds hn).2⟩
  · intro i
    have h := innerB_first_column_bounds hn i
    rw [abs_of_nonneg (by linarith [h.1])]
    exact h.2
  · intro i
    have h := innerB_last_column_bounds hn i
    rw [abs_of_nonneg (by linarith [h.1])]
    exact h.2

/-- Summary certificate eliminating every Green-matrix hypothesis previously
exposed by the concrete inner-chain interface. -/
theorem innerGreen_summary {n : Nat} (hn : 10 ≤ n) :
    ((n : ℝ) / 10 ≤ innerB n (innerLast (by omega : 0 < n))
        (innerFirst (by omega : 0 < n)) ∧
      innerB n (innerLast (by omega : 0 < n))
        (innerFirst (by omega : 0 < n)) ≤ 20 * (n : ℝ)) ∧
    innerB n (innerLast (by omega : 0 < n))
        (innerLast (by omega : 0 < n)) =
      innerB n (innerFirst (by omega : 0 < n))
        (innerFirst (by omega : 0 < n)) ∧
    ((3 / 5 : ℝ) ≤ innerC (by omega : 0 < n) ∧
      innerC (by omega : 0 < n) ≤ 120) ∧
    |innerC1 (by omega : 0 < n)| ≤ 2400 ∧
    |innerC2 (by omega : 0 < n)| ≤ 600 ∧
    (∀ a b : ℝ, IsInnerStationary (by omega : 0 < n)
      (innerC (by omega : 0 < n)) a b
        (innerMaximizer (by omega : 0 < n) a b)) := by
  let hnpos : 0 < n := by omega
  exact ⟨innerB_first_column_bounds hn (innerLast hnpos),
    innerB_endpoint_diagonal_eq hnpos, innerC_bounds hn,
    innerC1_uniform_bound hn, innerC2_uniform_bound hn,
    innerMaximizer_stationary hn⟩

private theorem innerForcing_single_eq_source {n : Nat} (hn : 0 < n)
    (a b : ℝ) (i : Fin n) :
    innerForcing hn a b (Pi.single i (1 : ℝ)) = innerSource hn a b i := by
  unfold innerForcing innerSource
  simp only [Pi.single_apply, Pi.sub_apply]
  by_cases hf : i = innerFirst hn <;>
    by_cases hl : i = innerLast hn <;> simp [hf, hl, eq_comm]

/-- The arbitrary-direction derivative from `InnerChain` specializes to the
displayed tridiagonal coordinate gradient. -/
theorem hasDerivAt_innerChain_dual_coordinate {n : Nat} (hn : 0 < n)
    (C a b : ℝ) (w : EVec n) (i : Fin n) :
    HasDerivAt
      (fun t : ℝ => innerChain hn C a b
        (w + t • Pi.single i (1 : ℝ)))
      (-innerSaddleGradW hn C a b w i) 0 := by
  convert hasDerivAt_innerChain_dual_line_zero hn C a b w
    (Pi.single i (1 : ℝ)) using 1
  rw [regularizedPathBilinear_comm,
    regularizedPathBilinear_single_left_eq_coord,
    innerForcing_single_eq_source]
  unfold innerSaddleGradW
  ring

end

end NCCLowerBoundVerification
