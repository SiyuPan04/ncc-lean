import NCC.Extensions.NCSC
import NCC.Extensions.GameStationarity
import NCCLowerBound.Simplified.InnerRelay
import NCCLowerBoundVerification.Lower.UniformInner
import NCCLowerBoundVerification.Oracle.ZeroRespectingAlgorithm

/-!
# A fixed-conditioned dual chain with an initialization-dependent obstruction

This is a new auxiliary example, not the manuscript's NCC hard objective.
Its matrix is exactly `I + pathLaplacian`: endpoint diagonal 2 and interior
diagonal 3 (the one-dimensional matrix is 1), with off-diagonal entries -1.
The forcing can grow while smoothness and strong concavity stay fixed.
The terminal-coordinate obstruction below is not an arbitrary-deterministic
lower bound: no resisting rotation is asserted in this module.
-/

namespace NCC.Extensions.NCSCZeroChainObstruction

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open PointwiseConjugate
open scoped BigOperators

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

def operator {d : ℕ} (y : EVec d) : EVec d :=
  fun i => y i + pathLaplacianCoord y i

def matrix (d : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  (1 - pathRegularization d) • (1 : Matrix (Fin d) (Fin d) ℝ) + innerM d

theorem matrix_action {d : ℕ} (y : EVec d) : (matrix d).mulVec y = operator y := by
  ext i
  simp only [matrix, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, innerM_mulVec_eq_coord,
    regularizedPathCoord, operator]
  ring

theorem matrix_symmetric (d : ℕ) : (matrix d).transpose = matrix d := by
  simp only [matrix, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one,
    innerM_symmetric]

theorem operator_selfAdjoint {d : ℕ} (y v : EVec d) :
    dot (operator y) v = dot y (operator v) := by
  rw [← matrix_action y, ← matrix_action v]
  change dotProduct ((matrix d).mulVec y) v = dotProduct y ((matrix d).mulVec v)
  rw [dotProduct_comm]
  have h := Matrix.dotProduct_transpose_mulVec (matrix d) y v
  rw [matrix_symmetric] at h
  exact h.symm

theorem operator_add {d : ℕ} (y v : EVec d) :
    operator (y + v) = operator y + operator v := by
  simp only [← matrix_action, Matrix.mulVec_add]

theorem operator_smul {d : ℕ} (a : ℝ) (y : EVec d) :
    operator (a • y) = a • operator y := by
  simp only [← matrix_action, Matrix.mulVec_smul]

theorem operator_sub {d : ℕ} (y v : EVec d) :
    operator (y - v) = operator y - operator v := by
  simp only [← matrix_action, Matrix.mulVec_sub]

def quadratic {d : ℕ} (y : EVec d) : ℝ := (1 / 2) * dot y (operator y)

theorem operator_energy {d : ℕ} (y : EVec d) :
    dot y (operator y) = vecSq y + pathEnergy d y := by
  have hp := NCCLowerBound.Simplified.InnerRelay.pathA_quadratic_eq d y
  simp only [NCCLowerBound.Simplified.InnerRelay.pathA_mulVec_eq_coord] at hp
  unfold dot operator
  simp only [mul_add, Finset.sum_add_distrib]
  rw [hp]
  congr 1
  unfold vecSq NCPLVerification.vecSq
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadratic_eq {d : ℕ} (y : EVec d) :
    quadratic y = (1 / 2) * (vecSq y + pathEnergy d y) := by
  rw [quadratic, operator_energy]

theorem quadratic_bounds {d : ℕ} (y : EVec d) :
    (1 / 2) * vecSq y ≤ quadratic y ∧ quadratic y ≤ (5 / 2) * vecSq y := by
  rw [quadratic_eq]
  constructor <;> linarith [pathEnergy_nonneg d y, pathEnergy_le_four_vecSq d y]

def operatorCLM (d : ℕ) : EVec d →L[ℝ] EVec d :=
  (Matrix.toLin' (matrix d)).toContinuousLinearMap

theorem operatorCLM_apply {d : ℕ} (y : EVec d) : operatorCLM d y = operator y :=
  matrix_action y

theorem hasFDerivAt_operator {d : ℕ} (y : EVec d) :
    HasFDerivAt operator (operatorCLM d) y := by
  rw [show (operator : EVec d → EVec d) = operatorCLM d from
    funext fun v => (operatorCLM_apply v).symm]
  exact (operatorCLM d).hasFDerivAt

theorem quadratic_hasFDerivAt {d : ℕ} (y : EVec d) :
    HasFDerivAt quadratic (residualCLM (operator y)) y := by
  have hcoord (i : Fin d) := (hasFDerivAt_apply (𝕜 := ℝ) i y).mul
    ((hasFDerivAt_apply (𝕜 := ℝ) i (operator y)).comp y (hasFDerivAt_operator y))
  have hs := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hcoord i)).const_mul (1 / 2 : ℝ)
  convert! hs using 1
  ext v
  simp only [residualCLM_apply, eDot, smul_apply, sum_apply, add_apply,
    ContinuousLinearMap.comp_apply, Function.comp_apply,
    ContinuousLinearMap.proj_apply, operatorCLM_apply, smul_eq_mul, Finset.sum_add_distrib]
  have hd := operator_selfAdjoint y v
  unfold dot at hd
  nlinarith

def objective (n : ℕ) (c : ℝ) (_x : EVec 1) (y : EVec (n + 1)) : ℝ :=
  c * y 0 - quadratic y

def gradient (n : ℕ) (c : ℝ) (y : EVec (n + 1)) : EVec (n + 1) :=
  Pi.single 0 c - operator y

theorem objective_contDiff (n : ℕ) (c : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (objective n c)) := by
  have heq : Function.uncurry (objective n c) =
      fun u : EVec 1 × EVec (n + 1) =>
        c * u.2 0 - (1 / 2) * (vecSq u.2 + pathEnergy (n + 1) u.2) := by
    funext u
    exact congrArg (c * u.2 0 - ·) (quadratic_eq u.2)
  rw [heq]
  unfold vecSq NCPLVerification.vecSq pathEnergy
  fun_prop

theorem objective_hasFDerivAt (n : ℕ) (c : ℝ) (x : EVec 1) (y : EVec (n + 1)) :
    HasFDerivAt (objective n c x) (residualCLM (gradient n c y)) y := by
  classical
  convert! ((hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin (n + 1)) y).const_mul c).sub
    (quadratic_hasFDerivAt y) using 1
  ext v
  simp [gradient, residualCLM_apply, eDot, Pi.single_apply, sub_mul, Finset.sum_sub_distrib]

theorem operator_squared_le {d : ℕ} (y : EVec d) : vecSq (operator y) ≤ 25 * vecSq y := by
  have heq : operator y = y + pathLaplacianVector y := rfl
  rw [heq, PointwiseConjugate.vecSq_add_expand]
  have hp := NCCLowerBound.Simplified.InnerRelay.pathA_quadratic_eq d y
  simp only [NCCLowerBound.Simplified.InnerRelay.pathA_mulVec_eq_coord] at hp
  have he : dot y (pathLaplacianVector y) = pathEnergy d y := hp
  rw [he]
  linarith [pathLaplacianVector_vecSq_le y, pathEnergy_le_four_vecSq d y]

theorem gradient_difference (n : ℕ) (c : ℝ) (y v : EVec (n + 1)) :
    gradient n c y - gradient n c v = -operator (y - v) := by
  rw [operator_sub]
  unfold gradient
  module

theorem gradient_lipschitz (n : ℕ) (c : ℝ) (y v : EVec (n + 1)) :
    vecSq (gradient n c y - gradient n c v) ≤ 5 ^ 2 * vecSq (y - v) := by
  rw [gradient_difference, Tracking.vecSq_neg]
  norm_num only [show (5 : ℝ) ^ 2 = 25 by norm_num]
  exact operator_squared_le _

theorem pathEnergy_convex (d : ℕ) :
    ConvexOn ℝ Set.univ (pathEnergy d) := by
  refine ⟨convex_univ, ?_⟩
  intro y _ v _ a b ha hb hab
  cases d with
  | zero => simp [pathEnergy]
  | succ d =>
      have hcoord (i : Fin d) :
          (a * (y i.castSucc - y i.succ) + b * (v i.castSucc - v i.succ)) ^ 2 ≤
            a * (y i.castSucc - y i.succ) ^ 2 + b * (v i.castSucc - v i.succ) ^ 2 :=
        (Even.convexOn_pow (𝕜 := ℝ) (show Even (2 : ℕ) by decide)).2
          (Set.mem_univ _) (Set.mem_univ _) ha hb hab
      have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoord i)
      simp only [pathEnergy, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have heq : ∀ i : Fin d,
          a * y i.castSucc + b * v i.castSucc - (a * y i.succ + b * v i.succ) =
            a * (y i.castSucc - y i.succ) + b * (v i.castSucc - v i.succ) := by
        intro i
        ring
      simp only [heq]
      simpa only [Finset.sum_add_distrib, ← Finset.mul_sum] using hs

/-- Fixed strong concavity 1, independent of chain length and forcing. -/
theorem objective_stronglyConcave (n : ℕ) (c : ℝ) (x : EVec 1) :
    ConcaveOn ℝ Set.univ (fun y => objective n c x y + quadraticCorrection 1 y) := by
  refine ⟨convex_univ, ?_⟩
  intro y _ v _ a b ha hb hab
  have hp := (pathEnergy_convex (n + 1)).2 (Set.mem_univ y) (Set.mem_univ v) ha hb hab
  simp only [objective, quadratic_eq, quadraticCorrection, one_div,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  nlinarith

def family (n : ℕ) (c : ℝ) : NCCInstance 1 (n + 1) where
  X := Set.univ
  Y := Set.univ
  f := objective n c
  gradX := fun _ _ => 0
  gradY := fun _ y => gradient n c y
  x0 := 0

/-- Literal feasible-domain NC-SC membership at fixed `(ell,mu,Delta)=(5,1,1)`.
The true primal value gap is zero, because the objective is independent of x. -/
theorem withinClass (n : ℕ) (c : ℝ) : NCSC.NCSCClass 5 1 1 (family n c) := by
  refine {
    ell_pos := by norm_num
    mu_pos := by norm_num
    Delta_pos := by norm_num
    primal_origin := Set.mem_univ _
    dual_origin := Set.mem_univ _
    initialization := rfl
    X_closed := isClosed_univ
    X_convex := convex_univ
    Y_closed := isClosed_univ
    Y_convex := convex_univ
    gradient_representation := ?_
    jointly_smooth := ?_
    dual_stronglyConcave := ?_
    initial_gap_pointwise := ?_ }
  · intro x _ y _
    have hd := (objective_hasFDerivAt n c x y).comp (x, y)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y)))
    convert! hd.hasFDerivWithinAt using 1
    apply ContinuousLinearMap.ext
    rintro ⟨dx, dy⟩
    simp [family, NCC.Model.jointGradientCLM, residualCLM_apply, eDot]
  · intro x _ y _ u _ v _
    have hg := gradient_lipschitz n c y v
    change vecSq (0 - (0 : EVec 1)) + vecSq (gradient n c y - gradient n c v) ≤
      5 ^ 2 * (vecSq (x - u) + vecSq (y - v))
    have hz : vecSq (0 : EVec 1) = 0 := by simp [vecSq, NCPLVerification.vecSq]
    rw [sub_self, hz, zero_add]
    nlinarith [vecSq_nonneg (x - u)]
  · intro x _
    exact objective_stronglyConcave n c x
  · intro x _
    change ValueOn Set.univ (objective n c) 0 - ValueOn Set.univ (objective n c) x ≤ 1
    have heq : ValueOn Set.univ (objective n c) 0 = ValueOn Set.univ (objective n c) x := rfl
    rw [heq, sub_self]
    norm_num

theorem initial_value_gap_zero (n : ℕ) (c : ℝ) :
    ValueOn Set.univ (objective n c) 0 -
      sInf (Set.range (ValueOn Set.univ (objective n c))) = 0 := by
  have heq : ValueOn Set.univ (objective n c) =
      fun _ : EVec 1 => ValueOn Set.univ (objective n c) 0 := rfl
  rw [heq]
  simp

theorem gradient_zero_of_zero_tail {n k : ℕ} (c : ℝ) (y : EVec (n + 1))
    (hy : ∀ i : Fin (n + 1), k ≤ i.val → y i = 0)
    (i : Fin (n + 1)) (hi : k + 1 ≤ i.val) : gradient n c y i = 0 := by
  have hs : y i = 0 := hy i (by omega)
  have hp := regularizedPathCoord_zero_of_zero_tail hy i hi
  have hz : pathLaplacianCoord y i = 0 := by
    simpa only [regularizedPathCoord, hs, mul_zero, zero_add] using hp
  have hne : i ≠ 0 := by
    intro hh
    have heq : i.val = 0 := congrArg Fin.val hh
    omega
  simp [gradient, operator, hs, hz, hne]

/-- The positive homogeneous solution of the interior recurrence. -/
def coefficient : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | k + 2 => 3 * coefficient (k + 1) - coefficient k

theorem coefficient_bounds (k : ℕ) :
    0 < coefficient k ∧ coefficient k ≤ coefficient (k + 1) ∧
      coefficient (k + 1) ≤ 3 * coefficient k := by
  induction k with
  | zero => norm_num [coefficient]
  | succ k ih =>
      rw [show k + 1 + 1 = k + 2 by omega, coefficient]
      constructor
      · linarith [ih.1, ih.2.1]
      constructor <;> linarith [ih.1, ih.2.1, ih.2.2]

theorem coefficient_le_pow3 (k : ℕ) : coefficient k ≤ 3 ^ k := by
  induction k with
  | zero => norm_num [coefficient]
  | succ k ih =>
      rw [pow_succ]
      nlinarith [(coefficient_bounds k).2.2]

theorem coefficient_sum_le_pow5 (d : ℕ) :
    (∑ i : Fin d, coefficient i.val) ≤ 5 ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hp : (3 : ℝ) ^ d ≤ 5 ^ d := by gcongr; norm_num
      have hc := coefficient_le_pow3 d
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 5) d]

def testVector (n : ℕ) : EVec (n + 1) := fun i => coefficient i.val

theorem testVector_first (n : ℕ) : testVector n 0 = 1 := rfl

theorem operator_testVector_zero {n : ℕ} (i : Fin (n + 1)) (hi : i.val < n) :
    operator (testVector n) i = 0 := by
  have hnext : i.val + 1 < n + 1 := by omega
  by_cases hz : i.val = 0
  · have hn : 0 < n := by omega
    norm_num [operator, pathLaplacianCoord, testVector, hz, coefficient, hn]
  · have hp : 0 < i.val := by omega
    have hrec : coefficient (i.val + 1) =
        3 * coefficient i.val - coefficient (i.val - 1) := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hz
      rw [hk]
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      rfl
    simp only [operator, pathLaplacianCoord, hp, hnext, ↓reduceDIte, testVector]
    rw [hrec]
    ring

theorem weighted_gradient_eq_forcing {n : ℕ} (c : ℝ) (y : EVec (n + 1))
    (htail : y (Fin.last n) = 0) : dot (gradient n c y) (testVector n) = c := by
  rw [gradient, dot_sub_left, operator_selfAdjoint]
  have hz : dot y (operator (testVector n)) = 0 := by
    unfold dot
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : i.val < n
    · rw [operator_testVector_zero i hi, mul_zero]
    · have heq : i = Fin.last n := Fin.ext (by simp; omega)
      rw [heq, htail, zero_mul]
  rw [hz, sub_zero]
  classical
  simp [dot, testVector, Pi.single_apply, coefficient]

theorem forcing_le_of_terminal_zero {n : ℕ} {c eps : ℝ}
    (heps : 0 ≤ eps) (y : EVec (n + 1)) (htail : y (Fin.last n) = 0)
    (hgradient : vecSq (gradient n c y) ≤ eps ^ 2) :
    c ≤ 5 ^ (n + 1) * eps := by
  have hcoord (i : Fin (n + 1)) : gradient n c y i ≤ eps := by
    have hi : gradient n c y i ^ 2 ≤ vecSq (gradient n c y) :=
      Finset.single_le_sum (fun j _ => sq_nonneg (gradient n c y j)) (Finset.mem_univ i)
    nlinarith
  rw [← weighted_gradient_eq_forcing c y htail]
  calc
    dot (gradient n c y) (testVector n) ≤
        ∑ i : Fin (n + 1), eps * coefficient i.val := by
      unfold dot testVector
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_right (hcoord i) (coefficient_bounds i.val).1.le
    _ = eps * ∑ i : Fin (n + 1), coefficient i.val := by rw [Finset.mul_sum]
    _ ≤ eps * 5 ^ (n + 1) := mul_le_mul_of_nonneg_left (coefficient_sum_le_pow5 _) heps
    _ = _ := mul_comm _ _

/-- No small gradient is possible on the terminal-zero hyperplane when
the endpoint forcing exceeds this explicit horizon-dependent threshold. -/
theorem gradient_large_of_terminal_zero {n : ℕ} {c eps : ℝ}
    (heps : 0 ≤ eps) (hc : 5 ^ (n + 1) * eps < c)
    (y : EVec (n + 1)) (htail : y (Fin.last n) = 0) :
    eps ^ 2 < vecSq (gradient n c y) := by
  by_contra h
  exact (not_le.mpr hc) (forcing_le_of_terminal_zero heps y htail (le_of_not_gt h))

theorem normal_univ_eq_zero {d : ℕ} {x b : EVec d}
    (hb : RelativeFOAM.IsEuclideanNormal Set.univ x b) : b = 0 := by
  have ht := hb (x + b) (Set.mem_univ _)
  have hs : vecSq b ≤ 0 := by
    simpa only [vecSq, NCPLVerification.vecSq, Pi.add_apply, add_sub_cancel_left, pow_two] using ht
  exact (ProjectionGeometry.vecSq_eq_zero_iff b).1 (le_antisymm hs (vecSq_nonneg b))

theorem fullSpace_GS_gradient_bound {n : ℕ} {c eps : ℝ}
    {x : EVec 1} {y : EVec (n + 1)} (h : IsGS (family n c) eps x y) :
    vecSq (gradient n c y) ≤ eps ^ 2 := by
  have hr : normalResidualSet Set.univ y (-gradient n c y) =
      {(WithLp.toLp 2 (-gradient n c y) : EuclideanSpace ℝ (Fin (n + 1)))} := by
    ext w
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [normal_univ_eq_zero hb]
      simp
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      subst w
      refine ⟨0, ?_, by simp⟩
      intro z _
      simp
  have hb := h.2.2.2.2
  change Metric.infDist 0 (normalResidualSet Set.univ y (-gradient n c y)) ≤ eps at hb
  rw [hr, Metric.infDist_singleton, dist_zero_left] at hb
  have hn : ‖(WithLp.toLp 2 (-gradient n c y) : EuclideanSpace ℝ (Fin (n + 1)))‖ ^ 2 =
      vecSq (gradient n c y) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [vecSq, NCPLVerification.vecSq]
  nlinarith [norm_nonneg (WithLp.toLp 2 (-gradient n c y) : EuclideanSpace ℝ (Fin (n + 1))), h.1]

theorem not_GS_of_terminal_zero {n : ℕ} {c eps : ℝ}
    (heps : 0 ≤ eps) (hc : 5 ^ (n + 1) * eps < c)
    (x : EVec 1) (y : EVec (n + 1)) (htail : y (Fin.last n) = 0) :
    ¬ IsGS (family n c) eps x y := by
  intro h
  exact (not_le.mpr (gradient_large_of_terminal_zero heps hc y htail))
    (fullSpace_GS_gradient_bound h)

theorem gradient_zeroChain (n : ℕ) (c : ℝ) :
    NCPLVerification.IsFirstOrderZeroChain (gradient n c) := by
  intro k y hy i hi
  exact gradient_zero_of_zero_tail c y hy i hi

/-- Actual joint zero-respecting oracle histories yield zero-respecting
dual histories. Primal coordinates cannot create new dual support. -/
theorem queriedDual_zeroRespecting {n : ℕ} (c : ℝ)
    (A : Oracle.DeterministicFOComponent (Set.univ : Set (EVec 1))
      (Set.univ : Set (EVec (n + 1))))
    (hA : A.IsZeroRespectingOn (family n c)) :
    NCPLVerification.QueriesAreZeroRespecting (gradient n c)
      (fun t => (A.queriedAt (family n c) t).2) := by
  intro t i hi
  have hi' : Oracle.standardJointQuery (A.queriedAt (family n c) t) (Fin.natAdd 1 i) ≠ 0 := by
    simpa [Oracle.standardJointQuery, Oracle.standardJointVector] using hi
  obtain ⟨s, hst, hs⟩ := hA t (Fin.natAdd 1 i) hi'
  refine ⟨s, hst, ?_⟩
  rw [Oracle.standardSaddleField_standardJointQuery] at hs
  simpa [Oracle.standardJointVector, family] using hs

theorem queried_terminal_zero {n : ℕ} (c : ℝ)
    (A : Oracle.DeterministicFOComponent (Set.univ : Set (EVec 1))
      (Set.univ : Set (EVec (n + 1))))
    (hA : A.IsZeroRespectingOn (family n c)) {t : ℕ} (ht : t < n + 1) :
    (A.queriedAt (family n c) t).2 (Fin.last n) = 0 :=
  NCPLVerification.sequential_query_discovery (gradient_zeroChain n c)
    (queriedDual_zeroRespecting c A hA) t (Fin.last n) (by simp; omega)

/-- For every prescribed finite horizon and positive tolerance there is
one fixed-conditioned, zero-primal-gap instance defeating all zero-respecting
deterministic queried histories through that horizon. This is a GS, not an
OS, obstruction; the primal value is constant. -/
theorem fixed_conditioned_GS_obstruction (n : ℕ) {eps : ℝ} (heps : 0 < eps) :
    ∃ c : ℝ,
      NCSC.NCSCClass 5 1 1 (family n c) ∧
      ValueOn Set.univ (objective n c) 0 -
        sInf (Set.range (ValueOn Set.univ (objective n c))) = 0 ∧
      ∀ A : Oracle.DeterministicFOComponent (Set.univ : Set (EVec 1))
          (Set.univ : Set (EVec (n + 1))),
        A.IsZeroRespectingOn (family n c) →
        ∀ t < n + 1, ¬ IsGS (family n c) eps
          (A.queriedAt (family n c) t).1 (A.queriedAt (family n c) t).2 := by
  let c := (5 ^ (n + 1) + 1) * eps
  have hc : 5 ^ (n + 1) * eps < c := by dsimp [c]; nlinarith
  refine ⟨c, withinClass n c, initial_value_gap_zero n c, ?_⟩
  intro A hA t ht
  exact not_GS_of_terminal_zero heps.le hc _ _ (queried_terminal_zero c A hA ht)

end

end NCC.Extensions.NCSCZeroChainObstruction
