import NCC.Lower.ZeroRespecting
import NCCLowerBoundVerification.Lower.TaggedResisting
import NCCLowerBoundVerification.Lower.TerminalConcrete

/-!
# Exact coordinate-permutation source for the tagged resisting oracle

The current objective has public primal blocks `(s,a,b)`. The generic
tagged resisting construction uses public blocks `(a,b,s)`. Here a fixed
orthogonal permutation, not a mere dimension cast, translates the actual
current scaled objective and both actual gradient fields into that layout.
The discovery order remains `(a,y_0,...,y_{n-1},b,s)` throughout.
-/

namespace NCC.Lower.TaggedSource

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open NCCLowerBoundVerification
open NCPLVerification (IsOrthonormalFrame evecBasis evecDotValue frameProject frameEmbed
  frameProject_frameEmbed frameEmbed_neg IsFirstOrderZeroChain rotatedF rotatedGradX rotatedGradY)
open NCC.Construction Composite
open Certificates Parameters MoreauObstruction

def permutationFrame {d D : ℕ} (e : Fin d ≃ Fin D) : Fin d → EVec D :=
  fun i => evecBasis (e i)

theorem permutationFrame_orthonormal {d D : ℕ} (e : Fin d ≃ Fin D) :
    IsOrthonormalFrame (permutationFrame e) := by
  intro i j
  simp [permutationFrame, evecDotValue, evecBasis, e.injective.eq_iff, eq_comm]

@[simp] theorem permutation_project {d D : ℕ} (e : Fin d ≃ Fin D)
    (x : EVec D) (i : Fin d) : frameProject (permutationFrame e) x i = x (e i) := by
  simp [frameProject, permutationFrame, evecDotValue, evecBasis]

@[simp] theorem permutation_embed {d D : ℕ} (e : Fin d ≃ Fin D)
    (x : EVec d) (i : Fin d) : frameEmbed (permutationFrame e) x (e i) = x i := by
  simp [frameEmbed, permutationFrame, evecBasis, e.injective.eq_iff]

/-- Current positions `s,a,b` map to old positions `2,0,1`. -/
def slotPermutation : Fin 3 ≃ Fin 3 :=
  (Equiv.swap 0 2).trans (Equiv.swap 0 1)

@[simp] theorem slotPermutation_state : slotPermutation 0 = 2 := by decide
@[simp] theorem slotPermutation_entrance : slotPermutation 1 = 0 := by decide
@[simp] theorem slotPermutation_exit : slotPermutation 2 = 1 := by decide

def primalPermutation (m : ℕ) : Fin (m * 3) ≃ Fin (3 * m) :=
  ((finProdFinEquiv.symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin m)) slotPermutation)).trans finProdFinEquiv).trans
      (finCongr (Nat.mul_comm m 3))

def dualPermutation (m n : ℕ) : Fin (m * n) ≃ Fin (n * m) :=
  finCongr (Nat.mul_comm m n)

def primalFrame (m : ℕ) : Fin (m * 3) → EVec (3 * m) :=
  permutationFrame (primalPermutation m)

def dualFrame (m n : ℕ) : Fin (m * n) → EVec (n * m) :=
  permutationFrame (dualPermutation m n)

theorem primalFrame_orthonormal (m : ℕ) : IsOrthonormalFrame (primalFrame m) :=
  permutationFrame_orthonormal _

theorem dualFrame_orthonormal (m n : ℕ) : IsOrthonormalFrame (dualFrame m n) :=
  permutationFrame_orthonormal _

@[simp] theorem primalPermutation_state {m : ℕ} (i : Fin m) :
    primalPermutation m (finProdFinEquiv (i, (0 : Fin 3))) =
      primalStateIndex (T := m + 1) i := by
  simp only [primalPermutation, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.prodCongr_apply]
  apply Fin.ext
  simp [primalStateIndex, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

@[simp] theorem primalPermutation_entrance {m : ℕ} (i : Fin m) :
    primalPermutation m (finProdFinEquiv (i, (1 : Fin 3))) =
      primalAIndex (T := m + 1) i := by
  simp only [primalPermutation, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.prodCongr_apply]
  apply Fin.ext
  simp [primalAIndex, finProdFinEquiv, Nat.mul_comm]

@[simp] theorem primalPermutation_exit {m : ℕ} (i : Fin m) :
    primalPermutation m (finProdFinEquiv (i, (2 : Fin 3))) =
      primalBIndex (T := m + 1) i := by
  simp only [primalPermutation, Equiv.trans_apply, Equiv.symm_apply_apply,
    Equiv.prodCongr_apply]
  apply Fin.ext
  simp [primalBIndex, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]

@[simp] theorem dualPermutation_block {m n : ℕ} (i : Fin m) (k : Fin n) :
    dualPermutation m n (finProdFinEquiv (i, k)) = dualBlockIndex (T := m + 1) i k := by
  apply Fin.ext
  simp [dualPermutation, dualBlockIndex, finProdFinEquiv, Nat.add_comm]

@[simp] theorem project_state {m : ℕ} (x : EVec (3 * m)) (i : Fin m) :
    state (frameProject (primalFrame m) x) i = primalState (T := m + 1) x i := by
  simp [state, primalFrame, primalState]

@[simp] theorem project_entrance {m : ℕ} (x : EVec (3 * m)) (i : Fin m) :
    entrance (frameProject (primalFrame m) x) i = primalA (T := m + 1) x i := by
  simp [entrance, primalFrame, primalA]

@[simp] theorem project_exit {m : ℕ} (x : EVec (3 * m)) (i : Fin m) :
    exit (frameProject (primalFrame m) x) i = primalB (T := m + 1) x i := by
  simp [exit, primalFrame, primalB]

@[simp] theorem project_dual {m n : ℕ} (y : EVec (n * m)) (i : Fin m) (k : Fin n) :
    frameProject (dualFrame m n) y (finProdFinEquiv (i, k)) =
      dualBlock (T := m + 1) y i k := by
  simp [dualFrame, dualBlock]

theorem serialize_project {m n : ℕ} (x : EVec (3 * m)) (y : EVec (n * m)) :
    serializeUnscaled (T := m + 1) (n := n) x y =
      Serialization.serialize (frameProject (primalFrame m) x) (frameProject (dualFrame m n) y) := by
  funext j
  rcases Serialization.index_cases (m := m) (n := n) j with
    ⟨i, rfl⟩ | ⟨i, k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · change serializedA (serializeUnscaled (T := m + 1) (n := n) x y) i = _
    rw [serializedA_serializeUnscaled, Serialization.serialize_a, project_entrance]
  · change serializedY (serializeUnscaled (T := m + 1) (n := n) x y) i k = _
    rw [serializedY_serializeUnscaled, Serialization.serialize_y, project_dual]
  · change serializedB (serializeUnscaled (T := m + 1) (n := n) x y) i = _
    rw [serializedB_serializeUnscaled, Serialization.serialize_b, project_exit]
  · change serializedState (serializeUnscaled (T := m + 1) (n := n) x y) i = _
    rw [serializedState_serializeUnscaled, Serialization.serialize_s, project_state]

@[simp] theorem project_unserializePrimal {m n : ℕ} (q : Serialization.Chain m n) :
    frameProject (primalFrame m) (unserializePrimal (T := m + 1) q) =
      Serialization.decodePrimal q := by
  have h := congrArg (Serialization.decodePrimal (m := m) (n := n))
    (serialize_project (m := m) (n := n)
      (unserializePrimal (T := m + 1) q) (unserializeDual (T := m + 1) q))
  simpa using h.symm

@[simp] theorem project_unserializeDual {m n : ℕ} (q : Serialization.Chain m n) :
    frameProject (dualFrame m n) (unserializeDual (T := m + 1) q) =
      Serialization.decodeDual q := by
  have h := congrArg (Serialization.decodeDual (m := m) (n := n))
    (serialize_project (m := m) (n := n)
      (unserializePrimal (T := m + 1) q) (unserializeDual (T := m + 1) q))
  simpa using h.symm

@[simp] theorem serialize_embed {m n : ℕ} (x : EVec (m * 3)) (y : EVec (m * n)) :
    serializeUnscaled (T := m + 1) (n := n)
        (frameEmbed (primalFrame m) x) (frameEmbed (dualFrame m n) y) =
      Serialization.serialize x y := by
  rw [serialize_project (m := m) (n := n), frameProject_frameEmbed (primalFrame_orthonormal m),
    frameProject_frameEmbed (dualFrame_orthonormal m n)]

/-- The source is the actual scaled current objective in the tagged layout. -/
def source {m n : ℕ} (hn : 0 < n) (ell D eps : ℝ) : NCCInstance (3 * m) (n * m) :=
  rotatedNCCInstance D (primalFrame m) (dualFrame m n)
    (ScaledMembership.scaled hn ell D eps)

@[simp] theorem primal_domain {m n : ℕ} (hn : 0 < n) (ell D eps : ℝ) :
    (source (m := m) hn ell D eps).X = Set.univ := rfl

@[simp] theorem dual_domain {m n : ℕ} (hn : 0 < n) (ell D eps : ℝ) :
    (source (m := m) hn ell D eps).Y = diameterBall (n * m) D := rfl

@[simp] theorem initialization {m n : ℕ} (hn : 0 < n) (ell D eps : ℝ) :
    (source (m := m) hn ell D eps).x0 = 0 := rfl

theorem analyticClass {m n : ℕ} (hm : 0 < m) (hn : 10 ≤ n)
    {ell D Delta eps : ℝ} (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hgap : amplitude constants ell eps * (Composite.c_Δ * (m : ℝ)) ≤ Delta) :
    IsNCCClass ell D Delta (source (m := m) (by omega : 0 < n) ell D eps) := by
  exact (ScaledMembership.analyticClass hm hn hell hD hDelta heps hgap).rotate_symmetric
    (ScaledMembership.primal_domain _ ell D eps) (ScaledMembership.dual_domain _ hell heps)
    (ScaledMembership.initialization _ ell D eps)
    (primalFrame_orthonormal m) (dualFrame_orthonormal m n)

theorem withinClass {m n : ℕ} (hm : 0 < m) (hn : 10 ≤ n)
    {ell D Delta eps : ℝ} (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hgap : amplitude constants ell eps * (Composite.c_Δ * (m : ℝ)) ≤ Delta) :
    Model.WithinClass ell D Delta (source (m := m) (by omega : 0 < n) ell D eps) := by
  apply Model.withinClass_of_analytic (analyticClass hm hn hell hD hDelta heps hgap)
  · exact Set.mem_univ _
  · exact zero_mem_diameterBall _ _ hD.le
  · rfl

theorem tagged_field_eq {m n : ℕ} (hn : 0 < n) (ell D eps : ℝ) :
    taggedSerializedSaddleFieldOf (T := m + 1) (n := n)
        (source (m := m) hn ell D eps).gradX (source (m := m) hn ell D eps).gradY =
      Serialization.fieldOf (ScaledMembership.scaled (m := m) hn ell D eps).gradX
        (ScaledMembership.scaled (m := m) hn ell D eps).gradY := by
  funext q
  simp only [taggedSerializedSaddleFieldOf, source, rotatedNCCInstance,
    rotatedGradX, rotatedGradY]
  rw [← frameEmbed_neg, serialize_embed (m := m) (n := n),
    project_unserializePrimal (m := m), project_unserializeDual (m := m)]
  rfl

theorem source_zeroChain {m n : ℕ} (hn : 0 < n) (ell D eps : ℝ) :
    IsFirstOrderZeroChain (taggedSerializedSaddleFieldOf (T := m + 1) (n := n)
      (source (m := m) hn ell D eps).gradX (source (m := m) hn ell D eps).gradY) := by
  rw [tagged_field_eq]
  exact ZeroRespecting.actual_scaled_field_zeroChain hn ell D eps

theorem scaled_maximum_attained {m n : ℕ} (hn : 0 < n)
    {ell D eps : ℝ} (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps)
    (x : EVec (m * 3)) :
    ∃ y, IsMaximizerOn (ScaledMembership.scaled (m := m) hn ell D eps).Y
      (ScaledMembership.scaled (m := m) hn ell D eps).f x y := by
  have hlam := scale_pos constants hell heps
  have hamp := amplitude_pos constants hell heps
  have hDs := div_pos hD hlam
  exact ⟨_, scaledObjective_maximizer hlam.ne' hamp.le
    (Composite.maximizer_spec hn (D / scale constants ell eps) hDs.le
      (unscaleCoords (scale constants ell eps) x))⟩

theorem value_covariance {m n : ℕ} (hn : 0 < n)
    {ell D eps : ℝ} (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps)
    (x : EVec (3 * m)) :
    ValueOn (source (m := m) hn ell D eps).Y (source (m := m) hn ell D eps).f x =
      ValueOn (ScaledMembership.scaled (m := m) hn ell D eps).Y
        (ScaledMembership.scaled (m := m) hn ell D eps).f (frameProject (primalFrame m) x) := by
  exact rotatedValue_eq (dualFrame_orthonormal m n)
    (ScaledMembership.dual_domain hn hell heps) (scaled_maximum_attained hn hell hD heps) x

theorem project_terminal {m : ℕ} (hm : 0 < m) (x : EVec (3 * m)) :
    frameProject (primalFrame m) x (terminalIndex hm) =
      x (terminalPrimalIndex (T := m + 1) (by omega)) := by
  change state (frameProject (primalFrame m) x) ⟨m - 1, by omega⟩ = _
  rw [project_state]
  unfold primalState terminalPrimalIndex
  congr 2

/-- Terminal OS failure for the genuine permuted, scaled current value. -/
theorem source_not_OS_terminal {m n : ℕ} (hm : 0 < m) (hn : 10 ≤ n)
    {ell D eps : ℝ} (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps)
    (hsize : (n : ℝ) ≤ constants.cD * (D / scale constants ell eps))
    {x : EVec (3 * m)}
    (hx : x (terminalPrimalIndex (T := m + 1) (by omega)) = 0) :
    ¬ IsOptimizationStationary Set.univ
      (ValueOn (diameterBall (n * m) D) (source (m := m) (by omega : 0 < n) ell D eps).f)
      ell eps x := by
  have hfun : ValueOn (diameterBall (n * m) D)
        (source (m := m) (by omega : 0 < n) ell D eps).f =
      liftedValueFunction (primalFrame m)
        (ValueOn (ScaledMembership.scaled (m := m) (by omega : 0 < n) ell D eps).Y
          (ScaledMembership.scaled (m := m) (by omega : 0 < n) ell D eps).f) := by
    funext z
    exact value_covariance (by omega) hell hD heps z
  rw [hfun]
  intro hos
  have hbase := (optimizationStationarity_lift_iff (primalFrame_orthonormal m) hell.le x).1 hos
  exact ScaledMembership.not_OS_at_terminal_zero hm hn hell hD heps hsize
    (by rw [project_terminal hm]; exact hx) hbase

end

end NCC.Lower.TaggedSource
