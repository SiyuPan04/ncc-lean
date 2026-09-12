import NCCLowerBoundVerification.NeighborhoodExtension
import NCCLowerBoundVerification.Oracle.Model
import NCPLVerification.InnerDifferentiability

/-!
# The paper's neighborhood-`C^1` function class

Definition 2.1 only asks that the objective on the closed set `X × Y` be the
restriction of a continuously differentiable function on an open
neighborhood.  The analytic development in `Basic` uses a global ambient
representative.  This file proves that the paper formulation can be
globalized without changing any feasible value or first-order oracle reply.
-/

namespace NCCLowerBoundVerification

noncomputable section

open Set Function

/-- The gradient fields are the derivatives of a `C^1` representative on an
open neighborhood of the feasible product set. -/
def RepresentsJointGradientNear {m n : Nat} (P : NCCInstance m n) : Prop :=
  ∃ U : Set (EVec m × EVec n),
    IsOpen U ∧
      P.X ×ˢ P.Y ⊆ U ∧
      ContDiffOn ℝ 1 (Function.uncurry P.f) U ∧
      ∀ x ∈ P.X, ∀ y ∈ P.Y, ∀ hx hy,
        fderiv ℝ (Function.uncurry P.f) (x, y) (hx, hy) =
          (∑ i : Fin m, P.gradX x y i * hx i) +
            ∑ j : Fin n, P.gradY x y j * hy j

/-- Definition 2.1 with its literal neighborhood-`C^1` convention. -/
structure IsPaperNCCClass {m n : Nat} (ell D Delta : ℝ)
    (P : NCCInstance m n) : Prop where
  ell_pos : 0 < ell
  D_pos : 0 < D
  Delta_pos : 0 < Delta
  x0_mem : P.x0 ∈ P.X
  X_nonempty : P.X.Nonempty
  X_closed : IsClosed P.X
  X_convex : Convex ℝ P.X
  Y_nonempty : P.Y.Nonempty
  Y_closed : IsClosed P.Y
  Y_convex : Convex ℝ P.Y
  gradient_representation : RepresentsJointGradientNear P
  jointly_smooth : ∀ x ∈ P.X, ∀ y ∈ P.Y,
    ∀ x' ∈ P.X, ∀ y' ∈ P.Y,
      jointSq (P.gradX x y - P.gradX x' y')
          (P.gradY x y - P.gradY x' y') ≤
        ell ^ 2 * jointSq (x - x') (y - y')
  dual_concave : ∀ x ∈ P.X, ConcaveOn ℝ P.Y (P.f x)
  maximum_attained : ∀ x ∈ P.X, ∃ y, IsMaximizerOn P.Y P.f x y
  value_bddBelow : BddBelow (ValueOn P.Y P.f '' P.X)
  initial_gap :
    ValueOn P.Y P.f P.x0 - sInf (ValueOn P.Y P.f '' P.X) ≤ Delta
  dual_diameter : ∀ y ∈ P.Y, ∀ y' ∈ P.Y, vecSq (y - y') ≤ D ^ 2

/-- A globally `C^1` member of the analytic class is, in particular, a
literal member of the paper's neighborhood class. -/
theorem IsNCCClass.toPaper {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (hC1 : ContDiff ℝ 1 (Function.uncurry P.f)) :
    IsPaperNCCClass ell D Delta P := by
  refine
    { ell_pos := hP.ell_pos
      D_pos := hP.D_pos
      Delta_pos := hP.Delta_pos
      x0_mem := hP.x0_mem
      X_nonempty := hP.X_nonempty
      X_closed := hP.X_closed
      X_convex := hP.X_convex
      Y_nonempty := hP.Y_nonempty
      Y_closed := hP.Y_closed
      Y_convex := hP.Y_convex
      gradient_representation := ?_
      jointly_smooth := hP.jointly_smooth
      dual_concave := hP.dual_concave
      maximum_attained := hP.maximum_attained
      value_bddBelow := hP.value_bddBelow
      initial_gap := hP.initial_gap
      dual_diameter := hP.dual_diameter }
  refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, hC1.contDiffOn, ?_⟩
  intro x _ y _ hx hy
  exact hP.gradient_representation.2 x y hx hy

/-- In finite dimensions, a represented derivative with continuous primal
and dual gradient fields is continuously differentiable.  This is the form
used to certify the explicit lower-bound objective. -/
theorem contDiff_one_of_representsJointGradient {m n : Nat}
    {F : EVec m → EVec n → ℝ}
    {gradX : EVec m → EVec n → EVec m}
    {gradY : EVec m → EVec n → EVec n}
    (hrep : NCPLVerification.RepresentsJointGradient F gradX gradY)
    (hgradX : Continuous (Function.uncurry gradX))
    (hgradY : Continuous (Function.uncurry gradY)) :
    ContDiff ℝ 1 (Function.uncurry F) := by
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by rfl,
    contDiff_succ_iff_fderiv_apply]
  refine ⟨hrep.1, ?_, ?_⟩
  · intro hzero
    simp at hzero
  · rintro ⟨hx, hy⟩
    rw [contDiff_zero]
    have heq :
        (fun z : EVec m × EVec n =>
          fderiv ℝ (Function.uncurry F) z (hx, hy)) =
        (fun z =>
          (∑ i : Fin m, gradX z.1 z.2 i * hx i) +
            ∑ j : Fin n, gradY z.1 z.2 j * hy j) := by
      funext z
      exact hrep.2 z.1 z.2 hx hy
    rw [heq]
    apply Continuous.add
    · apply continuous_finsetSum
      intro i _
      exact ((continuous_apply i).comp hgradX).mul continuous_const
    · apply continuous_finsetSum
      intro j _
      exact ((continuous_apply j).comp hgradY).mul continuous_const

/-- The primal coordinates of the derivative of a global representative. -/
def ambientGradX {m n : Nat} (H : EVec m × EVec n → ℝ)
    (x : EVec m) (y : EVec n) : EVec m :=
  fun i => fderiv ℝ H (x, y) (NCPLVerification.evecBasis i, 0)

/-- The dual coordinates of the derivative of a global representative. -/
def ambientGradY {m n : Nat} (H : EVec m × EVec n → ℝ)
    (x : EVec m) (y : EVec n) : EVec n :=
  fun j => fderiv ℝ H (x, y) (0, NCPLVerification.evecBasis j)

private theorem pair_eq_sum_primal_basis {m n : Nat}
    (hx : EVec m) :
    (hx, (0 : EVec n)) =
      ∑ i : Fin m, hx i • (NCPLVerification.evecBasis i, (0 : EVec n)) := by
  ext k
  · simp [Prod.fst_sum, NCPLVerification.evecBasis]
  · simp [Prod.snd_sum]

private theorem pair_eq_sum_dual_basis {m n : Nat}
    (hy : EVec n) :
    ((0 : EVec m), hy) =
      ∑ j : Fin n, hy j • ((0 : EVec m), NCPLVerification.evecBasis j) := by
  ext k
  · simp [Prod.fst_sum]
  · simp [Prod.snd_sum, NCPLVerification.evecBasis]

/-- Coordinate extraction from the Fréchet derivative really represents the
whole joint derivative, not merely its values on basis vectors. -/
theorem representsJointGradient_ambient {m n : Nat}
    (H : EVec m × EVec n → ℝ) (hH : Differentiable ℝ H) :
    NCPLVerification.RepresentsJointGradient (Function.curry H)
      (ambientGradX H) (ambientGradY H) := by
  constructor
  · simpa only [Function.uncurry_curry] using hH
  · intro x y hx hy
    let L := fderiv ℝ H (x, y)
    have hsplit : (hx, hy) = (hx, (0 : EVec n)) + ((0 : EVec m), hy) := by
      ext <;> simp
    change L (hx, hy) =
      (∑ i : Fin m, ambientGradX H x y i * hx i) +
        ∑ j : Fin n, ambientGradY H x y j * hy j
    rw [hsplit, map_add]
    congr 1
    · rw [pair_eq_sum_primal_basis hx, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [ambientGradX]
      change L (hx i • (NCPLVerification.evecBasis i, (0 : EVec n))) =
        L (NCPLVerification.evecBasis i, (0 : EVec n)) * hx i
      rw [map_smul]
      exact mul_comm _ _
    · rw [pair_eq_sum_dual_basis hy, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [ambientGradY]
      change L (hy j • ((0 : EVec m), NCPLVerification.evecBasis j)) =
        L ((0 : EVec m), NCPLVerification.evecBasis j) * hy j
      rw [map_smul]
      exact mul_comm _ _

variable {m n : Nat} {ell D Delta : ℝ} {P : NCCInstance m n}

private theorem ambientGradX_eq_of_near
    (G : GlobalC1Extension (P.X ×ˢ P.Y) (Function.uncurry P.f))
    (hformula : ∀ x ∈ P.X, ∀ y ∈ P.Y, ∀ hx hy,
      fderiv ℝ (Function.uncurry P.f) (x, y) (hx, hy) =
        (∑ i : Fin m, P.gradX x y i * hx i) +
          ∑ j : Fin n, P.gradY x y j * hy j)
    {x : EVec m} (hx : x ∈ P.X) {y : EVec n} (hy : y ∈ P.Y) :
    ambientGradX G.toFun x y = P.gradX x y := by
  funext i
  unfold ambientGradX
  rw [(G.eventuallyEq (x, y) ⟨hx, hy⟩).fderiv_eq]
  rw [hformula x hx y hy (NCPLVerification.evecBasis i) 0]
  simp [NCPLVerification.evecBasis]

private theorem ambientGradY_eq_of_near
    (G : GlobalC1Extension (P.X ×ˢ P.Y) (Function.uncurry P.f))
    (hformula : ∀ x ∈ P.X, ∀ y ∈ P.Y, ∀ hx hy,
      fderiv ℝ (Function.uncurry P.f) (x, y) (hx, hy) =
        (∑ i : Fin m, P.gradX x y i * hx i) +
          ∑ j : Fin n, P.gradY x y j * hy j)
    {x : EVec m} (hx : x ∈ P.X) {y : EVec n} (hy : y ∈ P.Y) :
    ambientGradY G.toFun x y = P.gradY x y := by
  funext j
  unfold ambientGradY
  rw [(G.eventuallyEq (x, y) ⟨hx, hy⟩).fderiv_eq]
  rw [hformula x hx y hy 0 (NCPLVerification.evecBasis j)]
  simp [NCPLVerification.evecBasis]

/-- A globalized instance together with the exact observational equivalence
needed by the shared local-oracle model. -/
structure PaperGlobalization (ell D Delta : ℝ) (P : NCCInstance m n) where
  globalized : NCCInstance m n
  class_mem : IsNCCClass ell D Delta globalized
  X_eq : globalized.X = P.X
  Y_eq : globalized.Y = P.Y
  x0_eq : globalized.x0 = P.x0
  oracle_eq_on : ∀ x ∈ P.X, ∀ y ∈ P.Y,
    Oracle.firstOrderOracle globalized (x, y) = Oracle.firstOrderOracle P (x, y)
  value_eq_on : EqOn (ValueOn globalized.Y globalized.f) (ValueOn P.Y P.f) P.X

/-- Every literal paper-class instance has a global representative in the
analytic class, with identical values, gradients, oracle replies and value
function on the feasible domains. -/
theorem exists_paperGlobalization
    (hP : IsPaperNCCClass ell D Delta P) :
    Nonempty (PaperGlobalization ell D Delta P) := by
  obtain ⟨U, hUopen, hprodU, hC1, hformula⟩ := hP.gradient_representation
  obtain ⟨G⟩ := exists_globalC1Extension (hP.X_closed.prod hP.Y_closed)
    hUopen hprodU hC1
  let Q : NCCInstance m n :=
    { X := P.X
      Y := P.Y
      f := Function.curry G.toFun
      gradX := ambientGradX G.toFun
      gradY := ambientGradY G.toFun
      x0 := P.x0 }
  have hfun : ∀ x ∈ P.X, ∀ y ∈ P.Y,
      Function.curry G.toFun x y = P.f x y := by
    intro x hx y hy
    exact G.eqOn ⟨hx, hy⟩
  have hvalue : ∀ x ∈ P.X,
      ValueOn P.Y (Function.curry G.toFun) x = ValueOn P.Y P.f x := by
    intro x hx
    obtain ⟨y, hy⟩ := hP.maximum_attained x hx
    have hyG : IsMaximizerOn P.Y (Function.curry G.toFun) x y := by
      refine ⟨hy.1, ?_⟩
      intro v hv
      rw [hfun x hx v hv, hfun x hx y hy.1]
      exact hy.2 v hv
    calc
      ValueOn P.Y (Function.curry G.toFun) x =
          Function.curry G.toFun x y := value_eq_of_isMaximizerOn hyG
      _ = P.f x y := hfun x hx y hy.1
      _ = ValueOn P.Y P.f x := (value_eq_of_isMaximizerOn hy).symm
  have himage :
      ValueOn P.Y (Function.curry G.toFun) '' P.X =
        ValueOn P.Y P.f '' P.X :=
    Set.image_congr hvalue
  have hQclass : IsNCCClass ell D Delta Q := by
    refine
      { ell_pos := hP.ell_pos
        D_pos := hP.D_pos
        Delta_pos := hP.Delta_pos
        x0_mem := hP.x0_mem
        X_nonempty := hP.X_nonempty
        X_closed := hP.X_closed
        X_convex := hP.X_convex
        Y_nonempty := hP.Y_nonempty
        Y_closed := hP.Y_closed
        Y_convex := hP.Y_convex
        gradient_representation := ?_
        jointly_smooth := ?_
        dual_concave := ?_
        maximum_attained := ?_
        value_bddBelow := ?_
        initial_gap := ?_
        dual_diameter := hP.dual_diameter }
    · exact representsJointGradient_ambient G.toFun
        (G.contDiff.differentiable (by norm_num))
    · intro x hx y hy x' hx' y' hy'
      change x ∈ P.X at hx
      change y ∈ P.Y at hy
      change x' ∈ P.X at hx'
      change y' ∈ P.Y at hy'
      change jointSq
          (ambientGradX G.toFun x y - ambientGradX G.toFun x' y')
          (ambientGradY G.toFun x y - ambientGradY G.toFun x' y') ≤ _
      rw [ambientGradX_eq_of_near G hformula hx hy,
        ambientGradX_eq_of_near G hformula hx' hy',
        ambientGradY_eq_of_near G hformula hx hy,
        ambientGradY_eq_of_near G hformula hx' hy']
      exact hP.jointly_smooth x hx y hy x' hx' y' hy'
    · intro x hx
      change x ∈ P.X at hx
      apply (hP.dual_concave x hx).congr
      intro y hy
      exact (hfun x hx y hy).symm
    · intro x hx
      change x ∈ P.X at hx
      obtain ⟨y, hy⟩ := hP.maximum_attained x hx
      change ∃ y, IsMaximizerOn P.Y (Function.curry G.toFun) x y
      refine ⟨y, hy.1, ?_⟩
      intro v hv
      rw [hfun x hx v hv, hfun x hx y hy.1]
      exact hy.2 v hv
    · rw [himage]
      exact hP.value_bddBelow
    · change ValueOn P.Y (Function.curry G.toFun) P.x0 -
          sInf (ValueOn P.Y (Function.curry G.toFun) '' P.X) ≤ Delta
      rw [hvalue P.x0 hP.x0_mem, himage]
      exact hP.initial_gap
  refine ⟨{
    globalized := Q
    class_mem := hQclass
    X_eq := rfl
    Y_eq := rfl
    x0_eq := rfl
    oracle_eq_on := ?_
    value_eq_on := hvalue }⟩
  intro x hx y hy
  unfold Oracle.firstOrderOracle
  dsimp [Q]
  rw [G.eqOn ⟨hx, hy⟩,
    ambientGradX_eq_of_near G hformula hx hy,
    ambientGradY_eq_of_near G hformula hx hy]
  rfl

/-- Proximal points only inspect objective values on the feasible primal set. -/
theorem isProxPoint_congr {phi psi : EVec m → ℝ} {X : Set (EVec m)}
    (h : EqOn phi psi X) {ell : ℝ} {x u : EVec m} :
    IsProxPoint X phi ell x u ↔ IsProxPoint X psi ell x u := by
  constructor
  · rintro ⟨hu, hmin⟩
    refine ⟨hu, ?_⟩
    intro v hv
    simpa only [h hu, h hv] using hmin v hv
  · rintro ⟨hu, hmin⟩
    refine ⟨hu, ?_⟩
    intro v hv
    simpa only [h hu, h hv] using hmin v hv

/-- Optimization stationarity is unchanged by pointwise equality on `X`. -/
theorem isOptimizationStationary_congr {phi psi : EVec m → ℝ}
    {X : Set (EVec m)} (h : EqOn phi psi X) {ell eps : ℝ} {x : EVec m} :
    IsOptimizationStationary X phi ell eps x ↔
      IsOptimizationStationary X psi ell eps x := by
  unfold IsOptimizationStationary
  constructor
  · rintro ⟨u, hu, hdist⟩
    exact ⟨u, (isProxPoint_congr h).mp hu, hdist⟩
  · rintro ⟨u, hu, hdist⟩
    exact ⟨u, (isProxPoint_congr h).mpr hu, hdist⟩

namespace Oracle.DeterministicFOComponent

/-- Two objectives with the same feasible oracle replies generate exactly the
same causal query transcript. -/
theorem queriedAt_eq_of_oracle_eq_on
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (A : DeterministicFOComponent X Y) (P Q : NCCInstance m n)
    (horacle : ∀ x ∈ X, ∀ y ∈ Y,
      Oracle.firstOrderOracle P (x, y) = Oracle.firstOrderOracle Q (x, y)) :
    ∀ t, queriedAt A P t = queriedAt A Q t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      rw [queriedAt_eq_nextQuery, queriedAt_eq_nextQuery]
      congr 1
      funext i
      change Oracle.firstOrderOracle P (queriedAt A P i) =
        Oracle.firstOrderOracle Q (queriedAt A Q i)
      calc
        Oracle.firstOrderOracle P (queriedAt A P i) =
            Oracle.firstOrderOracle Q (queriedAt A P i) := by
          exact horacle _ (queriedAt_mem A P i).1 _ (queriedAt_mem A P i).2
        _ = Oracle.firstOrderOracle Q (queriedAt A Q i) := by
          rw [ih i i.isLt]

end Oracle.DeterministicFOComponent

end

end NCCLowerBoundVerification
