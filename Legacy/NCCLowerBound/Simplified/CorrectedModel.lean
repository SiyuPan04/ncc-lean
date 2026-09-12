import NCCLowerBoundVerification.DiameterBall
import NCCLowerBoundVerification.Oracle.Complexity
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
# A type-correct model for the simplified NC--C manuscript

This module isolates the definitions used by the simplified lower-bound
statement and repairs two logical mismatches in the prose model.

* Membership in the NC--C function class does **not** include differentiability
  of the value function.  The old word "admissible" is represented separately
  by `IsOldAdmissible`, so it cannot silently shrink the quantified class.
* A call to the saddle oracle accepts a `FeasibleQuery`.  In particular, its
  dual coordinate carries a proof of membership in the bounded dual domain.

The deterministic algorithm is polymorphic in both finite dimensions.  Its
causality is inherited from the reply-history interface in
`NCCLowerBoundVerification.Oracle.Model`, and its hitting time uses the
Moreau/proximal stationarity predicate, which does not require the value
function itself to be differentiable.
-/

namespace NCCLowerBound
namespace Simplified
namespace CorrectedModel

open NCCLowerBoundVerification

noncomputable section

/-! ## Function class and the corrected admissibility boundary -/

/-- The function class in the simplified manuscript: unrestricted primal
space, diameter-`D` dual ball, origin initialization, and the fully quantified
analytic conditions already verified by `IsNCCClass`.

Crucially, there is no differentiability assumption on `ValueOn P.Y P.f`.
-/
def IsFunctionClass (ell D Delta : ℝ) {m n : Nat}
    (P : NCCInstance m n) : Prop :=
  P.X = Set.univ ∧
    P.Y = diameterBall n D ∧
    P.x0 = 0 ∧
    IsNCCClass ell D Delta P

/-- The extra condition called "admissible" in the original prose.  It is
strictly stronger than function-class membership and is deliberately not an
input to the corrected oracle or hitting-time definitions. -/
def IsOldAdmissible (ell D Delta : ℝ) {m n : Nat}
    (P : NCCInstance m n) : Prop :=
  IsFunctionClass ell D Delta P ∧
    Differentiable ℝ (ValueOn P.Y P.f)

theorem IsOldAdmissible.toFunctionClass {ell D Delta : ℝ} {m n : Nat}
    {P : NCCInstance m n} (hP : IsOldAdmissible ell D Delta P) :
    IsFunctionClass ell D Delta P :=
  hP.1

theorem IsOldAdmissible.value_differentiable {ell D Delta : ℝ}
    {m n : Nat} {P : NCCInstance m n}
    (hP : IsOldAdmissible ell D Delta P) :
    Differentiable ℝ (ValueOn P.Y P.f) :=
  hP.2

/-! ## Feasible first-order saddle oracle -/

/-- A query whose primal and dual coordinates are both feasible for `P`.
Using a subtype here makes an out-of-ball dual oracle call ill-typed. -/
abbrev FeasibleQuery {m n : Nat} (P : NCCInstance m n) :=
  {q : NCCLowerBoundVerification.Oracle.Query m n //
    q.1 ∈ P.X ∧ q.2 ∈ P.Y}

namespace FeasibleQuery

variable {m n : Nat} {P : NCCInstance m n}

theorem primal_mem (q : FeasibleQuery P) : q.1.1 ∈ P.X :=
  q.property.1

theorem dual_mem (q : FeasibleQuery P) : q.1.2 ∈ P.Y :=
  q.property.2

/-- For a member of the simplified class, feasibility explicitly places the
dual coordinate in the prescribed diameter ball. -/
theorem dual_mem_diameterBall {ell D Delta : ℝ}
    (hP : IsFunctionClass ell D Delta P) (q : FeasibleQuery P) :
    q.1.2 ∈ diameterBall n D := by
  rw [← hP.2.1]
  exact q.dual_mem

/-- The common primal--dual origin is a feasible query for every class
member. -/
def origin {ell D Delta : ℝ} (hP : IsFunctionClass ell D Delta P) :
    FeasibleQuery P :=
  ⟨(0, 0), by
    constructor
    · rw [hP.1]
      exact Set.mem_univ 0
    · rw [hP.2.1]
      exact zero_mem_diameterBall n D hP.2.2.2.D_pos.le⟩

end FeasibleQuery

/-- The local value and both partial gradients, callable only at a feasible
point. -/
def feasibleFirstOrderOracle {m n : Nat} (P : NCCInstance m n)
    (q : FeasibleQuery P) :
    NCCLowerBoundVerification.Oracle.OracleReply m n :=
  NCCLowerBoundVerification.Oracle.firstOrderOracle P q.1

@[simp] theorem feasibleFirstOrderOracle_value {m n : Nat}
    (P : NCCInstance m n) (q : FeasibleQuery P) :
    (feasibleFirstOrderOracle P q).value = P.f q.1.1 q.1.2 :=
  rfl

@[simp] theorem feasibleFirstOrderOracle_gradX {m n : Nat}
    (P : NCCInstance m n) (q : FeasibleQuery P) :
    (feasibleFirstOrderOracle P q).gradX = P.gradX q.1.1 q.1.2 :=
  rfl

@[simp] theorem feasibleFirstOrderOracle_gradY {m n : Nat}
    (P : NCCInstance m n) (q : FeasibleQuery P) :
    (feasibleFirstOrderOracle P q).gradY = P.gradY q.1.1 q.1.2 :=
  rfl

/-! ## Dimension-polymorphic deterministic algorithms -/

/-- One deterministic algorithm supplies an objective-independent causal
component in every pair of finite dimensions.  Every counterfactual query of
each component is constrained to `ℝ^m × diameterBall n D`. -/
structure DeterministicAlgorithm (D : ℝ) where
  component : (m n : Nat) →
    NCCLowerBoundVerification.Oracle.DeterministicFOComponent
      (Set.univ : Set (EVec m)) (diameterBall n D)

namespace DeterministicAlgorithm

variable {D : ℝ} (A : DeterministicAlgorithm D)

/-- The recursively generated query against `P`. -/
def queryAt {m n : Nat} (P : NCCInstance m n) (t : Nat) :
    NCCLowerBoundVerification.Oracle.Query m n :=
  NCCLowerBoundVerification.Oracle.DeterministicFOComponent.queriedAt
    (A.component m n) P t

/-- Every generated dual query lies in the bounded domain, not merely in the
ambient Euclidean space. -/
theorem queryAt_mem_modelDomain {m n : Nat} (P : NCCInstance m n)
    (t : Nat) :
    (A.queryAt P t).1 ∈ (Set.univ : Set (EVec m)) ∧
      (A.queryAt P t).2 ∈ diameterBall n D := by
  exact
    NCCLowerBoundVerification.Oracle.DeterministicFOComponent.queriedAt_mem
      (A.component m n) P t

theorem queryAt_dual_mem {m n : Nat} (P : NCCInstance m n)
    (t : Nat) :
    (A.queryAt P t).2 ∈ diameterBall n D :=
  (A.queryAt_mem_modelDomain P t).2

/-- On a member of the function class, model-domain feasibility is exactly
feasibility for the stored instance domains. -/
theorem queryAt_mem_instance {ell Delta : ℝ} {m n : Nat}
    (P : NCCInstance m n) (hP : IsFunctionClass ell D Delta P)
    (t : Nat) :
    (A.queryAt P t).1 ∈ P.X ∧ (A.queryAt P t).2 ∈ P.Y := by
  rw [hP.1, hP.2.1]
  exact A.queryAt_mem_modelDomain P t

/-- The public, proof-carrying form of the algorithm's time-`t` query. -/
def feasibleQueryAt {ell Delta : ℝ} {m n : Nat}
    (P : NCCInstance m n) (hP : IsFunctionClass ell D Delta P)
    (t : Nat) : FeasibleQuery P :=
  ⟨A.queryAt P t, A.queryAt_mem_instance P hP t⟩

/-- Oracle reply obtained through the feasible-query interface. -/
def replyAt {ell Delta : ℝ} {m n : Nat}
    (P : NCCInstance m n) (hP : IsFunctionClass ell D Delta P)
    (t : Nat) : NCCLowerBoundVerification.Oracle.OracleReply m n :=
  feasibleFirstOrderOracle P (A.feasibleQueryAt P hP t)

/-- The feasible wrapper returns exactly the reply used by the underlying
causal recursion. -/
theorem replyAt_eq_underlying {ell Delta : ℝ} {m n : Nat}
    (P : NCCInstance m n) (hP : IsFunctionClass ell D Delta P)
    (t : Nat) :
    A.replyAt P hP t =
      NCCLowerBoundVerification.Oracle.DeterministicFOComponent.replyAt
        (A.component m n) P t :=
  rfl

@[simp] theorem queryAt_zero {m n : Nat} (P : NCCInstance m n) :
    A.queryAt P 0 = (0, 0) := by
  exact
    NCCLowerBoundVerification.Oracle.DeterministicFOComponent.queriedAt_zero
      (A.component m n) P

/-! ## Hitting time without a value-differentiability premise -/

/-- The time-`t` primal query satisfies the Moreau/proximal OS predicate. -/
def HitsAt {m n : Nat} (P : NCCInstance m n) (ell eps : ℝ)
    (t : Nat) : Prop :=
  NCCLowerBoundVerification.Oracle.DeterministicFOComponent.HitsAt
    (A.component m n) P ell eps t

/-- Some one of the first `T` queries is optimization-stationary. -/
def HitsWithin {m n : Nat} (P : NCCInstance m n) (ell eps : ℝ)
    (T : Nat) : Prop :=
  NCCLowerBoundVerification.Oracle.DeterministicFOComponent.HitsWithin
    (A.component m n) P ell eps T

/-- Literal first hitting time, with `⊤` when the trajectory never hits.
This definition needs an `NCCInstance`, but no differentiability proof for its
value function. -/
def HittingTime {m n : Nat} (P : NCCInstance m n) (ell eps : ℝ) :
    WithTop Nat :=
  NCCLowerBoundVerification.Oracle.queriedHittingTime
    (A.component m n) P ell eps

theorem hittingTime_lt_iff {m n : Nat} (P : NCCInstance m n)
    (ell eps : ℝ) (T : Nat) :
    A.HittingTime P ell eps < (T : WithTop Nat) ↔
      A.HitsWithin P ell eps T := by
  exact
    NCCLowerBoundVerification.Oracle.queriedHittingTime_lt_iff
      (A.component m n) P ell eps T

/-- Class-restricted hitting time.  Its only class premise is
`IsFunctionClass`; the stronger `IsOldAdmissible` is absent. -/
def ClassHittingTime {ell Delta eps : ℝ} {m n : Nat}
    (P : NCCInstance m n) (_hP : IsFunctionClass ell D Delta P) :
    WithTop Nat :=
  A.HittingTime P ell eps

end DeterministicAlgorithm

/-! ## A complete counterexample to the old admissibility implication -/

/-- Embed a scalar as the unique coordinate of `EVec 1`. -/
def oneVec (a : ℝ) : EVec 1 :=
  fun _ ↦ a

/-- The one-dimensional bilinear saddle `f(x,y) = ell * x * y`. -/
def bilinearF (ell : ℝ) (x y : EVec 1) : ℝ :=
  ell * x 0 * y 0

def bilinearGradX (ell : ℝ) (_x y : EVec 1) : EVec 1 :=
  oneVec (ell * y 0)

def bilinearGradY (ell : ℝ) (x _y : EVec 1) : EVec 1 :=
  oneVec (ell * x 0)

/-- The bilinear example on `ℝ × [-1/2,1/2]`, represented using the
diameter-one ball. -/
def bilinearInstance (ell : ℝ) : NCCInstance 1 1 where
  X := Set.univ
  Y := diameterBall 1 1
  f := bilinearF ell
  gradX := bilinearGradX ell
  gradY := bilinearGradY ell
  x0 := 0

private def coord0 : EVec 1 →L[ℝ] ℝ :=
  ContinuousLinearMap.proj 0

private def coordX : (EVec 1 × EVec 1) →L[ℝ] ℝ :=
  coord0.comp (ContinuousLinearMap.fst ℝ (EVec 1) (EVec 1))

private def coordY : (EVec 1 × EVec 1) →L[ℝ] ℝ :=
  coord0.comp (ContinuousLinearMap.snd ℝ (EVec 1) (EVec 1))

private lemma bilinear_hasFDerivAt (ell : ℝ) (x y : EVec 1) :
    HasFDerivAt (Function.uncurry (bilinearF ell))
      (ell • (x 0 • coordY + y 0 • coordX)) (x, y) := by
  have hx : HasFDerivAt coordX coordX (x, y) := coordX.hasFDerivAt
  have hy : HasFDerivAt coordY coordY (x, y) := coordY.hasFDerivAt
  have h := (hx.mul hy).const_mul ell
  change HasFDerivAt
    (fun p : EVec 1 × EVec 1 ↦ ell * p.1 0 * p.2 0)
    (ell • (x 0 • coordY + y 0 • coordX)) (x, y)
  simpa [coordX, coordY, coord0, mul_assoc] using h

theorem bilinear_gradient_representation (ell : ℝ) :
    NCPLVerification.RepresentsJointGradient (bilinearF ell)
      (bilinearGradX ell) (bilinearGradY ell) := by
  constructor
  · intro p
    exact (bilinear_hasFDerivAt ell p.1 p.2).differentiableAt
  · intro x y hx hy
    rw [(bilinear_hasFDerivAt ell x y).fderiv]
    simp [bilinearGradX, bilinearGradY, oneVec, coordX, coordY, coord0]
    ring

theorem bilinear_jointly_smooth (ell : ℝ) (x y x' y' : EVec 1) :
    jointSq (bilinearGradX ell x y - bilinearGradX ell x' y')
        (bilinearGradY ell x y - bilinearGradY ell x' y') ≤
      ell ^ 2 * jointSq (x - x') (y - y') := by
  simp [jointSq, vecSq, NCPLVerification.vecSq, bilinearGradX,
    bilinearGradY, oneVec]
  ring_nf
  exact le_rfl

theorem bilinear_dual_concave (ell : ℝ) (x : EVec 1) :
    ConcaveOn ℝ (diameterBall 1 1) (bilinearF ell x) := by
  refine ⟨diameterBall_convex 1 1, ?_⟩
  intro y hy z hz a b ha hb hab
  simp [bilinearF]
  ring_nf
  exact le_rfl

/-- The endpoint selected according to the sign of the primal coordinate. -/
def bilinearMaximizer (x : EVec 1) : EVec 1 :=
  if 0 ≤ x 0 then oneVec (1 / 2) else oneVec (-1 / 2)

theorem unitDualBall_mem_iff (y : EVec 1) :
    y ∈ diameterBall 1 1 ↔ |y 0| ≤ (1 / 2 : ℝ) := by
  unfold diameterBall
  simp only [Set.mem_setOf_eq]
  rw [show vecSq y = y 0 ^ 2 by
    simp [NCCLowerBoundVerification.vecSq, NCPLVerification.vecSq]]
  simpa only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)] using
    (sq_le_sq (a := y 0) (b := (1 / 2 : ℝ)))

theorem bilinearMaximizer_isMaximizer (ell : ℝ) (hell : 0 < ell)
    (x : EVec 1) :
    IsMaximizerOn (diameterBall 1 1) (bilinearF ell) x
      (bilinearMaximizer x) := by
  constructor
  · rw [unitDualBall_mem_iff]
    unfold bilinearMaximizer
    split_ifs <;> norm_num [oneVec]
  · intro v hv
    have hvabs : |v 0| ≤ (1 / 2 : ℝ) := (unitDualBall_mem_iff v).mp hv
    have hvbounds : -(1 / 2 : ℝ) ≤ v 0 ∧ v 0 ≤ 1 / 2 := abs_le.mp hvabs
    unfold bilinearF bilinearMaximizer
    split_ifs with hx
    · change ell * x 0 * v 0 ≤ ell * x 0 * (1 / 2)
      exact mul_le_mul_of_nonneg_left hvbounds.2 (mul_nonneg hell.le hx)
    · have hxlt : x 0 < 0 := lt_of_not_ge hx
      have hvlower : (-1 / 2 : ℝ) ≤ v 0 := by
        linarith [hvbounds.1]
      change ell * x 0 * v 0 ≤ ell * x 0 * (-1 / 2)
      exact mul_le_mul_of_nonpos_left hvlower
        (mul_nonpos_of_nonneg_of_nonpos hell.le hxlt.le)

/-- The exact constrained value of the bilinear example. -/
theorem bilinearValue_eq (ell : ℝ) (hell : 0 < ell) (x : EVec 1) :
    ValueOn (diameterBall 1 1) (bilinearF ell) x =
      ell * |x 0| / 2 := by
  rw [value_eq_of_isMaximizerOn
    (bilinearMaximizer_isMaximizer ell hell x)]
  unfold bilinearF bilinearMaximizer
  split_ifs with hx
  · rw [abs_of_nonneg hx]
    change ell * x 0 * (1 / 2) = ell * x 0 / 2
    ring
  · have hxlt : x 0 < 0 := lt_of_not_ge hx
    rw [abs_of_neg hxlt]
    change ell * x 0 * (-1 / 2) = ell * -x 0 / 2
    ring

theorem bilinearValue_nonneg (ell : ℝ) (hell : 0 < ell)
    (x : EVec 1) :
    0 ≤ ValueOn (diameterBall 1 1) (bilinearF ell) x := by
  rw [bilinearValue_eq ell hell x]
  positivity

/-- The bilinear example satisfies the complete simplified function class,
including the initial-gap, attainment, smoothness, and diameter clauses. -/
theorem bilinearInstance_mem_functionClass (ell Delta : ℝ)
    (hell : 0 < ell) (hDelta : 0 < Delta) :
    IsFunctionClass ell 1 Delta (bilinearInstance ell) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  refine
    { ell_pos := hell
      D_pos := by norm_num
      Delta_pos := hDelta
      x0_mem := Set.mem_univ 0
      X_nonempty := Set.univ_nonempty
      X_closed := isClosed_univ
      X_convex := convex_univ
      Y_nonempty := diameterBall_nonempty 1 1 (by norm_num)
      Y_closed := diameterBall_closed 1 1
      Y_convex := diameterBall_convex 1 1
      gradient_representation := bilinear_gradient_representation ell
      jointly_smooth := ?_
      dual_concave := ?_
      maximum_attained := ?_
      value_bddBelow := ?_
      initial_gap := ?_
      dual_diameter := ?_ }
  · intro x hx y hy x' hx' y' hy'
    exact bilinear_jointly_smooth ell x y x' y'
  · intro x hx
    exact bilinear_dual_concave ell x
  · intro x hx
    exact ⟨bilinearMaximizer x,
      bilinearMaximizer_isMaximizer ell hell x⟩
  · refine ⟨0, ?_⟩
    rintro z ⟨x, hx, rfl⟩
    exact bilinearValue_nonneg ell hell x
  · have himage :
        (ValueOn (diameterBall 1 1) (bilinearF ell) ''
          (Set.univ : Set (EVec 1))).Nonempty :=
      Set.image_nonempty.mpr Set.univ_nonempty
    have hinf : 0 ≤ sInf
        (ValueOn (diameterBall 1 1) (bilinearF ell) ''
          (Set.univ : Set (EVec 1))) := by
      apply le_csInf himage
      rintro z ⟨x, hx, rfl⟩
      exact bilinearValue_nonneg ell hell x
    change ValueOn (diameterBall 1 1) (bilinearF ell) 0 -
      sInf (ValueOn (diameterBall 1 1) (bilinearF ell) '' Set.univ) ≤
        Delta
    rw [bilinearValue_eq ell hell]
    simp only [Pi.zero_apply, abs_zero, mul_zero, zero_div, zero_sub]
    linarith
  · intro y hy y' hy'
    exact diameterBall_vecSq_sub_le (by norm_num) hy hy'

private theorem not_differentiableAt_scaled_abs (ell : ℝ)
    (hell : ell ≠ 0) :
    ¬ DifferentiableAt ℝ (fun t : ℝ ↦ ell * |t| / 2) 0 := by
  intro h
  apply not_differentiableAt_abs_zero
  have hscaled := h.const_mul (2 / ell)
  refine hscaled.congr_of_eventuallyEq ?_
  filter_upwards with t
  field_simp

/-- Although the saddle is smooth, its value is not differentiable at the
origin. -/
theorem bilinearValue_not_differentiableAt_zero (ell : ℝ)
    (hell : 0 < ell) :
    ¬ DifferentiableAt ℝ
      (ValueOn (diameterBall 1 1) (bilinearF ell)) 0 := by
  intro h
  have hzero : oneVec 0 = (0 : EVec 1) := by
    funext i
    rfl
  have hAtEmbed : DifferentiableAt ℝ
      (ValueOn (diameterBall 1 1) (bilinearF ell)) (oneVec 0) := by
    rw [hzero]
    exact h
  have hEmbed : DifferentiableAt ℝ oneVec 0 := by
    rw [differentiableAt_pi]
    intro i
    simp [oneVec]
  have hcomp := hAtEmbed.comp 0 hEmbed
  apply not_differentiableAt_scaled_abs ell (ne_of_gt hell)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards with t
  simp only [Function.comp_apply]
  exact (bilinearValue_eq ell hell (oneVec t)).symm

/-- The complete class member is rejected by the prose's extra admissibility
condition. -/
theorem bilinearInstance_not_oldAdmissible (ell Delta : ℝ)
    (hell : 0 < ell) :
    ¬ IsOldAdmissible ell 1 Delta (bilinearInstance ell) := by
  intro hOld
  apply bilinearValue_not_differentiableAt_zero ell hell
  simpa [bilinearInstance] using hOld.value_differentiable 0

/-- Formal non-implication: the original value-differentiability requirement
does not follow from the NC--C function-class assumptions. -/
theorem functionClass_does_not_imply_oldAdmissible (ell Delta : ℝ)
    (hell : 0 < ell) (hDelta : 0 < Delta) :
    ∃ P : NCCInstance 1 1,
      IsFunctionClass ell 1 Delta P ∧
        ¬ IsOldAdmissible ell 1 Delta P := by
  exact ⟨bilinearInstance ell,
    bilinearInstance_mem_functionClass ell Delta hell hDelta,
    bilinearInstance_not_oldAdmissible ell Delta hell⟩

/-- The corrected hitting time is nevertheless well-typed on the bilinear
class member, demonstrating that the model does not depend on the erroneous
extra admissibility clause. -/
def bilinearClassHittingTime (A : DeterministicAlgorithm 1)
    (ell Delta eps : ℝ) (hell : 0 < ell) (hDelta : 0 < Delta) :
    WithTop Nat :=
  A.ClassHittingTime (bilinearInstance ell)
    (eps := eps) (bilinearInstance_mem_functionClass ell Delta hell hDelta)

end

end CorrectedModel
end Simplified
end NCCLowerBound
