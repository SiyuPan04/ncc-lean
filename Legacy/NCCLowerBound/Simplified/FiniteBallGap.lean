import NCCLowerBound.Simplified.CompositeProperties

/-!
# Finite-dual-ball initial gap for the five-component hard instance

This file proves the finite-radius part of Proposition `prop:initial-gap`
(lines 1376--1397 of the simplified manuscript).  The dual ball is defined
using the genuine block Euclidean square

`sum_i sum_j y(i,j)^2`.

The value below is the actual supremum over that ball.  At the primal origin,
the feasible zero dual vector is a maximizer.  At every primal point, the same
zero vector supplies the dimension-linear lower bound, so the infimum and
initial-gap conclusions do not use dual inactivity or any abstract
certificate.
-/

namespace NCCLowerBound
namespace Simplified
namespace FiniteBallGap

noncomputable section

open scoped BigOperators
open Set
open NCCLowerBoundVerification
open InnerRelay
open Composite

/-- The three primal blocks `(s,a,b)` of the composite construction. -/
abbrev PrimalPoint (M : Nat) :=
  (Fin M → ℝ) × ((Fin M → ℝ) × (Fin M → ℝ))

/-- The block dual variable, with one `N`-coordinate relay per outer block. -/
abbrev BlockDual (M N : Nat) := Fin M → InnerRelay.EVec N

/-- Squared Euclidean norm on the block dual space. -/
def blockVecSq {M N : Nat} (y : BlockDual M N) : ℝ :=
  ∑ i : Fin M, vecSq (y i)

/-- The centered block Euclidean ball of diameter `D`. -/
def finiteDualBall (M N : Nat) (D : ℝ) : Set (BlockDual M N) :=
  {y | blockVecSq y ≤ (D / 2) ^ 2}

/-- The all-zero primal point. -/
def primalOrigin (M : Nat) : PrimalPoint M :=
  (0, 0, 0)

/-- The all-zero dual block vector. -/
def zeroDual (M N : Nat) : BlockDual M N :=
  fun _ _ ↦ 0

/-- The actual finite-ball image of the saddle objective at a primal point. -/
def finiteBallImage {M N : Nat} (hN : 0 < N) (K D : ℝ)
    (x : PrimalPoint M) : Set ℝ :=
  (fun y ↦ hardObjective hN K x.1 x.2.1 x.2.2 y) ''
    finiteDualBall M N D

/-- The actual finite-ball value, defined as a supremum rather than by an
unconstrained contraction formula. -/
def finiteBallValue {M N : Nat} (hN : 0 < N) (K D : ℝ)
    (x : PrimalPoint M) : ℝ :=
  sSup (finiteBallImage hN K D x)

/-- The zero dual vector is feasible in every finite ball. -/
theorem zeroDual_mem_finiteDualBall {M N : Nat} {D : ℝ} (_hD : 0 < D) :
    zeroDual M N ∈ finiteDualBall M N D := by
  change blockVecSq (zeroDual M N) ≤ (D / 2) ^ 2
  unfold blockVecSq zeroDual vecSq NCPLVerification.vecSq
  simpa using sq_nonneg (D / 2)

/-- At the primal origin every dual value is nonpositive. -/
theorem hardObjective_origin_upper {M N : Nat} (hN : 0 < N) (K : ℝ)
    (y : BlockDual M N) :
    hardObjective hN K (0 : Fin M → ℝ) 0 0 y ≤ 0 := by
  have houter : outerComponent K (0 : Fin M → ℝ) 0 0 = 0 :=
    CompositeProperties.outerComponent_origin K
  have hinner : innerComponent hN (0 : Fin M → ℝ) 0 y ≤ 0 := by
    unfold innerComponent
    exact Finset.sum_nonpos fun i _ ↦ correctedH_zero_primal_nonpos hN (y i)
  unfold hardObjective
  rw [houter, zero_add]
  exact hinner

/-- Zero is the attained finite-ball maximum at the primal origin. -/
theorem origin_finiteBallImage_isGreatest {M N : Nat} (hN : 0 < N)
    (K : ℝ) {D : ℝ} (hD : 0 < D) :
    IsGreatest (finiteBallImage hN K D (primalOrigin M)) 0 := by
  constructor
  · refine ⟨zeroDual M N, zeroDual_mem_finiteDualBall hD, ?_⟩
    change hardObjective hN K (fun _ : Fin M ↦ 0) (fun _ ↦ 0)
      (fun _ ↦ 0) (fun _ _ ↦ 0) = 0
    exact hardObjective_origin (M := M) hN K
  · rintro z ⟨y, hy, rfl⟩
    simpa [primalOrigin] using hardObjective_origin_upper hN K y

/-- The finite-ball value at the primal origin is exactly zero. -/
@[simp] theorem finiteBallValue_origin {M N : Nat} (hN : 0 < N)
    (K : ℝ) {D : ℝ} (hD : 0 < D) :
    finiteBallValue hN K D (primalOrigin M) = 0 := by
  exact (origin_finiteBallImage_isGreatest hN K hD).csSup_eq

/-- Every finite-ball image is bounded above by the exact unconstrained
contraction. -/
theorem finiteBallImage_bddAbove {M N : Nat} (hN10 : 10 ≤ N)
    (K D : ℝ) (x : PrimalPoint M) :
    BddAbove (finiteBallImage (by omega : 0 < N) K D x) := by
  refine ⟨unconstrainedValue K x.1 x.2.1 x.2.2, ?_⟩
  rintro z ⟨y, hy, rfl⟩
  exact hardObjective_le_unconstrainedValue hN10 K x.1 x.2.1 x.2.2 y

/-- Substituting the feasible zero dual vector gives a global lower bound for
the genuine finite-ball value. -/
theorem finiteBallValue_lower {M N : Nat} (hN10 : 10 ≤ N)
    {K D : ℝ} (hK : 0 < K) (hD : 0 < D) (x : PrimalPoint M) :
    -(M : ℝ) * (154 + |phasePotential K 2|) ≤
      finiteBallValue (by omega : 0 < N) K D x := by
  let y0 : BlockDual M N := zeroDual M N
  have hy0 : y0 ∈ finiteDualBall M N D :=
    zeroDual_mem_finiteDualBall hD
  have hmember :
      hardObjective (by omega : 0 < N) K x.1 x.2.1 x.2.2 y0 ∈
        finiteBallImage (by omega : 0 < N) K D x :=
    ⟨y0, hy0, rfl⟩
  have hzeroLower :
      -(M : ℝ) * (154 + |phasePotential K 2|) ≤
        hardObjective (by omega : 0 < N) K x.1 x.2.1 x.2.2 y0 := by
    change -(M : ℝ) * (154 + |phasePotential K 2|) ≤
      hardObjective (by omega : 0 < N) K x.1 x.2.1 x.2.2
        (fun _ _ ↦ 0)
    exact hardObjective_at_zeroDual_lower hN10 hK x.1 x.2.1 x.2.2
  unfold finiteBallValue
  exact hzeroLower.trans
    (le_csSup (finiteBallImage_bddAbove hN10 K D x) hmember)

/-- The range of the genuine finite-ball value has a dimension-linear lower
bound, uniformly in the positive diameter. -/
theorem finiteBallValue_bddBelow {M N : Nat} (hN10 : 10 ≤ N)
    {K D : ℝ} (hK : 0 < K) (hD : 0 < D) :
    BddBelow (Set.range
      (finiteBallValue (M := M) (by omega : 0 < N) K D)) := by
  refine ⟨-(M : ℝ) * (154 + |phasePotential K 2|), ?_⟩
  rintro z ⟨x, rfl⟩
  exact finiteBallValue_lower hN10 hK hD x

/-- The actual infimum of the finite-ball value. -/
def finiteBallInfimum (M N : Nat) (hN : 0 < N) (K D : ℝ) : ℝ :=
  sInf (Set.range (finiteBallValue (M := M) hN K D))

theorem finiteBallInfimum_lower {M N : Nat} (hN10 : 10 ≤ N)
    {K D : ℝ} (hK : 0 < K) (hD : 0 < D) :
    -(M : ℝ) * (154 + |phasePotential K 2|) ≤
      finiteBallInfimum M N (by omega : 0 < N) K D := by
  rw [finiteBallInfimum,
    le_csInf_iff (finiteBallValue_bddBelow hN10 hK hD)
      (Set.range_nonempty _)]
  rintro z ⟨x, rfl⟩
  exact finiteBallValue_lower hN10 hK hD x

/-- Proposition `prop:initial-gap` for every positive finite diameter, with an
explicit coefficient independent of `M`, `N`, and `D`. -/
theorem finiteBall_initial_gap {M N : Nat} (hN10 : 10 ≤ N)
    {K D : ℝ} (hK : 0 < K) (hD : 0 < D) :
    finiteBallValue (M := M) (by omega : 0 < N) K D (primalOrigin M) -
        finiteBallInfimum M N (by omega : 0 < N) K D ≤
      (M : ℝ) * (154 + |phasePotential K 2|) := by
  rw [finiteBallValue_origin (by omega : 0 < N) K hD]
  have h := finiteBallInfimum_lower (M := M) hN10 hK hD
  linarith

end

end FiniteBallGap
end Simplified
end NCCLowerBound
