import NCCLowerBoundVerification.Lower.ConcreteLowerBound
import NCCLowerBound.Simplified.CorrectedModel

/-!
# Main deterministic lower-bound endpoint for the simplified manuscript

The manuscript's raw definitions require the two repairs recorded in
`Simplified.CorrectedModel`: algorithms must make feasible dual queries and
the ambient NC--C class must not require its (generally nonsmooth) value
function to be differentiable.

This module records the fully kernel-checked endpoint with explicit positive
constants and a strict query horizon.  `PaperComplexityAtLeast` quantifies all
causal deterministic domain-wise algorithms; no measurability assumption is
used here.
-/

namespace NCCLowerBound
namespace Simplified

noncomputable section

open NCCLowerBoundVerification
open NCCLowerBoundVerification.Oracle
open NCCLowerBoundVerification.Lower

namespace CorrectedEndpoint

open CorrectedModel

/-- The positive numerical constant multiplying the accuracy regime. -/
def accuracyConstant : ℝ := concreteAccuracyConstant

/-- The positive numerical constant multiplying the cubic lower-bound rate. -/
def deterministicRateConstant : ℝ :=
  concreteLowerRateConstant concreteL0

theorem accuracyConstant_pos : 0 < accuracyConstant := by
  exact concreteAccuracyConstant_pos

theorem deterministicRateConstant_pos : 0 < deterministicRateConstant := by
  exact concreteLowerRateConstant_pos concreteL0_pos

/--
The direct endpoint for the repaired, dimension-polymorphic algorithm model.

For each such algorithm, this theorem returns an actual finite-dimensional
instance whose primal domain is all of Euclidean space, whose dual domain is
the diameter-`D` ball, and on which all queries before the displayed horizon
fail the proximal OS test.  Thus no domain relabelling or value-function
differentiability assumption is hidden in the final quantifiers.
-/
theorem corrected_algorithm_has_hard_instance
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ accuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta)))
    (A : DeterministicAlgorithm D) :
    ∃ P : NCCInstance
        (concreteHardDX concreteL0 ell D Delta eps)
        (concreteHardDY concreteL0 ell D Delta eps),
      IsFunctionClass ell D Delta P ∧
      DeterministicFOComponent.FailsWithin
        (A.component
          (concreteHardDX concreteL0 ell D Delta eps)
          (concreteHardDY concreteL0 ell D Delta eps))
        P ell eps (concreteHardK concreteL0 ell D Delta eps) ∧
      deterministicRateConstant *
          (ell ^ 2 * D * Delta / eps ^ 3) ≤
        (concreteHardK concreteL0 ell D Delta eps : ℝ) := by
  obtain ⟨P, hclass, _hpaper, hfail, hX, hY, hx0, hrate⟩ :=
    NCCLowerBoundVerification.concrete_deterministic_lower_bound_of_uniform_source
      concreteL0_pos hell hD hDelta heps
      (by simpa [accuracyConstant, concreteAccuracyConstant] using haccuracy)
      concrete_uniform_source
      (A.component
        (concreteHardDX concreteL0 ell D Delta eps)
        (concreteHardDY concreteL0 ell D Delta eps))
  refine ⟨P, ⟨hX, hY, hx0, hclass⟩, hfail, ?_⟩
  simpa [deterministicRateConstant, concreteLowerRateConstant] using hrate

/--
Operational, type-correct version of Theorem `thm:deterministic`.

`FailsWithin ... K` means that every queried primal iterate with index
`t < K` fails the Moreau-envelope stationarity test.  The hard dimension and
the hard instance may depend on the deterministic algorithm, exactly as in a
finite-horizon resisting-oracle lower bound.
-/
theorem deterministic_lower_bound_verified
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ accuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    PaperComplexityAtLeast ell D Delta eps
        (concreteHardK concreteL0 ell D Delta eps) ∧
      deterministicRateConstant *
          (ell ^ 2 * D * Delta / eps ^ 3) ≤
        (concreteHardK concreteL0 ell D Delta eps : ℝ) := by
  constructor
  · exact concrete_paperComplexityAtLeast_of_uniform_source
      concreteL0_pos hell hD hDelta heps
      (by simpa [accuracyConstant, concreteAccuracyConstant] using haccuracy)
      concrete_uniform_source
  · let A0 : DeterministicFOComponent
        (Set.univ : Set (EVec (concreteHardDX concreteL0 ell D Delta eps)))
        (diameterBall (concreteHardDY concreteL0 ell D Delta eps) D) :=
      { nextQuery := fun _ _ => (0, 0)
        next_mem := fun _ _ =>
          ⟨Set.mem_univ 0, zero_mem_diameterBall _ _ hD.le⟩
        initial_query := rfl }
    obtain ⟨_P, _hclass, _hpaper, _hfail, _hX, _hY, _hx0, hrate⟩ :=
      concrete_deterministic_lower_bound_of_uniform_source
        concreteL0_pos hell hD hDelta heps
        (by simpa [accuracyConstant, concreteAccuracyConstant] using haccuracy)
        concrete_uniform_source A0
    simpa [deterministicRateConstant, concreteLowerRateConstant] using hrate

/-- Existential-constant form mirroring the prose statement of the paper. -/
theorem exists_constants_deterministic_lower_bound :
    ∃ c0 cdet : ℝ,
      0 < c0 ∧ 0 < cdet ∧
      ∀ {ell D Delta eps : ℝ},
        0 < ell → 0 < D → 0 < Delta → 0 < eps →
        eps ≤ c0 * min (ell * D) (Real.sqrt (ell * Delta)) →
        ∃ K : Nat,
          PaperComplexityAtLeast ell D Delta eps K ∧
            cdet * (ell ^ 2 * D * Delta / eps ^ 3) ≤ (K : ℝ) := by
  refine ⟨accuracyConstant, deterministicRateConstant,
    accuracyConstant_pos, deterministicRateConstant_pos, ?_⟩
  intro ell D Delta eps hell hD hDelta heps haccuracy
  refine ⟨concreteHardK concreteL0 ell D Delta eps, ?_⟩
  exact deterministic_lower_bound_verified hell hD hDelta heps haccuracy

/-- Existential constants in the exact repaired algorithm interface. -/
theorem exists_constants_corrected_algorithm_lower_bound :
    ∃ c0 cdet : ℝ,
      0 < c0 ∧ 0 < cdet ∧
      ∀ {ell D Delta eps : ℝ},
        0 < ell → 0 < D → 0 < Delta → 0 < eps →
        eps ≤ c0 * min (ell * D) (Real.sqrt (ell * Delta)) →
        ∀ A : DeterministicAlgorithm D,
          ∃ (m n K : Nat) (P : NCCInstance m n),
            IsFunctionClass ell D Delta P ∧
            DeterministicFOComponent.FailsWithin
              (A.component m n) P ell eps K ∧
            cdet * (ell ^ 2 * D * Delta / eps ^ 3) ≤ (K : ℝ) := by
  refine ⟨accuracyConstant, deterministicRateConstant,
    accuracyConstant_pos, deterministicRateConstant_pos, ?_⟩
  intro ell D Delta eps hell hD hDelta heps haccuracy A
  obtain ⟨P, hP, hfail, hrate⟩ :=
    corrected_algorithm_has_hard_instance hell hD hDelta heps haccuracy A
  exact ⟨concreteHardDX concreteL0 ell D Delta eps,
    concreteHardDY concreteL0 ell D Delta eps,
    concreteHardK concreteL0 ell D Delta eps, P, hP, hfail, hrate⟩

end CorrectedEndpoint

end

end Simplified
end NCCLowerBound
