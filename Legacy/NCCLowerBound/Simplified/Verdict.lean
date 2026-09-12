import NCCLowerBound.Simplified.MainTheorem
import NCCLowerBound.Simplified.CurrentLowerBound

/-!
# Formal verdict for the simplified manuscript

The two results below deliberately separate the questions which the raw prose
conflates:

* the manuscript's NC--C class is **not** contained in the later class called
  `admissible`, because value differentiability does not follow; and
* after removing that extra premise and making every dual query feasible, the
  deterministic cubic lower-bound endpoint is a closed Lean theorem.

Thus this module is both a machine-checked refutation of the uncorrected model
and the shortest import for the corrected final statement.
-/

namespace NCCLowerBound
namespace Simplified
namespace Verdict

noncomputable section

open CorrectedModel CorrectedEndpoint
open CurrentLowerBound
open NCCLowerBoundVerification
open NCCLowerBoundVerification.Oracle

/-- The raw function-class assumptions do not imply the value-differentiable
`admissible` condition used by the manuscript's algorithm and complexity
definitions. -/
theorem old_admissibility_gap :
    ∀ ell Delta : ℝ, 0 < ell → 0 < Delta →
      ∃ P : NCCInstance 1 1,
        IsFunctionClass ell 1 Delta P ∧
          ¬ IsOldAdmissible ell 1 Delta P := by
  intro ell Delta hell hDelta
  exact functionClass_does_not_imply_oldAdmissible ell Delta hell hDelta

/-- Closed corrected endpoint, restated at the audit boundary. -/
theorem corrected_deterministic_endpoint :
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
  exact exists_constants_corrected_algorithm_lower_bound

/-- Closed corrected endpoint proved by the literal five-component
memory--pulse construction formalized in this project.  Unlike the preceding
independent cross-check, this theorem uses `CurrentHardProperties` and the
current construction all the way through the resisting lift. -/
theorem current_five_component_deterministic_endpoint :
    ∃ cacc crate : ℝ,
      0 < cacc ∧ 0 < crate ∧
      ∀ {ell D Delta eps : ℝ},
        0 < ell → 0 < D → 0 < Delta → 0 < eps →
        eps ≤ cacc * min (ell * D) (Real.sqrt (ell * Delta)) →
        ∀ A : DeterministicAlgorithm D,
          ∃ (m n T : Nat) (Q : NCCInstance m n),
            IsFunctionClass ell D Delta Q ∧
            DeterministicFOComponent.FailsWithin
              (A.component m n) Q ell eps T ∧
            0 < T ∧
            crate * (ell ^ 2 * D * Delta / eps ^ 3) ≤ (T : ℝ) := by
  exact exists_constants_current_deterministic_lower_bound

end

end Verdict
end Simplified
end NCCLowerBound
