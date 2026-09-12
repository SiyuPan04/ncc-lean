import NCCLowerBoundVerification.Lower.ComplexityThreshold
import NCCLowerBoundVerification.Lower.UniformSmoothness

/-!
# Assumption-free concrete deterministic lower bound

This module instantiates the assembly theorem with the dimension-independent
smoothness certificate for the explicit hard objective.  No analytic source
record remains as an assumption.
-/

namespace NCCLowerBoundVerification
namespace Lower

noncomputable section

open Oracle

/-- Numerical accuracy coefficient in `thm:main`. -/
def concreteAccuracyConstant : ℝ :=
  lowerAccuracyConstant concreteL0
    (concreteTerminalC0 concreteL0) concreteCy
    concreteUnscaledParameters.P1 concreteCDelta

theorem concreteAccuracyConstant_pos : 0 < concreteAccuracyConstant := by
  unfold concreteAccuracyConstant
  exact lowerAccuracyConstant_pos concreteL0_pos
    (concreteTerminalC0_pos concreteL0_pos) concreteCy_pos
    concreteUnscaledP1_pos concreteCDelta_pos

/-- The exact explicit hard family supplies every regularity record consumed
by the scaling and resisting construction. -/
theorem concrete_uniform_source :
    ∀ {T n : Nat} (hT : 1 ≤ T) (hn : 10 ≤ n) {D0 Delta0 : ℝ},
      0 < D0 → concreteDelta0 T ≤ Delta0 →
        ScalingSource concreteL0 D0 Delta0
          (unscaledNCCInstance (T := T) (n := n) (by omega)
            concreteUnscaledParameters D0) := by
  intro T n hT hn D0 Delta0 hD0 hgap
  exact concrete_unscaled_scalingSource hT hn hD0 hgap

/-- `thm:main` for the literal measurable algorithm class, with explicit
dimensions, horizon, numerical coefficient, and no remaining source
hypothesis. -/
theorem concrete_deterministic_paper_lower_bound
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ concreteAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    MeasurablePaperComplexityAtLeast ell D Delta eps
        (concreteHardK concreteL0 ell D Delta eps) ∧
      concreteLowerRateConstant concreteL0 *
          (ell ^ 2 * D * Delta / eps ^ 3) ≤
        (concreteHardK concreteL0 ell D Delta eps : ℝ) := by
  exact concrete_measurablePaper_lower_rate_of_uniform_source
    concreteL0_pos hell hD hDelta heps
    (by simpa [concreteAccuracyConstant] using haccuracy)
    concrete_uniform_source

/-- Literal infimum--supremum inequality corresponding to the lower half of
the paper's complexity theorem. -/
theorem concrete_paper_hitting_complexity_lower_bound
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ concreteAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    ((concreteHardK concreteL0 ell D Delta eps : Nat) : WithTop Nat) ≤
      measurablePaperHittingComplexity ell D Delta eps := by
  exact concrete_lower_bound_for_paper_hitting_complexity
    concreteL0_pos hell hD hDelta heps
    (by simpa [concreteAccuracyConstant] using haccuracy)
    concrete_uniform_source

end

end Lower
end NCCLowerBoundVerification
