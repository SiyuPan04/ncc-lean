import NCCLowerBoundVerification.Oracle.PaperComplexity
import NCCLowerBoundVerification.Upper.LogFreeCorollary
import NCCLowerBoundVerification.Upper.SharedOracle

/-!
# Paper-class shared-oracle upper threshold

The executable client is first proved correct for global analytic
representatives.  `PaperClass` then transports the same feasible transcript
and OS certificate to Definition 2.1's neighborhood-`C^1` instances.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace PaperSharedOracle

noncomputable section

open Oracle SharedOracle

/-- Published assembled oracle horizon of the executable shared client. -/
def sharedOracleBudget (ell D Delta eps : ℝ)
    (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) : Nat :=
  (UniformCost.assembledCost ell (ell / 8)
    (scheduleCurvature ell D eps hell hD heps)
    (scheduleStage ell D eps hell hD heps)
    (scheduleIterations ell D Delta eps hell hD heps)).oracleCalls

/-- The causal shared client solves every literal paper-class instance within
the assembled finite horizon. -/
theorem paperComplexityAtMost_sharedOracle
    (ell D Delta eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps) :
    PaperComplexityAtMost ell D Delta eps
      (sharedOracleBudget ell D Delta eps hell hD heps) := by
  apply paperComplexityAtMost_of_complexityAtMost
  simpa only [sharedOracleBudget] using
    complexityAtMost_sharedOracle ell D Delta eps hell hD hDelta heps

/-- The actual natural-valued horizon obeys the explicit uniform real-valued
rate from `ub:thm:uniform`. -/
theorem sharedOracleBudget_uniform_bound
    (ell D Delta eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps) :
    (sharedOracleBudget ell D Delta eps hell hD heps : ℝ) ≤
      UniformCost.uniformCostConstant *
        ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) := by
  have hcost := UniformCost.assembledCost_uniform_bound
    hell hD hDelta heps
    (target := scheduleTarget ell D eps)
    (r := scheduleCurvature ell D eps hell hD heps)
    (J := scheduleStage ell D eps hell hD heps)
    (T := scheduleIterations ell D Delta eps hell hD heps)
    (by rfl) (by rfl) (by rfl) (by rfl)
  simpa only [sharedOracleBudget] using hcost.1

/-- Causal paper-class upper threshold and its numerical rate comparison. -/
theorem paper_shared_upper_rate
    (ell D Delta eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps) :
    PaperComplexityAtMost ell D Delta eps
        (sharedOracleBudget ell D Delta eps hell hD heps) ∧
      (sharedOracleBudget ell D Delta eps hell hD heps : ℝ) ≤
        UniformCost.uniformCostConstant *
          ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) :=
  ⟨paperComplexityAtMost_sharedOracle ell D Delta eps
      hell hD hDelta heps,
    sharedOracleBudget_uniform_bound ell D Delta eps
      hell hD hDelta heps⟩

/-- In the nontrivial accuracy regime, the executable shared horizon has the
paper's log-free cubic rate. -/
theorem sharedOracleBudget_logFree_bound
    (ell D Delta eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hepsD : eps ≤ ell * D)
    (hgap : (1 / 4 : ℝ) ≤ ell * Delta / eps ^ 2) :
    (sharedOracleBudget ell D Delta eps hell hD heps : ℝ) ≤
      LogFreeCorollary.logFreeCostConstant *
        (ell ^ 2 * D * Delta / eps ^ 3) := by
  have hbudget := sharedOracleBudget_uniform_bound ell D Delta eps
    hell hD hDelta heps
  have hrate := LogFreeCorollary.uniform_rate_le_logFree
    hell hD hDelta heps hepsD hgap
  calc
    (sharedOracleBudget ell D Delta eps hell hD heps : ℝ) ≤
        UniformCost.uniformCostConstant *
          ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) := hbudget
    _ ≤ UniformCost.uniformCostConstant *
        (5 * (ell ^ 2 * D * Delta / eps ^ 3)) :=
      mul_le_mul_of_nonneg_left hrate UniformCost.uniformCostConstant_pos.le
    _ = LogFreeCorollary.logFreeCostConstant *
        (ell ^ 2 * D * Delta / eps ^ 3) := by
      unfold LogFreeCorollary.logFreeCostConstant
      ring

theorem paper_shared_logFree_upper_rate
    (ell D Delta eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hepsD : eps ≤ ell * D)
    (hgap : (1 / 4 : ℝ) ≤ ell * Delta / eps ^ 2) :
    PaperComplexityAtMost ell D Delta eps
        (sharedOracleBudget ell D Delta eps hell hD heps) ∧
      (sharedOracleBudget ell D Delta eps hell hD heps : ℝ) ≤
        LogFreeCorollary.logFreeCostConstant *
          (ell ^ 2 * D * Delta / eps ^ 3) :=
  ⟨paperComplexityAtMost_sharedOracle ell D Delta eps
      hell hD hDelta heps,
    sharedOracleBudget_logFree_bound ell D Delta eps
      hell hD hDelta heps hepsD hgap⟩

end

end PaperSharedOracle
end Upper
end NCCLowerBoundVerification
