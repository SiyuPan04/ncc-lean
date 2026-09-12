import NCCLowerBoundVerification.Lower.ConcreteLowerBound
import NCCLowerBoundVerification.Upper.SharedOracleMeasurable

/-!
# Explicit optimal deterministic complexity certificate

This file combines the assumption-free hard family with the executable shared
upper horizon.  The certificate records both finite threshold statements,
their cubic real-valued comparisons, and the corresponding inequalities for
the literal infimum--supremum hitting-time complexity.
-/

namespace NCCLowerBoundVerification

noncomputable section

open Oracle

/-- A pointwise, explicit-constant version of the paper's `Θ` statement. -/
structure MeasurablePaperThetaCertificate
    (ell D Delta eps c C rate : ℝ) where
  lowerHorizon : Nat
  upperHorizon : Nat
  c_pos : 0 < c
  C_pos : 0 < C
  rate_pos : 0 < rate
  lower_threshold :
    MeasurablePaperComplexityAtLeast ell D Delta eps lowerHorizon
  upper_threshold :
    MeasurablePaperComplexityAtMost ell D Delta eps upperHorizon
  lower_rate : c * rate ≤ (lowerHorizon : ℝ)
  upper_rate : (upperHorizon : ℝ) ≤ C * rate
  hitting_lower :
    (lowerHorizon : WithTop Nat) ≤
      measurablePaperHittingComplexity ell D Delta eps
  hitting_upper :
    measurablePaperHittingComplexity ell D Delta eps ≤
      (upperHorizon : WithTop Nat)

/-- Proposition-valued formulation of the paper's pointwise `Θ` conclusion.
The two horizons are explicit fields of the inhabited certificate. -/
def MeasurablePaperTheta
    (ell D Delta eps c C rate : ℝ) : Prop :=
  Nonempty (MeasurablePaperThetaCertificate ell D Delta eps c C rate)

/-- Once the explicit shared client has its Borel certificate, all remaining
mathematics combines into the literal optimal-complexity conclusion. -/
def optimal_deterministic_complexity_of_measurable_upper
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ Lower.concreteAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta)))
    (hupper : MeasurablePaperComplexityAtMost ell D Delta eps
      (Upper.PaperSharedOracle.sharedOracleBudget
        ell D Delta eps hell hD heps)) :
    MeasurablePaperThetaCertificate ell D Delta eps
      (Lower.concreteLowerRateConstant concreteL0)
      Upper.LogFreeCorollary.logFreeCostConstant
      (ell ^ 2 * D * Delta / eps ^ 3) := by
  have hlower := Lower.concrete_deterministic_paper_lower_bound
    hell hD hDelta heps haccuracy
  have hregime := lower_accuracy_implies_logFree_regime
    hell hD hDelta heps concreteL0_pos
    (concreteTerminalC0_pos concreteL0_pos) concreteCy_pos
    concreteUnscaledP1_pos concreteCDelta_pos
    (by simpa [Lower.concreteAccuracyConstant] using haccuracy)
  let K := concreteHardK concreteL0 ell D Delta eps
  let B := Upper.PaperSharedOracle.sharedOracleBudget
    ell D Delta eps hell hD heps
  refine
    { lowerHorizon := K
      upperHorizon := B
      c_pos := Lower.concreteLowerRateConstant_pos concreteL0_pos
      C_pos := Upper.LogFreeCorollary.logFreeCostConstant_pos
      rate_pos := by positivity
      lower_threshold := ?_
      upper_threshold := ?_
      lower_rate := ?_
      upper_rate := ?_
      hitting_lower := ?_
      hitting_upper := ?_ }
  · simpa [K] using hlower.1
  · simpa [B] using hupper
  · simpa [K] using hlower.2
  · dsimp [B]
    exact Upper.PaperSharedOracle.sharedOracleBudget_logFree_bound
      ell D Delta eps hell hD hDelta heps hregime.1 hregime.2
  · apply le_measurablePaperHittingComplexity_of_atLeast
    simpa [K] using hlower.1
  · apply measurablePaperHittingComplexity_le_of_atMost
    simpa [B] using hupper

/-- Proposition-valued wrapper for the conditional final combination. -/
theorem measurablePaperTheta_of_measurable_upper
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ Lower.concreteAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta)))
    (hupper : MeasurablePaperComplexityAtMost ell D Delta eps
      (Upper.PaperSharedOracle.sharedOracleBudget
        ell D Delta eps hell hD heps)) :
    MeasurablePaperTheta ell D Delta eps
      (Lower.concreteLowerRateConstant concreteL0)
      Upper.LogFreeCorollary.logFreeCostConstant
      (ell ^ 2 * D * Delta / eps ^ 3) :=
  ⟨optimal_deterministic_complexity_of_measurable_upper
    hell hD hDelta heps haccuracy hupper⟩

/-- Corollary `cor:optimal-det-complexity`: for the paper's literal Borel
domain-wise deterministic algorithm class, the queried hitting complexity is
trapped between two explicit positive numerical multiples of the cubic rate.
There are no remaining source, regularity, or measurability premises. -/
theorem concrete_optimal_deterministic_first_order_complexity
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ Lower.concreteAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    MeasurablePaperTheta ell D Delta eps
      (Lower.concreteLowerRateConstant concreteL0)
      Upper.LogFreeCorollary.logFreeCostConstant
      (ell ^ 2 * D * Delta / eps ^ 3) :=
  measurablePaperTheta_of_measurable_upper hell hD hDelta heps haccuracy
    (Upper.SharedOracleMeasurable.measurablePaperComplexityAtMost_sharedOracle
      ell D Delta eps hell hD hDelta heps)

end

end NCCLowerBoundVerification
