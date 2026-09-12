import NCCLowerBoundVerification.Lower.ScalingArithmetic

/-!
# From the headline accuracy hypothesis to the lower-size regime

The paper closes the deterministic lower bound by saying that its two raw
chain-size inequalities follow after choosing a sufficiently small numerical
constant.  This file makes that choice explicit and proves both inequalities.
-/

namespace NCCLowerBoundVerification

noncomputable section

/-- An explicit numerical accuracy constant.  Its first branch makes the
inner-chain length at least `20`; its second branch makes the outer-chain
length at least `4`.  The extra `min 1` lets the latter implication be proved
without hiding a square-root comparison. -/
def lowerAccuracyConstant (ell0 c0 Cy P1 cDelta : ℝ) : ℝ :=
  min (c0 / (160 * Cy * P1 * ell0))
    (min 1 (c0 ^ 2 / (128 * cDelta * ell0)))

theorem lowerAccuracyConstant_pos
    {ell0 c0 Cy P1 cDelta : ℝ}
    (hell0 : 0 < ell0) (hc0 : 0 < c0) (hCy : 0 < Cy)
    (hP1 : 0 < P1) (hcDelta : 0 < cDelta) :
    0 < lowerAccuracyConstant ell0 c0 Cy P1 cDelta := by
  unfold lowerAccuracyConstant
  exact lt_min
    (div_pos hc0 (by positivity))
    (lt_min zero_lt_one (div_pos (sq_pos_of_pos hc0) (by positivity)))

/-- The headline condition
`eps ≤ c' * min (ell * D) (sqrt (ell * Delta))`, with the explicit `c'`
above, implies exactly the two hypotheses of `ass:lower-size`. -/
theorem lower_size_regime_of_accuracy
    {ell D Delta eps ell0 c0 Cy P1 cDelta : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps) (hell0 : 0 < ell0) (hc0 : 0 < c0)
    (hCy : 0 < Cy) (hP1 : 0 < P1) (hcDelta : 0 < cDelta)
    (haccuracy : eps ≤ lowerAccuracyConstant ell0 c0 Cy P1 cDelta *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    20 ≤ c0 * ell * D / (8 * Cy * P1 * ell0 * eps) ∧
      4 ≤ c0 ^ 2 * ell * Delta /
        (32 * cDelta * ell0 * eps ^ 2) := by
  let c' := lowerAccuracyConstant ell0 c0 Cy P1 cDelta
  have hc' : 0 < c' := lowerAccuracyConstant_pos hell0 hc0 hCy hP1 hcDelta
  have hcA : c' ≤ c0 / (160 * Cy * P1 * ell0) := by
    dsimp [c']
    exact min_le_left _ _
  have hcOne : c' ≤ 1 := by
    dsimp [c', lowerAccuracyConstant]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hcQ : c' ≤ c0 ^ 2 / (128 * cDelta * ell0) := by
    dsimp [c', lowerAccuracyConstant]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have haccD : eps ≤ c' * (ell * D) := by
    calc
      eps ≤ c' * min (ell * D) (Real.sqrt (ell * Delta)) := haccuracy
      _ ≤ c' * (ell * D) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hc'.le
  have haccRoot : eps ≤ c' * Real.sqrt (ell * Delta) := by
    calc
      eps ≤ c' * min (ell * D) (Real.sqrt (ell * Delta)) := haccuracy
      _ ≤ c' * Real.sqrt (ell * Delta) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hc'.le
  constructor
  · have hscaledA : c' * (ell * D) ≤
        (c0 / (160 * Cy * P1 * ell0)) * (ell * D) :=
      mul_le_mul_of_nonneg_right hcA (mul_nonneg hell.le hD.le)
    have hepsBound : eps ≤
        (c0 / (160 * Cy * P1 * ell0)) * (ell * D) :=
      haccD.trans hscaledA
    have hden : 0 < 160 * Cy * P1 * ell0 := by positivity
    have hepsBound' : eps ≤
        (c0 * ell * D) / (160 * Cy * P1 * ell0) := by
      calc
        eps ≤ (c0 / (160 * Cy * P1 * ell0)) * (ell * D) := hepsBound
        _ = (c0 * ell * D) / (160 * Cy * P1 * ell0) := by ring
    have hmul := (le_div_iff₀ hden).mp hepsBound'
    rw [le_div_iff₀ (by positivity : 0 < 8 * Cy * P1 * ell0 * eps)]
    nlinarith
  · have hS : 0 ≤ ell * Delta := mul_nonneg hell.le hDelta.le
    have hsqrt : 0 ≤ Real.sqrt (ell * Delta) := Real.sqrt_nonneg _
    have hrootNonneg : 0 ≤ c' * Real.sqrt (ell * Delta) :=
      mul_nonneg hc'.le hsqrt
    have hepsSqRoot : eps ^ 2 ≤
        (c' * Real.sqrt (ell * Delta)) ^ 2 := by
      nlinarith [sq_nonneg (c' * Real.sqrt (ell * Delta) - eps)]
    have hcSq : c' ^ 2 ≤ c0 ^ 2 / (128 * cDelta * ell0) := by
      have hself : c' ^ 2 ≤ c' := by nlinarith
      exact hself.trans hcQ
    have hepsSq : eps ^ 2 ≤
        (c0 ^ 2 / (128 * cDelta * ell0)) * (ell * Delta) := by
      calc
        eps ^ 2 ≤ (c' * Real.sqrt (ell * Delta)) ^ 2 := hepsSqRoot
        _ = c' ^ 2 * (ell * Delta) := by
          rw [mul_pow, Real.sq_sqrt hS]
        _ ≤ (c0 ^ 2 / (128 * cDelta * ell0)) * (ell * Delta) :=
          mul_le_mul_of_nonneg_right hcSq hS
    rw [le_div_iff₀ (by positivity :
      0 < 32 * cDelta * ell0 * eps ^ 2)]
    have hden : 0 < 128 * cDelta * ell0 := by positivity
    have hepsSq' : eps ^ 2 ≤
        (c0 ^ 2 * ell * Delta) / (128 * cDelta * ell0) := by
      calc
        eps ^ 2 ≤ (c0 ^ 2 / (128 * cDelta * ell0)) *
            (ell * Delta) := hepsSq
        _ = (c0 ^ 2 * ell * Delta) / (128 * cDelta * ell0) := by ring
    have hmul := (le_div_iff₀ hden).mp hepsSq'
    nlinarith

/-- The same explicit headline accuracy hypothesis also implies both
nontrivial-regime assumptions used by the log-free upper corollary. -/
theorem lower_accuracy_implies_logFree_regime
    {ell D Delta eps ell0 c0 Cy P1 cDelta : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps) (hell0 : 0 < ell0) (hc0 : 0 < c0)
    (hCy : 0 < Cy) (hP1 : 0 < P1) (hcDelta : 0 < cDelta)
    (haccuracy : eps ≤ lowerAccuracyConstant ell0 c0 Cy P1 cDelta *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    eps ≤ ell * D ∧ (1 / 4 : ℝ) ≤ ell * Delta / eps ^ 2 := by
  let c' := lowerAccuracyConstant ell0 c0 Cy P1 cDelta
  have hc' : 0 < c' := lowerAccuracyConstant_pos hell0 hc0 hCy hP1 hcDelta
  have hcOne : c' ≤ 1 := by
    dsimp [c', lowerAccuracyConstant]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have haccD : eps ≤ c' * (ell * D) := by
    exact haccuracy.trans
      (mul_le_mul_of_nonneg_left (min_le_left _ _) hc'.le)
  have hepsD : eps ≤ ell * D := by
    calc
      eps ≤ c' * (ell * D) := haccD
      _ ≤ 1 * (ell * D) :=
        mul_le_mul_of_nonneg_right hcOne (mul_nonneg hell.le hD.le)
      _ = ell * D := one_mul _
  have haccRoot : eps ≤ c' * Real.sqrt (ell * Delta) := by
    exact haccuracy.trans
      (mul_le_mul_of_nonneg_left (min_le_right _ _) hc'.le)
  have hsqrt : 0 ≤ Real.sqrt (ell * Delta) := Real.sqrt_nonneg _
  have hepsSq : eps ^ 2 ≤
      (c' * Real.sqrt (ell * Delta)) ^ 2 := by
    nlinarith [sq_nonneg (c' * Real.sqrt (ell * Delta) - eps)]
  have hcSq : c' ^ 2 ≤ 1 := by nlinarith [sq_nonneg (c' - 1)]
  have hellDelta : 0 ≤ ell * Delta := mul_nonneg hell.le hDelta.le
  have hepsSqFinal : eps ^ 2 ≤ ell * Delta := by
    calc
      eps ^ 2 ≤ (c' * Real.sqrt (ell * Delta)) ^ 2 := hepsSq
      _ = c' ^ 2 * (ell * Delta) := by
        rw [mul_pow, Real.sq_sqrt hellDelta]
      _ ≤ 1 * (ell * Delta) :=
        mul_le_mul_of_nonneg_right hcSq hellDelta
      _ = ell * Delta := one_mul _
  constructor
  · exact hepsD
  · rw [le_div_iff₀ (sq_pos_of_pos heps)]
    nlinarith

end

end NCCLowerBoundVerification
