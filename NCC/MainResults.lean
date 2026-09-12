import NCC.Lower.DeterministicLower
import NCC.Upper.Theorem
import NCC.Oracle.PositiveDimension

/-!
# Matching deterministic complexity for the current source class

Both sides refer to the same infimum-over-causal-algorithms and
supremum-over-within-domain-instances quantity. The hard instance,
derivatives, query transcripts, and upper program are genuine checked
objects, not assumed certificate interfaces.

`source_matching_oracle_complexity` uses exactly the manuscript's positive
primal and dual dimensions. The older `matching_oracle_complexity` is
retained for the enlarged helper class that also allows zero dimensions.
-/
namespace NCC.MainResults
noncomputable section
open Lower.Parameters Lower.Certificates

theorem accuracyConstant_le_one : c0 constants ≤ 1 := by
  have hy : 1 ≤ Construction.Terminal.c_y := by
    nlinarith [Construction.Terminal.c_y_pos, Construction.Terminal.c_y_sq]
  have hcd : constants.cD ≤ 1 := by
    change 1 / (40 * Construction.Terminal.c_y) ≤ 1
    apply (div_le_iff₀ (by positivity)).2
    linarith
  have hg := constants.g0_le
  have hg0 := constants.g0_pos
  have hl := constants.ell0_pos
  apply (min_le_left _ _).trans
  apply (div_le_iff₀ (by positivity : 0 < 80 * constants.ell0)).2
  have hc := mul_le_mul_of_nonneg_right hcd hg0.le
  nlinarith

theorem accuracy_implies_rate_regime {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 constants * min (ell * D) (Real.sqrt (ell * Delta))) :
    eps ≤ ell * D ∧ eps ^ 2 ≤ ell * Delta := by
  have hmin : 0 ≤ min (ell * D) (Real.sqrt (ell * Delta)) := by positivity
  have hc := mul_le_mul_of_nonneg_right accuracyConstant_le_one hmin
  have he : eps ≤ min (ell * D) (Real.sqrt (ell * Delta)) := by linarith
  refine ⟨he.trans (min_le_left _ _), ?_⟩
  have hs := he.trans (min_le_right _ _)
  have hroot := Real.sq_sqrt (mul_pos hell hDelta).le
  nlinarith [Real.sqrt_nonneg (ell * Delta)]

theorem uniformRate_le_cubic {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 constants * min (ell * D) (Real.sqrt (ell * Delta))) :
    Upper.Theorem.uniformRate ell D Delta eps ≤
      2 * (ell ^ 2 * D * Delta / eps ^ 3) := by
  obtain ⟨hB, hA⟩ := accuracy_implies_rate_regime hell hD hDelta heps hacc
  have hBb : 1 ≤ ell * D / eps := (one_le_div heps).2 hB
  have hAb : 1 ≤ ell * Delta / eps ^ 2 := (one_le_div (sq_pos_of_pos heps)).2 hA
  have hmul := mul_le_mul_of_nonneg_right
    (show ell * Delta / eps ^ 2 + 1 ≤ 2 * (ell * Delta / eps ^ 2) by linarith)
    (by positivity : 0 ≤ ell * D / eps)
  unfold Upper.Theorem.uniformRate
  rw [max_eq_right hBb]
  calc
    _ ≤ 2 * (ell * Delta / eps ^ 2) * (ell * D / eps) := hmul
    _ = _ := by field_simp

/-- The common regime from the current deterministic lower theorem gives
matching upper and lower bounds with numerical constants. -/
theorem matching_oracle_complexity {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 constants * min (ell * D) (Real.sqrt (ell * Delta))) :
    ENNReal.ofReal (c1 constants * (ell ^ 2 * D * Delta / eps ^ 3)) ≤
      Complexity.minimaxOracleComplexity ell D Delta eps ∧
    Complexity.minimaxOracleComplexity ell D Delta eps ≤
      ENNReal.ofReal ((2 * (Upper.CurrentCost.traceRateConstant + 3)) *
        (ell ^ 2 * D * Delta / eps ^ 3)) := by
  refine ⟨Lower.DeterministicLower.current_deterministic_lower hell hD hDelta heps hacc, ?_⟩
  apply (Upper.Theorem.minimaxOracleComplexity_upper hell hD hDelta heps).trans
  apply ENNReal.ofReal_le_ofReal
  have hc : 0 ≤ Upper.CurrentCost.traceRateConstant + 3 := by
    linarith [Upper.CurrentCost.traceRateConstant_pos]
  have hb := mul_le_mul_of_nonneg_left (uniformRate_le_cubic hell hD hDelta heps hacc) hc
  nlinarith

/-- Matching cubic bounds for the exact positive-dimensional source class,
with one objective-independent algorithm family on its known domains. -/
theorem source_matching_oracle_complexity {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 constants * min (ell * D) (Real.sqrt (ell * Delta))) :
    ENNReal.ofReal (c1 constants * (ell ^ 2 * D * Delta / eps ^ 3)) ≤
      Complexity.PositiveDimension.minimaxOracleComplexity ell D Delta eps ∧
    Complexity.PositiveDimension.minimaxOracleComplexity ell D Delta eps ≤
      ENNReal.ofReal ((2 * (Upper.CurrentCost.traceRateConstant + 3)) *
        (ell ^ 2 * D * Delta / eps ^ 3)) := by
  refine ⟨Complexity.PositiveDimension.oracleComplexity_lower hell hD hDelta heps hacc, ?_⟩
  apply (Complexity.PositiveDimension.oracleComplexity_upper hell hD hDelta heps).trans
  apply ENNReal.ofReal_le_ofReal
  have hc : 0 ≤ Upper.CurrentCost.traceRateConstant + 3 := by
    linarith [Upper.CurrentCost.traceRateConstant_pos]
  have hb := mul_le_mul_of_nonneg_left (uniformRate_le_cubic hell hD hDelta heps hacc) hc
  nlinarith

end
end NCC.MainResults
