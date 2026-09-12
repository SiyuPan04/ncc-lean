import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Scalar algebra for the lower-bound terminal obstruction

This file verifies the scalar calculations in `main.tex`, specifically the
effective quadratic link, Lemma `lem:bounded-connector`, and Proposition
`prop:terminal-gradient`.

The analytic inputs are hypotheses, not conclusions of this file: existence
of a frontier state, the connector gradient formulas after the unconstrained
maximizer is shown feasible, the nonpositive regularizer derivative, and the
norm/inner-product estimates producing the connector inequality. In
particular, these theorems do not establish differentiability, feasibility of
the dual maximizer, or the lower bound for the complete constructed instance.
-/

namespace NCC.Lower

/-- The scalar effective link from equation `eq:effective-link`. This
definition does not assert that the inner maximization equals this link. -/
def effectiveLink (a b : ℝ) : ℝ := a ^ 2 - a * b + b ^ 2

theorem effectiveLink_completed_square (a b : ℝ) :
    effectiveLink a b = (a - b) ^ 2 / 2 + (a ^ 2 + b ^ 2) / 2 := by
  unfold effectiveLink
  ring

theorem effectiveLink_coercive (a b : ℝ) :
    (a ^ 2 + b ^ 2) / 2 ≤ effectiveLink a b := by
  rw [effectiveLink_completed_square]
  nlinarith only [sq_nonneg (a - b)]

theorem effectiveLink_nonneg (a b : ℝ) : 0 ≤ effectiveLink a b := by
  have h := effectiveLink_coercive a b
  nlinarith only [h, sq_nonneg a, sq_nonneg b]

/-- Exact first-order expansion, including the quadratic remainder.
No differentiation theorem is assumed or claimed by this identity. -/
theorem effectiveLink_increment (a b da db : ℝ) :
    effectiveLink (a + da) (b + db) - effectiveLink a b =
      (2 * a - b) * da + (2 * b - a) * db + effectiveLink da db := by
  unfold effectiveLink
  ring

/-- The component bounds used in the paper follow from the squared bound;
no square-root or norm library is needed for this scalar implication. -/
theorem components_of_small_squared_sum {ga gb : ℝ}
    (hsmall : ga ^ 2 + gb ^ 2 ≤ (1 / 4 : ℝ) ^ 2) :
    -(1 / 4 : ℝ) ≤ ga ∧ ga ≤ (1 / 4 : ℝ) ∧
      -(1 / 4 : ℝ) ≤ gb ∧ gb ≤ (1 / 4 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · nlinarith only [hsmall, sq_nonneg gb, sq_nonneg (ga + 1 / 4)]
  · nlinarith only [hsmall, sq_nonneg gb, sq_nonneg (ga - 1 / 4)]
  · nlinarith only [hsmall, sq_nonneg ga, sq_nonneg (gb + 1 / 4)]
  · nlinarith only [hsmall, sq_nonneg ga, sq_nonneg (gb - 1 / 4)]

/-- Solving the two frontier connector equations. The identification of
`ga` and `gb` with derivatives of the value function is an analytic input. -/
theorem frontier_connector_identity {a b s ga gb : ℝ}
    (hga : ga = 2 * a - b - 4) (hgb : gb = 2 * b - a - s) :
    b = (4 + 2 * s + ga + 2 * gb) / 3 := by
  linarith only [hga, hgb]

/-- The manuscript's stronger quantitative bound. Only the lower endpoint
of the low-state interval is needed for this arithmetic step. -/
theorem frontier_connector_gt_sixty_one_sixtieths {a b s ga gb : ℝ}
    (hs : -(1 / 10 : ℝ) < s)
    (hga : ga = 2 * a - b - 4) (hgb : gb = 2 * b - a - s)
    (hsmall : ga ^ 2 + gb ^ 2 ≤ (1 / 4 : ℝ) ^ 2) :
    (61 / 60 : ℝ) < b := by
  obtain ⟨hga_lower, _, hgb_lower, _⟩ :=
    components_of_small_squared_sum hsmall
  have hidentity := frontier_connector_identity hga hgb
  linarith only [hs, hga_lower, hgb_lower, hidentity]

/-- In the frontier interval `(-1/10, 1/5]`, a small connector gradient
forces `b > 1`. The upper endpoint is recorded to match the analytic input. -/
theorem frontier_connector_gt_one {a b s ga gb : ℝ}
    (hs : -(1 / 10 : ℝ) < s ∧ s ≤ (1 / 5 : ℝ))
    (hga : ga = 2 * a - b - 4) (hgb : gb = 2 * b - a - s)
    (hsmall : ga ^ 2 + gb ^ 2 ≤ (1 / 4 : ℝ) ^ 2) :
    1 < b := by
  have h := frontier_connector_gt_sixty_one_sixtieths hs.1 hga hgb hsmall
  linarith only [h]

/-- The scalar state derivative is strictly below `-1` once the connector
and regularizer derivative bounds are supplied. -/
theorem state_derivative_lt_neg_one {b regularizerDerivative : ℝ}
    (hb : 1 < b) (hregularizer : regularizerDerivative ≤ 0) :
    regularizerDerivative - b < -1 := by
  linarith only [hb, hregularizer]

/-- Combined frontier calculation. The regularizer derivative sign and
both connector derivative formulas remain explicit analytic assumptions. -/
theorem frontier_state_derivative_lt_neg_one
    {a b s ga gb regularizerDerivative : ℝ}
    (hs : -(1 / 10 : ℝ) < s ∧ s ≤ (1 / 5 : ℝ))
    (hga : ga = 2 * a - b - 4) (hgb : gb = 2 * b - a - s)
    (hsmall : ga ^ 2 + gb ^ 2 ≤ (1 / 4 : ℝ) ^ 2)
    (hregularizer : regularizerDerivative ≤ 0) :
    regularizerDerivative - b < -1 := by
  exact state_derivative_lt_neg_one
    (frontier_connector_gt_one hs hga hgb hsmall) hregularizer

/-- Scalar form of the final contradiction. The full gradient norm bound
must separately justify `hsmall` and the state-component bound `hstate`. -/
theorem frontier_small_gradient_impossible
    {a b s ga gb regularizerDerivative : ℝ}
    (hs : -(1 / 10 : ℝ) < s ∧ s ≤ (1 / 5 : ℝ))
    (hga : ga = 2 * a - b - 4) (hgb : gb = 2 * b - a - s)
    (hsmall : ga ^ 2 + gb ^ 2 ≤ (1 / 4 : ℝ) ^ 2)
    (hregularizer : regularizerDerivative ≤ 0)
    (hstate : (regularizerDerivative - b) ^ 2 ≤ (1 / 4 : ℝ) ^ 2) :
    False := by
  have hnegative :=
    frontier_state_derivative_lt_neg_one hs hga hgb hsmall hregularizer
  nlinarith only [hstate, hnegative,
    sq_nonneg (regularizerDerivative - b + 1 / 4)]

/-- The connector estimate after the analytic radial coercivity,
Cauchy-Schwarz, and outer-gradient estimates have supplied `hbound`.
The zero case is included by the nonnegative hypothesis on `v`. -/
theorem connector_norm_le {v : ℝ} (hv : 0 ≤ v)
    (hbound : (2 / 5 : ℝ) * v ^ 2 - 7 * v ≤ (1 / 4 : ℝ) * v) :
    v ≤ (145 / 8 : ℝ) := by
  rcases eq_or_lt_of_le hv with hzero | hpositive
  · rw [← hzero]
    norm_num
  · by_contra h
    have hlarge : (145 / 8 : ℝ) < v := lt_of_not_ge h
    have hproduct : 0 < v * (v - 145 / 8) :=
      mul_pos hpositive (by linarith only [hlarge])
    nlinarith only [hbound, hproduct]

theorem connector_norm_lt_twenty {v : ℝ} (hv : 0 ≤ v)
    (hbound : (2 / 5 : ℝ) * v ^ 2 - 7 * v ≤ (1 / 4 : ℝ) * v) :
    v < 20 := by
  have h := connector_norm_le hv hbound
  linarith only [h]

theorem connector_bound_constant_lt_twenty : (145 / 8 : ℝ) < 20 := by
  norm_num

end NCC.Lower
