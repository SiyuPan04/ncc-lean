import NCCLowerBoundVerification.Upper.HomotopySchedule
import NCCLowerBoundVerification.Upper.BlockCostConcrete

/-!
# Geometric cost of all homotopy stages

Although the number of curvature stages is logarithmic, their condition
numbers form a geometric series.  The exact estimates below show that the
total cost is controlled by the final stage, without an extra logarithm.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace HomotopyCost

noncomputable section

open Tracking RelativeFOAM BlockCostConcrete

def stageCondition (mu r0 : ℝ) (j : Nat) : ℝ :=
  Real.sqrt (mu / Tracking.curvature r0 j)

theorem curvature_pos {r0 : ℝ} (hr0 : 0 < r0) (j : Nat) :
    0 < Tracking.curvature r0 j := by
  unfold Tracking.curvature
  positivity

theorem stageCondition_succ {mu r0 : ℝ}
    (hmu : 0 < mu) (hr0 : 0 < r0) (j : Nat) :
    stageCondition mu r0 (j + 1) = 2 * stageCondition mu r0 j := by
  have hrj : 0 < Tracking.curvature r0 j := curvature_pos hr0 j
  have hratio : mu / (Tracking.curvature r0 j / 4) =
      4 * (mu / Tracking.curvature r0 j) := by
    field_simp [ne_of_gt hrj]
  unfold stageCondition
  rw [Tracking.curvature_succ, hratio,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num

theorem homotopy_condition_sum_le {mu r0 : ℝ}
    (hmu : 0 < mu) (hr0 : 0 < r0) (J : Nat) :
    (∑ j ∈ Finset.range J, stageCondition mu r0 (j + 1)) ≤
      2 * stageCondition mu r0 J := by
  induction J with
  | zero =>
      simp [stageCondition]
  | succ J ih =>
      rw [Finset.sum_range_succ]
      have hrec := stageCondition_succ hmu hr0 J
      rw [hrec]
      nlinarith

def homotopyOracleCalls (mu r0 rho : ℝ) (J : Nat) : Nat :=
  ∑ j ∈ Finset.range J,
    (feasibleBlockCost mu (Tracking.curvature r0 (j + 1)) rho).oracleCalls

def homotopyProjections (mu r0 rho : ℝ) (J : Nat) : Nat :=
  ∑ j ∈ Finset.range J,
    (feasibleBlockCost mu (Tracking.curvature r0 (j + 1)) rho).projections

/-- Both total resource counts are at most twice the final-stage
`sqrt(mu/r_J)` cost. -/
theorem homotopy_total_cost_le {mu r0 rho : ℝ}
    (hmu : 0 < mu) (hr0 : 0 < r0) (hr0mu : r0 ≤ mu / 8)
    (hrho : 0 < rho) (hrho1 : rho < 1) (J : Nat) :
    let C := (2 * Real.log (1 / rho) + 1) *
      (ProjectedMicro.feasibleMicroIterations + 1 : ℝ)
    (homotopyOracleCalls mu r0 rho J : ℝ) ≤
        2 * C * stageCondition mu r0 J ∧
      (homotopyProjections mu r0 rho J : ℝ) ≤
        2 * C * stageCondition mu r0 J := by
  dsimp
  let C := (2 * Real.log (1 / rho) + 1) *
    (ProjectedMicro.feasibleMicroIterations + 1 : ℝ)
  have hlog : 0 < Real.log (1 / rho) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hrho).2 (by simpa using hrho1)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hstage (j : Nat) (hj : j ∈ Finset.range J) :
      let rj := Tracking.curvature r0 (j + 1)
      ((feasibleBlockCost mu rj rho).oracleCalls : ℝ) ≤
          C * stageCondition mu r0 (j + 1) ∧
        ((feasibleBlockCost mu rj rho).projections : ℝ) ≤
          C * stageCondition mu r0 (j + 1) := by
    dsimp
    have hrj : 0 < Tracking.curvature r0 (j + 1) :=
      curvature_pos hr0 (j + 1)
    have hrj0 : Tracking.curvature r0 (j + 1) ≤ r0 := by
      unfold Tracking.curvature
      exact Tracking.div_pow_le_self hr0.le (by norm_num) (j + 1)
    have hcost := feasibleBlockCost_lt_sqrt_ratio hmu hrj
      (hrj0.trans hr0mu) hrho hrho1
    constructor
    · simpa [C, stageCondition] using hcost.1.le
    · simpa [C, stageCondition] using hcost.2.le
  have horacle : (homotopyOracleCalls mu r0 rho J : ℝ) ≤
      ∑ j ∈ Finset.range J, C * stageCondition mu r0 (j + 1) := by
    unfold homotopyOracleCalls
    push_cast
    exact Finset.sum_le_sum fun j hj ↦ (hstage j hj).1
  have hprojection : (homotopyProjections mu r0 rho J : ℝ) ≤
      ∑ j ∈ Finset.range J, C * stageCondition mu r0 (j + 1) := by
    unfold homotopyProjections
    push_cast
    exact Finset.sum_le_sum fun j hj ↦ (hstage j hj).2
  have hsum := homotopy_condition_sum_le hmu hr0 J
  have hscaled := mul_le_mul_of_nonneg_left hsum hC
  rw [Finset.mul_sum] at hscaled
  constructor <;> nlinarith

end

end HomotopyCost
end Upper
end NCCLowerBoundVerification
