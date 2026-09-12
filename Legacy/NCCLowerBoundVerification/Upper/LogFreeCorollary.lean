import NCCLowerBoundVerification.Upper.MainTheorem

/-!
# The nontrivial-regime log-free corollary

This file expands the final `O(ell^2 D Delta / eps^3)` simplification in the
paper.  In particular, the two regime hypotheses are used explicitly; no
asymptotic-notation step is left implicit.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace LogFreeCorollary

noncomputable section

open MainTheorem UniformSchedule HomotopySchedule

def logFreeCostConstant : ℝ :=
  5 * UniformCost.uniformCostConstant

theorem logFreeCostConstant_pos : 0 < logFreeCostConstant := by
  unfold logFreeCostConstant
  exact mul_pos (by norm_num) UniformCost.uniformCostConstant_pos

/-- The uniform rate reduces to the headline cubic-accuracy rate under the
two hypotheses printed in `ub:cor:log-free`. -/
theorem uniform_rate_le_logFree
    {ell D Delta eps : ℝ} (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hepsD : eps ≤ ell * D)
    (hgap : (1 / 4 : ℝ) ≤ ell * Delta / eps ^ 2) :
    (ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps) ≤
      5 * (ell ^ 2 * D * Delta / eps ^ 3) := by
  let A := ell * Delta / eps ^ 2
  let M := ell * D / eps
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hM : 1 ≤ M := by
    dsimp [M]
    exact (le_div_iff₀ heps).2 (by simpa using hepsD)
  have hAplus : A + 1 ≤ 5 * A := by
    have hgapA : (1 / 4 : ℝ) ≤ A := by simpa [A] using hgap
    nlinarith
  have hmul : (A + 1) * M ≤ (5 * A) * M :=
    mul_le_mul_of_nonneg_right hAplus (zero_le_one.trans hM)
  have hidentity : A * M = ell ^ 2 * D * Delta / eps ^ 3 := by
    dsimp [A, M]
    field_simp [heps.ne']
  rw [max_eq_right hM]
  calc
    (ell * Delta / eps ^ 2 + 1) * (ell * D / eps) =
        (A + 1) * M := rfl
    _ ≤ (5 * A) * M := hmul
    _ = 5 * (ell ^ 2 * D * Delta / eps ^ 3) := by
      rw [← hidentity]
      ring

/-- Corollary `ub:cor:log-free`, with one explicit numerical constant for
both first-order oracle calls and projections. -/
theorem log_free_upper_bound_of_class {m n : Nat}
    {ell D Delta eps : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (heps : 0 < eps)
    (hepsD : eps ≤ ell * D)
    (hgap : (1 / 4 : ℝ) ≤ ell * Delta / eps ^ 2) :
    (∃ x, IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps x) ∧
    (let target := targetCurvature ell D eps
     let J := homotopyStage (ell / 8) target
       (div_pos hP.ell_pos (by norm_num))
       (targetCurvature_pos hP.ell_pos hP.D_pos heps)
     let r := Tracking.curvature (ell / 8) J
     let T := paperOuterIterations ell Delta r D eps
     let headline := ell ^ 2 * D * Delta / eps ^ 3
     ((UniformCost.assembledCost ell (ell / 8) r J T).oracleCalls : ℝ) ≤
         logFreeCostConstant * headline ∧
       ((UniformCost.assembledCost ell (ell / 8) r J T).projections : ℝ) ≤
         logFreeCostConstant * headline) := by
  refine ⟨MainTheorem.exists_OS_of_class hP heps, ?_⟩
  dsimp only
  have hcost := MainTheorem.class_uniform_cost_bound hP heps
  dsimp only at hcost
  have hrate := uniform_rate_le_logFree hP.ell_pos hP.D_pos
    hP.Delta_pos heps hepsD hgap
  have hC : 0 ≤ UniformCost.uniformCostConstant :=
    UniformCost.uniformCostConstant_pos.le
  constructor
  · exact hcost.1.trans (by
      calc
        UniformCost.uniformCostConstant *
            ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) ≤
            UniformCost.uniformCostConstant *
              (5 * (ell ^ 2 * D * Delta / eps ^ 3)) :=
          mul_le_mul_of_nonneg_left hrate hC
        _ = logFreeCostConstant *
              (ell ^ 2 * D * Delta / eps ^ 3) := by
          unfold logFreeCostConstant
          ring)
  · exact hcost.2.trans (by
      calc
        UniformCost.uniformCostConstant *
            ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) ≤
            UniformCost.uniformCostConstant *
              (5 * (ell ^ 2 * D * Delta / eps ^ 3)) :=
          mul_le_mul_of_nonneg_left hrate hC
        _ = logFreeCostConstant *
              (ell ^ 2 * D * Delta / eps ^ 3) := by
          unfold logFreeCostConstant
          ring)

end

end LogFreeCorollary
end Upper
end NCCLowerBoundVerification
