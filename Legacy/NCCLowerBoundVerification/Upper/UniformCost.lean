import NCCLowerBoundVerification.Upper.UniformTheorem

/-!
# Explicit oracle and projection count for the uniform upper theorem

The homotopy has logarithmically many stages, but their square-root condition
numbers form a geometric sum.  This file combines that sum with the literal
outer ceiling horizon and gives one numerical constant multiplying the
paper's uniform rate.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace UniformCost

noncomputable section

open RelativeFOAM HomotopyCost BlockCostConcrete
open OuterTrajectoryConcrete HomotopySchedule UniformSchedule

def blockConstant (rho : ℝ) : ℝ :=
  (2 * Real.log (1 / rho) + 1) *
    (ProjectedMicro.feasibleMicroIterations + 1 : ℝ)

def uniformCostConstant : ℝ :=
  4501 * (6 * blockConstant (1 / 400) + 1) +
    12 * blockConstant (1 / 8)

theorem blockConstant_pos {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    0 < blockConstant rho := by
  unfold blockConstant
  have hlog : 0 < Real.log (1 / rho) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hrho).2 (by simpa using hrho1)
  positivity

theorem uniformCostConstant_pos : 0 < uniformCostConstant := by
  have h400 : 0 < blockConstant (1 / 400) :=
    blockConstant_pos (by norm_num) (by norm_num)
  have h8 : 0 < blockConstant (1 / 8) :=
    blockConstant_pos (by norm_num) (by norm_num)
  unfold uniformCostConstant
  positivity

def assembledCost (ell r0 r : ℝ) (J T : Nat) : Cost where
  oracleCalls := homotopyOracleCalls ell r0 (1 / 8) J +
    (outerTrajectoryCost ell r T ProjectedMicro.feasibleMicroIterations).oracleCalls
  projections := homotopyProjections ell r0 (1 / 8) J +
    (outerTrajectoryCost ell r T ProjectedMicro.feasibleMicroIterations).projections

/-- Both resources used by the literal schedule are bounded by the same
explicit numerical multiple of the uniform rate. -/
theorem assembledCost_uniform_bound
    {ell D Delta eps target r : ℝ} {J T : Nat}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (htarget : target = targetCurvature ell D eps)
    (hJ : J = homotopyStage (ell / 8) target
      (div_pos hell (by norm_num))
      (by simpa [htarget] using targetCurvature_pos hell hD heps))
    (hr : r = Tracking.curvature (ell / 8) J)
    (hT : T = paperOuterIterations ell Delta r D eps) :
    let rate := (ell * Delta / eps ^ 2 + 1) *
      max 1 (ell * D / eps)
    ((assembledCost ell (ell / 8) r J T).oracleCalls : ℝ) ≤
        uniformCostConstant * rate ∧
      ((assembledCost ell (ell / 8) r J T).projections : ℝ) ≤
        uniformCostConstant * rate := by
  dsimp
  subst target
  subst J
  let target := targetCurvature ell D eps
  have htargetPos : 0 < target := targetCurvature_pos hell hD heps
  let J := homotopyStage (ell / 8) target
    (div_pos hell (by norm_num)) htargetPos
  subst r
  let r := Tracking.curvature (ell / 8) J
  subst T
  let T := paperOuterIterations ell Delta r D eps
  let A := ell * Delta / eps ^ 2
  let M := max 1 (ell * D / eps)
  let C400 := blockConstant (1 / 400)
  let C8 := blockConstant (1 / 8)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hM : 1 ≤ M := by dsimp [M]; exact le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hAp : 1 ≤ A + 1 := by linarith
  have hrate0 : 0 ≤ (A + 1) * M := mul_nonneg (by linarith) hM0
  have hcompare := homotopyStage_target_comparison_total
    (div_pos hell (by norm_num)) htargetPos
    (targetCurvature_le_ell_div_eight
      (ell := ell) (D := D) (eps := eps))
  have hrlower : target / 4 < r := by simpa [J, r] using hcompare.1
  have hrupper : r ≤ target := by simpa [J, r] using hcompare.2
  have hrpos : 0 < r := by
    dsimp [r]
    exact curvature_pos (div_pos hell (by norm_num)) J
  have hrle : r ≤ ell / 8 :=
    hrupper.trans (targetCurvature_le_ell_div_eight
      (ell := ell) (D := D) (eps := eps))
  have hsqrt : Real.sqrt (ell / r) < 6 * M := by
    simpa [M] using sqrt_ratio_lt_six_max hell hD heps hrpos hrlower
  have hC400 : 0 < C400 := by
    dsimp [C400]
    exact blockConstant_pos (by norm_num) (by norm_num)
  have hC8 : 0 < C8 := by
    dsimp [C8]
    exact blockConstant_pos (by norm_num) (by norm_num)
  have hblock := feasibleBlockCost_lt_sqrt_ratio hell hrpos hrle
    (by norm_num : (0 : ℝ) < 1 / 400)
    (by norm_num : (1 / 400 : ℝ) < 1)
  have hblockOracle :
      ((feasibleBlockCost ell r (1 / 400)).oracleCalls : ℝ) ≤
        6 * C400 * M := by
    exact (calc
      _ < C400 * Real.sqrt (ell / r) := by simpa [C400, blockConstant] using hblock.1
      _ < C400 * (6 * M) :=
        mul_lt_mul_of_pos_left hsqrt hC400
      _ = 6 * C400 * M := by ring).le
  have hblockProjection :
      ((feasibleBlockCost ell r (1 / 400)).projections : ℝ) ≤
        6 * C400 * M := by
    exact (calc
      _ < C400 * Real.sqrt (ell / r) := by simpa [C400, blockConstant] using hblock.2
      _ < C400 * (6 * M) :=
        mul_lt_mul_of_pos_left hsqrt hC400
      _ = 6 * C400 * M := by ring).le
  have hrD : r * D ^ 2 ≤ eps ^ 2 / (8 * ell) := by
    have ht := hrupper.trans (targetCurvature_le_bias_branch
      (ell := ell) (D := D) (eps := eps))
    have hmul := mul_le_mul_of_nonneg_right ht (sq_nonneg D)
    calc
      r * D ^ 2 ≤ (eps ^ 2 / (8 * ell * D ^ 2)) * D ^ 2 := hmul
      _ = eps ^ 2 / (8 * ell) := by field_simp [hell.ne', hD.ne']
  have hTraw := paperOuterIterations_lt_gap_bound hell hDelta.le
    hrpos.le heps hrD
  have hTbound : (T : ℝ) ≤ 4501 * (A + 1) := by
    have hTrawA : (T : ℝ) < 4000 * A + 501 := by
      dsimp [T, A]
      convert hTraw using 1 <;> ring
    exact (calc
      (T : ℝ) < 4000 * A + 501 := hTrawA
      _ < 4501 * (A + 1) := by nlinarith).le
  have hT0 : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
  have houterOracle :
      ((outerTrajectoryCost ell r T ProjectedMicro.feasibleMicroIterations).oracleCalls : ℝ) ≤
        (4501 * (6 * C400 + 1)) * ((A + 1) * M) := by
    rw [outerTrajectoryCost_oracleCalls]
    push_cast
    have hprod := mul_le_mul hTbound hblockOracle
      (by positivity : 0 ≤ ((feasibleBlockCost ell r (1 / 400)).oracleCalls : ℝ))
      (by positivity : 0 ≤ 4501 * (A + 1))
    have hone : 1 ≤ (A + 1) * M := by
      calc
        1 = 1 * 1 := by ring
        _ ≤ (A + 1) * M := mul_le_mul hAp hM (by norm_num) (by linarith)
    calc
      (T : ℝ) * blockIterations (alpha ell r) (1 / 400) *
            (ProjectedMicro.feasibleMicroIterations + 1) + 1 =
          (T : ℝ) *
            ((feasibleBlockCost ell r (1 / 400)).oracleCalls : ℝ) + 1 := by
              simp [feasibleBlockCost]
              ring
      _ ≤ (4501 * (A + 1)) * (6 * C400 * M) + 1 := by
        simpa [add_comm] using add_le_add_right hprod 1
      _ ≤ (4501 * (6 * C400 + 1)) * ((A + 1) * M) := by
        nlinarith [mul_nonneg (by linarith : 0 ≤ A + 1) hM0]
  have houterProjection :
      ((outerTrajectoryCost ell r T ProjectedMicro.feasibleMicroIterations).projections : ℝ) ≤
        (4501 * (6 * C400 + 1)) * ((A + 1) * M) := by
    rw [outerTrajectoryCost_projections]
    push_cast
    have hblockPlus :
        ((feasibleBlockCost ell r (1 / 400)).projections : ℝ) + 1 ≤
          (6 * C400 + 1) * M := by
      nlinarith
    have hprod := mul_le_mul hTbound hblockPlus
      (by positivity : 0 ≤ ((feasibleBlockCost ell r (1 / 400)).projections : ℝ) + 1)
      (by positivity : 0 ≤ 4501 * (A + 1))
    calc
      (T : ℝ) *
          (blockIterations (alpha ell r) (1 / 400) *
            (ProjectedMicro.feasibleMicroIterations + 1) + 1) =
          (T : ℝ) *
            (((feasibleBlockCost ell r (1 / 400)).projections : ℝ) + 1) := by
              simp [feasibleBlockCost]
      _ ≤ (4501 * (A + 1)) * ((6 * C400 + 1) * M) := hprod
      _ = (4501 * (6 * C400 + 1)) * ((A + 1) * M) := by ring
  have hhom := homotopy_total_cost_le hell
    (div_pos hell (by norm_num)) (le_rfl)
    (by norm_num : (0 : ℝ) < 1 / 8)
    (by norm_num : (1 / 8 : ℝ) < 1) J
  have hhomOracle : (homotopyOracleCalls ell (ell / 8) (1 / 8) J : ℝ) ≤
      12 * C8 * ((A + 1) * M) := by
    calc
      _ ≤ 2 * C8 * Real.sqrt (ell / r) := by
        simpa [C8, blockConstant, stageCondition, r] using hhom.1
      _ ≤ 2 * C8 * (6 * M) :=
        mul_le_mul_of_nonneg_left hsqrt.le (by positivity)
      _ = 12 * C8 * M := by ring
      _ ≤ 12 * C8 * ((A + 1) * M) := by
        have := mul_le_mul_of_nonneg_right hAp hM0
        nlinarith
  have hhomProjection : (homotopyProjections ell (ell / 8) (1 / 8) J : ℝ) ≤
      12 * C8 * ((A + 1) * M) := by
    calc
      _ ≤ 2 * C8 * Real.sqrt (ell / r) := by
        simpa [C8, blockConstant, stageCondition, r] using hhom.2
      _ ≤ 2 * C8 * (6 * M) :=
        mul_le_mul_of_nonneg_left hsqrt.le (by positivity)
      _ = 12 * C8 * M := by ring
      _ ≤ 12 * C8 * ((A + 1) * M) := by
        have := mul_le_mul_of_nonneg_right hAp hM0
        nlinarith
  constructor
  · unfold assembledCost
    push_cast
    calc
      _ ≤ 12 * C8 * ((A + 1) * M) +
          (4501 * (6 * C400 + 1)) * ((A + 1) * M) := by
        convert add_le_add hhomOracle houterOracle using 1
      _ = uniformCostConstant * ((A + 1) * M) := by
        dsimp [uniformCostConstant, C400, C8]
        ring
      _ = uniformCostConstant *
          ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) := by
        rfl
  · unfold assembledCost
    push_cast
    calc
      _ ≤ 12 * C8 * ((A + 1) * M) +
          (4501 * (6 * C400 + 1)) * ((A + 1) * M) := by
        convert add_le_add hhomProjection houterProjection using 1
      _ = uniformCostConstant * ((A + 1) * M) := by
        dsimp [uniformCostConstant, C400, C8]
        ring
      _ = uniformCostConstant *
          ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) := by
        rfl

end

end UniformCost
end Upper
end NCCLowerBoundVerification
