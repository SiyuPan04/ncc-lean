import NCC.Upper.Selection

/-!
# Mathematical output guarantee for the current algorithm

This run uses the first successful projected micro test, the least geometric
stage reaching the current target, the reset budget `15 * (Delta + r * D²)`,
the current horizon, and the least-index minimizer of the current observable.
Its feasibility and optimization-stationarity conclusions follow from class
membership. No contraction, proximal existence, initial energy, or descent
premise is supplied by the caller.

The general statement permits the feasible datum `P.x0`. The final theorem
specializes it explicitly to the current printed initialization `P.x0 = 0`.
This file proves the mathematical output guarantee, not an oracle-program
implementation or an oracle-complexity theorem.
-/

namespace NCC.Upper.CurrentRun

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open OuterTrajectoryConcrete HomotopySchedule UniformSchedule InitialGapBounds
open AnalyticBridge

variable {m n : Nat} {ell D Delta eps : ℝ} {P : NCCInstance m n}

/-- First geometric regularization level reaching the current target. -/
def stage (hP : IsNCCClass ell D Delta P) (heps : 0 < eps) : Nat :=
  homotopyStage (ell / 8) (targetCurvature ell D eps)
    (div_pos hP.ell_pos (by norm_num))
    (targetCurvature_pos hP.ell_pos hP.D_pos heps)

def finalCurvature (hP : IsNCCClass ell D Delta P) (heps : 0 < eps) : ℝ :=
  Tracking.curvature (ell / 8) (stage hP heps)

theorem finalCurvature_pos (hP : IsNCCClass ell D Delta P) (heps : 0 < eps) :
    0 < finalCurvature hP heps :=
  HomotopyCost.curvature_pos (div_pos hP.ell_pos (by norm_num)) _

/-- Both sides of the literal final-curvature interval, including stage zero. -/
theorem finalCurvature_interval (hP : IsNCCClass ell D Delta P) (heps : 0 < eps) :
    targetCurvature ell D eps / 4 < finalCurvature hP heps ∧
      finalCurvature hP heps ≤ targetCurvature ell D eps :=
  homotopyStage_target_comparison_total
    (div_pos hP.ell_pos (by norm_num))
    (targetCurvature_pos hP.ell_pos hP.D_pos heps)
    targetCurvature_le_ell_div_eight

def initialSnapshot (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) : Snapshot (m := m) P.Y :=
  initializedSnapshot (D := D) (Delta := Delta)
    (firstStopSystemFamily hP) hzero (stage hP heps)

def output (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) : EVec m :=
  Selection.selectedAnchor (firstStopSystemFamily hP (stage hP heps))
    (initialSnapshot hP hzero heps) (Selection.outerIterations ell Delta eps)
    (Selection.outerIterations_pos hP.ell_pos hP.Delta_pos)

theorem initialSnapshot_z (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    (initialSnapshot hP hzero heps).z = P.x0 := rfl

theorem initialSnapshot_budget (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    (initialSnapshot hP hzero heps).B =
      15 * (Delta + finalCurvature hP heps * D ^ 2) := rfl

theorem output_mem (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    output hP hzero heps ∈ P.X :=
  Selection.selectedAnchor_mem _ _ hP.x0_mem _ _

/-- OS for the exact current mathematical output, with all analytic data
constructed from the NC–C class. The legacy OS predicate is accompanied
by the separate `output_mem` theorem to supply the feasible-anchor clause. -/
theorem output_is_OS (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (output hP hzero heps) := by
  let J := stage hP heps
  let r := finalCurvature hP heps
  let sys := firstStopSystemFamily hP J
  let R0 := initialSnapshot hP hzero heps
  let T := Selection.outerIterations ell Delta eps
  have hr : 0 < r := finalCurvature_pos hP heps
  have hrupper : r ≤ targetCurvature ell D eps :=
    (finalCurvature_interval hP heps).2
  have hrle : r ≤ ell / 8 := hrupper.trans targetCurvature_le_ell_div_eight
  have hE0 : snapshotEnergy sys R0 ≤ R0.B :=
    initializedSnapshot_energy hP hzero (firstStopSystemFamily hP) J
  have hB0 : 0 ≤ R0.B := by
    change 0 ≤ 15 * (Delta + r * D ^ 2)
    exact mul_nonneg (by norm_num)
      (add_nonneg hP.Delta_pos.le (mul_nonneg hr.le (sq_nonneg D)))
  have hT : 0 < T := Selection.outerIterations_pos hP.ell_pos hP.Delta_pos
  have hweakR : IsWeaklyConvexOn ell P.X (DualRegularizedValueOn P.Y P.f r) :=
    NCCLowerBoundVerification.Upper.IsNCCClass.regularizedValue_weaklyConvex hP
  have hlower : ∀ z, regularizedClassLower P r D ≤
      regularizedEnvelope P.X P.Y P.f ell r (MainTheorem.classProxFamily hP J) z :=
    regularizedClassLower_le_envelope hP hzero hr.le hP.ell_pos.le _
  have hgrad := Selection.selected_regularized_gradient_bound
    hP.X_nonempty hP.ell_pos hr hrle hweakR sys R0 hE0 hB0 T hT
    (regularizedClassLower P r D) hlower
  have hpotential : snapshotPotential sys R0 - regularizedClassLower P r D ≤
      31 * (Delta + r * D ^ 2) :=
    initial_snapshot_potential_bound hP hzero hr.le sys R0 rfl le_rfl
  have hcoeff : 0 ≤ 32 * ell / (T : ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) hP.ell_pos.le) (Nat.cast_nonneg T)
  have hgradBudget :
      vecSq (residualGradient (MainTheorem.classProxFamily hP J)
        (output hP hzero heps)) ≤
        (32 * ell / (T : ℝ)) * (31 * (Delta + r * D ^ 2)) :=
    hgrad.trans (mul_le_mul_of_nonneg_left hpotential hcoeff)
  have hbiasBudget : 2 * ell * r * D ^ 2 ≤ eps ^ 2 / 4 :=
    homotopy_output_bias_budget hP.ell_pos hP.D_pos heps hr hrupper
  have hmass : ell * (r * D ^ 2) ≤ eps ^ 2 / 8 := by
    nlinarith
  have hreg :
      vecSq (residualGradient (MainTheorem.classProxFamily hP J)
        (output hP hzero heps)) < eps ^ 2 / 4 :=
    Selection.current_horizon_gradient_budget hP.ell_pos hP.Delta_pos heps
      hmass hgradBudget
  have hweak : IsWeaklyConvexOn ell P.X (ValueOn P.Y P.f) := by
    simpa [IsWeaklyConvexOn, quadraticCorrection] using hP.value_weakConvexity
  let hexists : HasProxEverywhere P.X (ValueOn P.Y P.f) ell :=
    NCCLowerBoundVerification.Upper.IsNCCClass.value_hasProxEverywhere hP
  have hYnorm : ∀ y ∈ P.Y, vecSq y ≤ D ^ 2 :=
    NCCLowerBoundVerification.Upper.IsNCCClass.dual_vecSq_le hP hzero
  have hmax : ∀ x, ∃ y, IsMaximizerOn P.Y P.f x y :=
    NCCLowerBoundVerification.Upper.IsNCCClass.maximum_attained_everywhere hP
  have hmaxR : ∀ x, ∃ y, IsMaximizerOn P.Y
      (fun u v => P.f u v - r / 2 * vecSq v) x y :=
    NCCLowerBoundVerification.Upper.IsNCCClass.regularized_maximum_attained hP
  have hbias := dualRegularizedValue_uniform_bias hr.le hYnorm hmax hmaxR
  have hdiff := residualGradient_regularization_vecSq_le hP.ell_pos hweak hweakR
    hexists (MainTheorem.classProxFamily hP J) hbias (output hP hzero heps)
  have hdiffSmall := hdiff.trans hbiasBudget
  let g := residualGradient hexists (output hP hzero heps)
  let gR := residualGradient (MainTheorem.classProxFamily hP J) (output hP hzero heps)
  have htriangle := ScaledOperator.vecSq_add_le_two (g - gR) gR
  have hsum : g - gR + gR = g := by abel
  rw [hsum] at htriangle
  have htrue : vecSq g ≤ eps ^ 2 :=
    Tracking.stationarity_from_smoothed_and_bias htriangle hdiffSmall hreg.le
  exact optimizationStationary_of_residualGradient hP.ell_pos heps.le hexists
    (output hP hzero heps) htrue

/-- Literal zero initialization and both clauses of the printed OS output.
This is an output theorem only; it does not claim the oracle-complexity
part of Theorem 3.3. -/
theorem current_algorithm_from_origin (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (hinit : P.x0 = 0) (heps : 0 < eps) :
    (initialSnapshot hP hzero heps).z = 0 ∧
      output hP hzero heps ∈ P.X ∧
      IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
        (output hP hzero heps) :=
  ⟨(initialSnapshot_z hP hzero heps).trans hinit,
    output_mem hP hzero heps, output_is_OS hP hzero heps⟩

end
end NCC.Upper.CurrentRun
