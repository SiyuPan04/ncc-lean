import NCC.Upper.WithinRun

/-!
# Actual current-program execution and cost on the feasible-domain class

The exact objective-independent `CurrentProgram.program` is reused.
This file proves its genuine evaluation against the `WithinClass`
first-stop systems, and bounds its actual trace using the generic
all-branch compositional cap. There is no ambient-class conversion,
objective extension, or assumed execution correspondence.
-/
namespace NCC.Upper.WithinProgram
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open RelativeFOAM RelativeFOAMContraction ProjectionGeometry
open OuterTrajectoryConcrete HomotopyRun HomotopySchedule UniformSchedule
open SharedOracle AdaptiveMicroProgram AnalyticBridge CurrentProgram
open WithinSystem WithinFirstStop WithinRun
set_option maxHeartbeats 3000000
variable {m n : Nat} {ell D Delta eps r : ℝ} {P : NCCInstance m n}

theorem eval_macroStepProgram {D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) (S : ValidState (m := m) P.Y) :
    Oracle.Program.eval P
      (AdaptiveFOAMProgram.macroStepProgram (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S) =
      foamStep ell r ((firstStopSystemWithProx hP hr hrle hprox).oracle z)
        ((firstStopSystemWithProx hP hr hrle hprox).oracle_feasible z) S := by
  apply Subtype.ext
  simp only [AdaptiveFOAMProgram.macroStepProgram, Oracle.Program.eval_bind, Oracle.Program.eval_pure]
  rw [(WithinFirstStop.program_correct hP hr.le hrle z S.1).1]
  rfl

theorem eval_blockProgram {D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) (k : Nat) (S : ValidState (m := m) P.Y) :
    Oracle.Program.eval P
      (AdaptiveFOAMProgram.blockProgram (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z k S) =
      ((foamStep ell r ((firstStopSystemWithProx hP hr hrle hprox).oracle z)
        ((firstStopSystemWithProx hP hr hrle hprox).oracle_feasible z))^[k]) S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
      rw [AdaptiveFOAMProgram.blockProgram, Oracle.Program.eval_bind, ih, eval_macroStepProgram]
      rw [Function.iterate_succ_apply]

theorem eval_callProgram {D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) P.Y) :
    Oracle.Program.eval P
      (AdaptiveFOAMProgram.callProgram (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z rho S) =
      ((foamStep ell r ((firstStopSystemWithProx hP hr hrle hprox).oracle z)
        ((firstStopSystemWithProx hP hr hrle hprox).oracle_feasible z))^[
          blockIterations (alpha ell r) rho]) S :=
  eval_blockProgram hP hr hrle hprox z _ S

/-- The exact current family, including its chosen proximal-existence proof,
is the one used by the class-level output theorem. -/
theorem eval_callProgram_eq_family {D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (j : Nat)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) P.Y) :
    Oracle.Program.eval P
      (AdaptiveFOAMProgram.callProgram (r := Tracking.curvature (ell / 8) j) hP.ell_pos
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z rho S) =
      ((foamStep ell (Tracking.curvature (ell / 8) j)
        ((firstStopSystemFamily hP j).oracle z)
        ((firstStopSystemFamily hP j).oracle_feasible z))^[
          blockIterations (alpha ell (Tracking.curvature (ell / 8) j)) rho]) S :=
  eval_callProgram hP _ _ (WithinFirstStop.proxFamily hP j) z rho S

/-- At the current outer contraction factor this is literally `runBlock`. -/
theorem eval_callProgram_eq_runBlock {D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (j : Nat)
    (z : EVec m) (S : ValidState (m := m) P.Y) :
    Oracle.Program.eval P
      (AdaptiveFOAMProgram.callProgram (r := Tracking.curvature (ell / 8) j) hP.ell_pos
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z (1 / 400) S) =
      runBlock (firstStopSystemFamily hP j) z S :=
  eval_callProgram_eq_family hP j z (1 / 400) S


theorem eval_startupProgram {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) :
    Oracle.Program.eval P
      (CurrentProgram.startupProgram hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hzero) =
      startupState (firstStopSystemFamily hP 0) hzero := by
  apply Subtype.ext
  simp only [CurrentProgram.startupProgram, Oracle.Program.eval_bind, Oracle.Program.eval_pure,
    startupState_val]
  rw [(WithinFirstStop.program_correct hP (div_nonneg hP.ell_pos.le (by norm_num)) le_rfl
    P.x0 (StartupConcrete.coincidentState ((-ell) • P.x0) 0)).1]
  have hfam (V : ValidState (m := m) P.Y) :
      (firstStopSystemFamily hP 0).oracle P.x0 V =
      firstStopOracle hP (WithinFirstStop.level_pos hP 0).le (WithinFirstStop.level_le hP 0)
        P.x0 V.1 := rfl
  rw [hfam]
  simp only [Tracking.curvature, pow_zero, div_one, startupSeed]

theorem eval_warmProgram {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (z0 : EVec m) (J : Nat)
    (S : ValidState (m := m) P.Y) :
    Oracle.Program.eval P
      (CurrentProgram.warmProgram hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z0 J S) =
      homotopyState (firstStopSystemFamily hP) z0 S J := by
  induction J with
  | zero => rfl
  | succ J ih =>
      rw [CurrentProgram.warmProgram, Oracle.Program.eval_bind, ih, homotopyState_succ]
      exact eval_callProgram_eq_family hP (J + 1) z0 (1 / 8) _

theorem eval_nextProgram {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (J : Nat) (R : FeasibleSnapshot P.X P.Y) :
    (Oracle.Program.eval P
      (CurrentProgram.nextProgram (r := Tracking.curvature (ell / 8) J) hP.ell_pos
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) R)).1 =
      nextSnapshot (firstStopSystemFamily hP J) R.1 := by
  unfold CurrentProgram.nextProgram nextSnapshot
  simp only [Oracle.Program.eval_bind, Oracle.Program.eval_pure]
  rw [eval_callProgram_eq_runBlock]
  rfl

theorem eval_historyProgram_at {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (J T : Nat)
    (R0 : FeasibleSnapshot P.X P.Y) (i : Nat) (hi : i ≤ T) :
    (Oracle.Program.eval P
      (CurrentProgram.historyProgram (r := Tracking.curvature (ell / 8) J) hP.ell_pos
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) T R0) i).1 =
      trajectory (firstStopSystemFamily hP J) R0.1 i := by
  induction T generalizing i with
  | zero => have hi0 : i = 0 := by omega
            subst i
            rfl
  | succ T ih =>
      simp only [CurrentProgram.historyProgram, Oracle.Program.eval_bind, Oracle.Program.eval_pure]
      by_cases hit : i = T + 1
      · subst i
        simp only [ite_true]
        rw [eval_nextProgram, ih T le_rfl]
        rfl
      · simp only [if_neg hit]
        exact ih i (by omega)

theorem localScore_eq_observable {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (J : Nat) (R : Snapshot (m := m) P.Y) :
    CurrentProgram.localScore ell (chosenProjectX hP) R = observable (firstStopSystemFamily hP J) R := rfl

theorem eval_initializeProgram {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) :
    (Oracle.Program.eval P
      (CurrentProgram.initializeProgram hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP)
        P.x0 hP.x0_mem hzero D Delta J)).1 =
      initializedSnapshot (D := D) (Delta := Delta) (firstStopSystemFamily hP) hzero J := by
  simp only [CurrentProgram.initializeProgram, Oracle.Program.eval_bind, Oracle.Program.eval_pure,
    eval_startupProgram, eval_warmProgram]
  rfl

theorem eval_history_selected {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (J T : Nat) (hT : 0 < T)
    (R0 : FeasibleSnapshot P.X P.Y) :
    CurrentProgram.selectHistory ell (chosenProjectX hP) T hT
      (Oracle.Program.eval P
        (CurrentProgram.historyProgram (r := Tracking.curvature (ell / 8) J) hP.ell_pos
          (chosenProjectX hP) (chosenProjectY hP)
          (chosenProjectX_spec hP) (chosenProjectY_spec hP) T R0)) =
      Selection.selectedAnchor (firstStopSystemFamily hP J) R0.1 T hT := by
  let H := Oracle.Program.eval P
    (CurrentProgram.historyProgram (r := Tracking.curvature (ell / 8) J) hP.ell_pos
      (chosenProjectX hP) (chosenProjectY hP)
      (chosenProjectX_spec hP) (chosenProjectY_spec hP) T R0)
  let sys := firstStopSystemFamily hP J
  have hscores (i : Nat) (hi : i < T) :
      CurrentProgram.localScore ell (chosenProjectX hP) (H i).1 = observable sys (trajectory sys R0.1 i) := by
    rw [localScore_eq_observable, eval_historyProgram_at hP J T R0 i hi.le]
  have hsel := leastMinimizer_congr
    (fun i => CurrentProgram.localScore ell (chosenProjectX hP) (H i).1)
    (fun i => observable sys (trajectory sys R0.1 i)) T hT hscores
  unfold CurrentProgram.selectHistory Selection.selectedAnchor Selection.selectedIndex
  change (H _).1.z = _
  rw [hsel, eval_historyProgram_at hP J T R0 _
    (Selection.leastMinimizer_spec _ T hT).1.le]

theorem eval_program {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    Oracle.Program.eval P
      (CurrentProgram.program hP.ell_pos hP.D_pos hP.Delta_pos heps
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hzero) =
      WithinRun.output hP hzero heps := by
  simp only [CurrentProgram.program, Oracle.Program.eval_bind, Oracle.Program.eval_pure]
  rw [eval_history_selected, eval_initializeProgram]
  rfl


theorem program_numerical_count (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    (queryTrace P
      (CurrentProgram.program hP.ell_pos hP.D_pos hP.Delta_pos heps
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hzero)).length ≤
      (ProjectedMicro.feasibleMicroIterations + 1) +
        HomotopyCost.homotopyOracleCalls ell (ell / 8) (1 / 8) (stage hP heps) +
        Selection.outerIterations ell Delta eps *
          (BlockCostConcrete.feasibleBlockCost ell (finalCurvature hP heps) (1 / 400)).oracleCalls := by
  have hd := CurrentProgram.program_depth hP.ell_pos hP.D_pos hP.Delta_pos heps
    (chosenProjectX hP) (chosenProjectY hP) (chosenProjectX_spec hP) (chosenProjectY_spec hP)
    P.x0 hP.x0_mem hzero
  have hc := hd.trace_length P
  rw [causalHomotopyCalls_eq] at hc
  simpa only [CurrentProgram.numericalStage, stage, finalCurvature,
    BlockCostConcrete.feasibleBlockCost_oracleCalls] using hc

open HomotopyCost BlockCostConcrete

theorem program_uniform_query_bound (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    ((queryTrace P
      (CurrentProgram.program hP.ell_pos hP.D_pos hP.Delta_pos heps
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hzero)).length : ℝ) ≤
      CurrentCost.traceRateConstant *
        ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) := by
  let J := stage hP heps
  let r := finalCurvature hP heps
  let T := Selection.outerIterations ell Delta eps
  let A := ell * Delta / eps ^ 2
  let M := max 1 (ell * D / eps)
  let C8 := UniformCost.blockConstant (1 / 8)
  let C400 := UniformCost.blockConstant (1 / 400)
  have hr : 0 < r := finalCurvature_pos hP heps
  have hrle : r ≤ ell / 8 := level_le hP J
  have hA : 0 ≤ A := div_nonneg
    (mul_nonneg hP.ell_pos.le hP.Delta_pos.le) (sq_nonneg eps)
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hAp : 1 ≤ A + 1 := by linarith
  have hrate : 1 ≤ (A + 1) * M := by
    simpa using mul_le_mul hAp hM (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
  have hC8 : 0 < C8 := UniformCost.blockConstant_pos (by norm_num) (by norm_num)
  have hC400 : 0 < C400 := UniformCost.blockConstant_pos (by norm_num) (by norm_num)
  have hsqrt : Real.sqrt (ell / r) ≤ 6 * M :=
    (UniformSchedule.sqrt_ratio_lt_six_max hP.ell_pos hP.D_pos heps hr
      (finalCurvature_interval hP heps).1).le
  have hblock0 := (feasibleBlockCost_lt_sqrt_ratio hP.ell_pos hr hrle
    (by norm_num : (0 : ℝ) < 1 / 400) (by norm_num : (1 / 400 : ℝ) < 1)).1.le
  have hblock : ((feasibleBlockCost ell r (1 / 400)).oracleCalls : ℝ) ≤
      6 * C400 * M := by
    calc
      _ ≤ C400 * Real.sqrt (ell / r) := hblock0
      _ ≤ C400 * (6 * M) := mul_le_mul_of_nonneg_left hsqrt hC400.le
      _ = 6 * C400 * M := by ring
  have hT : (T : ℝ) ≤ 4001 * (A + 1) :=
    CurrentCost.current_horizon_upper hP.ell_pos hP.Delta_pos
  have houter : (T : ℝ) * ((feasibleBlockCost ell r (1 / 400)).oracleCalls : ℝ) ≤
      24006 * C400 * ((A + 1) * M) := by
    have hm := mul_le_mul hT hblock (Nat.cast_nonneg _)
      (show 0 ≤ 4001 * (A + 1) by positivity)
    calc
      _ ≤ (4001 * (A + 1)) * (6 * C400 * M) := hm
      _ = 24006 * C400 * ((A + 1) * M) := by ring
  have hhom0 := (homotopy_total_cost_le hP.ell_pos
    (div_pos hP.ell_pos (by norm_num)) le_rfl
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1) J).1
  have hhom : (homotopyOracleCalls ell (ell / 8) (1 / 8) J : ℝ) ≤
      12 * C8 * ((A + 1) * M) := by
    calc
      _ ≤ 2 * C8 * Real.sqrt (ell / r) := hhom0
      _ ≤ 2 * C8 * (6 * M) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = 12 * C8 * M := by ring
      _ ≤ 12 * C8 * ((A + 1) * M) := by
        have hm := mul_le_mul_of_nonneg_right hAp hM0
        exact mul_le_mul_of_nonneg_left (by simpa using hm) (by positivity)
  have hstart : (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) ≤
      (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) * ((A + 1) * M) := by
    have hm := mul_le_mul_of_nonneg_left hrate
      (show (0 : ℝ) ≤ ProjectedMicro.feasibleMicroIterations + 1 by positivity)
    simpa using hm
  have hraw : ((queryTrace P
      (CurrentProgram.program hP.ell_pos hP.D_pos hP.Delta_pos heps
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hzero)).length : ℝ) ≤
      (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) +
        (homotopyOracleCalls ell (ell / 8) (1 / 8) J : ℝ) +
        (T : ℝ) * ((feasibleBlockCost ell r (1 / 400)).oracleCalls : ℝ) := by
    exact_mod_cast program_numerical_count hP hzero heps
  calc
    _ ≤ (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) +
        (homotopyOracleCalls ell (ell / 8) (1 / 8) J : ℝ) +
        (T : ℝ) * ((feasibleBlockCost ell r (1 / 400)).oracleCalls : ℝ) := hraw
    _ ≤ (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) * ((A + 1) * M) +
        12 * C8 * ((A + 1) * M) + 24006 * C400 * ((A + 1) * M) :=
      add_le_add (add_le_add hstart hhom) houter
    _ = CurrentCost.traceRateConstant * ((ell * Delta / eps ^ 2 + 1) *
        max 1 (ell * D / eps)) := by
      unfold CurrentCost.traceRateConstant
      dsimp [A, M, C8, C400]
      ring

theorem eval_program_is_OS (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    Moreau.Within.IsOS hP eps
      (Oracle.Program.eval P
        (CurrentProgram.program hP.ell_pos hP.D_pos hP.Delta_pos heps
          (chosenProjectX hP) (chosenProjectY hP)
          (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hzero)) := by
  rw [eval_program]
  exact WithinRun.output_is_OS hP hzero heps

/-- Counterfactual histories remain feasible for the same source-class
program. The fallback is the prescribed feasible initial point. -/
theorem program_all_histories_feasible (hP : WithinClass ell D Delta P) (heps : 0 < eps)
    (t : Nat) (history : Oracle.ReplyHistory m n t) :
    let q := Oracle.Program.queryAfterHistory
      (CurrentProgram.program hP.ell_pos hP.D_pos hP.Delta_pos heps
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hP.dual_origin)
      (P.x0, 0) t history
    q.1 ∈ P.X ∧ q.2 ∈ P.Y :=
  CurrentProgram.program_all_histories_feasible hP.ell_pos hP.D_pos hP.Delta_pos heps
    (chosenProjectX hP) (chosenProjectY hP)
    (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hP.dual_origin
    (P.x0, 0) ⟨hP.x0_mem, hP.dual_origin⟩ t history

/-- Actual output and counted-execution upper guarantee for the source
class. This does not yet package the client as the paper's algorithm type. -/
theorem feasible_program_correct (hP : WithinClass ell D Delta P) (heps : 0 < eps) :
    let p := CurrentProgram.program hP.ell_pos hP.D_pos hP.Delta_pos heps
      (chosenProjectX hP) (chosenProjectY hP)
      (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hP.dual_origin
    Moreau.Within.IsOS hP eps (Oracle.Program.eval P p) ∧
      ((queryTrace P p).length : ℝ) ≤ CurrentCost.traceRateConstant *
        ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) :=
  ⟨eval_program_is_OS hP hP.dual_origin heps,
    program_uniform_query_bound hP hP.dual_origin heps⟩

end
end NCC.Upper.WithinProgram
