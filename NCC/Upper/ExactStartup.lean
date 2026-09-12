import NCC.Upper.WithinProgram

/-!
# The sharp printed initial-state lemma

This module closes `lem:startup-state` with coefficient 5 and the actual
gap Phi(0) - inf_X Phi, not merely the class budget Delta. The constructed
state is the current reply-driven first-success micro output followed by
the printed coincident reset. Its genuine oracle trace has a universal cap.
-/
namespace NCC.Upper.ExactStartup
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open PointwiseConjugate RelativeFOAM RelativeFOAMContraction ScaledOperator
open ProjectionGeometry TrackingConcrete OuterTrajectoryConcrete
open HomotopyRun StartupConcrete InitialGapBounds HomotopySchedule UniformSchedule
open AnalyticBridge WithinFirstStop AdaptiveMicroProgram
set_option maxHeartbeats 3000000
variable {m n : Nat} {ell D Delta r : ℝ} {P : NCCInstance m n}

/-- Phi(0) minus its genuine infimum over the primal feasible set. -/
def actualGap (P : NCCInstance m n) : ℝ := ValueOn P.Y P.f 0 - classValueInf P

/-- The real infimum is not the fallback value of an empty or
unbounded-below set: it is a genuine greatest lower bound. -/
theorem infimum_certificate (hP : WithinClass ell D Delta P) :
    IsGLB (ValueOn P.Y P.f '' P.X) (classValueInf P) :=
  isGLB_csInf ⟨ValueOn P.Y P.f 0, 0, hP.primal_origin, rfl⟩ hP.value_bddBelow

theorem actualGap_nonneg (hP : WithinClass ell D Delta P) : 0 ≤ actualGap P := by
  have hl := WithinRun.classValueInf_le hP hP.primal_origin
  unfold actualGap
  linarith

theorem actualGap_le (hP : WithinClass ell D Delta P) : actualGap P ≤ Delta :=
  hP.initial_gap

theorem regularized_initial_gap_exact (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) :
    DualRegularizedValueOn P.Y P.f r 0 - regularizedClassLower P r D ≤
      actualGap P + r / 2 * D ^ 2 := by
  have hbias := dualRegularizedValue_bias hr
    (WithinRun.dual_vecSq_le hP hP.dual_origin)
    (hP.maximum_attained hP.primal_origin)
    (hP.regularized_maximum_attained 0 hP.primal_origin)
  unfold regularizedClassLower actualGap
  linarith

/-- The proximal displacement estimate retains the actual primal gap. -/
theorem selected_regularizedProx_displacement_exact (hP : WithinClass ell D Delta P)
    (hr : 0 ≤ r)
    (hexistsR : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell) :
    ell * vecSq (P.x0 - selectedProx hexistsR P.x0) ≤
      actualGap P + r / 2 * D ^ 2 := by
  apply TrackingAnalytic.prox_displacement_from_initial_gap hP.x0_mem
    (selectedProx_spec hexistsR P.x0)
    (WithinRun.regularizedClassLower_le hP hP.dual_origin hr
      (selectedProx_spec hexistsR P.x0).1)
  simpa only [hP.initialization] using regularized_initial_gap_exact hP hr

/-- The sharp 5-bound for the actual coincident startup state. Only the
local oracle certificate of the supplied genuine system is used. -/
theorem startup_energy_exact (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (hr : r = ell / 8)
    (hexists0 : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (sys0 : OuterSystem P.X P.Y P.f ell r hexists0) :
    energyAt sys0 P.x0 (startupState sys0 hzero) ≤
      5 * (actualGap P + (3 / 2 : ℝ) * (ell / 8) * D ^ 2) := by
  subst r
  let Sseed := startupSeed (ell := ell) hzero
  let O := sys0.oracle P.x0 Sseed
  let st := sys0.stationary P.x0
  have hfast : IsGammaSubgradient P.X P.Y
      (decurved P.f ell (ell / 8) P.x0) O.qFastNext
      ⟨O.yFastNext, sys0.oracle_feasible P.x0 Sseed⟩ O.xFast O.wFastNext :=
    sys0.oracle_subgradient P.x0 Sseed
  have hres : RelativeResidual ell (ell / 8)
      (coincidentState ((-ell) • P.x0) 0)
      (startupOutput O.xFast O.qFastNext O.yFastNext O.wFastNext) := by
    simpa [Sseed, startupSeed, O, startupOutput] using sys0.oracle_residual P.x0 Sseed
  have hprimal : ell * vecSq (P.x0 - selectedProx hexists0 P.x0) ≤
      actualGap P + (ell / 8) / 2 * D ^ 2 :=
    selected_regularizedProx_displacement_exact hP
      (div_nonneg hP.ell_pos.le (by norm_num)) hexists0
  have hstartup := startup_pzr_computable_majorant
    hP.ell_pos (actualGap_nonneg hP) (sq_nonneg D)
    hfast st.subgradient st.stationQ st.stationY hres hprimal
    (WithinRun.dual_vecSq_le hP hzero st.yStar.1 st.yStar.2)
  dsimp [energyAt, startupState, Sseed, O, st]
  exact hstartup.1

/-- Energy of the state returned by the literal current startup program,
at the source's prescribed primal-dual origin. -/
theorem evaluated_startup_energy_exact (hP : WithinClass ell D Delta P) :
    energyAt (firstStopSystemFamily hP 0) 0
      (Oracle.Program.eval P (CurrentProgram.startupProgram hP.ell_pos
        (WithinSystem.chosenProjectX hP) (WithinSystem.chosenProjectY hP)
        (WithinSystem.chosenProjectX_spec hP) (WithinSystem.chosenProjectY_spec hP)
        0 hP.dual_origin)) ≤
      5 * (actualGap P + (3 / 2 : ℝ) * (ell / 8) * D ^ 2) := by
  have heval := WithinProgram.eval_startupProgram hP hP.dual_origin
  rw [hP.initialization] at heval
  rw [heval]
  have hE := startup_energy_exact hP hP.dual_origin
    (show Tracking.curvature (ell / 8) 0 = ell / 8 by simp [Tracking.curvature])
    (WithinFirstStop.proxFamily hP 0) (firstStopSystemFamily hP 0)
  simpa only [hP.initialization] using hE

/-- Full literal initial-state conclusion: sharp actual-gap energy bound
and a universal number of genuine first-order saddle-oracle calls. -/
theorem startup_state_construction (hP : WithinClass ell D Delta P) :
    let p := CurrentProgram.startupProgram hP.ell_pos
      (WithinSystem.chosenProjectX hP) (WithinSystem.chosenProjectY hP)
      (WithinSystem.chosenProjectX_spec hP) (WithinSystem.chosenProjectY_spec hP)
      0 hP.dual_origin
    energyAt (firstStopSystemFamily hP 0) 0 (Oracle.Program.eval P p) ≤
        5 * (ValueOn P.Y P.f 0 - sInf (ValueOn P.Y P.f '' P.X) +
          (3 / 2 : ℝ) * (ell / 8) * D ^ 2) ∧
      (queryTrace P p).length ≤ ProjectedMicro.feasibleMicroIterations + 1 := by
  refine ⟨evaluated_startup_energy_exact hP, ?_⟩
  exact (CurrentProgram.startupProgram_depth hP.ell_pos
    (WithinSystem.chosenProjectX hP) (WithinSystem.chosenProjectY hP)
    (WithinSystem.chosenProjectX_spec hP) (WithinSystem.chosenProjectY_spec hP)
    0 hP.dual_origin).trace_length P

theorem startup_all_histories_feasible (hP : WithinClass ell D Delta P)
    (t : Nat) (history : Oracle.ReplyHistory m n t) :
    let q := Oracle.Program.queryAfterHistory
      (CurrentProgram.startupProgram hP.ell_pos
        (WithinSystem.chosenProjectX hP) (WithinSystem.chosenProjectY hP)
        (WithinSystem.chosenProjectX_spec hP) (WithinSystem.chosenProjectY_spec hP)
        0 hP.dual_origin) (0, 0) t history
    q.1 ∈ P.X ∧ q.2 ∈ P.Y :=
  Oracle.Program.queryAfterHistory_mem _ (0, 0) ⟨hP.primal_origin, hP.dual_origin⟩ t history

end
end NCC.Upper.ExactStartup
