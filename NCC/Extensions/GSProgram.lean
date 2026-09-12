import NCC.Extensions.GSRun
import NCC.Extensions.ProjectedReadout

/-!
# Reply-driven tracked and refined GS preparation

The constructor receives only known projections and numerical data.
It returns the selected feasible snapshot and an actual first-stop FOAM
refinement at its anchor. Every query is feasible after every history.
The projected normal-residual readout is not part of this preparation.
-/
namespace NCC.Extensions.GSProgram
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open RelativeFOAM RelativeFOAMContraction ProjectionGeometry
open OuterTrajectoryConcrete HomotopyRun SharedOracle
open NCC.Upper NCC.Upper.AnalyticBridge NCC.Upper.AdaptiveMicroProgram
open NCC.Upper.CurrentProgram NCC.Upper.WithinSystem NCC.Upper.WithinFirstStop
set_option maxHeartbeats 3000000
variable {m n : Nat} {ell D Delta eta : ℝ} {P : NCCInstance m n}
  {X : Set (EVec m)} {Y : Set (EVec n)}

def selectSnapshot (ell : ℝ) (projectX : EVec m → EVec m)
    (T : Nat) (hT : 0 < T) (H : Nat → FeasibleSnapshot X Y) : FeasibleSnapshot X Y :=
  H (Selection.leastMinimizer (fun i => localScore ell projectX (H i).1) T hT)

def program (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y)
    (D Delta : ℝ) (J T : Nat) (hT : 0 < T) (rho : ℝ) :
    Oracle.Program X Y (FeasibleSnapshot X Y × ValidState (m := m) Y) := do
  let R0 ← CurrentProgram.initializeProgram hell projectX projectY hprojX hprojY
    z0 hz0 hzero D Delta J
  let H ← CurrentProgram.historyProgram (r := Tracking.curvature (ell / 8) J)
    hell projectX projectY hprojX hprojY T R0
  let R := selectSnapshot ell projectX T hT H
  let S ← AdaptiveFOAMProgram.callProgram (r := Tracking.curvature (ell / 8) J)
    hell projectX projectY hprojX hprojY R.1.z rho R.1.state
  Oracle.Program.pure (R, S)

def numericalCount (ell : ℝ) (J T : Nat) (rho : ℝ) : Nat :=
  (ProjectedMicro.feasibleMicroIterations + 1) + causalHomotopyCalls ell J +
    T * (blockIterations (alpha ell (Tracking.curvature (ell / 8) J)) (1 / 400) *
      (ProjectedMicro.feasibleMicroIterations + 1)) +
    blockIterations (alpha ell (Tracking.curvature (ell / 8) J)) rho *
      (ProjectedMicro.feasibleMicroIterations + 1)

theorem program_depth (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y)
    (D Delta : ℝ) (J T : Nat) (hT : 0 < T) (rho : ℝ) :
    DepthAtMost (program hell projectX projectY hprojX hprojY z0 hz0 hzero
      D Delta J T hT rho) (numericalCount ell J T rho) := by
  let tail (H : Nat → FeasibleSnapshot X Y) :
      Oracle.Program X Y (FeasibleSnapshot X Y × ValidState (m := m) Y) := do
    let R := selectSnapshot ell projectX T hT H
    let S ← AdaptiveFOAMProgram.callProgram (r := Tracking.curvature (ell / 8) J)
      hell projectX projectY hprojX hprojY R.1.z rho R.1.state
    Oracle.Program.pure (R, S)
  have htail (H : Nat → FeasibleSnapshot X Y) :=
    (AdaptiveFOAMProgram.callProgram_depth (r := Tracking.curvature (ell / 8) J)
      hell projectX projectY hprojX hprojY
      (selectSnapshot ell projectX T hT H).1.z rho
      (selectSnapshot ell projectX T hT H).1.state).bind
      (fun S => .pure (selectSnapshot ell projectX T hT H, S))
      (fun _ => DepthAtMost.pure _ 0)
  have hhistory (R0 : FeasibleSnapshot X Y) :=
    (CurrentProgram.historyProgram_depth (r := Tracking.curvature (ell / 8) J)
      hell projectX projectY hprojX hprojY T R0).bind tail htail
  have hinit := (CurrentProgram.initializeProgram_depth hell projectX projectY hprojX hprojY
    z0 hz0 hzero D Delta J).bind _ hhistory
  simpa only [program, tail, numericalCount, Nat.add_zero, Nat.add_assoc] using hinit

theorem program_actual_count (P : NCCInstance m n) (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y)
    (D Delta : ℝ) (J T : Nat) (hT : 0 < T) (rho : ℝ) :
    (queryTrace P (program hell projectX projectY hprojX hprojY z0 hz0 hzero
      D Delta J T hT rho)).length ≤ numericalCount ell J T rho :=
  (program_depth hell projectX projectY hprojX hprojY z0 hz0 hzero D Delta J T hT rho).trace_length P

theorem program_all_histories_feasible (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y)
    (D Delta : ℝ) (J T : Nat) (hT : 0 < T) (rho : ℝ)
    (t : Nat) (history : Oracle.ReplyHistory m n t) :
    let q := Oracle.Program.queryAfterHistory
      (program hell projectX projectY hprojX hprojY z0 hz0 hzero D Delta J T hT rho)
      (z0, 0) t history
    q.1 ∈ X ∧ q.2 ∈ Y :=
  Oracle.Program.queryAfterHistory_mem _ (z0, 0) ⟨hz0, hzero⟩ t history

theorem eval_history_selected_snapshot (hP : WithinClass ell D Delta P)
    (J T : Nat) (hT : 0 < T) (R0 : FeasibleSnapshot P.X P.Y) :
    (selectSnapshot ell (chosenProjectX hP) T hT
      (Oracle.Program.eval P (CurrentProgram.historyProgram
        (r := Tracking.curvature (ell / 8) J) hP.ell_pos
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) T R0))).1 =
      trajectory (firstStopSystemFamily hP J) R0.1
        (Selection.selectedIndex (firstStopSystemFamily hP J) R0.1 T hT) := by
  let H := Oracle.Program.eval P (CurrentProgram.historyProgram
    (r := Tracking.curvature (ell / 8) J) hP.ell_pos
    (chosenProjectX hP) (chosenProjectY hP)
    (chosenProjectX_spec hP) (chosenProjectY_spec hP) T R0)
  let sys := firstStopSystemFamily hP J
  have hscores (i : Nat) (hi : i < T) :
      localScore ell (chosenProjectX hP) (H i).1 = observable sys (trajectory sys R0.1 i) := by
    rw [WithinProgram.localScore_eq_observable,
      WithinProgram.eval_historyProgram_at hP J T R0 i hi.le]
  have hsel := leastMinimizer_congr
    (fun i => localScore ell (chosenProjectX hP) (H i).1)
    (fun i => observable sys (trajectory sys R0.1 i)) T hT hscores
  unfold selectSnapshot Selection.selectedIndex
  change (H _).1 = _
  rw [hsel, WithinProgram.eval_historyProgram_at hP J T R0 _
    (Selection.leastMinimizer_spec _ T hT).1.le]

theorem eval_program (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) (rho : ℝ) :
    let out := Oracle.Program.eval P
      (program hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hzero
        D Delta J (GSRun.horizon ell D Delta eta J) (GSRun.horizon_pos hP J) rho)
    out.1.1 = GSRun.selectedSnapshot (eta := eta) hP hzero J ∧
      out.2 = GSRun.refinedState (eta := eta) hP hzero J rho := by
  simp only [program, Oracle.Program.eval_bind, Oracle.Program.eval_pure]
  rw [WithinProgram.eval_callProgram_eq_family]
  have hs := eval_history_selected_snapshot hP J (GSRun.horizon ell D Delta eta J)
    (GSRun.horizon_pos hP J)
    (Oracle.Program.eval P (CurrentProgram.initializeProgram hP.ell_pos
      (chosenProjectX hP) (chosenProjectY hP) (chosenProjectX_spec hP)
      (chosenProjectY_spec hP) P.x0 hP.x0_mem hzero D Delta J))
  rw [WithinProgram.eval_initializeProgram] at hs
  constructor
  · exact hs
  · exact congrArg (fun R : Snapshot (m := m) P.Y =>
      ((foamStep ell (Tracking.curvature (ell / 8) J)
        ((firstStopSystemFamily hP J).oracle R.z)
        ((firstStopSystemFamily hP J).oracle_feasible R.z))^[
          blockIterations (alpha ell (Tracking.curvature (ell / 8) J)) rho]) R.state) hs

open HomotopyCost BlockCostConcrete

/-- Geometric initialization plus T outer calls and one genuine refinement.
The logarithmic dependence on the final contraction is explicit in
`UniformCost.blockConstant rho`; no desired target is assigned as a cost. -/
theorem numericalCount_le (hell : 0 < ell) (J T : Nat)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    (numericalCount ell J T rho : ℝ) ≤
      (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) +
      (2 * UniformCost.blockConstant (1 / 8) +
        (T : ℝ) * UniformCost.blockConstant (1 / 400) + UniformCost.blockConstant rho) *
          Real.sqrt (ell / Tracking.curvature (ell / 8) J) := by
  have hr : 0 < Tracking.curvature (ell / 8) J :=
    HomotopyCost.curvature_pos (div_pos hell (by norm_num)) J
  have hrle : Tracking.curvature (ell / 8) J ≤ ell / 8 := by
    unfold Tracking.curvature
    exact Tracking.div_pow_le_self (div_nonneg hell.le (by norm_num)) (by norm_num) J
  have hhom := (homotopy_total_cost_le hell
    (div_pos hell (by norm_num)) le_rfl (by norm_num : (0 : ℝ) < 1 / 8)
    (by norm_num : (1 / 8 : ℝ) < 1) J).1
  have houter := (feasibleBlockCost_lt_sqrt_ratio hell hr hrle
    (by norm_num : (0 : ℝ) < 1 / 400) (by norm_num : (1 / 400 : ℝ) < 1)).1.le
  have hrefine := (feasibleBlockCost_lt_sqrt_ratio hell hr hrle hrho hrho1).1.le
  have houterT := mul_le_mul_of_nonneg_left houter (Nat.cast_nonneg T)
  unfold numericalCount
  rw [causalHomotopyCalls_eq]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  rw [feasibleBlockCost_oracleCalls] at houterT hrefine
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at houterT hrefine
  unfold UniformCost.blockConstant
  unfold stageCondition at hhom
  nlinarith

open ScaledOperator ProjectedReadout

def rawPair (ell : ℝ) (projectX : EVec m → EVec m) (S : ValidState (m := m) Y) : Pair m n :=
  pack (projectX ((-ell⁻¹) • S.1.qFast)) S.1.yFast

def replySaddle (ell r : ℝ) (z : EVec m) (q : Oracle.Query m n)
    (reply : Oracle.OracleReply m n) : Pair m n :=
  pack (reply.gradX + (2 * ell) • (q.1 - z)) (-reply.gradY + r • q.2)

theorem replySaddle_true (P : NCCInstance m n) (ell r : ℝ) (z : EVec m)
    (x : EVec m) (y : EVec n) :
    replySaddle ell r z (x, y) (Oracle.firstOrderOracle P (x, y)) =
      saddlePair P ell r z (pack x y) := by
  unfold replySaddle saddlePair
  simp only [unpackX_pack, unpackY_pack, Oracle.firstOrderOracle_gradX,
    Oracle.firstOrderOracle_gradY]
  congr 1
  ext i
  simp only [saddleX, ClassOperator.gradXHat,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- One feasible query supplies both gradient coordinates for the final
normal-cone readout. The known projections need no objective evaluation. -/
def readoutProgram (ell r : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (_hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : ValidState (m := m) Y) : Oracle.Program X Y (Oracle.Query m n) :=
  let q := (projectX ((-ell⁻¹) • S.1.qFast), S.1.yFast)
  .query q ⟨hprojX.mem _, S.2⟩ fun reply =>
    let w := pairProject projectX projectY
      (rawPair ell projectX S - ell⁻¹ • replySaddle ell r z q reply)
    .pure (unpackX w, unpackY w)

theorem readoutProgram_depth (ell r : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : ValidState (m := m) Y) :
    DepthAtMost (readoutProgram ell r projectX projectY hprojX hprojY z S) 1 :=
  DepthAtMost.query _ _ _ 0 (fun _ => DepthAtMost.pure _ 0)

theorem eval_readoutProgram (P : NCCInstance m n) (ell r : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : ValidState (m := m) Y) :
    Oracle.Program.eval P (readoutProgram ell r projectX projectY hprojX hprojY z S) =
      (unpackX (readoutPair P ell r projectX projectY z (rawPair ell projectX S)),
        unpackY (readoutPair P ell r projectX projectY z (rawPair ell projectX S))) := by
  simp only [readoutProgram, Oracle.Program.eval_query, Oracle.Program.eval_pure,
    replySaddle_true]
  rfl

theorem refined_readout_hasGSWitness {eps : ℝ} (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    let J := GSRun.stage hP.ell_pos hP.D_pos heps
    let r := Tracking.curvature (ell / 8) J
    let R := GSRun.selectedSnapshot (eta := eps / 2) hP hzero J
    let S := GSRun.refinedState (eta := eps / 2) hP hzero J (GSRun.refinementFactor ell r)
    let out := Oracle.Program.eval P (readoutProgram ell r (chosenProjectX hP) (chosenProjectY hP)
      (chosenProjectX_spec hP) (chosenProjectY_spec hP) R.z S)
    HasGSWitness P eps out.1 out.2 := by
  dsimp only
  have hell := hP.ell_pos
  let J := GSRun.stage hP.ell_pos hP.D_pos heps
  let r := Tracking.curvature (ell / 8) J
  let R := GSRun.selectedSnapshot (eta := eps / 2) hP hzero J
  let S := GSRun.refinedState (eta := eps / 2) hP hzero J (GSRun.refinementFactor ell r)
  let sys := firstStopSystemFamily hP J
  let W := canonicalSaddle hP (level_pos hP J) (level_le hP J)
    (chosenProjectX_spec hP) (chosenProjectY_spec hP) R.z
  let u := rawPair ell (chosenProjectX hP) S
  have hr : 0 < r := level_pos hP J
  have hrle : r ≤ ell := (level_le hP J).trans (by linarith [hP.ell_pos])
  have hWx : W.x = selectedProx (WithinFirstStop.proxFamily hP J) R.z :=
    canonicalSaddle_x hP (level_pos hP J) (level_le hP J)
      (chosenProjectX_spec hP) (chosenProjectY_spec hP) _ R.z
  have hWy : W.y = (sys.stationary R.z).yStar.1 := rfl
  have hdist : vecSq (u - pack W.x W.y) ≤ 2 * energyAt sys R.z S / r := by
    rw [hWx, hWy]
    change vecSq (pack (readout sys S) S.1.yFast -
      pack (selectedProx (WithinFirstStop.proxFamily hP J) R.z) (sys.stationary R.z).yStar.1) ≤ _
    rw [← pack_sub, vecSq_pack]
    exact GSRun.fast_pair_distance_le_energy hP.ell_pos hr hrle sys R.z S
  have hbud := GSRun.final_refinement_budgets hP hzero J heps
  have hE : energyAt sys R.z S < r * eps ^ 2 / (1000000 * ell ^ 2) := hbud.2
  have hprecision : 50000 * ell ^ 2 * vecSq (u - pack W.x W.y) ≤ eps ^ 2 := by
    have hd := (le_div_iff₀ hr).1 hdist
    have he := (lt_div_iff₀ (show 0 < 1000000 * ell ^ 2 by positivity)).1 hE
    have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 50000 * ell ^ 2 by positivity)
    have heps2 := sq_nonneg eps
    have : (50000 * ell ^ 2 * vecSq (u - pack W.x W.y)) * r ≤ eps ^ 2 * r := by
      nlinarith
    exact (mul_le_mul_iff_left₀ hr).1 this
  have hanchor : 64 * ell ^ 2 * vecSq (R.z - W.x) ≤ eps ^ 2 := by
    have hg := hbud.1
    unfold residualGradient at hg
    rw [vecSq_smul] at hg
    rw [hWx]
    nlinarith
  have hdual : 16 * r ^ 2 * D ^ 2 ≤ eps ^ 2 := by
    have hb : r * D ≤ eps / 64 := GSRun.finalCurvature_bias hP.ell_pos hP.D_pos heps
    have hrd : 0 ≤ r * D := mul_nonneg hr.le hP.D_pos.le
    nlinarith [sq_nonneg (eps / 64 - r * D)]
  rw [eval_readoutProgram]
  apply readoutPair_hasGSWitness hP hr.le hrle heps
    (chosenProjectX_spec hP) (chosenProjectY_spec hP) W
  · change u ∈ pairSet P.X P.Y
    simpa only [u, rawPair, pairSet, Set.mem_setOf_eq, unpackX_pack, unpackY_pack] using
      And.intro ((chosenProjectX_spec hP).mem ((-ell⁻¹) • S.1.qFast)) S.2
  · exact hprecision
  · exact hanchor
  · exact hdual

theorem numerical_horizon_pos {eps : ℝ}
    (hell : 0 < ell) (hDelta : 0 < Delta) (J : Nat) :
    0 < GSRun.horizon ell D Delta (eps / 2) J := by
  have hr := HomotopyCost.curvature_pos
    (div_pos hell (by norm_num : (0 : ℝ) < 8)) J
  apply Selection.outerIterations_pos hell
  exact add_pos_of_pos_of_nonneg hDelta (mul_nonneg hr.le (sq_nonneg D))

/-- Full numerical GS client. Its regularization schedule, outer horizon,
refinement tolerance and readout are all fixed before objective replies. -/
def fullProgram {eps : ℝ} (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y) :
    Oracle.Program X Y (Oracle.Query m n) := do
  let J := GSRun.stage hell hD heps
  let r := Tracking.curvature (ell / 8) J
  let out ← program hell projectX projectY hprojX hprojY z0 hz0 hzero D Delta J
    (GSRun.horizon ell D Delta (eps / 2) J) (numerical_horizon_pos hell hDelta J)
    (GSRun.refinementFactor ell r)
  readoutProgram ell r projectX projectY hprojX hprojY out.1.1.z out.2

def fullNumericalCount {eps : ℝ} (hell : 0 < ell) (hD : 0 < D)
    (heps : 0 < eps) (Delta : ℝ) : Nat :=
  let J := GSRun.stage hell hD heps
  let r := Tracking.curvature (ell / 8) J
  numericalCount ell J (GSRun.horizon ell D Delta (eps / 2) J)
    (GSRun.refinementFactor ell r) + 1

theorem fullProgram_depth {eps : ℝ} (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y) :
    DepthAtMost (fullProgram hell hD hDelta heps projectX projectY hprojX hprojY z0 hz0 hzero)
      (fullNumericalCount hell hD heps Delta) := by
  unfold fullProgram fullNumericalCount
  exact (program_depth hell projectX projectY hprojX hprojY z0 hz0 hzero D Delta _ _ _ _).bind
    _ (fun out => readoutProgram_depth _ _ projectX projectY hprojX hprojY out.1.1.z out.2)

theorem fullProgram_actual_count {eps : ℝ} (P : NCCInstance m n)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y) :
    (queryTrace P
      (fullProgram hell hD hDelta heps projectX projectY hprojX hprojY z0 hz0 hzero)).length ≤
      fullNumericalCount hell hD heps Delta :=
  (fullProgram_depth hell hD hDelta heps projectX projectY hprojX hprojY z0 hz0 hzero).trace_length P

theorem fullProgram_all_histories_feasible {eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y)
    (t : Nat) (history : Oracle.ReplyHistory m n t) :
    let q := Oracle.Program.queryAfterHistory
      (fullProgram hell hD hDelta heps projectX projectY hprojX hprojY z0 hz0 hzero)
      (z0, 0) t history
    q.1 ∈ X ∧ q.2 ∈ Y :=
  Oracle.Program.queryAfterHistory_mem _ (z0, 0) ⟨hz0, hzero⟩ t history

/-- Genuine game stationarity of the output of the reply-driven client. -/
theorem fullProgram_hasGSWitness {eps : ℝ} (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    let out := Oracle.Program.eval P (fullProgram hP.ell_pos hP.D_pos hP.Delta_pos heps
      (chosenProjectX hP) (chosenProjectY hP) (chosenProjectX_spec hP) (chosenProjectY_spec hP)
      P.x0 hP.x0_mem hzero)
    HasGSWitness P eps out.1 out.2 := by
  simp only [fullProgram, Oracle.Program.eval_bind]
  let J := GSRun.stage hP.ell_pos hP.D_pos heps
  have hs := eval_program (eta := eps / 2) hP hzero J
    (GSRun.refinementFactor ell (Tracking.curvature (ell / 8) J))
  rw [hs.1, hs.2]
  exact refined_readout_hasGSWitness hP hzero heps

end
end NCC.Extensions.GSProgram
