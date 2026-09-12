import NCC.Upper.AdaptiveFOAMProgram

/-!
# The current reply-driven startup, homotopy, and outer program

All program constructors receive only numerical parameters, known
projection geometry, and initial data. Objective values and gradients
can enter only through local oracle replies. The client performs the
literal current horizon of outer transitions and selects the least index
minimizing the current squared observable among the first `T` anchors.
-/

namespace NCC.Upper.CurrentProgram

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open RelativeFOAM RelativeFOAMContraction ProjectionGeometry
open SharedOracle SystemInstantiation OuterTrajectoryConcrete
open HomotopyRun HomotopySchedule UniformSchedule
open AnalyticBridge AdaptiveMicroProgram

set_option maxHeartbeats 2000000

variable {m n : Nat} {ell r D Delta eps : ℝ}
  {X : Set (EVec m)} {Y : Set (EVec n)}

/-- One first-success micro solve followed by the printed coincident reset. -/
def startupProgram (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (_hzero : (0 : EVec n) ∈ Y) :
    Oracle.Program X Y (ValidState (m := m) Y) := do
  let O ← AdaptiveMicroProgram.program (r := ell / 8) hell projectX projectY
    hprojX hprojY z0 (StartupConcrete.coincidentState ((-ell) • z0) 0)
  Oracle.Program.pure
    ⟨StartupConcrete.coincidentState O.1.qFastNext O.1.yFastNext, O.2⟩

/-- Reuse the returned state as curvature is divided by four. -/
def warmProgram (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) : Nat → ValidState (m := m) Y →
      Oracle.Program X Y (ValidState (m := m) Y)
  | 0, S => Oracle.Program.pure S
  | j + 1, S => do
      let Sold ← warmProgram hell projectX projectY hprojX hprojY z0 j S
      AdaptiveFOAMProgram.callProgram (r := Tracking.curvature (ell / 8) (j + 1))
        hell projectX projectY hprojX hprojY z0 (1 / 8) Sold

theorem eval_startupProgram {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) :
    Oracle.Program.eval P
      (startupProgram hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hzero) =
      startupState (firstStopSystemFamily hP 0) hzero := by
  apply Subtype.ext
  simp only [startupProgram, Oracle.Program.eval_bind, Oracle.Program.eval_pure,
    startupState_val]
  rw [(program_correct hP (div_nonneg hP.ell_pos.le (by norm_num)) le_rfl
    P.x0 (StartupConcrete.coincidentState ((-ell) • P.x0) 0)).1]
  have hfam (V : ValidState (m := m) P.Y) :
      (firstStopSystemFamily hP 0).oracle P.x0 V =
      firstStopOracle hP (CurrentCost.level_pos hP 0).le (CurrentCost.level_le hP 0)
        P.x0 V.1 := rfl
  rw [hfam]
  simp only [Tracking.curvature, pow_zero, div_one, startupSeed]

theorem eval_warmProgram {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (z0 : EVec m) (J : Nat)
    (S : ValidState (m := m) P.Y) :
    Oracle.Program.eval P
      (warmProgram hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z0 J S) =
      homotopyState (firstStopSystemFamily hP) z0 S J := by
  induction J with
  | zero => rfl
  | succ J ih =>
      rw [warmProgram, Oracle.Program.eval_bind, ih, homotopyState_succ]
      exact AdaptiveFOAMProgram.eval_callProgram_eq_family hP (J + 1) z0 (1 / 8) _

theorem startupProgram_depth (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hzero : (0 : EVec n) ∈ Y) :
    DepthAtMost (startupProgram hell projectX projectY hprojX hprojY z0 hzero)
      (ProjectedMicro.feasibleMicroIterations + 1) := by
  let finish : FeasibleMicroOutput m Y → Oracle.Program X Y (ValidState (m := m) Y) :=
    fun O => .pure ⟨StartupConcrete.coincidentState O.1.qFastNext O.1.yFastNext, O.2⟩
  have hb := (program_depth (r := ell / 8) hell projectX projectY hprojX hprojY
    z0 (StartupConcrete.coincidentState ((-ell) • z0) 0)).bind
      finish (fun _ => DepthAtMost.pure _ 0)
  simpa [startupProgram, finish] using hb

theorem warmProgram_depth (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (J : Nat) (S : ValidState (m := m) Y) :
    DepthAtMost (warmProgram hell projectX projectY hprojX hprojY z0 J S)
      (causalHomotopyCalls ell J) := by
  induction J with
  | zero => exact DepthAtMost.pure S 0
  | succ J ih =>
      exact ih.bind _ (fun Sold => AdaptiveFOAMProgram.callProgram_depth hell
        projectX projectY hprojX hprojY z0 (1 / 8) Sold)

theorem startupProgram_trace_length {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) :
    (queryTrace P
      (startupProgram hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hzero)).length =
      (CurrentCost.startupTrace hP hzero).length := by
  rw [startupProgram, queryTrace_bind, List.length_append]
  simpa only [queryTrace, List.length_nil, Nat.add_zero, CurrentCost.startupTrace,
    CurrentCost.microTrace_length, startupSeed] using
    (program_correct hP (div_nonneg hP.ell_pos.le (by norm_num)) le_rfl
      P.x0 (StartupConcrete.coincidentState ((-ell) • P.x0) 0)).2

theorem warmProgram_trace_length {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) :
    (queryTrace P
      (warmProgram hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 J
          (startupState (firstStopSystemFamily hP 0) hzero))).length =
      (CurrentCost.warmTrace hP hzero J).length := by
  induction J with
  | zero => rfl
  | succ J ih =>
      rw [warmProgram, queryTrace_bind, List.length_append, ih, eval_warmProgram,
        CurrentCost.warmTrace, List.length_append]
      congr 1
      exact AdaptiveFOAMProgram.blockProgram_trace_length_eq_macroTrace hP
        (CurrentCost.level_pos hP (J + 1)) (CurrentCost.level_le hP (J + 1))
        (MainTheorem.classProxFamily hP (J + 1)) P.x0 _ _

/-- One translated outer call. The next anchor is a known projection of
the retained fast state and the majorant uses the literal current update. -/
def nextProgram (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (R : FeasibleSnapshot X Y) : Oracle.Program X Y (FeasibleSnapshot X Y) :=
  let zNext := projectX ((-ell⁻¹) • R.1.state.1.qFast)
  let d := zNext - R.1.z
  do
    let Snext ← AdaptiveFOAMProgram.callProgram (r := r) hell projectX projectY
      hprojX hprojY zNext (1 / 400) (coTranslateValid ell d R.1.state)
    Oracle.Program.pure
      ⟨{ z := zNext
         state := Snext
         B := Tracking.nextMajorant (1 / 400) ell (vecSq d) R.1.B }, hprojX.mem _⟩

/-- Store every anchor through time `T`, using exactly `T` outer calls.
Values outside the visited range are harmless retained initial data. -/
def historyProgram (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY) : Nat → FeasibleSnapshot X Y →
      Oracle.Program X Y (Nat → FeasibleSnapshot X Y)
  | 0, R0 => Oracle.Program.pure (fun _ => R0)
  | t + 1, R0 => do
      let H ← historyProgram hell projectX projectY hprojX hprojY t R0
      let Rnext ← nextProgram (r := r) hell projectX projectY hprojX hprojY (H t)
      Oracle.Program.pure (fun i => if i = t + 1 then Rnext else H i)

theorem eval_nextProgram {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (J : Nat) (R : FeasibleSnapshot P.X P.Y) :
    (Oracle.Program.eval P
      (nextProgram (r := Tracking.curvature (ell / 8) J) hP.ell_pos
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) R)).1 =
      nextSnapshot (firstStopSystemFamily hP J) R.1 := by
  unfold nextProgram nextSnapshot
  simp only [Oracle.Program.eval_bind, Oracle.Program.eval_pure]
  rw [AdaptiveFOAMProgram.eval_callProgram_eq_runBlock]
  rfl

theorem eval_historyProgram_at {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (J T : Nat)
    (R0 : FeasibleSnapshot P.X P.Y) (i : Nat) (hi : i ≤ T) :
    (Oracle.Program.eval P
      (historyProgram (r := Tracking.curvature (ell / 8) J) hP.ell_pos
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) T R0) i).1 =
      trajectory (firstStopSystemFamily hP J) R0.1 i := by
  induction T generalizing i with
  | zero => have hi0 : i = 0 := by omega
            subst i
            rfl
  | succ T ih =>
      simp only [historyProgram, Oracle.Program.eval_bind, Oracle.Program.eval_pure]
      by_cases hit : i = T + 1
      · subst i
        simp only [ite_true]
        rw [eval_nextProgram, ih T le_rfl]
        rfl
      · simp only [if_neg hit]
        exact ih i (by omega)

theorem nextProgram_depth (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY) (R : FeasibleSnapshot X Y) :
    DepthAtMost (nextProgram (r := r) hell projectX projectY hprojX hprojY R)
      (blockIterations (alpha ell r) (1 / 400) * (ProjectedMicro.feasibleMicroIterations + 1)) := by
  let zNext := projectX ((-ell⁻¹) • R.1.state.1.qFast)
  let d := zNext - R.1.z
  let finish : ValidState (m := m) Y → Oracle.Program X Y (FeasibleSnapshot X Y) :=
    fun Snext => .pure
      ⟨{ z := zNext, state := Snext,
         B := Tracking.nextMajorant (1 / 400) ell (vecSq d) R.1.B }, hprojX.mem _⟩
  have hb := (AdaptiveFOAMProgram.callProgram_depth (r := r) hell projectX projectY
    hprojX hprojY zNext (1 / 400) (coTranslateValid ell d R.1.state)).bind
      finish (fun _ => DepthAtMost.pure _ 0)
  simpa [nextProgram, zNext, d, finish] using hb

theorem historyProgram_depth (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY) (T : Nat) (R0 : FeasibleSnapshot X Y) :
    DepthAtMost (historyProgram (r := r) hell projectX projectY hprojX hprojY T R0)
      (T * (blockIterations (alpha ell r) (1 / 400) *
        (ProjectedMicro.feasibleMicroIterations + 1))) := by
  induction T with
  | zero => simpa [historyProgram] using (DepthAtMost.pure (X := X) (Y := Y) (fun _ => R0) 0)
  | succ T ih =>
      let finish (H : Nat → FeasibleSnapshot X Y) (Rnext : FeasibleSnapshot X Y) :
          Oracle.Program X Y (Nat → FeasibleSnapshot X Y) :=
        .pure (fun i => if i = T + 1 then Rnext else H i)
      have htail (H : Nat → FeasibleSnapshot X Y) :=
        (nextProgram_depth (r := r) hell projectX projectY hprojX hprojY (H T)).bind
          (finish H) (fun _ => DepthAtMost.pure _ 0)
      have hb := ih.bind _ htail
      simpa [historyProgram, finish, Nat.succ_mul] using hb

theorem nextProgram_trace_length_at {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps)
    (t : Nat) (R : FeasibleSnapshot P.X P.Y)
    (hR : R.1 = trajectory (firstStopSystemFamily hP (CurrentRun.stage hP heps))
      (CurrentRun.initialSnapshot hP hzero heps) t) :
    (queryTrace P
      (nextProgram (r := CurrentRun.finalCurvature hP heps) hP.ell_pos
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) R)).length =
      (CurrentCost.outerStageTrace hP hzero heps t).length := by
  rw [nextProgram, queryTrace_bind, List.length_append]
  change (queryTrace P _).length + 0 = _
  rw [Nat.add_zero, AdaptiveFOAMProgram.callProgram,
    AdaptiveFOAMProgram.blockProgram_trace_length_eq_macroTrace hP
      (CurrentRun.finalCurvature_pos hP heps) (CurrentCost.level_le hP _)
      (MainTheorem.classProxFamily hP _)]
  rw [hR]
  rfl

theorem historyProgram_trace_length {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps)
    (T : Nat) (R0 : FeasibleSnapshot P.X P.Y)
    (hR0 : R0.1 = CurrentRun.initialSnapshot hP hzero heps) :
    (queryTrace P
      (historyProgram (r := CurrentRun.finalCurvature hP heps) hP.ell_pos
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) T R0)).length =
      (CurrentCost.outerTrace hP hzero heps T).length := by
  induction T with
  | zero => rfl
  | succ T ih =>
      rw [historyProgram, queryTrace_bind, List.length_append, ih,
        queryTrace_bind, List.length_append]
      change _ + ((queryTrace P _).length + 0) = _
      rw [Nat.add_zero, CurrentCost.outerTrace, List.length_append]
      congr 1
      apply nextProgram_trace_length_at hP hzero heps T
      simpa only [CurrentRun.finalCurvature, hR0] using
        eval_historyProgram_at hP (CurrentRun.stage hP heps) T R0 T le_rfl

/-- The visible score uses only known projections and the retained state. -/
def localScore (ell : ℝ) (projectX : EVec m → EVec m)
    (R : Snapshot (m := m) Y) : ℝ :=
  ell * vecSq (projectX ((-ell⁻¹) • R.state.1.qFast) - R.z) + R.B

theorem localScore_eq_observable {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (J : Nat) (R : Snapshot (m := m) P.Y) :
    localScore ell (chosenProjectX hP) R = observable (firstStopSystemFamily hP J) R := rfl

/-- Finite least-index selection depends only on the inspected range. -/
theorem leastMinimizer_congr (q q' : Nat → ℝ) (T : Nat) (hT : 0 < T)
    (hq : ∀ i, i < T → q i = q' i) :
    Selection.leastMinimizer q T hT = Selection.leastMinimizer q' T hT := by
  classical
  have hl := Selection.leastMinimizer_spec q T hT
  have hr := Selection.leastMinimizer_spec q' T hT
  apply Nat.le_antisymm
  · change Nat.find _ ≤ _
    apply Nat.find_min'
    refine ⟨hr.1, fun i hi => ?_⟩
    rw [hq _ hr.1, hq i hi]
    exact hr.2 i hi
  · change Nat.find _ ≤ _
    apply Nat.find_min'
    refine ⟨hl.1, fun i hi => ?_⟩
    rw [← hq _ hl.1, ← hq i hi]
    exact hl.2 i hi

def numericalStage (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) : Nat :=
  homotopyStage (ell / 8) (targetCurvature ell D eps)
    (div_pos hell (by norm_num)) (targetCurvature_pos hell hD heps)

/-- Startup and warm calls, followed by the actual-state budget reset. -/
def initializeProgram (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y)
    (D Delta : ℝ) (J : Nat) : Oracle.Program X Y (FeasibleSnapshot X Y) := do
  let Sstart ← startupProgram hell projectX projectY hprojX hprojY z0 hzero
  let Sfinal ← warmProgram hell projectX projectY hprojX hprojY z0 J Sstart
  Oracle.Program.pure
    ⟨{ z := z0, state := Sfinal,
       B := 15 * (Delta + Tracking.curvature (ell / 8) J * D ^ 2) }, hz0⟩

theorem eval_initializeProgram {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) :
    (Oracle.Program.eval P
      (initializeProgram hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP)
        P.x0 hP.x0_mem hzero D Delta J)).1 =
      initializedSnapshot (D := D) (Delta := Delta) (firstStopSystemFamily hP) hzero J := by
  simp only [initializeProgram, Oracle.Program.eval_bind, Oracle.Program.eval_pure,
    eval_startupProgram, eval_warmProgram]
  rfl

theorem initializeProgram_depth (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y)
    (D Delta : ℝ) (J : Nat) :
    DepthAtMost (initializeProgram hell projectX projectY hprojX hprojY z0 hz0 hzero D Delta J)
      ((ProjectedMicro.feasibleMicroIterations + 1) + causalHomotopyCalls ell J) := by
  let finish : ValidState (m := m) Y → Oracle.Program X Y (FeasibleSnapshot X Y) :=
    fun Sfinal => .pure
      ⟨{ z := z0, state := Sfinal,
         B := 15 * (Delta + Tracking.curvature (ell / 8) J * D ^ 2) }, hz0⟩
  have htail (Sstart : ValidState (m := m) Y) :=
    (warmProgram_depth hell projectX projectY hprojX hprojY z0 J Sstart).bind
      finish (fun _ => DepthAtMost.pure _ 0)
  have hb := (startupProgram_depth hell projectX projectY hprojX hprojY z0 hzero).bind _ htail
  simpa [initializeProgram, finish] using hb

theorem initializeProgram_trace_length {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) :
    (queryTrace P
      (initializeProgram hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP)
        P.x0 hP.x0_mem hzero D Delta J)).length =
      (CurrentCost.startupTrace hP hzero).length + (CurrentCost.warmTrace hP hzero J).length := by
  rw [initializeProgram, queryTrace_bind, List.length_append, startupProgram_trace_length,
    queryTrace_bind, List.length_append, eval_startupProgram, warmProgram_trace_length]
  rfl

def selectHistory (ell : ℝ) (projectX : EVec m → EVec m)
    (T : Nat) (hT : 0 < T) (H : Nat → FeasibleSnapshot X Y) : EVec m :=
  (H (Selection.leastMinimizer (fun i => localScore ell projectX (H i).1) T hT)).1.z

theorem selectHistory_mem (ell : ℝ) (projectX : EVec m → EVec m)
    (T : Nat) (hT : 0 < T) (H : Nat → FeasibleSnapshot X Y) :
    selectHistory ell projectX T hT H ∈ X :=
  (H (Selection.leastMinimizer (fun i => localScore ell projectX (H i).1) T hT)).2

theorem eval_history_selected {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (J T : Nat) (hT : 0 < T)
    (R0 : FeasibleSnapshot P.X P.Y) :
    selectHistory ell (chosenProjectX hP) T hT
      (Oracle.Program.eval P
        (historyProgram (r := Tracking.curvature (ell / 8) J) hP.ell_pos
          (chosenProjectX hP) (chosenProjectY hP)
          (chosenProjectX_spec hP) (chosenProjectY_spec hP) T R0)) =
      Selection.selectedAnchor (firstStopSystemFamily hP J) R0.1 T hT := by
  let H := Oracle.Program.eval P
    (historyProgram (r := Tracking.curvature (ell / 8) J) hP.ell_pos
      (chosenProjectX hP) (chosenProjectY hP)
      (chosenProjectX_spec hP) (chosenProjectY_spec hP) T R0)
  let sys := firstStopSystemFamily hP J
  have hscores (i : Nat) (hi : i < T) :
      localScore ell (chosenProjectX hP) (H i).1 = observable sys (trajectory sys R0.1 i) := by
    rw [localScore_eq_observable, eval_historyProgram_at hP J T R0 i hi.le]
  have hsel := leastMinimizer_congr
    (fun i => localScore ell (chosenProjectX hP) (H i).1)
    (fun i => observable sys (trajectory sys R0.1 i)) T hT hscores
  unfold selectHistory Selection.selectedAnchor Selection.selectedIndex
  change (H _).1.z = _
  rw [hsel, eval_historyProgram_at hP J T R0 _
    (Selection.leastMinimizer_spec _ T hT).1.le]

/-- The current algorithm, with no objective supplied to the constructor. -/
def program (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y) :
    Oracle.Program X Y (EVec m) := do
  let J := numericalStage hell hD heps
  let r := Tracking.curvature (ell / 8) J
  let T := Selection.outerIterations ell Delta eps
  let R0 ← initializeProgram hell projectX projectY hprojX hprojY z0 hz0 hzero D Delta J
  let H ← historyProgram (r := r) hell projectX projectY hprojX hprojY T R0
  Oracle.Program.pure (selectHistory ell projectX T (Selection.outerIterations_pos hell hDelta) H)

theorem eval_program {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    Oracle.Program.eval P
      (program hP.ell_pos hP.D_pos hP.Delta_pos heps
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hzero) =
      CurrentRun.output hP hzero heps := by
  simp only [program, Oracle.Program.eval_bind, Oracle.Program.eval_pure]
  rw [eval_history_selected, eval_initializeProgram]
  rfl

/-- Uniform finite cap on every possible reply branch. It is a sum of
the genuine compositional query caps, not a definition of desired cost. -/
theorem program_depth (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y) :
    let J := numericalStage hell hD heps
    let r := Tracking.curvature (ell / 8) J
    DepthAtMost (program hell hD hDelta heps projectX projectY hprojX hprojY z0 hz0 hzero)
      ((ProjectedMicro.feasibleMicroIterations + 1) + causalHomotopyCalls ell J +
        Selection.outerIterations ell Delta eps *
          (blockIterations (alpha ell r) (1 / 400) * (ProjectedMicro.feasibleMicroIterations + 1))) := by
  dsimp only
  let J := numericalStage hell hD heps
  let r := Tracking.curvature (ell / 8) J
  let T := Selection.outerIterations ell Delta eps
  let finish : (Nat → FeasibleSnapshot X Y) → Oracle.Program X Y (EVec m) :=
    fun H => .pure (selectHistory ell projectX T (Selection.outerIterations_pos hell hDelta) H)
  have htail (R0 : FeasibleSnapshot X Y) :=
    (historyProgram_depth (r := r) hell projectX projectY hprojX hprojY T R0).bind
      finish (fun _ => DepthAtMost.pure _ 0)
  have hb := (initializeProgram_depth hell projectX projectY hprojX hprojY z0 hz0 hzero D Delta J).bind
    _ htail
  simpa [program, J, r, T, finish] using hb

/-- Executed first-stop counts exactly match the complete current
semantic count, including the literal `T` (not `T-1`) outer calls. -/
theorem program_trace_length {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    (queryTrace P
      (program hP.ell_pos hP.D_pos hP.Delta_pos heps
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hzero)).length =
      (CurrentCost.runTrace hP hzero heps).length := by
  rw [program, queryTrace_bind, List.length_append, initializeProgram_trace_length,
    queryTrace_bind, List.length_append]
  change _ + ((queryTrace P _).length + 0) = _
  rw [Nat.add_zero]
  have hh := historyProgram_trace_length hP hzero heps
    (Selection.outerIterations ell Delta eps) _
    (eval_initializeProgram hP hzero (CurrentRun.stage hP heps))
  dsimp only [CurrentRun.finalCurvature, CurrentRun.stage, numericalStage] at hh ⊢
  rw [hh]
  simp only [CurrentCost.runTrace, List.length_append, CurrentRun.stage]

theorem program_uniform_query_bound {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    ((queryTrace P
      (program hP.ell_pos hP.D_pos hP.Delta_pos heps
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hzero)).length : ℝ) ≤
      CurrentCost.traceRateConstant * (ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps) := by
  rw [program_trace_length]
  simpa only [mul_assoc] using CurrentCost.runTrace_uniform_bound hP hzero heps

theorem program_all_histories_feasible
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y)
    (fallback : Oracle.Query m n) (hfallback : fallback.1 ∈ X ∧ fallback.2 ∈ Y)
    (t : Nat) (history : Oracle.ReplyHistory m n t) :
    let q := Oracle.Program.queryAfterHistory
      (program hell hD hDelta heps projectX projectY hprojX hprojY z0 hz0 hzero)
        fallback t history
    q.1 ∈ X ∧ q.2 ∈ Y :=
  Oracle.Program.queryAfterHistory_mem _ fallback hfallback t history

/-- Even arbitrary instance replies leave the returned anchor feasible. -/
theorem eval_program_mem (P : NCCInstance m n)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z0 : EVec m) (hz0 : z0 ∈ X) (hzero : (0 : EVec n) ∈ Y) :
    Oracle.Program.eval P
      (program hell hD hDelta heps projectX projectY hprojX hprojY z0 hz0 hzero) ∈ X := by
  simp only [program, Oracle.Program.eval_bind, Oracle.Program.eval_pure]
  exact selectHistory_mem _ _ _ _ _

theorem eval_program_is_OS {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (Oracle.Program.eval P
        (program hP.ell_pos hP.D_pos hP.Delta_pos heps
          (chosenProjectX hP) (chosenProjectY hP)
          (chosenProjectX_spec hP) (chosenProjectY_spec hP) P.x0 hP.x0_mem hzero)) := by
  rw [eval_program]
  exact CurrentRun.output_is_OS hP hzero heps

end
end NCC.Upper.CurrentProgram
