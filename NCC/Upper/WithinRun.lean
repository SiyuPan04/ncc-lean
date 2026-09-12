import NCC.Upper.WithinFirstStop

/-!
# Current output guarantee for the feasible-domain source class

All gap, startup, and homotopy premises are discharged directly from
`WithinClass`. The final stationarity vector is the actual gradient of
the actual Moreau envelope, using only feasible-domain differentiation.
-/
namespace NCC.Upper.WithinRun
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open PointwiseConjugate RelativeFOAM RelativeFOAMContraction ScaledOperator
open ProjectionGeometry TrackingConcrete OuterTrajectoryConcrete
open HomotopyRun StartupConcrete InitialGapBounds HomotopySchedule UniformSchedule
open AnalyticBridge WithinFirstStop
set_option maxHeartbeats 3000000
variable {m n : Nat} {ell D Delta eps : ℝ} {P : NCCInstance m n}

theorem dual_vecSq_le (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (y : EVec n) (hy : y ∈ P.Y) : vecSq y ≤ D ^ 2 := by
  simpa only [sub_zero] using hP.dual_diameter y hy 0 hzero

theorem classValueInf_le {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    {x : EVec m} (hx : x ∈ P.X) :
    classValueInf P ≤ ValueOn P.Y P.f x := by
  unfold classValueInf
  exact csInf_le hP.value_bddBelow ⟨x, hx, rfl⟩

theorem regularizedClassLower_le {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (hr : 0 ≤ r)
    {x : EVec m} (hx : x ∈ P.X) :
    regularizedClassLower P r D ≤
      DualRegularizedValueOn P.Y P.f r x := by
  have hbias := dualRegularizedValue_bias hr
    (dual_vecSq_le hP hzero)
    (hP.maximum_attained hx)
    (hP.regularized_maximum_attained x hx)
  have hinf := classValueInf_le hP hx
  unfold regularizedClassLower
  linarith

theorem regularized_initial_gap {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (hr : 0 ≤ r) :
    DualRegularizedValueOn P.Y P.f r P.x0 -
        regularizedClassLower P r D ≤ Delta + r / 2 * D ^ 2 := by
  have hbias := dualRegularizedValue_bias hr
    (dual_vecSq_le hP hzero)
    (hP.maximum_attained hP.x0_mem)
    (hP.regularized_maximum_attained P.x0 hP.x0_mem)
  unfold regularizedClassLower classValueInf
  have hgap : ValueOn P.Y P.f P.x0 - sInf (ValueOn P.Y P.f '' P.X) ≤ Delta := by
    simpa only [hP.initialization] using hP.initial_gap
  linarith [hgap]

/-- The actual selected regularized prox point obeys the startup displacement
bound used by `startup_pzr_computable_majorant`. -/
theorem selected_regularizedProx_displacement {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    (hr : 0 ≤ r)
    (hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell) :
    ell * vecSq (P.x0 - selectedProx hexistsR P.x0) ≤
      Delta + r / 2 * D ^ 2 := by
  apply TrackingAnalytic.prox_displacement_from_initial_gap hP.x0_mem
    (selectedProx_spec hexistsR P.x0)
    (regularizedClassLower_le hP hzero hr
      (selectedProx_spec hexistsR P.x0).1)
  exact regularized_initial_gap hP hzero hr

/-- The chosen lower level also bounds the genuine regularized Moreau
envelope at every anchor. -/
theorem regularizedClassLower_le_envelope {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    (hr : 0 ≤ r) (hell : 0 ≤ ell)
    (hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell) (z : EVec m) :
    regularizedClassLower P r D ≤
      regularizedEnvelope P.X P.Y P.f ell r hexistsR z := by
  have hvalue := regularizedClassLower_le hP hzero hr
    (selectedProx_spec hexistsR z).1
  have hsq : 0 ≤ ell * vecSq (selectedProx hexistsR z - z) := by
    exact mul_nonneg hell (Tracking.vecSq_nonneg _)
  unfold regularizedEnvelope moreauEnvelope proxObjective
  linarith

/-- At the original anchor, the regularized Moreau envelope inherits the same
`Delta + r D²/2` upper gap. -/
theorem initial_envelope_gap {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (hr : 0 ≤ r)
    (hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell) :
    regularizedEnvelope P.X P.Y P.f ell r hexistsR P.x0 -
        regularizedClassLower P r D ≤ Delta + r / 2 * D ^ 2 := by
  have hprox := (selectedProx_spec hexistsR P.x0).2 P.x0 hP.x0_mem
  have hzeroSq : vecSq (P.x0 - P.x0) = 0 := by
    simp [vecSq, NCPLVerification.vecSq]
  unfold regularizedEnvelope moreauEnvelope proxObjective
  rw [hzeroSq] at hprox
  have hgap := regularized_initial_gap hP hzero hr
  linarith

/-- The constant `31` in the final certificate calculation follows from a
homotopy energy majorant `B ≤ 15 (Delta + r D²)`. -/
theorem initial_snapshot_potential_bound {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    (hr : 0 ≤ r)
    {hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell}
    (sys : OuterSystem P.X P.Y P.f ell r hexistsR)
    (R : Snapshot (m := m) P.Y) (hz : R.z = P.x0)
    (hB : R.B ≤ 15 * (Delta + r * D ^ 2)) :
    snapshotPotential sys R - regularizedClassLower P r D ≤
      31 * (Delta + r * D ^ 2) := by
  have henv := initial_envelope_gap hP hzero hr hexistsR
  unfold snapshotPotential
  rw [hz]
  nlinarith

theorem startup_snapshot_energy {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y)
    (hr : r = ell / 8)
    (hexists0 : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell)
    (sys0 : OuterSystem P.X P.Y P.f ell r hexists0) :
    let R0 : Snapshot (m := m) P.Y :=
      { z := P.x0
        state := startupState sys0 hzero
        B := 8 * (Delta + (ell / 8) * D ^ 2) }
    snapshotEnergy sys0 R0 ≤ R0.B := by
  subst r
  dsimp
  let Sseed := startupSeed (ell := ell) hzero
  let O := sys0.oracle P.x0 Sseed
  let st := sys0.stationary P.x0
  have hfast : IsGammaSubgradient P.X P.Y
      (decurved P.f ell (ell / 8) P.x0) O.qFastNext
      ⟨O.yFastNext, sys0.oracle_feasible P.x0 Sseed⟩ O.xFast O.wFastNext :=
    sys0.oracle_subgradient P.x0 Sseed
  have hres : RelativeResidual ell (ell / 8) (coincidentState
      ((-ell) • P.x0) 0)
      (startupOutput O.xFast O.qFastNext O.yFastNext O.wFastNext) := by
    simpa [Sseed, startupSeed, O, startupOutput] using
      sys0.oracle_residual P.x0 Sseed
  have hprimal : ell * vecSq
      (P.x0 - selectedProx hexists0 P.x0) ≤
        Delta + (ell / 8) / 2 * D ^ 2 := by
    simpa using selected_regularizedProx_displacement hP hzero
      (div_nonneg hP.ell_pos.le (by norm_num)) hexists0
  have hstartup := startup_pzr_computable_majorant
    hP.ell_pos hP.Delta_pos.le (sq_nonneg D)
    hfast st.subgradient st.stationQ st.stationY hres
    hprimal
    (dual_vecSq_le hP hzero
      st.yStar.1 st.yStar.2)
  dsimp [snapshotEnergy, energyAt, startupState, Sseed, O, st]
  simpa using hstartup.2


theorem initialized_homotopy_snapshot {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    {prox : ProxFamily P.X P.Y P.f ell (ell / 8)}
    (systems : SystemFamily P.X P.Y P.f ell (ell / 8) prox) (j : Nat) :
    let S0 := startupState (systems 0) hzero
    let B0 := 8 * (Delta + (ell / 8) * D ^ 2)
    let Rj := homotopySnapshot (D := D) (B0 := B0)
      systems P.x0 S0 j
    snapshotEnergy (systems j) Rj ≤ Rj.B ∧
      0 ≤ Rj.B ∧
      Rj.B ≤ 15 * (Delta + Tracking.curvature (ell / 8) j * D ^ 2) := by
  dsimp
  let B0 : ℝ := 8 * (Delta + (ell / 8) * D ^ 2)
  let S0 : ValidState (m := m) P.Y := startupState (systems 0) hzero
  have hE0 : snapshotEnergy (systems 0)
      (homotopySnapshot (D := D) (B0 := B0) systems P.x0 S0 0) ≤ B0 := by
    have hs := startup_snapshot_energy hP hzero
      (by simp [Tracking.curvature]) (prox 0) (systems 0)
    simpa [B0, S0, homotopySnapshot, homotopyState,
      Tracking.homotopyMajorant, Tracking.curvature] using hs
  have henergy := homotopySnapshot_energy_le hP.ell_pos
    (div_pos hP.ell_pos (by norm_num)) (le_rfl) hP.D_pos.le
    (fun y => dual_vecSq_le
      hP hzero y.1 y.2)
    systems P.x0 S0 hE0 j
  have hB0 : 0 ≤ B0 := by
    dsimp [B0]
    exact mul_nonneg (by norm_num)
      (add_nonneg hP.Delta_pos.le
        (mul_nonneg (div_nonneg hP.ell_pos.le (by norm_num)) (sq_nonneg D)))
  have hnonneg := homotopyMajorant_nonneg
    (r0 := ell / 8) (D2 := D ^ 2) (B0 := B0)
    (div_nonneg hP.ell_pos.le (by norm_num)) (sq_nonneg D) hB0 j
  have huniform := Tracking.homotopy_uniform_majorant
    (r0 := ell / 8) (D2 := D ^ 2) (Delta := Delta)
    j hP.Delta_pos.le
    (div_nonneg hP.ell_pos.le (by norm_num)) (sq_nonneg D)
  have henergy' : snapshotEnergy (systems j)
      (homotopySnapshot (D := D) (B0 := B0) systems P.x0 S0 j) ≤
        (homotopySnapshot (D := D) (B0 := B0) systems P.x0 S0 j).B := by
    simpa [homotopySnapshot] using henergy
  have hnonneg' : 0 ≤
      (homotopySnapshot (D := D) (B0 := B0) systems P.x0 S0 j).B := by
    simpa [homotopySnapshot] using hnonneg
  have huniform' :
      (homotopySnapshot (D := D) (B0 := B0) systems P.x0 S0 j).B ≤
        15 * (Delta + Tracking.curvature (ell / 8) j * D ^ 2) := by
    simpa [homotopySnapshot, B0] using huniform
  simpa [S0, B0] using ⟨henergy', hnonneg', huniform'⟩

theorem initializedSnapshot_energy (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y)
    {prox : ProxFamily P.X P.Y P.f ell (ell / 8)}
    (systems : SystemFamily P.X P.Y P.f ell (ell / 8) prox) (j : Nat) :
    snapshotEnergy (systems j)
      (initializedSnapshot (D := D) (Delta := Delta) systems hzero j) ≤
      (initializedSnapshot (D := D) (Delta := Delta) systems hzero j).B := by
  have h := initialized_homotopy_snapshot hP hzero systems j
  exact h.1.trans h.2.2

/-- First geometric regularization level reaching the current target. -/
def stage (hP : WithinClass ell D Delta P) (heps : 0 < eps) : Nat :=
  homotopyStage (ell / 8) (targetCurvature ell D eps)
    (div_pos hP.ell_pos (by norm_num))
    (targetCurvature_pos hP.ell_pos hP.D_pos heps)

def finalCurvature (hP : WithinClass ell D Delta P) (heps : 0 < eps) : ℝ :=
  Tracking.curvature (ell / 8) (stage hP heps)

theorem finalCurvature_pos (hP : WithinClass ell D Delta P) (heps : 0 < eps) :
    0 < finalCurvature hP heps :=
  HomotopyCost.curvature_pos (div_pos hP.ell_pos (by norm_num)) _

/-- Both sides of the literal final-curvature interval, including stage zero. -/
theorem finalCurvature_interval (hP : WithinClass ell D Delta P) (heps : 0 < eps) :
    targetCurvature ell D eps / 4 < finalCurvature hP heps ∧
      finalCurvature hP heps ≤ targetCurvature ell D eps :=
  homotopyStage_target_comparison_total
    (div_pos hP.ell_pos (by norm_num))
    (targetCurvature_pos hP.ell_pos hP.D_pos heps)
    targetCurvature_le_ell_div_eight

def initialSnapshot (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) : Snapshot (m := m) P.Y :=
  initializedSnapshot (D := D) (Delta := Delta)
    (firstStopSystemFamily hP) hzero (stage hP heps)

def output (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) : EVec m :=
  Selection.selectedAnchor (firstStopSystemFamily hP (stage hP heps))
    (initialSnapshot hP hzero heps) (Selection.outerIterations ell Delta eps)
    (Selection.outerIterations_pos hP.ell_pos hP.Delta_pos)

theorem initialSnapshot_z (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    (initialSnapshot hP hzero heps).z = P.x0 := rfl

theorem initialSnapshot_budget (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    (initialSnapshot hP hzero heps).B =
      15 * (Delta + finalCurvature hP heps * D ^ 2) := rfl

theorem output_mem (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    output hP hzero heps ∈ P.X :=
  Selection.selectedAnchor_mem _ _ hP.x0_mem _ _

/-- Feasible optimization stationarity for the actual Moreau gradient,
with all algorithmic and analytic premises derived from the source class. -/
theorem output_is_OS (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    Moreau.Within.IsOS hP eps (output hP hzero heps) := by
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
    WithinRegularization.value_weaklyConvex hP
  have hlower : ∀ z, regularizedClassLower P r D ≤
      regularizedEnvelope P.X P.Y P.f ell r (WithinFirstStop.proxFamily hP J) z :=
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
      vecSq (residualGradient (WithinFirstStop.proxFamily hP J)
        (output hP hzero heps)) ≤
        (32 * ell / (T : ℝ)) * (31 * (Delta + r * D ^ 2)) :=
    hgrad.trans (mul_le_mul_of_nonneg_left hpotential hcoeff)
  have hbiasBudget : 2 * ell * r * D ^ 2 ≤ eps ^ 2 / 4 :=
    homotopy_output_bias_budget hP.ell_pos hP.D_pos heps hr hrupper
  have hmass : ell * (r * D ^ 2) ≤ eps ^ 2 / 8 := by
    nlinarith
  have hreg :
      vecSq (residualGradient (WithinFirstStop.proxFamily hP J)
        (output hP hzero heps)) < eps ^ 2 / 4 :=
    Selection.current_horizon_gradient_budget hP.ell_pos hP.Delta_pos heps
      hmass hgradBudget
  have htarget : r ≤ eps ^ 2 / (8 * ell * D ^ 2) :=
    hrupper.trans targetCurvature_le_bias_branch
  exact WithinRegularization.os_of_regularized_gradient hP hr.le heps htarget
    (output_mem hP hzero heps) hreg.le

end
end NCC.Upper.WithinRun
