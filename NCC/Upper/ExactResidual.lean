import NCC.Upper.WithinProgram

/-!
# The literal residual lemma with the actual envelope infimum

The infimum is certified as a greatest lower bound of a nonempty,
bounded-below range. The current startup, trajectory, and least-Q output
are used directly; no initial-energy or analytic-system premise is added.
-/
namespace NCC.Upper.ExactResidual
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open OuterTrajectoryConcrete AnalyticBridge WithinFirstStop WithinRun InitialGapBounds
set_option maxHeartbeats 3000000
variable {m n : Nat} {ell D Delta eps r : ℝ} {P : NCCInstance m n}

theorem envelope_bddBelow (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) :
    BddBelow (Set.range (WithinRegularization.envelope hP hr)) := by
  refine ⟨regularizedClassLower P r D, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact regularizedClassLower_le_envelope hP hP.dual_origin hr hP.ell_pos.le _ z

theorem envelope_infimum (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) :
    IsGLB (Set.range (WithinRegularization.envelope hP hr))
      (sInf (Set.range (WithinRegularization.envelope hP hr))) :=
  isGLB_csInf (Set.range_nonempty _) (envelope_bddBelow hP hr)

theorem selected_gradient_actual_infimum (hP : WithinClass ell D Delta P)
    (hr : 0 < r) (hrle : r ≤ ell / 8)
    {hexistsR : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell}
    (sys : OuterSystem P.X P.Y P.f ell r hexistsR)
    (R0 : Snapshot (m := m) P.Y)
    (hE0 : snapshotEnergy sys R0 ≤ R0.B) (hB0 : 0 ≤ R0.B)
    (T : Nat) (hT : 0 < T) :
    vecSq (WithinRegularization.gradient hP hr.le
      (Selection.selectedAnchor sys R0 T hT)) ≤
      (32 * ell / (T : ℝ)) * (snapshotPotential sys R0 -
        sInf (Set.range (WithinRegularization.envelope hP hr.le))) := by
  apply Selection.selected_regularized_gradient_bound hP.X_nonempty hP.ell_pos
    hr hrle (WithinRegularization.value_weaklyConvex hP) sys R0 hE0 hB0 T hT
  intro z
  exact csInf_le (envelope_bddBelow hP hr.le) ⟨z, rfl⟩

/-- All three printed residual conclusions, on the actual initialized
current trajectory and its least-index minimum-Q output. The first two
hold at every time, hence in particular throughout the printed horizon. -/
theorem residual_comparison (hP : WithinClass ell D Delta P) (heps : 0 < eps) :
    let J := stage hP heps
    let r := finalCurvature hP heps
    let hr := finalCurvature_pos hP heps
    let sys := firstStopSystemFamily hP J
    let R0 := initialSnapshot hP hP.dual_origin heps
    let T := Selection.outerIterations ell Delta eps
    (∀ t : Nat,
      observable sys (trajectory sys R0 t) ≤
        3 * (ell * vecSq (anchorError sys (trajectory sys R0 t)) +
          (trajectory sys R0 t).B) ∧
      vecSq (WithinRegularization.gradient hP hr.le (trajectory sys R0 t).z) ≤
        8 * ell * observable sys (trajectory sys R0 t)) ∧
    vecSq (WithinRegularization.gradient hP hr.le
      (output hP hP.dual_origin heps)) ≤
      (32 * ell / (T : ℝ)) * (snapshotPotential sys R0 -
        sInf (Set.range (WithinRegularization.envelope hP (r := r) hr.le))) := by
  dsimp only
  let J := stage hP heps
  let r := finalCurvature hP heps
  let sys := firstStopSystemFamily hP J
  let R0 := initialSnapshot hP hP.dual_origin heps
  have hr : 0 < r := finalCurvature_pos hP heps
  have hrle : r ≤ ell / 8 :=
    (finalCurvature_interval hP heps).2.trans UniformSchedule.targetCurvature_le_ell_div_eight
  have hE0 : snapshotEnergy sys R0 ≤ R0.B :=
    initializedSnapshot_energy hP hP.dual_origin (firstStopSystemFamily hP) J
  have hB0 : 0 ≤ R0.B := by
    change 0 ≤ 15 * (Delta + r * D ^ 2)
    have hDelta := hP.Delta_pos
    positivity
  have hEB := trajectory_energy_le_B hP.X_nonempty hP.ell_pos hr hrle sys R0 hE0
  constructor
  · intro t
    exact ⟨observable_le_three_residual hP.ell_pos hr sys _ (hEB t),
      regularizedGradient_sq_le_observable hP.ell_pos hr sys _ (hEB t)⟩
  · exact selected_gradient_actual_infimum hP hr hrle sys R0 hE0 hB0
      (Selection.outerIterations ell Delta eps)
      (Selection.outerIterations_pos hP.ell_pos hP.Delta_pos)

/-- The same actual-infimum bound for the genuinely evaluated, reply-driven
current client. Full differentiation of the displayed envelope is supplied
by `WithinRegularization.hasFDerivAt_envelope`. -/
theorem evaluated_program_gradient_bound (hP : WithinClass ell D Delta P)
    (heps : 0 < eps) :
    let hr := finalCurvature_pos hP heps
    let sys := firstStopSystemFamily hP (stage hP heps)
    let R0 := initialSnapshot hP hP.dual_origin heps
    vecSq (WithinRegularization.gradient hP hr.le
      (Oracle.Program.eval P
        (CurrentProgram.program hP.ell_pos hP.D_pos hP.Delta_pos heps
          (WithinSystem.chosenProjectX hP) (WithinSystem.chosenProjectY hP)
          (WithinSystem.chosenProjectX_spec hP) (WithinSystem.chosenProjectY_spec hP)
          P.x0 hP.x0_mem hP.dual_origin))) ≤
      (32 * ell / (Selection.outerIterations ell Delta eps : ℝ)) *
        (snapshotPotential sys R0 -
          sInf (Set.range (WithinRegularization.envelope hP hr.le))) := by
  dsimp only
  rw [WithinProgram.eval_program]
  exact (residual_comparison hP heps).2

end
end NCC.Upper.ExactResidual
