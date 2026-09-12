import NCCLowerBoundVerification.Upper.MainTheorem

/-!
# Current observable residual on actual FOAM states

The current manuscript minimizes `ell * ‖d‖² + B`, whereas the legacy
development minimizes `2 * ell * ‖d‖ + 2 * sqrt (ell * B)`. This module
proves the current observable's analytic estimates on the actual retained
FOAM state and resets the initial outer budget to the current value `15`.

The final theorem constructs every analytic system from `IsNCCClass`;
contraction, readout, stationary saddle points, and initial energy are not
extra hypotheses. The micro implementation selects the first successful
positive-index residual test, using the legacy universal cutoff only to
prove termination. This module does not assert the final theorem about the
current minimum-index output and total oracle cost.
-/

namespace NCC.Upper.AnalyticBridge

noncomputable section

open NCCLowerBoundVerification
open NCCLowerBoundVerification.Upper
open OuterTrajectoryConcrete HomotopyRun

variable {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
  {f : EVec m → EVec n → ℝ} {ell r : ℝ}
  {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}

/-- The current manuscript's `Q`, evaluated from the actual readout. -/
def observable (sys : OuterSystem X Y f ell r hexistsR)
    (R : Snapshot (m := m) Y) : ℝ :=
  ell * vecSq (stepDisplacement sys R) + R.B

/-- Current `Q ≤ 3R`, with the readout inequality proved analytically. -/
theorem observable_le_three_residual
    (hell : 0 < ell) (hr : 0 < r)
    (sys : OuterSystem X Y f ell r hexistsR)
    (R : Snapshot (m := m) Y)
    (hEB : snapshotEnergy sys R ≤ R.B) :
    observable sys R ≤
      3 * (ell * vecSq (anchorError sys R) + R.B) := by
  have hread : ell * vecSq (readoutError sys R) ≤ R.B :=
    (readout_error_le_energy hell hr sys R).trans hEB
  have hd := Tracking.vecSq_neg_add_le_two
    (anchorError sys R) (readoutError sys R)
  rw [← displacement_eq sys R] at hd
  have hscaled := mul_le_mul_of_nonneg_left hd hell.le
  have ha := mul_nonneg hell.le (Tracking.vecSq_nonneg (anchorError sys R))
  unfold observable
  nlinarith

/-- The actual regularized Moreau gradient satisfies the current bound. -/
theorem regularizedGradient_sq_le_observable
    (hell : 0 < ell) (hr : 0 < r)
    (sys : OuterSystem X Y f ell r hexistsR)
    (R : Snapshot (m := m) Y)
    (hEB : snapshotEnergy sys R ≤ R.B) :
    vecSq (residualGradient hexistsR R.z) ≤ 8 * ell * observable sys R := by
  have hread : ell * vecSq (readoutError sys R) ≤ R.B :=
    (readout_error_le_energy hell hr sys R).trans hEB
  have ha := Tracking.vecSq_neg_add_le_two
    (stepDisplacement sys R) (readoutError sys R)
  have heq : -stepDisplacement sys R + readoutError sys R =
      anchorError sys R := by
    rw [displacement_eq sys R]
    abel
  rw [heq] at ha
  have hscaled := mul_le_mul_of_nonneg_left ha
    (show 0 ≤ 4 * ell ^ 2 by positivity)
  have hreadScaled := mul_le_mul_of_nonneg_left hread
    (show 0 ≤ 8 * ell by positivity)
  unfold residualGradient
  rw [vecSq_smul]
  change (2 * ell) ^ 2 * vecSq (anchorError sys R) ≤ _
  unfold observable
  nlinarith

/-- Current `W⁺ - W ≤ -Q/4` on an actual FOAM outer update. -/
theorem observable_descent
    (hell : 0 < ell) (hr : 0 < r)
    (hweakR : IsWeaklyConvexOn ell X (DualRegularizedValueOn Y f r))
    (sys : OuterSystem X Y f ell r hexistsR)
    (R : Snapshot (m := m) Y)
    (hEB : snapshotEnergy sys R ≤ R.B) :
    snapshotPotential sys (nextSnapshot sys R) - snapshotPotential sys R ≤
      -(1 / 4 : ℝ) * observable sys R := by
  have hW := one_step_potential_descent hell hr hweakR sys R hEB
  have hQ := observable_le_three_residual hell hr sys R hEB
  linarith

/-! ## The appendix's first successful micro test -/

open RelativeFOAM RelativeFOAMContraction ScaledOperator SystemInstantiation

def microUAt (P : NCCInstance m n) (ell r : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (z : EVec m) (S : State m n) (s : Nat) : Pair m n :=
  projectedIterate (scaledProject ell projectX projectY)
    (scaledOperator ell r (qCenter ell r S) (yCenter ell r S)
      (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z))
    (M0 ^ 2)⁻¹ (scaledCenter ell (qCenter ell r S) (yCenter ell r S)) s

def microBAt (P : NCCInstance m n) (ell r : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (z : EVec m) (S : State m n) (s : Nat) : Pair m n :=
  projectedB (scaledProject ell projectX projectY)
    (scaledOperator ell r (qCenter ell r S) (yCenter ell r S)
      (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z))
    (M0 ^ 2)⁻¹ (scaledCenter ell (qCenter ell r S) (yCenter ell r S)) (s - 1)

def microOutputAt (P : NCCInstance m n) (ell r : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (z : EVec m) (S : State m n) (s : Nat) : MicroOutput m n :=
  decodeOutput ell (ClassOperator.gradXHat P ell z)
    (ClassOperator.gradYHat P ell z)
    (microUAt P ell r projectX projectY z S s)
    (microBAt P ell r projectX projectY z S s)

/-- Squaring both nonnegative lengths gives exactly the printed test.
The positive-index requirement models the repeat loop's mandatory first step. -/
def microStops (P : NCCInstance m n) (ell r : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (z : EVec m) (S : State m n) (s : Nat) : Prop :=
  1 ≤ s ∧ RelativeResidual ell r S
    (microOutputAt P ell r projectX projectY z S s)

theorem microStops_iff_printed_test (P : NCCInstance m n)
    {ell : ℝ} (hell : 0 < ell) (r : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (z : EVec m) (S : State m n) (s : Nat) :
    microStops P ell r projectX projectY z S s ↔
      1 ≤ s ∧
        ProjectedMicro.euclideanLength
          (scaledOperator ell r (qCenter ell r S) (yCenter ell r S)
            (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z)
            (microUAt P ell r projectX projectY z S s) +
            microBAt P ell r projectX projectY z S s) ≤
          ProjectedMicro.euclideanLength
            (microUAt P ell r projectX projectY z S s -
              scaledCenter ell (qCenter ell r S) (yCenter ell r S)) := by
  unfold microStops microOutputAt
  rw [← stopping_iff_relativeResidual hell]
  apply and_congr_right
  intro _
  constructor
  · exact Real.sqrt_le_sqrt
  · intro h
    have hleft := ProjectedMicro.euclideanLength_sq
      (scaledOperator ell r (qCenter ell r S) (yCenter ell r S)
        (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z)
        (microUAt P ell r projectX projectY z S s) +
        microBAt P ell r projectX projectY z S s)
    have hright := ProjectedMicro.euclideanLength_sq
      (microUAt P ell r projectX projectY z S s -
        scaledCenter ell (qCenter ell r S) (yCenter ell r S))
    have hnonneg := ProjectedMicro.euclideanLength_nonneg
      (scaledOperator ell r (qCenter ell r S) (yCenter ell r S)
        (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z)
        (microUAt P ell r projectX projectY z S s) +
        microBAt P ell r projectX projectY z S s)
    nlinarith

theorem exists_microStops {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) :
    ∃ s, microStops P ell r (chosenProjectX hP) (chosenProjectY hP) z S s := by
  refine ⟨ProjectedMicro.feasibleMicroIterations,
    ProjectedMicro.feasibleMicroIterations_positive, ?_⟩
  exact classOracle_residual hP hr hrle
    (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S

/-- The first successful residual test on the actual projected recurrence. -/
def firstStopIndex {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) : Nat := by
  classical
  exact Nat.find (exists_microStops hP hr hrle z S)

theorem firstStopIndex_spec {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) :
    microStops P ell r (chosenProjectX hP) (chosenProjectY hP) z S
      (firstStopIndex hP hr hrle z S) := by
  classical
  exact Nat.find_spec (exists_microStops hP hr hrle z S)

theorem firstStopIndex_minimal {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) (s : Nat)
    (hs : s < firstStopIndex hP hr hrle z S) :
    ¬ microStops P ell r (chosenProjectX hP) (chosenProjectY hP) z S s := by
  classical
  exact Nat.find_min (exists_microStops hP hr hrle z S) hs

/-- The exact first-stop loop never exceeds the universal cutoff. -/
theorem firstStopIndex_le_universal {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) :
    firstStopIndex hP hr hrle z S ≤ ProjectedMicro.feasibleMicroIterations := by
  classical
  unfold firstStopIndex
  apply Nat.find_min'
  exact ⟨ProjectedMicro.feasibleMicroIterations_positive,
    classOracle_residual hP hr hrle
      (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S⟩

def firstStopOracle {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) : MicroOutput m n :=
  microOutputAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S
    (firstStopIndex hP hr hrle z S)

theorem firstStopOracle_certificate {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) :
    (firstStopOracle hP hr hrle z S).xFast ∈ P.X ∧
      (firstStopOracle hP hr hrle z S).yFastNext ∈ P.Y ∧
      MicroNormalRelations P.X P.Y
        (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z)
        (firstStopOracle hP hr hrle z S) ∧
      RelativeResidual ell r S (firstStopOracle hP hr hrle z S) := by
  let project := scaledProject ell (chosenProjectX hP) (chosenProjectY hP)
  let A := scaledOperator ell r (qCenter ell r S) (yCenter ell r S)
    (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z)
  let center := scaledCenter ell (qCenter ell r S) (yCenter ell r S)
  let s := firstStopIndex hP hr hrle z S
  have hp : ProjectionGeometry.IsEuclideanProjection
      (scaledSet ell P.X P.Y) project :=
    scaledProject_isProjection hP.ell_pos (chosenProjectX_spec hP)
      (chosenProjectY_spec hP)
  have hs := (firstStopIndex_spec hP hr hrle z S).1
  have hu := projectedIterate_mem project A (M0 ^ 2)⁻¹ center hp.mem s
  have hb := projectedB_normal project A
    (show 0 < (M0 ^ 2)⁻¹ by norm_num [M0]) center hp.normal (s - 1)
  have hsEq : s - 1 + 1 = s := Nat.sub_add_cancel hs
  rw [hsEq] at hb
  have hn := decodeOutput_normalRelations hP.ell_pos
    (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z) hu hb
  exact ⟨hu.1, hu.2, hn, (firstStopIndex_spec hP hr hrle z S).2⟩

/-- The class-derived analytic system with precisely the appendix's micro loop. -/
def firstStopSystemWithProx {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell) :
    OuterSystem P.X P.Y P.f ell r hprox := by
  let oracle := fun (z : EVec m) (S : ValidState (m := m) P.Y) =>
    firstStopOracle hP hr.le hrle z S.1
  have hfeasible : ∀ z S, (oracle z S).yFastNext ∈ P.Y :=
    fun z S => (firstStopOracle_certificate hP hr.le hrle z S.1).2.1
  refine { outerSystemOfClassWithProx hP hr hrle hprox with
    oracle := oracle
    oracle_feasible := hfeasible
    oracle_subgradient := ?_
    oracle_residual := ?_ }
  · intro z S
    have hc := firstStopOracle_certificate hP hr.le hrle z S.1
    exact PointwiseConjugate.gamma_subgradient (gammaBddAbove_of_class hP z)
      hc.1 (ClassOperator.convexSupportX (r := r) hP z hc.1 hc.2.1)
      (ClassOperator.concaveSupportY (r := r) hP z hc.1 hc.2.1)
      hc.2.2.1.1 hc.2.2.1.2
  · intro z S
    exact (firstStopOracle_certificate hP hr.le hrle z S.1).2.2.2

def firstStopSystemFamily {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) :
    SystemFamily P.X P.Y P.f ell (ell / 8) (MainTheorem.classProxFamily hP) :=
  fun j => firstStopSystemWithProx hP
    (HomotopyCost.curvature_pos (div_pos hP.ell_pos (by norm_num)) j)
    (by
      unfold Tracking.curvature
      exact Tracking.div_pow_le_self (div_nonneg hP.ell_pos.le (by norm_num))
        (by norm_num) j)
    (MainTheorem.classProxFamily hP j)

/-- The actual homotopy state, with the current algorithm's outer budget. -/
def initializedSnapshot {ell D Delta : ℝ} {P : NCCInstance m n}
    {prox : ProxFamily P.X P.Y P.f ell (ell / 8)}
    (systems : SystemFamily P.X P.Y P.f ell (ell / 8) prox)
    (hzero : (0 : EVec n) ∈ P.Y) (j : Nat) : Snapshot (m := m) P.Y where
  z := P.x0
  state := homotopyState systems P.x0 (startupState (systems 0) hzero) j
  B := 15 * (Delta + Tracking.curvature (ell / 8) j * D ^ 2)

/-- Resetting the budget preserves the proved startup/homotopy invariant. -/
theorem initializedSnapshot_energy {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    {prox : ProxFamily P.X P.Y P.f ell (ell / 8)}
    (systems : SystemFamily P.X P.Y P.f ell (ell / 8) prox) (j : Nat) :
    snapshotEnergy (systems j)
        (initializedSnapshot (D := D) (Delta := Delta) systems hzero j) ≤
      (initializedSnapshot (D := D) (Delta := Delta) systems hzero j).B := by
  have h := initialized_homotopy_snapshot hP hzero systems j
  dsimp only at h
  exact h.1.trans h.2.2

/-- All current `Q` estimates hold along the class-constructed trajectory.
Only NC–C class membership and feasible dual origin are premises. The
printed initialization additionally specializes the class datum `P.x0` to
zero. Every curvature index is allowed here, so this applies in particular
to the manuscript's first index reaching its target curvature. -/
theorem class_trajectory_current_observable
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    (j t : Nat) :
    let sys := firstStopSystemFamily hP j
    let R0 := initializedSnapshot (D := D) (Delta := Delta)
      (firstStopSystemFamily hP) hzero j
    let Rt := trajectory sys R0 t
    observable sys Rt ≤ 3 *
        (ell * vecSq (anchorError sys Rt) + Rt.B) ∧
      vecSq (residualGradient (MainTheorem.classProxFamily hP j) Rt.z) ≤
        8 * ell * observable sys Rt ∧
      snapshotPotential sys (nextSnapshot sys Rt) - snapshotPotential sys Rt ≤
        -(1 / 4 : ℝ) * observable sys Rt := by
  dsimp only
  let sys := firstStopSystemFamily hP j
  let R0 := initializedSnapshot (D := D) (Delta := Delta)
    (firstStopSystemFamily hP) hzero j
  have hr : 0 < Tracking.curvature (ell / 8) j :=
    HomotopyCost.curvature_pos (div_pos hP.ell_pos (by norm_num)) j
  have hrle : Tracking.curvature (ell / 8) j ≤ ell / 8 := by
    unfold Tracking.curvature
    exact Tracking.div_pow_le_self
      (div_nonneg hP.ell_pos.le (by norm_num)) (by norm_num) j
  have hinit : snapshotEnergy sys R0 ≤ R0.B :=
    initializedSnapshot_energy hP hzero (firstStopSystemFamily hP) j
  have hEB := trajectory_energy_le_B hP.X_nonempty hP.ell_pos hr hrle
    sys R0 hinit t
  exact ⟨observable_le_three_residual hP.ell_pos hr sys _ hEB,
    regularizedGradient_sq_le_observable hP.ell_pos hr sys _ hEB,
    observable_descent hP.ell_pos hr
      (NCCLowerBoundVerification.Upper.IsNCCClass.regularizedValue_weaklyConvex hP)
      sys _ hEB⟩

end
end NCC.Upper.AnalyticBridge
