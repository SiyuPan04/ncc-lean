import NCC.Upper.WithinProgram

/-!
# Configurable tracked run and genuine final FOAM refinement

This module retains the least-Q snapshot at an arbitrary geometric
regularization level. The horizon includes the actual mass `r D²`.
The final refinement is the same finite first-stop FOAM iteration, not
an exact-saddle selection. Normal-cone game stationarity is a separate
readout obligation and is not inferred from envelope stationarity here.
-/
namespace NCC.Extensions.GSRun
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open RelativeFOAM RelativeFOAMContraction PointwiseConjugate
open OuterTrajectoryConcrete HomotopyRun HomotopySchedule
open NCC.Upper NCC.Upper.AnalyticBridge NCC.Upper.WithinFirstStop
set_option maxHeartbeats 3000000
variable {m n : Nat} {ell D Delta eta : ℝ} {P : NCCInstance m n}

def mass (ell D Delta : ℝ) (J : Nat) : ℝ :=
  Delta + Tracking.curvature (ell / 8) J * D ^ 2

theorem mass_pos (hP : WithinClass ell D Delta P) (J : Nat) :
    0 < mass ell D Delta J := by
  have hr := level_pos hP J
  dsimp only [mass]
  exact add_pos_of_pos_of_nonneg hP.Delta_pos (mul_nonneg hr.le (sq_nonneg D))

def horizon (ell D Delta eta : ℝ) (J : Nat) : Nat :=
  Selection.outerIterations ell (mass ell D Delta J) eta

theorem horizon_pos (hP : WithinClass ell D Delta P) (J : Nat) :
    0 < horizon ell D Delta eta J :=
  Selection.outerIterations_pos hP.ell_pos (mass_pos hP J)

def selectedSnapshot (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) : Snapshot (m := m) P.Y :=
  let sys := firstStopSystemFamily hP J
  let R0 := initializedSnapshot (D := D) (Delta := Delta) (firstStopSystemFamily hP) hzero J
  trajectory sys R0 (Selection.selectedIndex sys R0 (horizon ell D Delta eta J)
    (horizon_pos hP J))

theorem selectedSnapshot_mem (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) :
    (selectedSnapshot (eta := eta) hP hzero J).z ∈ P.X :=
  Selection.trajectory_anchor_mem _ _ hP.x0_mem _

theorem selected_energy_le_budget (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) :
    snapshotEnergy (firstStopSystemFamily hP J) (selectedSnapshot (eta := eta) hP hzero J) ≤
      (selectedSnapshot (eta := eta) hP hzero J).B := by
  apply trajectory_energy_le_B hP.X_nonempty hP.ell_pos (level_pos hP J) (level_le hP J)
  exact WithinRun.initializedSnapshot_energy hP hzero _ J

theorem selected_budget_nonneg (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) :
    0 ≤ (selectedSnapshot (eta := eta) hP hzero J).B := by
  apply trajectory_B_nonneg hP.ell_pos.le
  change 0 ≤ 15 * mass ell D Delta J
  exact mul_nonneg (by norm_num) (mass_pos hP J).le

theorem selected_observable_gap (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) :
    observable (firstStopSystemFamily hP J) (selectedSnapshot (eta := eta) hP hzero J) ≤
      124 * mass ell D Delta J / (horizon ell D Delta eta J : ℝ) := by
  let sys := firstStopSystemFamily hP J
  let R0 := initializedSnapshot (D := D) (Delta := Delta) (firstStopSystemFamily hP) hzero J
  let T := horizon ell D Delta eta J
  let w := fun t => snapshotPotential sys (trajectory sys R0 t)
  let q := fun t => observable sys (trajectory sys R0 t)
  let lower := InitialGapBounds.regularizedClassLower P (Tracking.curvature (ell / 8) J) D
  have hE0 := WithinRun.initializedSnapshot_energy hP hzero (firstStopSystemFamily hP) J
  have hEB := trajectory_energy_le_B hP.X_nonempty hP.ell_pos
    (level_pos hP J) (level_le hP J) sys R0 hE0
  have hB0 : 0 ≤ R0.B := by
    change 0 ≤ 15 * mass ell D Delta J
    exact mul_nonneg (by norm_num) (mass_pos hP J).le
  have hdescent : ∀ t, t < T → w (t + 1) - w t ≤ -(1 / 4 : ℝ) * q t := by
    intro t _
    exact AnalyticBridge.observable_descent hP.ell_pos (level_pos hP J)
      (WithinRegularization.value_weaklyConvex hP) sys _ (hEB t)
  have hterminal : lower ≤ w T := by
    have hB := trajectory_B_nonneg hP.ell_pos.le sys R0 hB0 T
    have hl := WithinRun.regularizedClassLower_le_envelope hP hzero
      (level_pos hP J).le hP.ell_pos.le (WithinFirstStop.proxFamily hP J)
      (trajectory sys R0 T).z
    dsimp [w, snapshotPotential, lower]
    linarith
  have hpotential : w 0 - lower ≤ 31 * mass ell D Delta J :=
    WithinRun.initial_snapshot_potential_bound hP hzero (level_pos hP J).le
      sys R0 rfl le_rfl
  have hres := Upper.selected_residual_bound w q T lower
    (q (Selection.selectedIndex sys R0 T (horizon_pos hP J))) (horizon_pos hP J)
    hdescent hterminal (Selection.leastMinimizer_spec q T (horizon_pos hP J)).2
  refine hres.trans ?_
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg T)
  linarith

theorem selected_observable_small (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) (heta : 0 < eta) :
    observable (firstStopSystemFamily hP J) (selectedSnapshot (eta := eta) hP hzero J) <
      eta ^ 2 / (32 * ell) := by
  let H := mass ell D Delta J
  let T := horizon ell D Delta eta J
  have hH : 0 < H := mass_pos hP J
  have hTr : 0 < (T : ℝ) := Nat.cast_pos.mpr (horizon_pos hP J)
  have he2 : 0 < eta ^ 2 := sq_pos_of_pos heta
  have hT := mul_le_mul_of_nonneg_right
    (Selection.outerIterations_lower (ell := ell) (Delta := H) (eps := eta)) he2.le
  have hcancel : 4000 * (ell * H / eta ^ 2 + 1) * eta ^ 2 =
      4000 * (ell * H + eta ^ 2) := by field_simp
  rw [hcancel] at hT
  have hq := selected_observable_gap (eta := eta) hP hzero J
  apply hq.trans_lt
  apply (div_lt_iff₀ hTr).2
  rw [div_mul_eq_mul_div]
  apply (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 32) hP.ell_pos)).2
  have hprod : 0 < ell * H := mul_pos hP.ell_pos hH
  change 124 * H * (32 * ell) < eta ^ 2 * (T : ℝ)
  change 4000 * (ell * H + eta ^ 2) ≤ (T : ℝ) * eta ^ 2 at hT
  nlinarith

theorem selected_budget_small (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) (heta : 0 < eta) :
    (selectedSnapshot (eta := eta) hP hzero J).B < eta ^ 2 / (32 * ell) := by
  have hq := selected_observable_small hP hzero J heta
  have hs : 0 ≤ ell * vecSq
      (readout (firstStopSystemFamily hP J) (selectedSnapshot (eta := eta) hP hzero J).state -
        (selectedSnapshot (eta := eta) hP hzero J).z) :=
    mul_nonneg hP.ell_pos.le (Tracking.vecSq_nonneg _)
  unfold observable stepDisplacement at hq
  linarith

theorem selected_gradient_small (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) (heta : 0 < eta) :
    vecSq (residualGradient (WithinFirstStop.proxFamily hP J)
      (selectedSnapshot (eta := eta) hP hzero J).z) < eta ^ 2 / 4 := by
  have hgrad := regularizedGradient_sq_le_observable hP.ell_pos (level_pos hP J)
    (firstStopSystemFamily hP J) (selectedSnapshot (eta := eta) hP hzero J)
    (selected_energy_le_budget hP hzero J)
  have hq := mul_lt_mul_of_pos_left (selected_observable_small hP hzero J heta)
    (mul_pos (by norm_num : (0 : ℝ) < 8) hP.ell_pos)
  have hcancel : 8 * ell * (eta ^ 2 / (32 * ell)) = eta ^ 2 / 4 := by
    field_simp [ne_of_gt hP.ell_pos]
    norm_num
  rw [hcancel] at hq
  exact hgrad.trans_lt hq

def refinedState (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) (rho : ℝ) : ValidState (m := m) P.Y :=
  let sys := firstStopSystemFamily hP J
  let R := selectedSnapshot (eta := eta) hP hzero J
  ((foamStep ell (Tracking.curvature (ell / 8) J) (sys.oracle R.z)
    (sys.oracle_feasible R.z))^[blockIterations (alpha ell (Tracking.curvature (ell / 8) J)) rho])
      R.state

theorem refined_energy (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) (heta : 0 < eta)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    energyAt (firstStopSystemFamily hP J) (selectedSnapshot (eta := eta) hP hzero J).z
      (refinedState (eta := eta) hP hzero J rho) < rho * (eta ^ 2 / (32 * ell)) := by
  let sys := firstStopSystemFamily hP J
  let R := selectedSnapshot (eta := eta) hP hzero J
  let st := sys.stationary R.z
  have hmin := (Pzr_unique_minimizer hP.ell_pos (level_pos hP J)
    st.subgradient st.stationQ st.stationY).1
  have henergy (V : ValidState (m := m) P.Y) :
      energyAt sys R.z V = energy ell (Tracking.curvature (ell / 8) J)
        st.qStar st.yStar.1
        (PzrTotal P.X P.Y (decurved P.f ell (Tracking.curvature (ell / 8) J) R.z)
          ell (Tracking.curvature (ell / 8) J))
        (Pzr P.X P.Y (decurved P.f ell (Tracking.curvature (ell / 8) J) R.z)
          ell (Tracking.curvature (ell / 8) J) st.qStar st.yStar) V.1 :=
    snapshotEnergy_eq_foamEnergy sys ⟨R.z, V, 0⟩
  have hc : energyAt sys R.z (refinedState (eta := eta) hP hzero J rho) ≤
      rho * energyAt sys R.z R.state := by
    rw [henergy, henergy]
    exact block_energy_contraction hP.ell_pos (level_pos hP J) (level_le hP J)
      st.qStar st.yStar hmin (sys.oracle R.z) (sys.oracle_feasible R.z)
      (sys.oracle_subgradient R.z) (sys.oracle_residual R.z) R.state hrho hrho1
  exact hc.trans_lt (mul_lt_mul_of_pos_left
    ((selected_energy_le_budget hP hzero J).trans_lt (selected_budget_small hP hzero J heta)) hrho)

/-- Both coordinates of the feasible fast readout are close to the
actual stationary pair. This is an energy consequence, not an assumed
approximate-saddle oracle interface. -/
theorem fast_pair_distance_le_energy
    {X : Set (EVec m)} {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ} {r : ℝ}
    (hell : 0 < ell) (hr : 0 < r) (hrle : r ≤ ell)
    {hprox : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hprox) (z : EVec m) (S : ValidState (m := m) Y) :
    vecSq (readout sys S - selectedProx hprox z) +
      vecSq (S.1.yFast - (sys.stationary z).yStar.1) ≤
        2 * energyAt sys z S / r := by
  let st := sys.stationary z
  have hx := readout_error_le_energy hell hr sys ⟨z, S, 0⟩
  have hstrong := TrackingConcrete.Pzr_isSubtypePairStrongMinimizer hell hr
    st.subgradient st.stationQ st.stationY S.1.qFast ⟨S.1.yFast, S.2⟩
  have hq : 0 ≤ 1 / ell * vecSq (S.1.qFast - st.qStar) :=
    mul_nonneg (div_nonneg (by norm_num) hell.le) (Tracking.vecSq_nonneg _)
  have hslowq : 0 ≤ 2 * alpha ell r / ell * vecSq (S.1.q - st.qStar) :=
    mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hell.le)
      (Tracking.vecSq_nonneg _)
  have hslowy : 0 ≤ 2 * r * vecSq (S.1.y - st.yStar.1) :=
    mul_nonneg (mul_nonneg (by norm_num) hr.le) (Tracking.vecSq_nonneg _)
  have hy : r * vecSq (S.1.yFast - st.yStar.1) ≤ energyAt sys z S := by
    unfold TrackingAnalytic.pairSq at hstrong
    unfold energyAt TrackingConcrete.constrainedEnergy
    dsimp only [st] at hstrong hq hslowq hslowy ⊢
    linarith
  have hx0 := Tracking.vecSq_nonneg (readout sys S - selectedProx hprox z)
  have hx' := mul_le_mul_of_nonneg_right hrle hx0
  apply (le_div_iff₀ hr).2
  change ell * vecSq (readout sys S - selectedProx hprox z) ≤ energyAt sys z S at hx
  dsimp only [st] at hy
  nlinarith

/-! The GS regularization is linear, not quadratic, in the tolerance. -/

def target (ell D eps : ℝ) : ℝ := min (ell / 8) (eps / (64 * D))

theorem target_pos {eps : ℝ} (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) :
    0 < target ell D eps :=
  lt_min (div_pos hell (by norm_num)) (div_pos heps (mul_pos (by norm_num) hD))

def stage {eps : ℝ} (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) : Nat :=
  homotopyStage (ell / 8) (target ell D eps)
    (div_pos hell (by norm_num)) (target_pos hell hD heps)

def finalCurvature {eps : ℝ} (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) : ℝ :=
  Tracking.curvature (ell / 8) (stage hell hD heps)

theorem finalCurvature_pos {eps : ℝ} (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) :
    0 < finalCurvature hell hD heps :=
  HomotopyCost.curvature_pos (div_pos hell (by norm_num)) _

theorem finalCurvature_interval {eps : ℝ} (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) :
    target ell D eps / 4 < finalCurvature hell hD heps ∧
      finalCurvature hell hD heps ≤ target ell D eps :=
  homotopyStage_target_comparison_total (div_pos hell (by norm_num))
    (target_pos hell hD heps) (min_le_left _ _)

theorem finalCurvature_bias {eps : ℝ} (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) :
    finalCurvature hell hD heps * D ≤ eps / 64 := by
  have hr := (finalCurvature_interval hell hD heps).2.trans (min_le_right _ _)
  have hm := mul_le_mul_of_nonneg_right hr hD.le
  have hc : eps / (64 * D) * D = eps / 64 := by field_simp [ne_of_gt hD]
  rwa [hc] at hm

def refinementFactor (ell r : ℝ) : ℝ := r / (1000000 * ell)

theorem refinementFactor_pos {r : ℝ} (hell : 0 < ell) (hr : 0 < r) :
    0 < refinementFactor ell r := div_pos hr (mul_pos (by norm_num) hell)

theorem refinementFactor_lt_one {r : ℝ} (hell : 0 < ell) (hrle : r ≤ ell / 8) :
    refinementFactor ell r < 1 := by
  apply (div_lt_one (mul_pos (by norm_num) hell)).2
  linarith

/-- With internal tolerance eps/2 the anchor gradient and final energy
meet concrete projected-normal readout budgets. -/
theorem final_refinement_budgets {eps : ℝ} (hP : WithinClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) (heps : 0 < eps) :
    let r := Tracking.curvature (ell / 8) J
    let R := selectedSnapshot (eta := eps / 2) hP hzero J
    let S := refinedState (eta := eps / 2) hP hzero J (refinementFactor ell r)
    vecSq (residualGradient (WithinFirstStop.proxFamily hP J) R.z) < eps ^ 2 / 16 ∧
      energyAt (firstStopSystemFamily hP J) R.z S < r * eps ^ 2 / (1000000 * ell ^ 2) := by
  dsimp only
  have hg := selected_gradient_small hP hzero J (div_pos heps (by norm_num : (0 : ℝ) < 2))
  have hE := refined_energy hP hzero J (div_pos heps (by norm_num : (0 : ℝ) < 2))
    (refinementFactor_pos hP.ell_pos (level_pos hP J))
    (refinementFactor_lt_one hP.ell_pos (level_le hP J))
  constructor
  · convert hg using 1
    ring
  · apply hE.trans_le
    unfold refinementFactor
    have hEq : Tracking.curvature (ell / 8) J / (1000000 * ell) *
        ((eps / 2) ^ 2 / (32 * ell)) =
        (Tracking.curvature (ell / 8) J * eps ^ 2 / (1000000 * ell ^ 2)) / 128 := by ring
    rw [hEq]
    have hnonneg : 0 ≤ Tracking.curvature (ell / 8) J * eps ^ 2 /
        (1000000 * ell ^ 2) := by
      exact div_nonneg (mul_nonneg (level_pos hP J).le (sq_nonneg eps)) (by positivity)
    linarith

end
end NCC.Extensions.GSRun
