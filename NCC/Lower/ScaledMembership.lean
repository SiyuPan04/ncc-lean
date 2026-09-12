import NCC.Lower.Certificates

/-! Exact scaling into the target class for the current hard instance. -/

namespace NCC.Lower.ScaledMembership

noncomputable section

open NCCLowerBoundVerification NCC.Construction
open Certificates Parameters MoreauObstruction

def scaled {m n : ℕ} (hn : 0 < n) (ell D eps : ℝ) : NCCInstance (m * 3) (m * n) :=
  scaleNCCInstance (scale constants ell eps) (amplitude constants ell eps)
    (Membership.unscaled hn (D / scale constants ell eps))

theorem primal_domain {m n : ℕ} (hn : 0 < n) (ell D eps : ℝ) :
    (scaled (m := m) hn ell D eps).X = Set.univ := rfl

theorem dual_domain {m n : ℕ} (hn : 0 < n) {ell D eps : ℝ}
    (hell : 0 < ell) (heps : 0 < eps) :
    (scaled (m := m) hn ell D eps).Y = diameterBall (m * n) D := by
  ext y
  change vecSq (unscaleCoords (scale constants ell eps) y) ≤
    ((D / scale constants ell eps) / 2) ^ 2 ↔ vecSq y ≤ (D / 2) ^ 2
  rw [vecSq_unscaleCoords]
  have hlam := scale_pos constants hell heps
  have heq : ((D / scale constants ell eps) / 2) ^ 2 =
      (D / 2) ^ 2 / (scale constants ell eps) ^ 2 := by ring
  rw [heq, one_div, inv_pow, inv_mul_eq_div,
    div_le_div_iff_of_pos_right (sq_pos_of_pos hlam)]

theorem initialization {m n : ℕ} (hn : 0 < n) (ell D eps : ℝ) :
    (scaled (m := m) hn ell D eps).x0 = 0 := by
  change scaleCoords (scale constants ell eps) (0 : EVec (m * 3)) = 0
  funext i
  simp [scaleCoords]

theorem analyticClass {m n : ℕ} (hm : 0 < m) (hn : 10 ≤ n)
    {ell D Delta eps : ℝ} (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hgap : amplitude constants ell eps * (Composite.c_Δ * (m : ℝ)) ≤ Delta) :
    IsNCCClass ell D Delta (scaled (m := m) (by omega : 0 < n) ell D eps) := by
  have hlam := scale_pos constants hell heps
  have hamp := amplitude_pos constants hell heps
  have hbase := Membership.analyticClass hm hn (div_pos hD hlam)
  have hsrc : ScalingSource constants.ell0 (D / scale constants ell eps)
      (Delta / amplitude constants ell eps)
      (Membership.unscaled (m := m) (by omega : 0 < n) (D / scale constants ell eps)) := by
    refine {
      x0_mem := hbase.x0_mem
      X_nonempty := hbase.X_nonempty
      X_closed := hbase.X_closed
      X_convex := hbase.X_convex
      Y_nonempty := hbase.Y_nonempty
      Y_closed := hbase.Y_closed
      Y_convex := hbase.Y_convex
      gradient_representation := hbase.gradient_representation
      jointly_smooth := hbase.jointly_smooth
      dual_concave := hbase.dual_concave
      maximum_attained := hbase.maximum_attained
      value_bddBelow := hbase.value_bddBelow
      initial_gap := ?_
      dual_diameter := hbase.dual_diameter }
    exact hbase.initial_gap.trans ((le_div_iff₀ hamp).2 (by nlinarith [hgap]))
  exact paper_scaleNCCInstance_isNCCClass hell constants.ell0_pos hD hDelta hlam hsrc

theorem withinClass {m n : ℕ} (hm : 0 < m) (hn : 10 ≤ n)
    {ell D Delta eps : ℝ} (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hgap : amplitude constants ell eps * (Composite.c_Δ * (m : ℝ)) ≤ Delta) :
    Model.WithinClass ell D Delta (scaled (m := m) (by omega : 0 < n) ell D eps) := by
  apply Model.withinClass_of_analytic (analyticClass hm hn hell hD hDelta heps hgap)
  · exact Set.mem_univ _
  · rw [dual_domain (by omega : 0 < n) hell heps]
    exact zero_mem_diameterBall (m * n) D hD.le
  · exact initialization (by omega) ell D eps

theorem floor_gap {ell Delta eps : ℝ} (hell : 0 < ell)
    (hDelta : 0 < Delta) (heps : 0 < eps) :
    amplitude constants ell eps *
      (Composite.c_Δ * (stages constants ell Delta eps : ℝ)) ≤ Delta := by
  have hg := scaled_gap_budget constants hell hDelta heps
  change (ell * scale constants ell eps ^ 2 / constants.ell0) *
    constants.cDelta * (stages constants ell Delta eps : ℝ) ≤ Delta / 2 at hg
  change (ell * scale constants ell eps ^ 2 / constants.ell0) *
    (constants.cDelta * (stages constants ell Delta eps : ℝ)) ≤ Delta
  nlinarith

theorem not_OS_at_terminal_zero {m n : ℕ} (hm : 0 < m) (hn : 10 ≤ n)
    {ell D eps : ℝ} (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps)
    (hsize : (n : ℝ) ≤ constants.cD * (D / scale constants ell eps))
    {x : EVec (m * 3)} (hx : x (terminalIndex hm) = 0) :
    ¬ IsOptimizationStationary (scaled (m := m) (by omega : 0 < n) ell D eps).X
      (ValueOn (scaled (m := m) (by omega : 0 < n) ell D eps).Y
        (scaled (m := m) (by omega : 0 < n) ell D eps).f) ell eps x := by
  have hDs := div_pos hD (scale_pos constants hell heps)
  apply scaled_saddle_not_OS constants hell heps
    (fun u => ⟨Composite.maximizer (by omega) _ hDs.le u,
      Composite.maximizer_spec (by omega) _ hDs.le u⟩)
    (value_representsGradient (by omega) hDs.le) (terminalIndex hm)
    (fun u hu => terminal_gradient_squared hm hn hDs hsize u hu) hx

end

end NCC.Lower.ScaledMembership
