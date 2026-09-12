import NCC.Upper.AnalyticBridge
import NCC.Upper.Recurrences
import Mathlib.Data.Finset.Max

/-!
# The current minimum-residual output and outer horizon

The selector minimizes the current scalar residual, not the older square-root
certificate. `Nat.find` imposes precisely the least-index tie rule. This is
an exact-real mathematical algorithm, as in the manuscript's oracle model;
it is not asserted to be executable floating-point code.
-/

namespace NCC.Upper.Selection

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open OuterTrajectoryConcrete AnalyticBridge

theorem exists_minimizer (q : Nat → ℝ) (T : Nat) (hT : 0 < T) :
    ∃ t, t < T ∧ ∀ i, i < T → q t ≤ q i := by
  obtain ⟨t, ht, hmin⟩ := (Finset.range T).exists_min_image q
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hT))
  exact ⟨t, Finset.mem_range.mp ht,
    fun i hi => hmin i (Finset.mem_range.mpr hi)⟩

def leastMinimizer (q : Nat → ℝ) (T : Nat) (hT : 0 < T) : Nat := by
  classical
  exact Nat.find (exists_minimizer q T hT)

theorem leastMinimizer_spec (q : Nat → ℝ) (T : Nat) (hT : 0 < T) :
    leastMinimizer q T hT < T ∧
      ∀ i, i < T → q (leastMinimizer q T hT) ≤ q i := by
  classical
  exact Nat.find_spec (exists_minimizer q T hT)

theorem leastMinimizer_tie (q : Nat → ℝ) (T : Nat) (hT : 0 < T)
    {i : Nat} (hi : i < T)
    (heq : q i = q (leastMinimizer q T hT)) : leastMinimizer q T hT ≤ i := by
  classical
  apply Nat.find_min'
  refine ⟨hi, ?_⟩
  intro j hj
  rw [heq]
  exact (leastMinimizer_spec q T hT).2 j hj

def outerIterations (ell Delta eps : ℝ) : Nat :=
  ⌈4000 * (ell * Delta / eps ^ 2 + 1)⌉₊

theorem outerIterations_lower {ell Delta eps : ℝ} :
    4000 * (ell * Delta / eps ^ 2 + 1) ≤ (outerIterations ell Delta eps : ℝ) :=
  Nat.le_ceil _

theorem outerIterations_pos {ell Delta eps : ℝ}
    (hell : 0 < ell) (hDelta : 0 < Delta) :
    0 < outerIterations ell Delta eps := by
  have harg : 0 < 4000 * (ell * Delta / eps ^ 2 + 1) := by positivity
  exact Nat.cast_pos.mp (harg.trans_le outerIterations_lower)

/-- The numerical budget for the current, uniformly valid horizon. -/
theorem current_horizon_gradient_budget {ell Delta eps mass gSq : ℝ}
    (hell : 0 < ell) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hmass : ell * mass ≤ eps ^ 2 / 8)
    (hg : gSq ≤ (32 * ell / (outerIterations ell Delta eps : ℝ)) *
      (31 * (Delta + mass))) : gSq < eps ^ 2 / 4 := by
  have hT := outerIterations_pos (eps := eps) hell hDelta
  have hTr : 0 < (outerIterations ell Delta eps : ℝ) := Nat.cast_pos.mpr hT
  have he2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hscaled := mul_le_mul_of_nonneg_right
    (outerIterations_lower (ell := ell) (Delta := Delta) (eps := eps)) he2.le
  have hcancel : 4000 * (ell * Delta / eps ^ 2 + 1) * eps ^ 2 =
      4000 * (ell * Delta + eps ^ 2) := by
    field_simp
  rw [hcancel] at hscaled
  have hg' : gSq * (outerIterations ell Delta eps : ℝ) ≤
      992 * ell * (Delta + mass) := by
    have hh := (le_div_iff₀ hTr).mp
      (show gSq ≤ (992 * ell * (Delta + mass)) /
        (outerIterations ell Delta eps : ℝ) by convert hg using 1; ring)
    exact hh
  have hprod := mul_pos hell hDelta
  have hlt : gSq * (outerIterations ell Delta eps : ℝ) <
      (eps ^ 2 / 4) * (outerIterations ell Delta eps : ℝ) := by
    nlinarith
  exact (mul_lt_mul_iff_left₀ hTr).mp hlt

variable {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
  {f : EVec m → EVec n → ℝ} {ell r : ℝ}
  {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}

def selectedIndex (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (T : Nat) (hT : 0 < T) : Nat :=
  leastMinimizer (fun t => observable sys (trajectory sys R0 t)) T hT

def selectedAnchor (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (T : Nat) (hT : 0 < T) : EVec m :=
  (trajectory sys R0 (selectedIndex sys R0 T hT)).z

/-- Every anchor is feasible: the initial anchor is assumed feasible and
each subsequent anchor is the Euclidean-projection readout. -/
theorem trajectory_anchor_mem (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (hR0 : R0.z ∈ X) (t : Nat) :
    (trajectory sys R0 t).z ∈ X := by
  cases t with
  | zero => exact hR0
  | succ t => exact sys.project_spec.mem _

/-- Feasibility is part of the current article's OS definition and is
proved separately from the proximal residual bound. -/
theorem selectedAnchor_mem (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (hR0 : R0.z ∈ X)
    (T : Nat) (hT : 0 < T) : selectedAnchor sys R0 T hT ∈ X :=
  trajectory_anchor_mem sys R0 hR0 (selectedIndex sys R0 T hT)

/-- All analytic premises here are actual state properties. The readout and
descent inequalities are discharged by `AnalyticBridge`, not postulated. -/
theorem selected_regularized_gradient_bound
    (hX : X.Nonempty) (hell : 0 < ell) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hweakR : IsWeaklyConvexOn ell X (DualRegularizedValueOn Y f r))
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y)
    (hE0 : snapshotEnergy sys R0 ≤ R0.B) (hB0 : 0 ≤ R0.B)
    (T : Nat) (hT : 0 < T) (lower : ℝ)
    (hlower : ∀ z, lower ≤ regularizedEnvelope X Y f ell r hexistsR z) :
    vecSq (residualGradient hexistsR (selectedAnchor sys R0 T hT)) ≤
      (32 * ell / (T : ℝ)) * (snapshotPotential sys R0 - lower) := by
  let w := fun t => snapshotPotential sys (trajectory sys R0 t)
  let q := fun t => observable sys (trajectory sys R0 t)
  have hEB := trajectory_energy_le_B hX hell hr hrle sys R0 hE0
  have hdescent : ∀ t, t < T → w (t + 1) - w t ≤ -(1 / 4 : ℝ) * q t := by
    intro t _
    exact AnalyticBridge.observable_descent hell hr hweakR sys _ (hEB t)
  have hterminal : lower ≤ w T := by
    have hB := trajectory_B_nonneg hell.le sys R0 hB0 T
    have hl := hlower (trajectory sys R0 T).z
    dsimp [w, snapshotPotential]
    linarith
  have hselected := (leastMinimizer_spec q T hT).2
  have hgrad := regularizedGradient_sq_le_observable hell hr sys
    (trajectory sys R0 (selectedIndex sys R0 T hT))
    (hEB (selectedIndex sys R0 T hT))
  exact selected_gradient_squared_bound w q T lower
    (q (selectedIndex sys R0 T hT)) ell
    (vecSq (residualGradient hexistsR (selectedAnchor sys R0 T hT)))
    hT hell.le hdescent hterminal hselected hgrad

end

end NCC.Upper.Selection
