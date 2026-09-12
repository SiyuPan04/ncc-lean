import NCCLowerBoundVerification.Upper.HomotopyConcrete

/-!
# Minimal dual-curvature homotopy schedule

This file turns the manuscript phrase "let `J` be the smallest integer" into
an actual `Nat.find`, proves existence, and derives the strict target/4 lower
comparison from minimality.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace HomotopySchedule

noncomputable section

open Tracking

theorem natCast_le_four_pow (j : Nat) :
    (j : ℝ) ≤ (4 : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ j ih =>
      have hp : (1 : ℝ) ≤ 4 ^ j := one_le_pow₀ (by norm_num)
      rw [pow_succ]
      push_cast
      nlinarith

theorem exists_curvature_le {r0 target : ℝ}
    (hr0 : 0 < r0) (htarget : 0 < target) :
    ∃ j : Nat, Tracking.curvature r0 j ≤ target := by
  obtain ⟨j, hj⟩ := exists_nat_gt (r0 / target)
  have hjpow : (j : ℝ) ≤ (4 : ℝ) ^ j := natCast_le_four_pow j
  have hratio : r0 / target < (4 : ℝ) ^ j := hj.trans_le hjpow
  have hpow : 0 < (4 : ℝ) ^ j := pow_pos (by norm_num) _
  have hmul : r0 < (4 : ℝ) ^ j * target :=
    (div_lt_iff₀ htarget).1 hratio
  refine ⟨j, ?_⟩
  unfold Tracking.curvature
  exact (div_le_iff₀ hpow).2 (le_of_lt (by simpa [mul_comm] using hmul))

def homotopyStage (r0 target : ℝ) (hr0 : 0 < r0)
    (htarget : 0 < target) : Nat :=
  Nat.find (exists_curvature_le hr0 htarget)

theorem homotopyStage_spec {r0 target : ℝ} (hr0 : 0 < r0)
    (htarget : 0 < target) :
    Tracking.curvature r0 (homotopyStage r0 target hr0 htarget) ≤ target := by
  exact Nat.find_spec (exists_curvature_le hr0 htarget)

theorem homotopyStage_minimal {r0 target : ℝ} (hr0 : 0 < r0)
    (htarget : 0 < target) {j : Nat}
    (hj : j < homotopyStage r0 target hr0 htarget) :
    target < Tracking.curvature r0 j := by
  exact lt_of_not_ge
    (Nat.find_min (exists_curvature_le hr0 htarget) hj)

/-- TeX `ub:eq:r-target-comparison`, including its strict lower side. -/
theorem homotopyStage_target_comparison {r0 target : ℝ}
    (hr0 : 0 < r0) (htarget : 0 < target)
    (hJ : homotopyStage r0 target hr0 htarget ≠ 0) :
    target / 4 <
        Tracking.curvature r0 (homotopyStage r0 target hr0 htarget) ∧
      Tracking.curvature r0 (homotopyStage r0 target hr0 htarget) ≤ target := by
  let J := homotopyStage r0 target hr0 htarget
  have hJpos : 0 < J := Nat.pos_of_ne_zero hJ
  have hprevIndex : J - 1 < J := by omega
  have hprev : target < Tracking.curvature r0 (J - 1) := by
    apply homotopyStage_minimal hr0 htarget
    simpa [J] using hprevIndex
  have hsucc : (J - 1) + 1 = J := by omega
  have hcurv := Tracking.curvature_succ r0 (J - 1)
  rw [hsucc] at hcurv
  constructor
  · rw [hcurv]
    linarith
  · simpa [J] using homotopyStage_spec hr0 htarget

/-- The exceptional zero-stage case is exactly `r0 ≤ target`. -/
theorem homotopyStage_eq_zero_iff {r0 target : ℝ}
    (hr0 : 0 < r0) (htarget : 0 < target) :
    homotopyStage r0 target hr0 htarget = 0 ↔ r0 ≤ target := by
  unfold homotopyStage
  rw [Nat.find_eq_zero]
  simp [Tracking.curvature]

/-- Unified target comparison, including the exceptional zero-stage case.
When the requested target is no larger than the starting curvature, the
selected final curvature always lies in `(target/4, target]`. -/
theorem homotopyStage_target_comparison_total {r0 target : ℝ}
    (hr0 : 0 < r0) (htarget : 0 < target) (htarget0 : target ≤ r0) :
    target / 4 <
        Tracking.curvature r0 (homotopyStage r0 target hr0 htarget) ∧
      Tracking.curvature r0 (homotopyStage r0 target hr0 htarget) ≤ target := by
  by_cases hJ : homotopyStage r0 target hr0 htarget = 0
  · have hr0target : r0 ≤ target :=
      (homotopyStage_eq_zero_iff hr0 htarget).mp hJ
    have heq : r0 = target := le_antisymm hr0target htarget0
    rw [hJ]
    simp only [Tracking.curvature, pow_zero, div_one, heq]
    exact ⟨by nlinarith, le_rfl⟩
  · exact homotopyStage_target_comparison hr0 htarget hJ

end

end HomotopySchedule
end Upper
end NCCLowerBoundVerification
