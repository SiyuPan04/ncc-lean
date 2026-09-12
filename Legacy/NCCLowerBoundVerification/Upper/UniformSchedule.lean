import NCCLowerBoundVerification.Upper.Tracking
import NCCLowerBoundVerification.Upper.HomotopySchedule

/-!
# Target curvature and outer-horizon arithmetic

This file verifies the literal parameter choices in Algorithm 1 and the
arithmetic in the proof of the uniform upper bound.  It deliberately keeps
the numerical constants visible.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace UniformSchedule

noncomputable section

/-- `r_epsilon` from Algorithm 1. -/
def targetCurvature (ell D eps : ℝ) : ℝ :=
  min (ell / 8) (eps ^ 2 / (8 * ell * D ^ 2))

theorem targetCurvature_pos {ell D eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) :
    0 < targetCurvature ell D eps := by
  unfold targetCurvature
  exact lt_min (by positivity) (by positivity)

theorem targetCurvature_le_ell_div_eight {ell D eps : ℝ} :
    targetCurvature ell D eps ≤ ell / 8 := by
  exact min_le_left _ _

theorem targetCurvature_le_bias_branch {ell D eps : ℝ} :
    targetCurvature ell D eps ≤ eps ^ 2 / (8 * ell * D ^ 2) := by
  exact min_le_right _ _

/-- At the target curvature the regularization bias spends at most one
quarter of the final squared stationarity budget. -/
theorem targetCurvature_bias_budget {ell D eps r : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps)
    (_hr0 : 0 ≤ r) (hr : r ≤ targetCurvature ell D eps) :
    2 * ell * r * D ^ 2 ≤ eps ^ 2 / 4 := by
  have ht := hr.trans (targetCurvature_le_bias_branch
    (ell := ell) (D := D) (eps := eps))
  have hcoef : 0 ≤ 2 * ell * D ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left ht hcoef
  calc
    2 * ell * r * D ^ 2 = (2 * ell * D ^ 2) * r := by ring
    _ ≤ (2 * ell * D ^ 2) * (eps ^ 2 / (8 * ell * D ^ 2)) := hmul
    _ = eps ^ 2 / 4 := by
      field_simp [ne_of_gt hell, ne_of_gt hD]
      ring

/-- The actual homotopy output, which may lie between `r_epsilon/4` and
`r_epsilon`, obeys the same perturbation budget. -/
theorem homotopy_output_bias_budget {ell D eps r : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps)
    (hr : 0 < r) (hrupper : r ≤ targetCurvature ell D eps) :
    2 * ell * r * D ^ 2 ≤ eps ^ 2 / 4 :=
  targetCurvature_bias_budget hell hD heps hr.le hrupper

/-- Quarter-minimality of the homotopy changes the target condition number
by only a numerical factor. -/
theorem sqrt_ratio_lt_six_max {ell D eps r : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) (hr : 0 < r)
    (hrlower : targetCurvature ell D eps / 4 < r) :
    Real.sqrt (ell / r) < 6 * max 1 (ell * D / eps) := by
  have hratio0 : 0 ≤ ell / r := by positivity
  have hs0 := Real.sqrt_nonneg (ell / r)
  have hs2 := Real.sq_sqrt hratio0
  by_cases hbranch : ell / 8 ≤ eps ^ 2 / (8 * ell * D ^ 2)
  · have ht : targetCurvature ell D eps = ell / 8 :=
      min_eq_left hbranch
    rw [ht] at hrlower
    have hratio : ell / r < 32 := by
      rw [div_lt_iff₀ hr]
      nlinarith
    have hsix : Real.sqrt (ell / r) < 6 := by
      nlinarith
    have hmax : 1 ≤ max 1 (ell * D / eps) := le_max_left _ _
    nlinarith
  · have hbranch' : eps ^ 2 / (8 * ell * D ^ 2) < ell / 8 :=
      lt_of_not_ge hbranch
    have ht : targetCurvature ell D eps =
        eps ^ 2 / (8 * ell * D ^ 2) := min_eq_right hbranch'.le
    rw [ht] at hrlower
    let q : ℝ := ell * D / eps
    have hq : 0 < q := by dsimp [q]; positivity
    have hden : 0 < 32 * ell * D ^ 2 := by positivity
    have hlow : eps ^ 2 / (32 * ell * D ^ 2) < r := by
      calc
        eps ^ 2 / (32 * ell * D ^ 2) =
            (eps ^ 2 / (8 * ell * D ^ 2)) / 4 := by ring
        _ < r := hrlower
    have hbase : eps ^ 2 < 32 * ell * D ^ 2 * r := by
      have h := (div_lt_iff₀ hden).1 hlow
      nlinarith
    have hratio : ell / r < 32 * q ^ 2 := by
      rw [div_lt_iff₀ hr]
      dsimp [q]
      field_simp [ne_of_gt heps]
      nlinarith
    have hsix : Real.sqrt (ell / r) < 6 * q := by
      have hq0 : 0 ≤ q := hq.le
      nlinarith [sq_nonneg (Real.sqrt (ell / r) - 6 * q)]
    have hqmax : q ≤ max 1 q := le_max_right _ _
    dsimp [q] at hqmax ⊢
    nlinarith

/-- Literal outer horizon of Algorithm 1. -/
def paperOuterIterations (ell Delta r D eps : ℝ) : ℕ :=
  Tracking.outerIterations ell (Delta + r * D ^ 2) eps

theorem paperOuterIterations_sandwich {ell Delta r D eps : ℝ}
    (hell : 0 ≤ ell) (hDelta : 0 ≤ Delta) (hr : 0 ≤ r)
    (heps : 0 < eps) :
    4000 * ell * (Delta + r * D ^ 2) / eps ^ 2 ≤
        (paperOuterIterations ell Delta r D eps : ℝ) ∧
      (paperOuterIterations ell Delta r D eps : ℝ) <
        4000 * ell * (Delta + r * D ^ 2) / eps ^ 2 + 1 := by
  apply Tracking.outerIterations_sandwich
  positivity

theorem paperOuterIterations_pos {ell Delta r D eps : ℝ}
    (hell : 0 < ell) (hDelta : 0 < Delta) (hr : 0 ≤ r)
    (heps : 0 < eps) :
    0 < paperOuterIterations ell Delta r D eps := by
  have hs := (paperOuterIterations_sandwich (D := D)
    hell.le hDelta.le hr heps).1
  have harg : 0 < 4000 * ell * (Delta + r * D ^ 2) / eps ^ 2 := by
    positivity
  have hcast : (0 : ℝ) < paperOuterIterations ell Delta r D eps :=
    harg.trans_le hs
  exact_mod_cast hcast

/-- The outer averaging inequality with the paper's horizon gives the strict
`epsilon^2/4` smoothed-certificate budget. -/
theorem paper_certificate_budget {ell Delta r D eps C2 : ℝ}
    (hell : 0 < ell) (hDelta : 0 < Delta) (hr : 0 ≤ r)
    (heps : 0 < eps)
    (hC : C2 ≤
      (32 * ell / (paperOuterIterations ell Delta r D eps : ℝ)) *
        (31 * (Delta + r * D ^ 2))) :
    C2 < eps ^ 2 / 4 := by
  let T : ℝ := paperOuterIterations ell Delta r D eps
  have hTlower := (paperOuterIterations_sandwich (D := D)
    hell.le hDelta.le hr heps).1
  have hTposNat := paperOuterIterations_pos (D := D) hell hDelta hr heps
  have hTpos : 0 < T := by
    dsimp [T]
    exact_mod_cast hTposNat
  have h992 := Tracking.certificate_gap_constant (T := T) hC
  exact h992.trans_lt
    (Tracking.final_certificate_arithmetic heps (by simpa [T] using hTlower) hTpos)

/-- Since `r D^2 ≤ epsilon^2/(8 ell)`, the literal ceiling horizon is at
most the principal gap term plus the numerical additive constant `501`. -/
theorem paperOuterIterations_lt_gap_bound {ell Delta r D eps : ℝ}
    (hell : 0 < ell) (hDelta : 0 ≤ Delta) (hr : 0 ≤ r)
    (heps : 0 < eps) (hrD : r * D ^ 2 ≤ eps ^ 2 / (8 * ell)) :
    (paperOuterIterations ell Delta r D eps : ℝ) <
      4000 * ell * Delta / eps ^ 2 + 501 := by
  have hs := (paperOuterIterations_sandwich (D := D)
    hell.le hDelta hr heps).2
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hscaled := mul_le_mul_of_nonneg_left hrD (by positivity : 0 ≤ 4000 * ell)
  have hterm : 4000 * ell * (r * D ^ 2) / eps ^ 2 ≤ 500 := by
    rw [div_le_iff₀ heps2]
    calc
      4000 * ell * (r * D ^ 2) ≤
          4000 * ell * (eps ^ 2 / (8 * ell)) := hscaled
      _ = 500 * eps ^ 2 := by
        field_simp [ne_of_gt hell]
        ring
  calc
    (paperOuterIterations ell Delta r D eps : ℝ) <
        4000 * ell * (Delta + r * D ^ 2) / eps ^ 2 + 1 := hs
    _ = 4000 * ell * Delta / eps ^ 2 +
        4000 * ell * (r * D ^ 2) / eps ^ 2 + 1 := by ring
    _ ≤ 4000 * ell * Delta / eps ^ 2 + 501 := by linarith

end

end UniformSchedule
end Upper
end NCCLowerBoundVerification
