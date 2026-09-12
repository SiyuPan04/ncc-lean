import NCC.Basic
import Mathlib

/-!
# Exact parameter arithmetic for the current zero-respecting lower bound

Source: `eq:lower-bound-parameters` and the proof of `thm:zr-lower`.
The constants below are numerical certificate constants, not assumed
certificates. This module proves their scaling/floor consequences and does
not claim to prove the analytic hard-instance or oracle hypotheses.
-/

namespace NCC.Lower.Parameters

noncomputable section

structure Constants where
  ell0 : ℝ
  g0 : ℝ
  cD : ℝ
  cDelta : ℝ
  ell0_pos : 0 < ell0
  g0_pos : 0 < g0
  cD_pos : 0 < cD
  cDelta_pos : 0 < cDelta
  g0_le : g0 ≤ ell0

def c0 (C : Constants) : ℝ :=
  min (C.cD * C.g0 / (80 * C.ell0))
    (C.g0 / Real.sqrt (128 * C.cDelta * C.ell0))

def c1 (C : Constants) : ℝ :=
  C.cD * C.g0 ^ 3 / (256 * C.cDelta * C.ell0 ^ 2)

def scale (C : Constants) (ell eps : ℝ) : ℝ :=
  4 * C.ell0 * eps / (C.g0 * ell)

def rawN (C : Constants) (ell D eps : ℝ) : ℝ :=
  C.cD * (D / scale C ell eps)

def rawM (C : Constants) (ell Delta eps : ℝ) : ℝ :=
  C.ell0 * Delta / (2 * C.cDelta * ell * (scale C ell eps) ^ 2)

def innerLength (C : Constants) (ell D eps : ℝ) : ℕ :=
  ⌊rawN C ell D eps⌋₊

def stages (C : Constants) (ell Delta eps : ℝ) : ℕ :=
  ⌊rawM C ell Delta eps⌋₊

theorem c0_pos (C : Constants) : 0 < c0 C := by
  have := C.cD_pos
  have := C.g0_pos
  have := C.ell0_pos
  have := C.cDelta_pos
  unfold c0
  positivity

theorem c1_pos (C : Constants) : 0 < c1 C := by
  have := C.cD_pos
  have := C.g0_pos
  have := C.ell0_pos
  have := C.cDelta_pos
  unfold c1
  positivity

theorem scale_pos (C : Constants) {ell eps : ℝ}
    (hell : 0 < ell) (heps : 0 < eps) : 0 < scale C ell eps := by
  exact div_pos (mul_pos (mul_pos (by norm_num) C.ell0_pos) heps)
    (mul_pos C.g0_pos hell)

theorem rawN_eq (C : Constants) (ell D eps : ℝ) :
    rawN C ell D eps = C.cD * C.g0 * ell * D / (4 * C.ell0 * eps) := by
  unfold rawN scale
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

theorem rawM_eq (C : Constants) {ell Delta eps : ℝ}
    (hell : 0 < ell) (heps : 0 < eps) :
    rawM C ell Delta eps =
      C.g0 ^ 2 * ell * Delta / (32 * C.cDelta * C.ell0 * eps ^ 2) := by
  unfold rawM scale
  field_simp [ne_of_gt C.ell0_pos, ne_of_gt C.g0_pos, ne_of_gt C.cDelta_pos,
    ne_of_gt hell, ne_of_gt heps]
  ring

/-- The first accuracy restriction makes the inner floor at least 20. -/
theorem rawN_ge_twenty (C : Constants) {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps)
    (hacc : eps ≤ c0 C * min (ell * D) (Real.sqrt (ell * Delta))) :
    20 ≤ rawN C ell D eps := by
  have hell0 := C.ell0_pos
  have hsmall : eps ≤ (C.cD * C.g0 / (80 * C.ell0)) * (ell * D) := by
    calc
      eps ≤ c0 C * min (ell * D) (Real.sqrt (ell * Delta)) := hacc
      _ ≤ c0 C * (ell * D) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (c0_pos C).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (min_le_left _ _) (mul_nonneg hell.le hD.le)
  rw [rawN_eq]
  apply (le_div_iff₀ (by positivity : 0 < 4 * C.ell0 * eps)).2
  have hsmall' := (le_div_iff₀ (by positivity : 0 < 80 * C.ell0)).1
    (show eps ≤ C.cD * C.g0 * (ell * D) / (80 * C.ell0) by
      simpa only [div_mul_eq_mul_div] using hsmall)
  nlinarith

/-- The second accuracy restriction makes the outer floor at least 4. -/
theorem rawM_ge_four (C : Constants) {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 C * min (ell * D) (Real.sqrt (ell * Delta))) :
    4 ≤ rawM C ell Delta eps := by
  have hell0 := C.ell0_pos
  have hcDelta := C.cDelta_pos
  have hs : 0 < Real.sqrt (128 * C.cDelta * C.ell0) := by
    apply Real.sqrt_pos.2
    positivity
  have hsmall : eps ≤
      (C.g0 / Real.sqrt (128 * C.cDelta * C.ell0)) * Real.sqrt (ell * Delta) := by
    calc
      eps ≤ c0 C * min (ell * D) (Real.sqrt (ell * Delta)) := hacc
      _ ≤ c0 C * Real.sqrt (ell * Delta) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (c0_pos C).le
      _ ≤ _ := mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.sqrt_nonneg _)
  have hm : eps * Real.sqrt (128 * C.cDelta * C.ell0) ≤
      C.g0 * Real.sqrt (ell * Delta) :=
    (le_div_iff₀ hs).1 (by simpa only [div_mul_eq_mul_div] using hsmall)
  have hm2 := mul_self_le_mul_self (by positivity :
      0 ≤ eps * Real.sqrt (128 * C.cDelta * C.ell0)) hm
  have hs2 := Real.sq_sqrt (show 0 ≤ 128 * C.cDelta * C.ell0 by positivity)
  have ht2 := Real.sq_sqrt (mul_nonneg hell.le hDelta.le)
  rw [rawM_eq C hell heps]
  apply (le_div_iff₀ (by positivity :
    0 < 32 * C.cDelta * C.ell0 * eps ^ 2)).2
  nlinarith [sq_nonneg eps]

theorem lengths_admissible (C : Constants) {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 C * min (ell * D) (Real.sqrt (ell * Delta))) :
    NCC.Admissible (stages C ell Delta eps) (innerLength C ell D eps) := by
  have hMr := rawM_ge_four C hell hDelta heps hacc
  have hNr := rawN_ge_twenty C hell hD heps hacc
  have hM : 4 ≤ stages C ell Delta eps :=
    (Nat.le_floor_iff (by linarith : 0 ≤ rawM C ell Delta eps)).2 hMr
  have hN : 20 ≤ innerLength C ell D eps :=
    (Nat.le_floor_iff (by linarith : 0 ≤ rawN C ell D eps)).2 hNr
  constructor <;> omega

theorem innerLength_le_raw (C : Constants) {ell D eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) :
    (innerLength C ell D eps : ℝ) ≤ C.cD * (D / scale C ell eps) := by
  apply Nat.floor_le
  exact mul_nonneg C.cD_pos.le (div_nonneg hD.le (scale_pos C hell heps).le)

/-- The strengthened current certificate is `c_Delta*M`, not `M+1`. -/
theorem scaled_gap_budget (C : Constants) {ell Delta eps : ℝ}
    (hell : 0 < ell) (hDelta : 0 < Delta) (heps : 0 < eps) :
    (ell * scale C ell eps ^ 2 / C.ell0) * C.cDelta *
      (stages C ell Delta eps : ℝ) ≤ Delta / 2 := by
  have hell0 := C.ell0_pos
  have hcDelta := C.cDelta_pos
  have hscale := scale_pos C hell heps
  have hfloor : (stages C ell Delta eps : ℝ) ≤ rawM C ell Delta eps :=
    Nat.floor_le (by unfold rawM; positivity)
  have hmul := mul_le_mul_of_nonneg_left hfloor
    (show 0 ≤ (ell * scale C ell eps ^ 2 / C.ell0) * C.cDelta by positivity)
  calc
    _ ≤ (ell * scale C ell eps ^ 2 / C.ell0) * C.cDelta *
        rawM C ell Delta eps := hmul
    _ = Delta / 2 := by
      unfold rawM
      field_simp [ne_of_gt C.ell0_pos, ne_of_gt C.cDelta_pos,
        ne_of_gt hell, ne_of_gt hscale]

theorem moreau_displacement_scale (C : Constants) {ell eps : ℝ}
    (hell : 0 < ell) (heps : 0 < eps) :
    eps / (2 * ell * scale C ell eps) = C.g0 / (8 * C.ell0) := by
  unfold scale
  field_simp [ne_of_gt C.ell0_pos, ne_of_gt C.g0_pos, ne_of_gt hell, ne_of_gt heps]
  ring

theorem moreau_terminal_threshold (C : Constants) {ell eps : ℝ}
    (hell : 0 < ell) (heps : 0 < eps) :
    eps / (2 * ell * scale C ell eps) < (1 : ℝ) / 5 := by
  have hell0 := C.ell0_pos
  rw [moreau_displacement_scale C hell heps]
  have : C.g0 / (8 * C.ell0) ≤ (1 : ℝ) / 8 := by
    apply (div_le_iff₀ (by positivity : 0 < 8 * C.ell0)).2
    nlinarith [C.g0_le]
  linarith

theorem scaled_gradient_margin (C : Constants) {ell eps : ℝ}
    (hell : 0 < ell) (heps : 0 < eps) :
    ell * scale C ell eps * C.g0 / C.ell0 = 4 * eps := by
  unfold scale
  field_simp [ne_of_gt C.ell0_pos, ne_of_gt C.g0_pos, ne_of_gt hell, ne_of_gt heps]

/-- Exact constant in the manuscript, with no loss from the inner floor
because the stage also has three primal coordinates. -/
theorem chain_length_lower (C : Constants) {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 C * min (ell * D) (Real.sqrt (ell * Delta))) :
    c1 C * (ell ^ 2 * D * Delta / eps ^ 3) ≤
      (NCC.chainLength (stages C ell Delta eps) (innerLength C ell D eps) : ℝ) := by
  have hM := rawM_ge_four C hell hDelta heps hacc
  have hN := rawN_ge_twenty C hell hD heps hacc
  have hMf : rawM C ell Delta eps / 2 ≤ (stages C ell Delta eps : ℝ) := by
    have := Nat.lt_floor_add_one (rawM C ell Delta eps)
    change rawM C ell Delta eps / 2 ≤ (⌊rawM C ell Delta eps⌋₊ : ℝ)
    linarith
  have hNf : rawN C ell D eps ≤ (innerLength C ell D eps : ℝ) + 3 := by
    have := Nat.lt_floor_add_one (rawN C ell D eps)
    change rawN C ell D eps ≤ (⌊rawN C ell D eps⌋₊ : ℝ) + 3
    linarith
  have hprod := mul_le_mul hMf hNf (by linarith : 0 ≤ rawN C ell D eps)
    (Nat.cast_nonneg (stages C ell Delta eps))
  calc
    _ = (rawM C ell Delta eps / 2) * rawN C ell D eps := by
      rw [rawM_eq C hell heps, rawN_eq]
      unfold c1
      field_simp [ne_of_gt C.cDelta_pos, ne_of_gt C.ell0_pos, ne_of_gt heps]
      ring
    _ ≤ (stages C ell Delta eps : ℝ) * ((innerLength C ell D eps : ℝ) + 3) := hprod
    _ = _ := by simp [NCC.chainLength]

end

end NCC.Lower.Parameters
