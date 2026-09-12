import Mathlib

/-!
# Floor and scaling arithmetic for the lower bound

This module expands the `Omega` calculation in `thm:zr` into a concrete
constant inequality, including both floor losses.
-/

namespace NCCLowerBoundVerification

noncomputable section

theorem half_le_natFloor {a : ℝ} (ha : 2 ≤ a) :
    a / 2 ≤ (⌊a⌋₊ : ℝ) := by
  have hfloor : a < (⌊a⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one a
  linarith

def lowerScale (ell ell0 eps c0 : ℝ) : ℝ :=
  4 * ell0 * eps / (c0 * ell)

def lowerNArg (D Cy P1 ell ell0 eps c0 : ℝ) : ℝ :=
  D / (2 * Cy * P1 * lowerScale ell ell0 eps c0)

def lowerTArg (Delta cDelta ell ell0 eps c0 : ℝ) : ℝ :=
  ell0 * Delta /
    (2 * cDelta * ell * (lowerScale ell ell0 eps c0) ^ 2)

def lowerN (D Cy P1 ell ell0 eps c0 : ℝ) : Nat :=
  ⌊lowerNArg D Cy P1 ell ell0 eps c0⌋₊

def lowerT (Delta cDelta ell ell0 eps c0 : ℝ) : Nat :=
  ⌊lowerTArg Delta cDelta ell ell0 eps c0⌋₊

theorem lowerNArg_eq
    {D Cy P1 ell ell0 eps c0 : ℝ}
    (hCy : Cy ≠ 0) (hP1 : P1 ≠ 0) (hell : ell ≠ 0)
    (hell0 : ell0 ≠ 0) (heps : eps ≠ 0) (hc0 : c0 ≠ 0) :
    lowerNArg D Cy P1 ell ell0 eps c0 =
      c0 * ell * D / (8 * Cy * P1 * ell0 * eps) := by
  unfold lowerNArg lowerScale
  field_simp [hCy, hP1, hell, hell0, heps, hc0]
  ring

theorem lowerTArg_eq
    {Delta cDelta ell ell0 eps c0 : ℝ}
    (hcDelta : cDelta ≠ 0) (hell : ell ≠ 0)
    (hell0 : ell0 ≠ 0) (heps : eps ≠ 0) (hc0 : c0 ≠ 0) :
    lowerTArg Delta cDelta ell ell0 eps c0 =
      c0 ^ 2 * ell * Delta / (32 * cDelta * ell0 * eps ^ 2) := by
  unfold lowerTArg lowerScale
  field_simp [hcDelta, hell, hell0, heps, hc0]
  ring

/-- Generic two-floor loss: if the raw inner length is at least `2` and the
raw outer length is at least `4`, the chain retains at least one quarter of
their product. -/
theorem floored_chain_product_lower {A B : ℝ}
    (hA : 2 ≤ A) (hB : 4 ≤ B) :
    A * B / 4 ≤ ((⌊B⌋₊ - 1) * (⌊A⌋₊ + 3) : Nat) := by
  have hAfloor : A / 2 ≤ (⌊A⌋₊ : ℝ) := half_le_natFloor hA
  have hBfloor : B / 2 ≤ (⌊B⌋₊ : ℝ) := half_le_natFloor (by linarith)
  have hBfloorStrict : B < (⌊B⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one B
  have hBfloorTwoReal : (2 : ℝ) ≤ (⌊B⌋₊ : ℝ) := by linarith
  have hBfloorTwo : 2 ≤ ⌊B⌋₊ := by exact_mod_cast hBfloorTwoReal
  have hsubcast : ((⌊B⌋₊ - 1 : Nat) : ℝ) = (⌊B⌋₊ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ ⌊B⌋₊)]
    norm_num
  have houter : B / 4 ≤ ((⌊B⌋₊ - 1 : Nat) : ℝ) := by
    rw [hsubcast]
    linarith
  have hinner : A / 2 ≤ ((⌊A⌋₊ + 3 : Nat) : ℝ) := by
    norm_cast at hAfloor ⊢
    exact_mod_cast hAfloor.trans (Nat.cast_le.2 (Nat.le_add_right ⌊A⌋₊ 3))
  have houterSharp : B / 2 ≤ ((⌊B⌋₊ - 1 : Nat) : ℝ) := by
    rw [hsubcast]
    linarith
  have houter0 : 0 ≤ B / 2 := by linarith
  have hinner0 : 0 ≤ (A / 2) := by linarith
  have hmul := mul_le_mul houterSharp hinner hinner0
    (Nat.cast_nonneg (⌊B⌋₊ - 1))
  norm_cast at hmul ⊢
  calc
    A * B / 4 = (B / 2) * (A / 2) := by ring
    _ ≤ (((⌊B⌋₊ - 1) * (⌊A⌋₊ + 3) : Nat) : ℝ) := by
      simpa only [Nat.cast_mul] using hmul

/-- Constant-bearing version of the lower-bound chain length after the
paper's choices of `lambda`, `n`, and `T`. -/
theorem scaled_chain_length_lower
    {ell D Delta eps ell0 c0 Cy P1 cDelta : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hell0 : 0 < ell0) (hc0 : 0 < c0) (hCy : 0 < Cy)
    (hP1 : 0 < P1) (hcDelta : 0 < cDelta)
    (hNregime : 20 ≤ c0 * ell * D / (8 * Cy * P1 * ell0 * eps))
    (hTregime : 4 ≤ c0 ^ 2 * ell * Delta /
      (32 * cDelta * ell0 * eps ^ 2)) :
    c0 ^ 3 / (1024 * Cy * P1 * cDelta * ell0 ^ 2) *
        (ell ^ 2 * D * Delta / eps ^ 3) ≤
      ((lowerT Delta cDelta ell ell0 eps c0 - 1) *
        (lowerN D Cy P1 ell ell0 eps c0 + 3) : Nat) := by
  have hNeq := lowerNArg_eq (D := D) (Cy := Cy) (P1 := P1)
    hCy.ne' hP1.ne' hell.ne' hell0.ne' heps.ne' hc0.ne'
  have hTeq := lowerTArg_eq (Delta := Delta) (cDelta := cDelta)
    hcDelta.ne' hell.ne' hell0.ne' heps.ne' hc0.ne'
  have hraw := floored_chain_product_lower
    (A := lowerNArg D Cy P1 ell ell0 eps c0)
    (B := lowerTArg Delta cDelta ell ell0 eps c0)
    (by rw [hNeq]; linarith)
    (by rw [hTeq]; exact hTregime)
  change _ ≤
    (((⌊lowerTArg Delta cDelta ell ell0 eps c0⌋₊ - 1) *
      (⌊lowerNArg D Cy P1 ell ell0 eps c0⌋₊ + 3) : Nat) : ℝ)
  rw [hNeq, hTeq] at hraw
  rw [hNeq, hTeq]
  calc
    c0 ^ 3 / (1024 * Cy * P1 * cDelta * ell0 ^ 2) *
        (ell ^ 2 * D * Delta / eps ^ 3) =
      (c0 * ell * D / (8 * Cy * P1 * ell0 * eps)) *
        (c0 ^ 2 * ell * Delta / (32 * cDelta * ell0 * eps ^ 2)) / 4 := by
          field_simp [hCy.ne', hP1.ne', hcDelta.ne', hell0.ne', heps.ne']
          ring
    _ ≤ _ := hraw

end

end NCCLowerBoundVerification
