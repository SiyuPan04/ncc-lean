import Mathlib

/-!
# Arithmetic normalization of the headline complexity rate

The paper states a uniform rate and then removes the additive/max terms in
the nontrivial accuracy regime.  This module checks that simplification with
explicit constants and no asymptotic notation.
-/

namespace NCCLowerBoundVerification

/-- The uniform expression is at most twice the log-free headline term in
the regime `eps² ≤ ell * Delta` and `eps ≤ ell * D`. -/
theorem uniformRate_le_two_mul_logFree
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hgap : eps ^ 2 ≤ ell * Delta) (hdiam : eps ≤ ell * D) :
    (ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps) ≤
      2 * (ell ^ 2 * D * Delta / eps ^ 3) := by
  have hepsSq : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hA : 1 ≤ ell * Delta / eps ^ 2 := by
    rw [le_div_iff₀ hepsSq]
    simpa using hgap
  have hB : 1 ≤ ell * D / eps := by
    rw [le_div_iff₀ heps]
    simpa using hdiam
  rw [max_eq_right hB]
  have hBnonneg : 0 ≤ ell * D / eps := le_trans zero_le_one hB
  calc
    (ell * Delta / eps ^ 2 + 1) * (ell * D / eps) ≤
        (2 * (ell * Delta / eps ^ 2)) * (ell * D / eps) := by
      apply mul_le_mul_of_nonneg_right _ hBnonneg
      linarith
    _ = 2 * (ell ^ 2 * D * Delta / eps ^ 3) := by
      field_simp [ne_of_gt heps]

/-- A convenient constant-carrying implication: any algorithm satisfying an
explicit multiple of the uniform expression automatically satisfies an
explicit multiple of the log-free expression. -/
theorem cost_le_uniform_implies_cost_le_logFree
    {cost C ell D Delta eps : ℝ}
    (hC : 0 ≤ C)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hgap : eps ^ 2 ≤ ell * Delta) (hdiam : eps ≤ ell * D)
    (hcost : cost ≤ C *
      ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps))) :
    cost ≤ (2 * C) * (ell ^ 2 * D * Delta / eps ^ 3) := by
  calc
    cost ≤ C * ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) := hcost
    _ ≤ C * (2 * (ell ^ 2 * D * Delta / eps ^ 3)) :=
      mul_le_mul_of_nonneg_left
        (uniformRate_le_two_mul_logFree hell hD hDelta heps hgap hdiam) hC
    _ = (2 * C) * (ell ^ 2 * D * Delta / eps ^ 3) := by ring

/-- Matching explicit upper and lower constant bounds imply a `Theta`
statement without using an opaque asymptotic notation. -/
theorem explicit_matching_bounds
    {cost rate c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hlower : c * rate ≤ cost) (hupper : cost ≤ C * rate) :
    ∃ c₀ C₀ : ℝ, 0 < c₀ ∧ 0 < C₀ ∧
      c₀ * rate ≤ cost ∧ cost ≤ C₀ * rate :=
  ⟨c, C, hc, hC, hlower, hupper⟩

end NCCLowerBoundVerification
