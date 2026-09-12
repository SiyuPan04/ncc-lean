import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar recurrences in the upper-bound proof

This file formalizes the numerical part of Section 7 of `main.tex`. In the
outer-loop lemmas, `a` denotes `ell * ‖z - xstar‖²`, `b` denotes the error
budget, and `d` denotes `ell * ‖znext - z‖²`. The Lyapunov function from
`eq:W` is represented explicitly by `p + 2 * b`.

The analytic estimates are hypotheses: these lemmas do not construct the
proximal points or a FOAM state, prove FOAM contraction, or prove the Moreau
envelope and gradient estimates. They verify the scalar consequences once
those inputs have been established. In particular, this is not a
formalization of the complete algorithm or its oracle complexity.
-/

namespace NCC.Upper

open scoped BigOperators

/-- The induction step for `eq:warm-budget-recursion`. Here `diameterSq`
stands for the square of the dual-domain diameter. -/
theorem warm_budget_step
    {delta rhoOld rhoNew diameterSq b bNext : ℝ}
    (hdelta : 0 ≤ delta) (hrho : 0 ≤ rhoNew)
    (hdiameter : 0 ≤ diameterSq)
    (hlevel : rhoOld = 4 * rhoNew)
    (hbudget : b ≤ 15 * (delta + rhoOld * diameterSq))
    (hupdate : bNext ≤ (1 / 8 : ℝ) *
      (b + (27 / 4 : ℝ) * rhoOld * diameterSq)) :
    bNext ≤ 15 * (delta + rhoNew * diameterSq) := by
  have hproduct : 0 ≤ rhoNew * diameterSq := mul_nonneg hrho hdiameter
  rw [hlevel] at hbudget hupdate
  nlinarith

/-- The warm-budget invariant in `prop:warm-start`, conditional on the
initial scalar bound and the displayed geometric budget recurrence. -/
theorem warm_budget_invariant
    (budget rho : ℕ → ℝ) (delta diameterSq : ℝ)
    (hdelta : 0 ≤ delta) (hdiameter : 0 ≤ diameterSq)
    (hrho : ∀ j, 0 ≤ rho j)
    (hzero : budget 0 ≤ 15 * (delta + rho 0 * diameterSq))
    (hlevel : ∀ j, rho j = 4 * rho (j + 1))
    (hupdate : ∀ j, budget (j + 1) ≤ (1 / 8 : ℝ) *
      (budget j + (27 / 4 : ℝ) * rho j * diameterSq)) :
    ∀ j, budget j ≤ 15 * (delta + rho j * diameterSq) := by
  intro j
  induction j with
  | zero => exact hzero
  | succ j ih =>
      exact warm_budget_step hdelta (hrho (j + 1)) hdiameter
        (hlevel j) ih (hupdate j)

/-- Substituting `eq:outer-step-bound` into `eq:outer-budget-update`. -/
theorem outer_budget_bound
    {a b d bNext : ℝ}
    (hstep : d ≤ 2 * a + 2 * b)
    (hupdate : bNext ≤ (2 * b + 24 * d) / 400) :
    bNext ≤ (48 / 400 : ℝ) * a + (50 / 400 : ℝ) * b := by
  linarith

/-- The numerical conclusion `eq:W-descent` in `lem:coupled-descent`,
assuming `eq:envelope-descent` and the scalar budget estimate. -/
theorem coupled_descent
    {p pNext a b bNext : ℝ}
    (ha : 0 ≤ a)
    (henvelope : pNext - p ≤ -a + b)
    (hbudget : bNext ≤ (48 / 400 : ℝ) * a + (50 / 400 : ℝ) * b) :
    (pNext + 2 * bNext) - (p + 2 * b) ≤ -(3 / 4 : ℝ) * (a + b) := by
  linarith

/-- `eq:W-descent` directly from the envelope estimate, displacement
estimate, and the update with contraction factor `1/400`. -/
theorem coupled_descent_from_update
    {p pNext a b d bNext : ℝ}
    (ha : 0 ≤ a)
    (henvelope : pNext - p ≤ -a + b)
    (hstep : d ≤ 2 * a + 2 * b)
    (hupdate : bNext ≤ (2 * b + 24 * d) / 400) :
    (pNext + 2 * bNext) - (p + 2 * b) ≤ -(3 / 4 : ℝ) * (a + b) := by
  exact coupled_descent ha henvelope (outer_budget_bound hstep hupdate)

/-- The scalar residual comparison `Q ≤ 3 R` in
`lem:observable-residual`, with `Q = d + b` and `R = a + b`. -/
theorem observable_residual_comparison
    {a b d : ℝ} (ha : 0 ≤ a) (hstep : d ≤ 2 * a + 2 * b) :
    d + b ≤ 3 * (a + b) := by
  linarith

/-- Combining `eq:W-descent` with `Q ≤ 3 R` gives the observable
decrease used in the proof of `eq:selected-gradient-bound`. -/
theorem observable_descent
    {w wNext r q : ℝ}
    (hdescent : wNext - w ≤ -(3 / 4 : ℝ) * r)
    (hcomparison : q ≤ 3 * r) :
    wNext - w ≤ -(1 / 4 : ℝ) * q := by
  linarith

/-- Finite telescoping of the observable decrease, conditional on the
terminal lower bound for the Lyapunov function. -/
theorem sum_observable_le_gap
    (w q : ℕ → ℝ) (T : ℕ) (lower : ℝ)
    (hdescent : ∀ t, t < T → w (t + 1) - w t ≤ -(1 / 4 : ℝ) * q t)
    (hlower : lower ≤ w T) :
    (∑ t ∈ Finset.range T, q t) ≤ 4 * (w 0 - lower) := by
  have htel : ∀ n, n ≤ T →
      (∑ t ∈ Finset.range n, q t) ≤ 4 * (w 0 - w n) := by
    intro n
    induction n with
    | zero =>
        intro _
        simp
    | succ n ih =>
        intro hn
        have hprevious := ih (Nat.le_of_succ_le hn)
        have hstep := hdescent n (Nat.lt_of_succ_le hn)
        rw [Finset.sum_range_succ]
        linarith
  have hsum := htel T le_rfl
  linarith

/-- The selected residual is at most `4 / T` times the initial gap.
The selection hypothesis explicitly says the chosen value is no larger
than every residual in the finite run; existence of an algorithmic
argmin is not assumed implicitly. -/
theorem selected_residual_bound
    (w q : ℕ → ℝ) (T : ℕ) (lower qSelected : ℝ)
    (hT : 0 < T)
    (hdescent : ∀ t, t < T → w (t + 1) - w t ≤ -(1 / 4 : ℝ) * q t)
    (hlower : lower ≤ w T)
    (hselected : ∀ t, t < T → qSelected ≤ q t) :
    qSelected ≤ 4 * (w 0 - lower) / (T : ℝ) := by
  have hminsum : (T : ℝ) * qSelected ≤ ∑ t ∈ Finset.range T, q t := by
    calc
      (T : ℝ) * qSelected = ∑ t ∈ Finset.range T, qSelected := by simp
      _ ≤ ∑ t ∈ Finset.range T, q t :=
        Finset.sum_le_sum (fun t ht => hselected t (Finset.mem_range.mp ht))
  have hsum := sum_observable_le_gap w q T lower hdescent hlower
  have hTreal : 0 < (T : ℝ) := Nat.cast_pos.mpr hT
  apply (le_div_iff₀ hTreal).2
  linarith

/-- The final scalar implication in `eq:selected-gradient-bound`.
The analytic estimate `gradientSq ≤ 8 * ell * qSelected` is an explicit
hypothesis, not proved by the recurrence argument. -/
theorem selected_gradient_squared_bound
    (w q : ℕ → ℝ) (T : ℕ) (lower qSelected ell gradientSq : ℝ)
    (hT : 0 < T) (hell : 0 ≤ ell)
    (hdescent : ∀ t, t < T → w (t + 1) - w t ≤ -(1 / 4 : ℝ) * q t)
    (hlower : lower ≤ w T)
    (hselected : ∀ t, t < T → qSelected ≤ q t)
    (hgradient : gradientSq ≤ 8 * ell * qSelected) :
    gradientSq ≤ (32 * ell / (T : ℝ)) * (w 0 - lower) := by
  have hq := selected_residual_bound w q T lower qSelected
    hT hdescent hlower hselected
  calc
    gradientSq ≤ 8 * ell * qSelected := hgradient
    _ ≤ 8 * ell * (4 * (w 0 - lower) / (T : ℝ)) :=
      mul_le_mul_of_nonneg_left hq (by linarith)
    _ = (32 * ell / (T : ℝ)) * (w 0 - lower) := by ring

/-- The numerical initial-gap estimate `eq:initial-W-bound`, where
`mass` represents `rho * diameterSq`. -/
theorem initial_lyapunov_gap
    {p lower delta mass b : ℝ}
    (hmass : 0 ≤ mass)
    (hvalue : p - lower ≤ delta + mass / 2)
    (hbudget : b ≤ 15 * (delta + mass)) :
    (p + 2 * b) - lower ≤ 31 * (delta + mass) := by
  linarith

end NCC.Upper
