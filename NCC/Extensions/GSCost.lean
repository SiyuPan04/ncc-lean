import Mathlib

/-!
# Scalar domination for the game-stationarity query count

This is numerical algebra only. It does not assume or manufacture an oracle
program: the caller supplies its proved literal count bound, schedule lower
bound, and outer-iteration estimate. The resulting constant is independent
of the target accuracy.
-/

namespace NCC.Extensions.GSCost

noncomputable section

def rateConstant (ell a b base warm outer e : ℝ) : ℝ :=
  base + (warm + b * outer + 1000000 * ell * e / a) * Real.sqrt (ell / a)

/-- A refinement cost bounded by `e/rho` is lower order than the tracked
outer cost when `r` is proportional to the target game-stationarity accuracy.
The complete bound has exactly the denominator `eps^2 * sqrt eps`. -/
theorem count_le {ell a b base warm outer e eps r rho T cost : ℝ}
    (hell : 0 < ell) (ha : 0 < a) (hb : 0 ≤ b) (hbase : 0 ≤ base)
    (hwarm : 0 ≤ warm) (houter : 0 ≤ outer) (he : 0 ≤ e)
    (heps : 0 < eps) (heps1 : eps ≤ 1) (hr : a * eps ≤ r)
    (hrho : rho = r / (1000000 * ell)) (hT : T ≤ b / eps ^ 2)
    (hcost : cost ≤ base + (warm + T * outer + e / rho) * Real.sqrt (ell / r)) :
    cost ≤ rateConstant ell a b base warm outer e / (eps ^ 2 * Real.sqrt eps) := by
  have hrpos : 0 < r := (mul_pos ha heps).trans_le hr
  have hspos := Real.sqrt_pos.2 heps
  have hsq : eps ^ 2 ≤ 1 := by nlinarith
  have hs1 : Real.sqrt eps ≤ 1 := Real.sqrt_le_one.mpr heps1
  have hden : 0 < eps ^ 2 * Real.sqrt eps := by positivity
  have hden1 : eps ^ 2 * Real.sqrt eps ≤ 1 := by nlinarith [Real.sqrt_nonneg eps]
  have hroot : Real.sqrt (ell / r) * Real.sqrt eps ≤ Real.sqrt (ell / a) := by
    rw [← Real.sqrt_mul (div_nonneg hell.le hrpos.le)]
    apply Real.sqrt_le_sqrt
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ hrpos ha).2
    have hm := mul_le_mul_of_nonneg_left hr hell.le
    nlinarith
  have hTs : T * eps ^ 2 ≤ b := (le_div_iff₀ (sq_pos_of_pos heps)).1 hT
  have hTouter : T * outer * eps ^ 2 ≤ b * outer := by
    have := mul_le_mul_of_nonneg_right hTs houter
    nlinarith
  have heq : e / rho = (1000000 * ell * e) / r := by
    rw [hrho]
    field_simp [hrpos.ne', hell.ne']
  have hediv := div_le_div_of_nonneg_left
    (by positivity : 0 ≤ 1000000 * ell * e) (mul_pos ha heps) hr
  have her : e / rho * eps ^ 2 ≤ 1000000 * ell * e / a := by
    calc
      _ ≤ (1000000 * ell * e) / (a * eps) * eps ^ 2 := by
        rw [heq]
        exact mul_le_mul_of_nonneg_right hediv (sq_nonneg eps)
      _ = (1000000 * ell * e / a) * eps := by field_simp
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left heps1
          (by positivity : 0 ≤ 1000000 * ell * e / a)
        simpa using this
  have hw : warm * eps ^ 2 ≤ warm := by
    simpa using mul_le_mul_of_nonneg_left hsq hwarm
  have hcoeff : (warm + T * outer + e / rho) * eps ^ 2 ≤
      warm + b * outer + 1000000 * ell * e / a := by nlinarith
  have hcoeff0 : 0 ≤ warm + b * outer + 1000000 * ell * e / a := by positivity
  have hprod := mul_le_mul hcoeff hroot (by positivity :
    0 ≤ Real.sqrt (ell / r) * Real.sqrt eps) hcoeff0
  have hbase' := mul_le_mul_of_nonneg_left hden1 hbase
  apply (le_div_iff₀ hden).2
  have hc := mul_le_mul_of_nonneg_right hcost hden.le
  unfold rateConstant
  nlinarith

end

end NCC.Extensions.GSCost
