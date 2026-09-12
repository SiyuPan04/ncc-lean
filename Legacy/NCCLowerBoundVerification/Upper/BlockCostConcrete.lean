import NCCLowerBoundVerification.Upper.ProjectedMicro
import NCCLowerBoundVerification.Upper.RelativeFOAMContraction

/-!
# Exact cost of a feasible relative-FOAM block

The analytic contraction modules count macrosteps, while the projected
micro-solver records its own fixed numerical cost.  This file composes the
two counters and proves the paper's `O(sqrt(mu/r) log(1/rho))` statement with
an explicit real-valued upper bound.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace BlockCostConcrete

noncomputable section

open RelativeFOAM ProjectedMicro

def feasibleBlockCost (mu r rho : ℝ) : RelativeFOAM.Cost :=
  RelativeFOAM.blockCost
    (RelativeFOAM.projectedMicroCost feasibleMicroIterations)
    (RelativeFOAM.blockIterations (RelativeFOAM.alpha mu r) rho)

@[simp] theorem feasibleBlockCost_oracleCalls (mu r rho : ℝ) :
    (feasibleBlockCost mu r rho).oracleCalls =
      RelativeFOAM.blockIterations (RelativeFOAM.alpha mu r) rho *
        (feasibleMicroIterations + 1) := rfl

@[simp] theorem feasibleBlockCost_projections (mu r rho : ℝ) :
    (feasibleBlockCost mu r rho).projections =
      RelativeFOAM.blockIterations (RelativeFOAM.alpha mu r) rho *
        (feasibleMicroIterations + 1) := rfl

/-- Exact ceiling-cost estimate before replacing `alpha` by its
`sqrt(r/mu)` formula. -/
theorem feasibleBlockCost_lt_alpha {mu r rho : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hrho : 0 < rho) (hrho1 : rho < 1) :
    ((feasibleBlockCost mu r rho).oracleCalls : ℝ) <
      (2 / RelativeFOAM.alpha mu r * Real.log (1 / rho) + 1) *
        (feasibleMicroIterations + 1) ∧
    ((feasibleBlockCost mu r rho).projections : ℝ) <
      (2 / RelativeFOAM.alpha mu r * Real.log (1 / rho) + 1) *
        (feasibleMicroIterations + 1) := by
  have hK := RelativeFOAM.blockIterations_lt
    (RelativeFOAM.alpha_pos hmu hr) hrho hrho1
  have hcost : (0 : ℝ) < feasibleMicroIterations + 1 := by positivity
  have hmul := mul_lt_mul_of_pos_right hK hcost
  simp only [feasibleBlockCost_oracleCalls,
    feasibleBlockCost_projections, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one]
  exact ⟨hmul, hmul⟩

/-- The conditioning identity used when reading the block bound. -/
theorem alpha_sq_eq_eight_mul_div {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r) :
    RelativeFOAM.alpha mu r ^ 2 = 8 * r / mu := by
  rw [RelativeFOAMContraction.alpha_sq_eq hmu hr]
  unfold RelativeFOAM.theta
  ring

theorem inv_alpha_le_sqrt_ratio {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) :
    1 / RelativeFOAM.alpha mu r ≤ Real.sqrt (mu / r) := by
  let a := RelativeFOAM.alpha mu r
  have ha : 0 < a := RelativeFOAM.alpha_pos hmu hr
  have ha2 : a ^ 2 = 8 * r / mu := by
    dsimp [a]
    exact alpha_sq_eq_eight_mul_div hmu hr.le
  have hratio : 0 ≤ mu / r := by positivity
  have hs0 : 0 ≤ Real.sqrt (mu / r) := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt (mu / r)) ^ 2 = mu / r :=
    Real.sq_sqrt hratio
  have hinv0 : 0 ≤ 1 / a := by positivity
  have hsquare : (1 / a) ^ 2 ≤ mu / r := by
    rw [div_pow]
    field_simp [ne_of_gt ha, ne_of_gt hmu, ne_of_gt hr] at ha2 ⊢
    nlinarith
  nlinarith

/-- For a constant contraction factor `rho`, both resource counts are
bounded by a numerical multiple of `sqrt(mu/r)`. -/
theorem feasibleBlockCost_lt_sqrt_ratio {mu r rho : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hrmu : r ≤ mu / 8)
    (hrho : 0 < rho) (hrho1 : rho < 1) :
    let C := (2 * Real.log (1 / rho) + 1) *
      (feasibleMicroIterations + 1 : ℝ)
    ((feasibleBlockCost mu r rho).oracleCalls : ℝ) <
        C * Real.sqrt (mu / r) ∧
      ((feasibleBlockCost mu r rho).projections : ℝ) <
        C * Real.sqrt (mu / r) := by
  dsimp
  let a := RelativeFOAM.alpha mu r
  have ha : 0 < a := RelativeFOAM.alpha_pos hmu hr
  have ha1 : a ≤ 1 := RelativeFOAM.alpha_le_one hmu hr.le hrmu
  have hlog : 0 < Real.log (1 / rho) := by
    apply Real.log_pos
    exact (lt_div_iff₀ hrho).2 (by simpa using hrho1)
  have hfactor : 2 / a * Real.log (1 / rho) + 1 ≤
      (2 * Real.log (1 / rho) + 1) * (1 / a) := by
    have hainv : 1 ≤ 1 / a := (le_div_iff₀ ha).2 (by simpa using ha1)
    field_simp [ne_of_gt ha]
    nlinarith
  have hcost0 : 0 < (feasibleMicroIterations + 1 : ℝ) := by positivity
  have hceil := feasibleBlockCost_lt_alpha hmu hr hrho hrho1
  have hinv := inv_alpha_le_sqrt_ratio hmu hr
  have hC0 : 0 ≤ 2 * Real.log (1 / rho) + 1 := by positivity
  have hright := mul_le_mul_of_nonneg_left hinv hC0
  have hfactorCost := mul_le_mul_of_nonneg_right hfactor hcost0.le
  have hrightCost := mul_le_mul_of_nonneg_right hright hcost0.le
  constructor
  · calc
      ((feasibleBlockCost mu r rho).oracleCalls : ℝ) <
          (2 / a * Real.log (1 / rho) + 1) *
            (feasibleMicroIterations + 1) := by simpa [a] using hceil.1
      _ ≤ (2 * Real.log (1 / rho) + 1) * (1 / a) *
            (feasibleMicroIterations + 1) := hfactorCost
      _ ≤ (2 * Real.log (1 / rho) + 1) * Real.sqrt (mu / r) *
            (feasibleMicroIterations + 1) := by simpa [a] using hrightCost
      _ = (2 * Real.log (1 / rho) + 1) *
            (feasibleMicroIterations + 1) * Real.sqrt (mu / r) := by ring
  · calc
      ((feasibleBlockCost mu r rho).projections : ℝ) <
          (2 / a * Real.log (1 / rho) + 1) *
            (feasibleMicroIterations + 1) := by simpa [a] using hceil.2
      _ ≤ (2 * Real.log (1 / rho) + 1) * (1 / a) *
            (feasibleMicroIterations + 1) := hfactorCost
      _ ≤ (2 * Real.log (1 / rho) + 1) * Real.sqrt (mu / r) *
            (feasibleMicroIterations + 1) := by simpa [a] using hrightCost
      _ = (2 * Real.log (1 / rho) + 1) *
            (feasibleMicroIterations + 1) * Real.sqrt (mu / r) := by ring

end

end BlockCostConcrete
end Upper
end NCCLowerBoundVerification
