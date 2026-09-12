import NCC.Extensions.NCSCProgram

/-!
# Fixed-curvature count with explicit NC-SC additive costs

The count keeps the actual initialization cost and the final refinement
cost separate from the leading accuracy term. The displayed sqrt(kappa)
comparison explicitly assumes `mu ≤ ell`; it is not silently inferred
on a degenerate dual domain.
-/
namespace NCC.Extensions.NCSCCost
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open NCC.Upper
set_option maxHeartbeats 3000000
variable {L r G eps ell mu : ℝ}

def leadingCost (L r G eps : ℝ) : ℝ :=
  4001 * UniformCost.blockConstant (1 / 400) * (L * G / eps ^ 2) * Real.sqrt (L / r)

def additiveCost (L r : ℝ) (initialCount : Nat) (rho : ℝ) : ℝ :=
  (initialCount : ℝ) +
    (4001 * UniformCost.blockConstant (1 / 400) + UniformCost.blockConstant rho) * Real.sqrt (L / r)

theorem fixedCount_split (hL : 0 < L) (hr : 0 < r) (hrle : r ≤ L / 8)
    (hG : 0 < G) (initialCount : Nat) {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    (NCSCProgram.fixedCount L r initialCount (Selection.outerIterations L G eps) rho : ℝ) ≤
      additiveCost L r initialCount rho + leadingCost L r G eps := by
  have hbase := NCSCProgram.fixedCount_le hL hr hrle initialCount
    (Selection.outerIterations L G eps) hrho hrho1
  have hT := CurrentCost.current_horizon_upper (eps := eps) hL hG
  have hC := UniformCost.blockConstant_pos
    (by norm_num : (0 : ℝ) < 1 / 400) (by norm_num : (1 / 400 : ℝ) < 1)
  have hm := mul_le_mul_of_nonneg_right hT
    (mul_nonneg hC.le (Real.sqrt_nonneg (L / r)))
  unfold leadingCost additiveCost
  nlinarith

theorem sqrt_condition_le (_hell : 0 < ell) (hmu : 0 < mu) (hmuell : mu ≤ ell) :
    Real.sqrt (NCSC.internalSmoothness ell mu / mu) ≤ 4 * Real.sqrt (ell / mu) := by
  have hL : NCSC.internalSmoothness ell mu ≤ 16 * ell := by
    unfold NCSC.internalSmoothness
    linarith
  have hratio := div_le_div_of_nonneg_right hL hmu.le
  have hs := Real.sqrt_le_sqrt hratio
  have heq : 16 * ell / mu = 16 * (ell / mu) := by ring
  rw [heq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)] at hs
  norm_num at hs
  exact hs

/-- Only the leading accuracy term is bounded here. Initial and final
refinement costs remain in `additiveCost` rather than disappearing into
an unspecified uniform-in-parameters constant. -/
theorem leadingCost_sqrt_kappa (hell : 0 < ell) (hmu : 0 < mu)
    (hmuell : mu ≤ ell) (hG : 0 ≤ G) :
    leadingCost (NCSC.internalSmoothness ell mu) mu G eps ≤
      256064 * UniformCost.blockConstant (1 / 400) *
        (ell * G / eps ^ 2) * Real.sqrt (ell / mu) := by
  have hLpos : 0 < NCSC.internalSmoothness ell mu := by
    unfold NCSC.internalSmoothness
    positivity
  have hL : NCSC.internalSmoothness ell mu ≤ 16 * ell := by
    unfold NCSC.internalSmoothness
    linarith
  have hs := sqrt_condition_le hell hmu hmuell
  have hC := UniformCost.blockConstant_pos
    (by norm_num : (0 : ℝ) < 1 / 400) (by norm_num : (1 / 400 : ℝ) < 1)
  have hLG := mul_le_mul_of_nonneg_right hL hG
  have hfrac := div_le_div_of_nonneg_right hLG (sq_nonneg eps)
  have hm := mul_le_mul hfrac hs
    (Real.sqrt_nonneg _) (show 0 ≤ 16 * ell * G / eps ^ 2 by positivity)
  have hm' := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4001 * UniformCost.blockConstant (1 / 400) by positivity)
  calc
    _ = 4001 * UniformCost.blockConstant (1 / 400) *
        (NCSC.internalSmoothness ell mu * G / eps ^ 2 *
          Real.sqrt (NCSC.internalSmoothness ell mu / mu)) := by
      unfold leadingCost
      ring
    _ ≤ 4001 * UniformCost.blockConstant (1 / 400) *
        (16 * ell * G / eps ^ 2 * (4 * Real.sqrt (ell / mu))) := hm'
    _ = _ := by ring

theorem fixedCount_sqrt_kappa (hell : 0 < ell) (hmu : 0 < mu)
    (hmuell : mu ≤ ell) (hG : 0 < G) (initialCount : Nat)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    (NCSCProgram.fixedCount (NCSC.internalSmoothness ell mu) mu initialCount
      (Selection.outerIterations (NCSC.internalSmoothness ell mu) G eps) rho : ℝ) ≤
      additiveCost (NCSC.internalSmoothness ell mu) mu initialCount rho +
        256064 * UniformCost.blockConstant (1 / 400) *
          (ell * G / eps ^ 2) * Real.sqrt (ell / mu) := by
  have hL : 0 < NCSC.internalSmoothness ell mu := by
    unfold NCSC.internalSmoothness
    positivity
  have hmuL : mu ≤ NCSC.internalSmoothness ell mu / 8 := by
    unfold NCSC.internalSmoothness
    linarith
  exact (fixedCount_split hL hmu hmuL hG initialCount hrho hrho1).trans
    (add_le_add_right (leadingCost_sqrt_kappa hell hmu hmuell hG.le) _)

end
end NCC.Extensions.NCSCCost
