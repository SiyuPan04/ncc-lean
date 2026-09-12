import NCCLowerBoundVerification.Lower.Activation
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Infinite smoothness and flat tails of the activation family

This file completes the arbitrary-order part of
`lem:Psi-family-properties` in `Upper+Lower_unified_lower.tex`.  The first
gate is built from the extension of `x ↦ exp (-1 / x^2)` by zero on the
nonpositive half-line.  We prove directly that this extension is smooth,
then transfer the result to `Psi1` and its translate `Psi2`.  Finally, the
flat-tail assertion is stated literally using `iteratedDeriv`.
-/

namespace NCCLowerBoundVerification

noncomputable section

open Filter Polynomial Set
open scoped Topology ContDiff

namespace ActivationInfinity

/-! ## The flat exponential splice -/

/-- `p(x⁻¹) exp (-x⁻²)` tends to zero as `x → 0`.  This is the
arbitrary-polynomial estimate needed to differentiate through the splice
any finite number of times. -/
theorem tendsto_polynomial_inv_mul_expNegInvSqGlue_zero (p : ℝ[X]) :
    Tendsto
      (fun x : ℝ ↦ p.eval x⁻¹ * NCPLVerification.expNegInvSqGlue x)
      (𝓝 0) (𝓝 0) := by
  have hquad : Tendsto (fun y : ℝ ↦ y - y ^ 2) atTop atBot := by
    rw [tendsto_atBot]
    intro b
    filter_upwards [eventually_ge_atTop (max 2 (-b))] with y hy
    have hy2 : 2 ≤ y := le_trans (le_max_left _ _) hy
    have hyb : -b ≤ y := le_trans (le_max_right _ _) hy
    nlinarith
  have hexp : Tendsto (fun y : ℝ ↦ Real.exp (y - y ^ 2)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hquad
  have hpoly : Tendsto (fun y : ℝ ↦ p.eval y / Real.exp y) atTop (𝓝 0) :=
    p.tendsto_div_exp_atTop
  have hatTop : Tendsto
      (fun y : ℝ ↦ p.eval y * Real.exp (-(y ^ 2))) atTop (𝓝 0) := by
    convert hpoly.mul hexp using 1
    · funext y
      rw [div_eq_mul_inv, ← Real.exp_neg]
      calc
        p.eval y * Real.exp (-(y ^ 2)) =
            p.eval y * Real.exp ((-y) + (y - y ^ 2)) := by
              apply congrArg (fun z : ℝ ↦ p.eval y * Real.exp z)
              ring
        _ = p.eval y * (Real.exp (-y) * Real.exp (y - y ^ 2)) := by
              rw [Real.exp_add]
        _ = p.eval y * Real.exp (-y) * Real.exp (y - y ^ 2) :=
          (mul_assoc _ _ _).symm
    · simp
  simp only [NCPLVerification.expNegInvSqGlue, mul_ite, mul_zero]
  refine tendsto_const_nhds.if ?_
  simp only [not_le]
  have h := hatTop.comp tendsto_inv_nhdsGT_zero
  exact h.congr' (by
    filter_upwards with x
    rfl)

/-- Differentiating `p(x⁻¹) exp (-x⁻²)` produces another expression of
the same form. -/
theorem hasDerivAt_polynomial_eval_inv_mul_expNegInvSqGlue
    (p : ℝ[X]) (x : ℝ) :
    HasDerivAt
      (fun x : ℝ ↦ p.eval x⁻¹ * NCPLVerification.expNegInvSqGlue x)
      ((X ^ 2 * (2 * X * p - derivative p)).eval x⁻¹ *
        NCPLVerification.expNegInvSqGlue x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [NCPLVerification.expNegInvSqGlue_of_nonpos hx.le, mul_zero]
    refine (hasDerivAt_const _ 0).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hx] with y hy
    rw [NCPLVerification.expNegInvSqGlue_of_nonpos hy.le, mul_zero]
  · rw [NCPLVerification.expNegInvSqGlue_zero, mul_zero,
      hasDerivAt_iff_tendsto_slope]
    refine
      ((tendsto_polynomial_inv_mul_expNegInvSqGlue_zero (p * X)).mono_left
        inf_le_left).congr (fun y ↦ ?_)
    simp [slope_def_field, div_eq_mul_inv, mul_right_comm]
  · have hp := (p.hasDerivAt x⁻¹).comp x (hasDerivAt_inv hx.ne')
    have hf := NCPLVerification.hasDerivAt_expNegInvSqGlue x
    have hprod := hp.mul hf
    convert! hprod.congr_of_eventuallyEq _ using 1
    · rw [NCPLVerification.expNegInvSqGlueDeriv, if_neg hx.not_ge]
      rw [NCPLVerification.expNegInvSqGlue, if_neg hx.not_ge]
      simp
      ring
    · filter_upwards with y
      rfl

theorem differentiable_polynomial_eval_inv_mul_expNegInvSqGlue (p : ℝ[X]) :
    Differentiable ℝ
      (fun x : ℝ ↦ p.eval x⁻¹ * NCPLVerification.expNegInvSqGlue x) :=
  fun x ↦
    (hasDerivAt_polynomial_eval_inv_mul_expNegInvSqGlue p x).differentiableAt

theorem continuous_polynomial_eval_inv_mul_expNegInvSqGlue (p : ℝ[X]) :
    Continuous
      (fun x : ℝ ↦ p.eval x⁻¹ * NCPLVerification.expNegInvSqGlue x) :=
  (differentiable_polynomial_eval_inv_mul_expNegInvSqGlue p).continuous

/-- Every polynomial-weighted flat exponential is `C^n` for arbitrary
finite or infinite `n`. -/
theorem contDiff_polynomial_eval_inv_mul_expNegInvSqGlue
    {n : ℕ∞} (p : ℝ[X]) :
    ContDiff ℝ n
      (fun x : ℝ ↦ p.eval x⁻¹ * NCPLVerification.expNegInvSqGlue x) := by
  apply contDiff_all_iff_nat.2 (fun m ↦ ?_) n
  induction m generalizing p with
  | zero =>
      exact contDiff_zero.2
        (continuous_polynomial_eval_inv_mul_expNegInvSqGlue p)
  | succ m ihm =>
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
      refine contDiff_succ_iff_deriv.2
        ⟨differentiable_polynomial_eval_inv_mul_expNegInvSqGlue p,
          by simp, ?_⟩
      convert! ihm (X ^ 2 * (2 * X * p - derivative p)) using 2
      exact (hasDerivAt_polynomial_eval_inv_mul_expNegInvSqGlue p _).deriv

/-- The exact flat-exponential splice used by `Psi1` is infinitely smooth. -/
theorem contDiff_expNegInvSqGlue {n : ℕ∞} :
    ContDiff ℝ n NCPLVerification.expNegInvSqGlue := by
  simpa using contDiff_polynomial_eval_inv_mul_expNegInvSqGlue (n := n) 1

end ActivationInfinity

/-! ## The two activations -/

/-- `Psi1` is `C^∞`, as claimed in `lem:Psi-family-properties`. -/
theorem contDiff_Psi1 : ContDiff ℝ ∞ Psi1 := by
  unfold Psi1 NCPLVerification.carmonPsi
  have hflat : ContDiff ℝ ∞ NCPLVerification.expNegInvSqGlue :=
    ActivationInfinity.contDiff_expNegInvSqGlue
  have harg : ContDiff ℝ ∞ (fun t : ℝ ↦ 2 * t - 1) := by
    fun_prop
  simpa only [Function.comp_apply] using contDiff_const.mul (hflat.comp harg)

/-- `Psi2`, the translate of `Psi1`, is `C^∞`. -/
theorem contDiff_Psi2 : ContDiff ℝ ∞ Psi2 := by
  unfold Psi2
  have harg : ContDiff ℝ ∞ (fun t : ℝ ↦ t - 1 / 2) := by
    fun_prop
  simpa only [Function.comp_def] using contDiff_Psi1.comp harg

/-- Every iterated derivative of `Psi1`, including order zero, vanishes
on the full closed left tail `(-∞, 1/2]`. -/
theorem iteratedDeriv_Psi1_eq_zero_of_le_half
    (k : ℕ) {t : ℝ} (ht : t ≤ 1 / 2) :
    iteratedDeriv k Psi1 t = 0 := by
  let s : Set ℝ := Iic (1 / 2)
  have hEq : Set.EqOn Psi1 (fun _ : ℝ ↦ 0) s := by
    intro x hx
    exact Psi1_eq_zero_of_le_half hx
  calc
    iteratedDeriv k Psi1 t = iteratedDerivWithin k Psi1 s t :=
      (iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Iic (1 / 2))
        (contDiff_Psi1.of_le (by
          exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))).contDiffAt ht).symm
    _ = iteratedDerivWithin k (fun _ : ℝ ↦ 0) s t :=
      iteratedDerivWithin_congr hEq ht
    _ = iteratedDeriv k (fun _ : ℝ ↦ 0) t :=
      iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Iic (1 / 2))
        contDiff_const.contDiffAt ht
    _ = 0 := by simp

/-- The two left-tail identities for `Psi2` that are stated explicitly in
`lem:Psi-family-properties`, written in the same iterated-derivative
notation as the arbitrary-order `Psi1` result. -/
theorem iteratedDeriv_Psi2_zero_and_one_of_le_one
    {t : ℝ} (ht : t ≤ 1) :
    iteratedDeriv 0 Psi2 t = 0 ∧ iteratedDeriv 1 Psi2 t = 0 := by
  constructor
  · simpa only [iteratedDeriv_zero] using Psi2_eq_zero_of_le_one ht
  · rw [iteratedDeriv_one, deriv_Psi2]
    exact Psi2Deriv_eq_zero_of_le_one ht

end

end NCCLowerBoundVerification
