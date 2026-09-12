import NCPLVerification.CarmonDifferentiability
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Uniform scalar and outer-chain smoothness bounds

This file supplies explicit global constants for the two scalar functions in
the Carmon chain.  These estimates are independent of the chain length.
-/

namespace NCPLVerification

noncomputable section

private theorem pow_four_mul_exp_neg_sq_le_two (u : ℝ) :
    u ^ 4 * Real.exp (-(u ^ 2)) ≤ 2 := by
  have h := Real.pow_div_factorial_le_exp (u ^ 2) (sq_nonneg u) 2
  norm_num [div_eq_mul_inv] at h
  have hpow : (u ^ 2) ^ 2 ≤ 2 * Real.exp (u ^ 2) := by nlinarith
  have hdiv := (div_le_iff₀ (Real.exp_pos (u ^ 2))).2 hpow
  rw [Real.exp_neg]
  change u ^ 4 * (Real.exp (u ^ 2))⁻¹ ≤ 2
  have heq : (u ^ 2) ^ 2 = u ^ 4 := by ring
  rw [heq] at hdiv
  exact hdiv

private theorem pow_six_mul_exp_neg_sq_le_six (u : ℝ) :
    u ^ 6 * Real.exp (-(u ^ 2)) ≤ 6 := by
  have h := Real.pow_div_factorial_le_exp (u ^ 2) (sq_nonneg u) 3
  norm_num [div_eq_mul_inv] at h
  have hpow : (u ^ 2) ^ 3 ≤ 6 * Real.exp (u ^ 2) := by nlinarith
  have hdiv := (div_le_iff₀ (Real.exp_pos (u ^ 2))).2 hpow
  rw [Real.exp_neg]
  change u ^ 6 * (Real.exp (u ^ 2))⁻¹ ≤ 6
  have heq : (u ^ 2) ^ 3 = u ^ 6 := by ring
  rw [heq] at hdiv
  exact hdiv

theorem abs_expNegInvSqGlueSecond_le_thirtySix (x : ℝ) :
    |expNegInvSqGlueSecond x| ≤ 36 := by
  by_cases hx : x ≤ 0
  · simp [expNegInvSqGlueSecond, hx]
  · have hxpos : 0 < x := lt_of_not_ge hx
    let u := x⁻¹
    have hu0 : 0 ≤ u := (inv_pos.mpr hxpos).le
    have h4 := pow_four_mul_exp_neg_sq_le_two u
    have h6 := pow_six_mul_exp_neg_sq_le_six u
    have he0 : 0 ≤ Real.exp (-(u ^ 2)) := (Real.exp_pos _).le
    have habs : |4 * u ^ 6 - 6 * u ^ 4| ≤ 4 * u ^ 6 + 6 * u ^ 4 := by
      calc
        |4 * u ^ 6 - 6 * u ^ 4| ≤ |4 * u ^ 6| + |6 * u ^ 4| := abs_sub _ _
        _ = 4 * u ^ 6 + 6 * u ^ 4 := by
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    rw [expNegInvSqGlueSecond, if_neg hx]
    change |(4 * u ^ 6 - 6 * u ^ 4) * Real.exp (-(u ^ 2))| ≤ 36
    rw [abs_mul, abs_of_nonneg he0]
    have hm := mul_le_mul_of_nonneg_right habs he0
    nlinarith

theorem abs_expNegInvSqGlueDeriv_le_four (x : ℝ) :
    |expNegInvSqGlueDeriv x| ≤ 4 := by
  by_cases hx : x ≤ 0
  · simp [expNegInvSqGlueDeriv, hx]
  · have hxpos : 0 < x := lt_of_not_ge hx
    let u := x⁻¹
    have hu0 : 0 ≤ u := (inv_pos.mpr hxpos).le
    have he0 : 0 ≤ Real.exp (-(u ^ 2)) := (Real.exp_pos _).le
    have he1 : Real.exp (-(u ^ 2)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (sq_nonneg u)
    have hcore : u ^ 3 * Real.exp (-(u ^ 2)) ≤ 2 := by
      by_cases hu : u ≤ 1
      · have hu2 : u ^ 2 ≤ 1 := by nlinarith [sq_nonneg (1 - u)]
        have hu3 : u ^ 3 ≤ 1 := by
          nlinarith [mul_nonneg (sq_nonneg u) (sub_nonneg.mpr hu)]
        have hm := mul_le_mul hu3 he1 he0 (by norm_num : (0 : ℝ) ≤ 1)
        exact hm.trans (by norm_num)
      · have hu1 : 1 ≤ u := le_of_not_ge hu
        have hp : u ^ 3 ≤ u ^ 4 := by nlinarith [sq_nonneg u, pow_nonneg hu0 3]
        have hm := mul_le_mul_of_nonneg_right hp he0
        exact hm.trans (pow_four_mul_exp_neg_sq_le_two u)
    rw [expNegInvSqGlueDeriv, if_neg hx]
    change |2 * u ^ 3 * Real.exp (-(u ^ 2))| ≤ 4
    rw [abs_of_nonneg (by positivity)]
    nlinarith

theorem hasDerivAt_carmonPsiDeriv (t : ℝ) :
    HasDerivAt carmonPsiDeriv (carmonPsiSecond t) t := by
  unfold carmonPsiDeriv carmonPsiSecond
  have harg : HasDerivAt (fun s : ℝ ↦ 2 * s - 1) 2 t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul 2 |>.sub_const 1)
  have hcomp := (hasDerivAt_expNegInvSqGlueDeriv (2 * t - 1)).comp t harg
  have h := hcomp.const_mul (2 * Real.exp 1)
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · ring

theorem deriv_carmonPsiDeriv (t : ℝ) :
    deriv carmonPsiDeriv t = carmonPsiSecond t :=
  (hasDerivAt_carmonPsiDeriv t).deriv

theorem differentiable_carmonPsiDeriv : Differentiable ℝ carmonPsiDeriv :=
  fun t ↦ (hasDerivAt_carmonPsiDeriv t).differentiableAt

theorem abs_carmonPsiSecond_le_fourHundredThirtyTwo (t : ℝ) :
    |carmonPsiSecond t| ≤ 432 := by
  unfold carmonPsiSecond
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_of_pos (Real.exp_pos 1)]
  have hs := abs_expNegInvSqGlueSecond_le_thirtySix (2 * t - 1)
  calc
    4 * Real.exp 1 * |expNegInvSqGlueSecond (2 * t - 1)| ≤
        4 * 3 * 36 := by gcongr <;> exact Real.exp_one_lt_three.le
    _ = 432 := by norm_num

theorem carmonPsiDeriv_lipschitz :
    LipschitzWith (432 : NNReal) carmonPsiDeriv := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_carmonPsiDeriv
  intro t
  rw [deriv_carmonPsiDeriv, ← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using abs_carmonPsiSecond_le_fourHundredThirtyTwo t

theorem carmonPsiDeriv_abs_sub_le (s t : ℝ) :
    |carmonPsiDeriv s - carmonPsiDeriv t| ≤ 432 * |s - t| := by
  simpa [Real.norm_eq_abs] using carmonPsiDeriv_lipschitz.norm_sub_le s t

theorem abs_carmonPsiDeriv_le_twentyFour (t : ℝ) :
    |carmonPsiDeriv t| ≤ 24 := by
  unfold carmonPsiDeriv
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_pos (Real.exp_pos 1)]
  have h := abs_expNegInvSqGlueDeriv_le_four (2 * t - 1)
  calc
    2 * Real.exp 1 * |expNegInvSqGlueDeriv (2 * t - 1)| ≤
        2 * 3 * 4 := by gcongr <;> exact Real.exp_one_lt_three.le
    _ = 24 := by norm_num

theorem carmonPsi_abs_sub_le (s t : ℝ) :
    |carmonPsi s - carmonPsi t| ≤ 24 * |s - t| := by
  have h : LipschitzWith (24 : NNReal) carmonPsi := by
    apply lipschitzWith_of_nnnorm_deriv_le differentiable_carmonPsi
    intro x
    rw [deriv_carmonPsi, ← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs] using abs_carmonPsiDeriv_le_twentyFour x
  simpa [Real.norm_eq_abs] using h.norm_sub_le s t

def carmonPhiSecond (t : ℝ) : ℝ :=
  -Real.sqrt (Real.exp 1) * t * carmonGaussian t

theorem hasDerivAt_carmonGaussian (t : ℝ) :
    HasDerivAt carmonGaussian (-t * carmonGaussian t) t := by
  unfold carmonGaussian
  have hinner : HasDerivAt (fun s : ℝ ↦ -(1 / 2 : ℝ) * s ^ 2) (-t) t := by
    simpa using ((hasDerivAt_id t).pow 2 |>.const_mul (-(1 / 2 : ℝ)))
  simpa [mul_comm, mul_left_comm, mul_assoc] using hinner.exp

theorem hasDerivAt_carmonPhiDeriv (t : ℝ) :
    HasDerivAt carmonPhiDeriv (carmonPhiSecond t) t := by
  unfold carmonPhiDeriv carmonPhiSecond
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (hasDerivAt_carmonGaussian t).const_mul (Real.sqrt (Real.exp 1))

theorem deriv_carmonPhiDeriv (t : ℝ) :
    deriv carmonPhiDeriv t = carmonPhiSecond t :=
  (hasDerivAt_carmonPhiDeriv t).deriv

theorem differentiable_carmonPhiDeriv : Differentiable ℝ carmonPhiDeriv :=
  fun t ↦ (hasDerivAt_carmonPhiDeriv t).differentiableAt

theorem sqrt_exp_one_le_two : Real.sqrt (Real.exp 1) ≤ 2 := by
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith [Real.exp_one_lt_three]

theorem abs_mul_carmonGaussian_le_two (t : ℝ) :
    |t| * carmonGaussian t ≤ 2 := by
  have hg0 := (carmonGaussian_pos t).le
  have hg1 := carmonGaussian_le_one t
  by_cases ht : |t| ≤ 1
  · nlinarith [abs_nonneg t]
  · have ht1 : 1 ≤ |t| := le_of_not_ge ht
    let a : ℝ := t ^ 2 / 2
    have ha0 : 0 ≤ a := by dsimp [a]; positivity
    have h := Real.pow_div_factorial_le_exp a ha0 1
    norm_num at h
    have hsq : t ^ 2 ≤ 2 * Real.exp a := by
      dsimp [a] at h ⊢
      nlinarith
    have habsq : |t| ≤ t ^ 2 := by
      nlinarith [sq_abs t, abs_nonneg t]
    have hnum : |t| ≤ 2 * Real.exp a := habsq.trans hsq
    have hdiv := (div_le_iff₀ (Real.exp_pos a)).2 hnum
    have hgauss : carmonGaussian t = (Real.exp a)⁻¹ := by
      unfold carmonGaussian
      dsimp [a]
      rw [show -(1 / 2 : ℝ) * t ^ 2 = -(t ^ 2 / 2) by ring,
        Real.exp_neg]
    rw [hgauss]
    simpa [div_eq_mul_inv] using hdiv

theorem abs_carmonPhiSecond_le_four (t : ℝ) :
    |carmonPhiSecond t| ≤ 4 := by
  unfold carmonPhiSecond
  rw [abs_mul, abs_mul, abs_neg,
    abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_pos (carmonGaussian_pos t)]
  have h := abs_mul_carmonGaussian_le_two t
  nlinarith [sqrt_exp_one_le_two, Real.sqrt_nonneg (Real.exp 1)]

theorem carmonPhiDeriv_lipschitz :
    LipschitzWith (4 : NNReal) carmonPhiDeriv := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_carmonPhiDeriv
  intro t
  rw [deriv_carmonPhiDeriv, ← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using abs_carmonPhiSecond_le_four t

theorem carmonPhiDeriv_abs_sub_le (s t : ℝ) :
    |carmonPhiDeriv s - carmonPhiDeriv t| ≤ 4 * |s - t| := by
  simpa [Real.norm_eq_abs] using carmonPhiDeriv_lipschitz.norm_sub_le s t

theorem abs_carmonPhiDeriv_le_two (t : ℝ) :
    |carmonPhiDeriv t| ≤ 2 := by
  unfold carmonPhiDeriv
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_pos (carmonGaussian_pos t)]
  have hg := carmonGaussian_le_one t
  have hg0 := (carmonGaussian_pos t).le
  nlinarith [sqrt_exp_one_le_two, Real.sqrt_nonneg (Real.exp 1)]

theorem carmonPhi_abs_sub_le (s t : ℝ) :
    |carmonPhi s - carmonPhi t| ≤ 2 * |s - t| := by
  have h : LipschitzWith (2 : NNReal) carmonPhi := by
    apply lipschitzWith_of_nnnorm_deriv_le differentiable_carmonPhi
    intro x
    rw [deriv_carmonPhi, ← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs] using abs_carmonPhiDeriv_le_two x
  simpa [Real.norm_eq_abs] using h.norm_sub_le s t

private theorem abs_mul_sub_mul_le (a b c d : ℝ) :
    |a * b - c * d| ≤ |a| * |b - d| + |d| * |a - c| := by
  have h := abs_add_le (a * (b - d)) ((a - c) * d)
  have heq : a * b - c * d = a * (b - d) + (a - c) * d := by ring
  rw [heq]
  calc
    |a * (b - d) + (a - c) * d| ≤
        |a * (b - d)| + |(a - c) * d| := h
    _ = |a| * |b - d| + |d| * |a - c| := by
      rw [abs_mul, abs_mul, mul_comm |d| |a - c|]

theorem abs_carmonPsi_le_three (t : ℝ) : |carmonPsi t| ≤ 3 := by
  rw [abs_of_nonneg (carmonPsi_nonneg t)]
  exact (carmonPsi_le_exp_one t).trans Real.exp_one_lt_three.le

theorem abs_carmonPhi_le_cap (t : ℝ) : |carmonPhi t| ≤ carmonPhiCap := by
  rw [abs_of_nonneg (carmonPhi_nonneg t)]
  exact carmonPhi_le_cap t

def carmonPrevDiff {T : Nat} (x x' : EVec T) (i : Fin T) : ℝ :=
  if hi : i.1 = 0 then 0 else
    |x ⟨i.1 - 1, by omega⟩ - x' ⟨i.1 - 1, by omega⟩|

def carmonNextDiff {T : Nat} (x x' : EVec T) (i : Fin T) : ℝ :=
  if hi : i.1 + 1 < T then
    |x ⟨i.1 + 1, hi⟩ - x' ⟨i.1 + 1, hi⟩|
  else 0

theorem carmonPrevDiff_nonneg {T : Nat} (x x' : EVec T) (i : Fin T) :
    0 ≤ carmonPrevDiff x x' i := by
  unfold carmonPrevDiff
  split <;> positivity

theorem carmonNextDiff_nonneg {T : Nat} (x x' : EVec T) (i : Fin T) :
    0 ≤ carmonNextDiff x x' i := by
  unfold carmonNextDiff
  split <;> positivity

theorem carmonIncoming_abs_sub_le {T : Nat} (x x' : EVec T) (i : Fin T) :
    |carmonIncoming x i - carmonIncoming x' i| ≤
      96 * carmonPrevDiff x x' i + 24 * |x i - x' i| := by
  by_cases hi : i.1 = 0
  · rw [carmonIncoming, dif_pos hi, carmonIncoming, dif_pos hi]
    simp only [carmonPrevDiff, dif_pos hi]
    exact (carmonPhiDeriv_abs_sub_le (x i) (x' i)).trans (by
      nlinarith [abs_nonneg (x i - x' i)])
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    rw [carmonIncoming, dif_neg hi, carmonIncoming, dif_neg hi]
    have hn := abs_mul_sub_mul_le
      (carmonPsi (-x p)) (carmonPhiDeriv (-x i))
      (carmonPsi (-x' p)) (carmonPhiDeriv (-x' i))
    have hp := abs_mul_sub_mul_le
      (carmonPsi (x p)) (carmonPhiDeriv (x i))
      (carmonPsi (x' p)) (carmonPhiDeriv (x' i))
    have hsum := abs_add_le
      (carmonPsi (-x p) * carmonPhiDeriv (-x i) -
        carmonPsi (-x' p) * carmonPhiDeriv (-x' i))
      (carmonPsi (x p) * carmonPhiDeriv (x i) -
        carmonPsi (x' p) * carmonPhiDeriv (x' i))
    have hpsiN := carmonPsi_abs_sub_le (-x p) (-x' p)
    have hpsiP := carmonPsi_abs_sub_le (x p) (x' p)
    have hphiN := carmonPhiDeriv_abs_sub_le (-x i) (-x' i)
    have hphiP := carmonPhiDeriv_abs_sub_le (x i) (x' i)
    have hpsiAbsN := abs_carmonPsi_le_three (-x p)
    have hpsiAbsP := abs_carmonPsi_le_three (x p)
    have hphiAbsN := abs_carmonPhiDeriv_le_two (-x' i)
    have hphiAbsP := abs_carmonPhiDeriv_le_two (x' i)
    have hneg :
        |carmonPsi (-x p) * carmonPhiDeriv (-x i) -
          carmonPsi (-x' p) * carmonPhiDeriv (-x' i)| ≤
          12 * |x i - x' i| + 48 * |x p - x' p| := by
      have hpsiN' : |carmonPsi (-x p) - carmonPsi (-x' p)| ≤
          24 * |x p - x' p| := by
        calc
          _ ≤ 24 * |x' p - x p| := by
            simpa only [neg_sub_neg, abs_neg] using hpsiN
          _ = 24 * |x p - x' p| := by rw [abs_sub_comm]
      have hphiN' : |carmonPhiDeriv (-x i) - carmonPhiDeriv (-x' i)| ≤
          4 * |x i - x' i| := by
        calc
          _ ≤ 4 * |x' i - x i| := by
            simpa only [neg_sub_neg, abs_neg] using hphiN
          _ = 4 * |x i - x' i| := by rw [abs_sub_comm]
      nlinarith [abs_nonneg (carmonPhiDeriv (-x i) - carmonPhiDeriv (-x' i)),
        abs_nonneg (carmonPsi (-x p) - carmonPsi (-x' p))]
    have hpos :
        |carmonPsi (x p) * carmonPhiDeriv (x i) -
          carmonPsi (x' p) * carmonPhiDeriv (x' i)| ≤
          12 * |x i - x' i| + 48 * |x p - x' p| := by
      nlinarith [abs_nonneg (carmonPhiDeriv (x i) - carmonPhiDeriv (x' i)),
        abs_nonneg (carmonPsi (x p) - carmonPsi (x' p))]
    have heq :
        (carmonPsi (-x p) * carmonPhiDeriv (-x i) +
          carmonPsi (x p) * carmonPhiDeriv (x i)) -
        (carmonPsi (-x' p) * carmonPhiDeriv (-x' i) +
          carmonPsi (x' p) * carmonPhiDeriv (x' i)) =
        (carmonPsi (-x p) * carmonPhiDeriv (-x i) -
          carmonPsi (-x' p) * carmonPhiDeriv (-x' i)) +
        (carmonPsi (x p) * carmonPhiDeriv (x i) -
          carmonPsi (x' p) * carmonPhiDeriv (x' i)) := by ring
    rw [heq]
    rw [carmonPrevDiff, dif_neg hi]
    change _ ≤ 96 * |x p - x' p| + 24 * |x i - x' i|
    nlinarith

theorem carmonForward_abs_sub_le {T : Nat} (x x' : EVec T) (i : Fin T) :
    |carmonForward x i - carmonForward x' i| ≤
      864 * carmonPhiCap * |x i - x' i| +
        96 * carmonNextDiff x x' i := by
  by_cases hi : i.1 + 1 < T
  · let n : Fin T := ⟨i.1 + 1, hi⟩
    rw [carmonForward, dif_pos hi, carmonForward, dif_pos hi]
    have hn := abs_mul_sub_mul_le
      (carmonPsiDeriv (-x i)) (carmonPhi (-x n))
      (carmonPsiDeriv (-x' i)) (carmonPhi (-x' n))
    have hp := abs_mul_sub_mul_le
      (carmonPsiDeriv (x i)) (carmonPhi (x n))
      (carmonPsiDeriv (x' i)) (carmonPhi (x' n))
    have hpsiN := carmonPsiDeriv_abs_sub_le (-x i) (-x' i)
    have hpsiP := carmonPsiDeriv_abs_sub_le (x i) (x' i)
    have hphiN := carmonPhi_abs_sub_le (-x n) (-x' n)
    have hphiP := carmonPhi_abs_sub_le (x n) (x' n)
    have hpsiAbsN := abs_carmonPsiDeriv_le_twentyFour (-x i)
    have hpsiAbsP := abs_carmonPsiDeriv_le_twentyFour (x i)
    have hphiAbsN := abs_carmonPhi_le_cap (-x' n)
    have hphiAbsP := abs_carmonPhi_le_cap (x' n)
    have hpsiN' : |carmonPsiDeriv (-x i) - carmonPsiDeriv (-x' i)| ≤
        432 * |x i - x' i| := by
      calc
        _ ≤ 432 * |x' i - x i| := by
          simpa only [neg_sub_neg, abs_neg] using hpsiN
        _ = 432 * |x i - x' i| := by rw [abs_sub_comm]
    have hphiN' : |carmonPhi (-x n) - carmonPhi (-x' n)| ≤
        2 * |x n - x' n| := by
      calc
        _ ≤ 2 * |x' n - x n| := by
          simpa only [neg_sub_neg, abs_neg] using hphiN
        _ = 2 * |x n - x' n| := by rw [abs_sub_comm]
    have hneg :
        |carmonPsiDeriv (-x i) * carmonPhi (-x n) -
          carmonPsiDeriv (-x' i) * carmonPhi (-x' n)| ≤
          432 * carmonPhiCap * |x i - x' i| +
            48 * |x n - x' n| := by
      nlinarith [carmonPhiCap_nonneg,
        abs_nonneg (carmonPhi (-x n) - carmonPhi (-x' n)),
        abs_nonneg (carmonPsiDeriv (-x i) - carmonPsiDeriv (-x' i))]
    have hpos :
        |carmonPsiDeriv (x i) * carmonPhi (x n) -
          carmonPsiDeriv (x' i) * carmonPhi (x' n)| ≤
          432 * carmonPhiCap * |x i - x' i| +
            48 * |x n - x' n| := by
      nlinarith [carmonPhiCap_nonneg,
        abs_nonneg (carmonPhi (x n) - carmonPhi (x' n)),
        abs_nonneg (carmonPsiDeriv (x i) - carmonPsiDeriv (x' i))]
    have hsum := abs_add_le
      (carmonPsiDeriv (-x i) * carmonPhi (-x n) -
        carmonPsiDeriv (-x' i) * carmonPhi (-x' n))
      (carmonPsiDeriv (x i) * carmonPhi (x n) -
        carmonPsiDeriv (x' i) * carmonPhi (x' n))
    have heq :
        (carmonPsiDeriv (-x i) * carmonPhi (-x n) +
          carmonPsiDeriv (x i) * carmonPhi (x n)) -
        (carmonPsiDeriv (-x' i) * carmonPhi (-x' n) +
          carmonPsiDeriv (x' i) * carmonPhi (x' n)) =
        (carmonPsiDeriv (-x i) * carmonPhi (-x n) -
          carmonPsiDeriv (-x' i) * carmonPhi (-x' n)) +
        (carmonPsiDeriv (x i) * carmonPhi (x n) -
          carmonPsiDeriv (x' i) * carmonPhi (x' n)) := by ring
    rw [heq, carmonNextDiff, dif_pos hi]
    change _ ≤ 864 * carmonPhiCap * |x i - x' i| + 96 * |x n - x' n|
    nlinarith
  · simp [carmonForward, hi, carmonNextDiff]
    nlinarith [carmonPhiCap_nonneg, abs_nonneg (x i - x' i)]

def carmonSmoothC : ℝ := 100 + 900 * carmonPhiCap

theorem carmonSmoothC_nonneg : 0 ≤ carmonSmoothC := by
  unfold carmonSmoothC
  nlinarith [carmonPhiCap_nonneg]

theorem carmonGradient_component_abs_sub_le {T : Nat}
    (x x' : EVec T) (i : Fin T) :
    |carmonGradient T x i - carmonGradient T x' i| ≤
      carmonSmoothC *
        (carmonPrevDiff x x' i + |x i - x' i| + carmonNextDiff x x' i) := by
  have hin := carmonIncoming_abs_sub_le x x' i
  have hfor := carmonForward_abs_sub_le x x' i
  have htri := abs_add_le
    (carmonIncoming x i - carmonIncoming x' i)
    (carmonForward x i - carmonForward x' i)
  have heq :
      carmonGradient T x i - carmonGradient T x' i =
        -((carmonIncoming x i - carmonIncoming x' i) +
          (carmonForward x i - carmonForward x' i)) := by
    unfold carmonGradient
    ring
  rw [heq, abs_neg]
  have hp0 := carmonPrevDiff_nonneg x x' i
  have hn0 := carmonNextDiff_nonneg x x' i
  have hc0 := carmonPhiCap_nonneg
  unfold carmonSmoothC
  nlinarith [abs_nonneg (x i - x' i)]

private theorem sum_prevShift_sq_le {T : Nat} (d : EVec T) :
    (∑ i : Fin T, (if hi : i.1 = 0 then 0 else
      d ⟨i.1 - 1, by omega⟩) ^ 2) ≤ ∑ i : Fin T, d i ^ 2 := by
  cases T with
  | zero => simp
  | succ n =>
      rw [Fin.sum_univ_succ]
      simp
      rw [Fin.sum_univ_castSucc]
      exact le_add_of_nonneg_right (sq_nonneg (d (Fin.last n)))

private theorem sum_nextShift_sq_le {T : Nat} (d : EVec T) :
    (∑ i : Fin T, (if hi : i.1 + 1 < T then
      d ⟨i.1 + 1, hi⟩ else 0) ^ 2) ≤ ∑ i : Fin T, d i ^ 2 := by
  cases T with
  | zero => simp
  | succ n =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Nat.add_lt_add_iff_right, Fin.is_lt, dite_true,
        Fin.val_last, lt_self_iff_false, dite_false, zero_pow (by norm_num : (2 : Nat) ≠ 0),
        add_zero]
      rw [Fin.sum_univ_succ]
      exact le_add_of_nonneg_left (sq_nonneg _)

theorem sum_carmonPrevDiff_sq_le {T : Nat} (x x' : EVec T) :
    (∑ i : Fin T, carmonPrevDiff x x' i ^ 2) ≤ vecSq (x - x') := by
  have h := sum_prevShift_sq_le (fun i : Fin T ↦ |x i - x' i|)
  unfold vecSq carmonPrevDiff
  simpa only [Pi.sub_apply, sq_abs] using h

theorem sum_carmonNextDiff_sq_le {T : Nat} (x x' : EVec T) :
    (∑ i : Fin T, carmonNextDiff x x' i ^ 2) ≤ vecSq (x - x') := by
  have h := sum_nextShift_sq_le (fun i : Fin T ↦ |x i - x' i|)
  unfold vecSq carmonNextDiff
  simpa only [Pi.sub_apply, sq_abs] using h

def carmonSmoothL : ℝ := 3 * carmonSmoothC

theorem carmonSmoothL_nonneg : 0 ≤ carmonSmoothL := by
  unfold carmonSmoothL
  exact mul_nonneg (by norm_num) carmonSmoothC_nonneg

/-- Carmon fact (C1): the outer gradient has a global Lipschitz constant that
does not depend on the chain length. -/
theorem carmonGradient_lipschitz_sq (T : Nat) (x x' : EVec T) :
    vecSq (carmonGradient T x - carmonGradient T x') ≤
      carmonSmoothL ^ 2 * vecSq (x - x') := by
  have hpoint (i : Fin T) :
      (carmonGradient T x i - carmonGradient T x' i) ^ 2 ≤
        3 * carmonSmoothC ^ 2 *
          (carmonPrevDiff x x' i ^ 2 + |x i - x' i| ^ 2 +
            carmonNextDiff x x' i ^ 2) := by
    have habs := carmonGradient_component_abs_sub_le x x' i
    let p := carmonPrevDiff x x' i
    let c := |x i - x' i|
    let n := carmonNextDiff x x' i
    have hp0 : 0 ≤ p := carmonPrevDiff_nonneg x x' i
    have hc0 : 0 ≤ c := abs_nonneg _
    have hn0 : 0 ≤ n := carmonNextDiff_nonneg x x' i
    have hsum0 : 0 ≤ p + c + n := by positivity
    have hright0 : 0 ≤ carmonSmoothC * (p + c + n) :=
      mul_nonneg carmonSmoothC_nonneg hsum0
    have hsquare :
        (carmonGradient T x i - carmonGradient T x' i) ^ 2 ≤
          (carmonSmoothC * (p + c + n)) ^ 2 := by
      rw [← sq_abs (carmonGradient T x i - carmonGradient T x' i)]
      nlinarith [mul_nonneg
        (sub_nonneg.mpr habs)
        (add_nonneg hright0 (abs_nonneg
          (carmonGradient T x i - carmonGradient T x' i)))]
    have hthree : (p + c + n) ^ 2 ≤ 3 * (p ^ 2 + c ^ 2 + n ^ 2) := by
      nlinarith [sq_nonneg (p - c), sq_nonneg (p - n), sq_nonneg (c - n)]
    change (carmonGradient T x i - carmonGradient T x' i) ^ 2 ≤
      3 * carmonSmoothC ^ 2 * (p ^ 2 + c ^ 2 + n ^ 2)
    calc
      _ ≤ (carmonSmoothC * (p + c + n)) ^ 2 := hsquare
      _ = carmonSmoothC ^ 2 * (p + c + n) ^ 2 := by ring
      _ ≤ carmonSmoothC ^ 2 * (3 * (p ^ 2 + c ^ 2 + n ^ 2)) :=
        mul_le_mul_of_nonneg_left hthree (sq_nonneg carmonSmoothC)
      _ = 3 * carmonSmoothC ^ 2 * (p ^ 2 + c ^ 2 + n ^ 2) := by ring
  have hprev := sum_carmonPrevDiff_sq_le x x'
  have hnext := sum_carmonNextDiff_sq_le x x'
  have hcur : (∑ i : Fin T, |x i - x' i| ^ 2) = vecSq (x - x') := by
    unfold vecSq
    simp only [Pi.sub_apply, sq_abs]
  have hneighbors :
      (∑ i : Fin T,
        (carmonPrevDiff x x' i ^ 2 + |x i - x' i| ^ 2 +
          carmonNextDiff x x' i ^ 2)) ≤
        3 * vecSq (x - x') := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hcur]
    nlinarith
  unfold vecSq
  calc
    (∑ i : Fin T,
        (carmonGradient T x - carmonGradient T x') i ^ 2) =
        ∑ i : Fin T, (carmonGradient T x i - carmonGradient T x' i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rfl
    _ ≤ ∑ i : Fin T, 3 * carmonSmoothC ^ 2 *
        (carmonPrevDiff x x' i ^ 2 + |x i - x' i| ^ 2 +
          carmonNextDiff x x' i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact hpoint i
    _ = 3 * carmonSmoothC ^ 2 *
        (∑ i : Fin T,
          (carmonPrevDiff x x' i ^ 2 + |x i - x' i| ^ 2 +
            carmonNextDiff x x' i ^ 2)) := by
      rw [Finset.mul_sum]
    _ ≤ 3 * carmonSmoothC ^ 2 * (3 * ∑ i : Fin T, (x - x') i ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [vecSq] using hneighbors
      · positivity
    _ = carmonSmoothL ^ 2 * ∑ i : Fin T, (x - x') i ^ 2 := by
      unfold carmonSmoothL
      ring

end

end NCPLVerification
