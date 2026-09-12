import NCC.Construction.Scalar.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! Sharp numerical estimates for the exact current scalar construction. -/

namespace NCC.Construction

noncomputable section

open Set Filter
open scoped Topology

private def zArg (t : ℝ) : ℝ := (2 * t - 1) / (2 * t * (1 - t))
private def sigmaArg (t : ℝ) : ℝ := 1 / (2 * t * (1 - t)) - 1
private def psiArg (t : ℝ) : ℝ := sigmaArg t * (sigmaArg t + 1)
private def logisticHalf (z : ℝ) : ℝ := (1 + Real.exp (-2 * z))⁻¹

private theorem argument_den_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    0 < 2 * t * (1 - t) := by positivity

private theorem sigmaArg_ge_one {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    1 ≤ sigmaArg t := by
  have hd := argument_den_pos h0 h1
  have hb : 2 * (2 * t * (1 - t)) ≤ 1 := by nlinarith [sq_nonneg (2 * t - 1)]
  have h := (le_div_iff₀ hd).mpr hb
  dsimp [sigmaArg]
  linarith

private theorem sigmaArg_sq {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    sigmaArg t ^ 2 = 1 + zArg t ^ 2 := by
  dsimp [sigmaArg, zArg]
  field_simp [h0.ne', (sub_pos.mpr h1).ne']
  ring

private theorem hasDerivAt_zArg {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt zArg (2 * psiArg t) t := by
  have hnum := ((hasDerivAt_id t).const_mul 2).sub_const 1
  have hden := ((hasDerivAt_id t).const_mul 2).mul ((hasDerivAt_id t).const_sub 1)
  convert! hnum.div hden (argument_den_pos h0 h1).ne' using 1
  dsimp [psiArg, sigmaArg]
  field_simp [h0.ne', (sub_pos.mpr h1).ne']
  ring

private theorem hasDerivAt_sigmaArg {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt sigmaArg (2 * zArg t * (sigmaArg t + 1)) t := by
  have hden := ((hasDerivAt_id t).const_mul 2).mul ((hasDerivAt_id t).const_sub 1)
  convert! ((hasDerivAt_const t 1).div hden (argument_den_pos h0 h1).ne').sub_const 1
    using 1
  dsimp [sigmaArg, zArg]
  field_simp [h0.ne', (sub_pos.mpr h1).ne']
  ring

private theorem hasDerivAt_psiArg {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt psiArg (2 * zArg t * (sigmaArg t + 1) * (2 * sigmaArg t + 1)) t := by
  convert! (hasDerivAt_sigmaArg h0 h1).mul ((hasDerivAt_sigmaArg h0 h1).add_const 1)
    using 1
  ring

private theorem step_eq_logisticHalf {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    step t = logisticHalf (zArg t) := by
  rw [step_eq_exp_ratio h0 h1]
  have hz : -2 * zArg t = -1 / (1 - t) - (-1 / t) := by
    dsimp [zArg]
    field_simp [h0.ne', (sub_pos.mpr h1).ne']
    ring
  rw [logisticHalf, hz, Real.exp_sub]
  have hsum : Real.exp (-1 / t) + Real.exp (-1 / (1 - t)) ≠ 0 := by positivity
  field_simp [Real.exp_ne_zero, hsum]

private theorem hasDerivAt_logisticHalf (z : ℝ) :
    HasDerivAt logisticHalf (1 / (2 * Real.cosh z ^ 2)) z := by
  have he : 1 + Real.exp (-2 * z) ≠ 0 := by positivity
  have h := ((((hasDerivAt_id z).const_mul (-2)).exp).const_add 1).inv he
  convert! h using 1
  simp only [id_eq, mul_one]
  rw [Real.cosh_eq, show -2 * z = -(z + z) by ring]
  simp only [Real.exp_neg, Real.exp_add]
  have hp := Real.exp_pos z
  field_simp [Real.exp_ne_zero, (show Real.exp z + (Real.exp z)⁻¹ ≠ 0 by positivity)]

private theorem hasDerivAt_step_inside {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt step (psiArg t / Real.cosh (zArg t) ^ 2) t := by
  have h := (hasDerivAt_logisticHalf (zArg t)).comp t (hasDerivAt_zArg h0 h1)
  have heq : step =ᶠ[𝓝 t] fun u ↦ logisticHalf (zArg u) := by
    filter_upwards [lt_mem_nhds h0, gt_mem_nhds h1] with u hu0 hu1
    exact step_eq_logisticHalf hu0 hu1
  convert! h.congr_of_eventuallyEq heq using 1
  ring

/-- A finite partial sum of the proved `cosh` power series gives the
quartic lower bound used in the manuscript. -/
theorem cosh_sq_ge_quartic (z : ℝ) :
    1 + z ^ 2 + z ^ 4 / 3 ≤ Real.cosh z ^ 2 := by
  have hs := sum_le_hasSum (Finset.range 3)
    (fun n (_ : n ∉ Finset.range 3) ↦
      show 0 ≤ (2 * z) ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) by
        rw [mul_comm 2 n, pow_mul]
        positivity) (Real.hasSum_cosh (2 * z))
  norm_num [Finset.sum_range_succ] at hs
  rw [Real.cosh_two_mul] at hs
  nlinarith [Real.cosh_sq_sub_sinh_sq z]

private theorem deriv_step_inside_le_two {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    deriv step t ≤ 2 := by
  rw [(hasDerivAt_step_inside h0 h1).deriv]
  apply (div_le_iff₀ (sq_pos_of_pos (Real.cosh_pos _))).mpr
  have hs := sigmaArg_ge_one h0 h1
  have hsq := sigmaArg_sq h0 h1
  have hc := cosh_sq_ge_quartic (zArg t)
  dsimp [psiArg]
  nlinarith [sq_nonneg (zArg t ^ 2)]

private theorem deriv_step_eq_zero_left {t : ℝ} (ht : t ≤ 0) : deriv step t = 0 := by
  refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic 0 t ht)
  exact (hasDerivWithinAt_const t (Iic 0) 0).congr_of_mem (fun _ hx ↦ step_eq_zero hx) ht

private theorem deriv_step_eq_zero_right {t : ℝ} (ht : 1 ≤ t) : deriv step t = 0 := by
  refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Ici 1 t ht)
  exact (hasDerivWithinAt_const t (Ici 1) 1).congr_of_mem (fun _ hx ↦ step_eq_one hx) ht

theorem deriv_step_mem (t : ℝ) : deriv step t ∈ Icc (0 : ℝ) 2 := by
  refine ⟨step_monotone.deriv_nonneg, ?_⟩
  by_cases h0 : t ≤ 0
  · rw [deriv_step_eq_zero_left h0]
    norm_num
  by_cases h1 : 1 ≤ t
  · rw [deriv_step_eq_zero_right h1]
    norm_num
  exact deriv_step_inside_le_two (lt_of_not_ge h0) (lt_of_not_ge h1)

theorem p_second_derivative_mem (t : ℝ) : deriv (deriv p) t ∈ Icc (0 : ℝ) 2 := by
  rw [show deriv p = step from funext deriv_p]
  exact deriv_step_mem t

private theorem psi_sq_le_cosh {sigma z : ℝ} (hsq : sigma ^ 2 = 1 + z ^ 2) :
    (sigma * (sigma + 1)) ^ 2 ≤ 6 * Real.cosh z ^ 2 := by
  have hpoly : (sigma * (sigma + 1)) ^ 2 ≤ 2 * (sigma ^ 4 + sigma ^ 2 + 1) := by
    nlinarith [sq_nonneg (sigma * (sigma - 1))]
  have hfour : sigma ^ 4 = (1 + z ^ 2) ^ 2 := by
    calc
      sigma ^ 4 = (sigma ^ 2) ^ 2 := by ring
      _ = (1 + z ^ 2) ^ 2 := by rw [hsq]
  nlinarith [cosh_sq_ge_quartic z]

private theorem hyperbolic_bracket_abs_le {sigma z : ℝ} (hs : 1 ≤ sigma)
    (hsq : sigma ^ 2 = 1 + z ^ 2) :
    |z * (2 * sigma + 1) / sigma - 2 * (sigma * (sigma + 1)) * Real.tanh z| ≤
      2 * (sigma * (sigma + 1)) := by
  have hspos : 0 < sigma := by linarith
  have hpsi : 0 ≤ sigma * (sigma + 1) := by positivity
  have hz : |z| ≤ sigma := by
    apply (sq_le_sq₀ (abs_nonneg z) hspos.le).mp
    rw [sq_abs]
    linarith
  have ha : |z * (2 * sigma + 1) / sigma| ≤ 2 * (sigma * (sigma + 1)) := by
    rw [abs_div, abs_mul, abs_of_pos hspos,
      abs_of_pos (show 0 < 2 * sigma + 1 by linarith)]
    calc
      |z| * (2 * sigma + 1) / sigma ≤ 2 * sigma + 1 := by
        apply (div_le_iff₀ hspos).mpr
        nlinarith [mul_le_mul_of_nonneg_right hz (show 0 ≤ 2 * sigma + 1 by linarith)]
      _ ≤ 2 * (sigma * (sigma + 1)) := by nlinarith
  have hb : |2 * (sigma * (sigma + 1)) * Real.tanh z| ≤
      2 * (sigma * (sigma + 1)) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * (sigma * (sigma + 1)))]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_tanh_lt_one z).le
  obtain ⟨halo, hahi⟩ := abs_le.mp ha
  obtain ⟨hblo, hbhi⟩ := abs_le.mp hb
  by_cases hz0 : 0 ≤ z
  · have ha0 : 0 ≤ z * (2 * sigma + 1) / sigma := by positivity
    have htan : 0 ≤ Real.tanh z := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.mpr hz0) (Real.cosh_pos _).le
    have hb0 : 0 ≤ 2 * (sigma * (sigma + 1)) * Real.tanh z := by positivity
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · have hz0' : z ≤ 0 := (lt_of_not_ge hz0).le
    have ha0 : z * (2 * sigma + 1) / sigma ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hz0' (by positivity)) hspos.le
    have htan : Real.tanh z ≤ 0 := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonpos_of_nonpos_of_nonneg (Real.sinh_nonpos_iff.mpr hz0') (Real.cosh_pos _).le
    have hb0 : 2 * (sigma * (sigma + 1)) * Real.tanh z ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) htan
    exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem hasDerivAt_step_deriv_inside {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    HasDerivAt (deriv step)
      ((2 * psiArg t / Real.cosh (zArg t) ^ 2) *
        (zArg t * (2 * sigmaArg t + 1) / sigmaArg t -
          2 * psiArg t * Real.tanh (zArg t))) t := by
  have h := (hasDerivAt_psiArg h0 h1).div
    ((hasDerivAt_zArg h0 h1).cosh.pow 2) (pow_ne_zero 2 (Real.cosh_pos _).ne')
  have heq : deriv step =ᶠ[𝓝 t] fun u ↦ psiArg u / Real.cosh (zArg u) ^ 2 := by
    filter_upwards [lt_mem_nhds h0, gt_mem_nhds h1] with u hu0 hu1
    exact (hasDerivAt_step_inside hu0 hu1).deriv
  convert! h.congr_of_eventuallyEq heq using 1
  rw [Real.tanh_eq_sinh_div_cosh]
  have hs : sigmaArg t ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (sigmaArg_ge_one h0 h1))
  simp only [psiArg, Pi.pow_apply]
  field_simp [hs, (Real.cosh_pos (zArg t)).ne']
  ring

private theorem step_second_derivative_abs_le_inside {t : ℝ} (h0 : 0 < t) (h1 : t < 1) :
    |deriv (deriv step) t| ≤ 24 := by
  rw [(hasDerivAt_step_deriv_inside h0 h1).deriv, abs_mul]
  have hs := sigmaArg_ge_one h0 h1
  have hsq := sigmaArg_sq h0 h1
  have hpsi : 0 ≤ psiArg t := by dsimp [psiArg]; positivity
  have hcosh : 0 < Real.cosh (zArg t) ^ 2 := sq_pos_of_pos (Real.cosh_pos _)
  rw [abs_of_nonneg (show 0 ≤ 2 * psiArg t / Real.cosh (zArg t) ^ 2 by positivity)]
  calc
    _ ≤ (2 * psiArg t / Real.cosh (zArg t) ^ 2) * (2 * psiArg t) :=
      mul_le_mul_of_nonneg_left (hyperbolic_bracket_abs_le hs hsq) (by positivity)
    _ = 4 * psiArg t ^ 2 / Real.cosh (zArg t) ^ 2 := by ring
    _ ≤ 24 := by
      apply (div_le_iff₀ hcosh).mpr
      have hb := psi_sq_le_cosh hsq
      dsimp [psiArg]
      nlinarith

theorem step_second_derivative_abs_le (t : ℝ) : |deriv (deriv step) t| ≤ 24 := by
  by_cases h0 : t ≤ 0
  · have hz : deriv (deriv step) t = 0 := by
      refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic 0 t h0)
      exact (hasDerivWithinAt_const t (Iic 0) 0).congr_of_mem
        (fun _ hx ↦ deriv_step_eq_zero_left hx) h0
    rw [hz]
    norm_num
  by_cases h1 : 1 ≤ t
  · have hz : deriv (deriv step) t = 0 := by
      refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Ici 1 t h1)
      exact (hasDerivWithinAt_const t (Ici 1) 0).congr_of_mem
        (fun _ hx ↦ deriv_step_eq_zero_right hx) h1
    rw [hz]
    norm_num
  exact step_second_derivative_abs_le_inside (lt_of_not_ge h0) (lt_of_not_ge h1)

theorem p_third_derivative_abs_le (t : ℝ) : |deriv (deriv (deriv p)) t| ≤ 24 := by
  rw [show deriv p = step from funext deriv_p]
  exact step_second_derivative_abs_le t

private theorem hasDerivAt_step (t : ℝ) : HasDerivAt step (deriv step t) t :=
  ((step_contDiff (k := 1)).differentiable (by norm_num) t).hasDerivAt

private theorem hasDerivAt_step_deriv (t : ℝ) :
    HasDerivAt (deriv step) (deriv (deriv step) t) t :=
  ((step_contDiff (k := 2)).differentiable_deriv_two t).hasDerivAt

theorem hasDerivAt_q (t : ℝ) :
    HasDerivAt q ((5 / 4) * deriv step ((5 * t - 1) / 4)) t := by
  rw [show q = fun u ↦ step ((5 * u - 1) / 4) from funext q_eq_step]
  convert! (hasDerivAt_step ((5 * t - 1) / 4)).comp t
    ((((hasDerivAt_id t).const_mul 5).sub_const 1).div_const 4) using 1
  ring

theorem deriv_q (t : ℝ) : deriv q t = (5 / 4) * deriv step ((5 * t - 1) / 4) :=
  (hasDerivAt_q t).deriv

theorem q_derivative_mem (t : ℝ) : deriv q t ∈ Icc (0 : ℝ) (5 / 2) := by
  rw [deriv_q]
  obtain ⟨hlo, hhi⟩ := deriv_step_mem ((5 * t - 1) / 4)
  constructor <;> linarith

theorem hasDerivAt_q_deriv (t : ℝ) :
    HasDerivAt (deriv q) ((25 / 16) * deriv (deriv step) ((5 * t - 1) / 4)) t := by
  rw [show deriv q = fun u ↦ (5 / 4) * deriv step ((5 * u - 1) / 4) from funext deriv_q]
  convert! ((hasDerivAt_step_deriv ((5 * t - 1) / 4)).comp t
    ((((hasDerivAt_id t).const_mul 5).sub_const 1).div_const 4)).const_mul (5 / 4) using 1
  ring

theorem q_second_derivative_abs_le (t : ℝ) : |deriv (deriv q) t| ≤ 75 / 2 := by
  rw [(hasDerivAt_q_deriv t).deriv, abs_mul]
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 25 / 16)]
  linarith [step_second_derivative_abs_le ((5 * t - 1) / 4)]

theorem hasDerivAt_identityExtension_deriv (radius t : ℝ) :
    HasDerivAt (deriv (identityExtension radius))
      (deriv step (t + (radius + 1)) - deriv step (t - radius)) t := by
  rw [show deriv (identityExtension radius) =
      fun u ↦ step (u + (radius + 1)) - step (u - radius) from
    funext (deriv_identityExtension radius)]
  convert! ((hasDerivAt_step (t + (radius + 1))).comp t
    ((hasDerivAt_id t).add_const (radius + 1))).sub
      ((hasDerivAt_step (t - radius)).comp t ((hasDerivAt_id t).sub_const radius)) using 1
  ring

theorem identityExtension_second_derivative_abs_le (radius t : ℝ) :
    |deriv (deriv (identityExtension radius)) t| ≤ 2 := by
  rw [(hasDerivAt_identityExtension_deriv radius t).deriv]
  obtain ⟨hlo₁, hhi₁⟩ := deriv_step_mem (t + (radius + 1))
  obtain ⟨hlo₂, hhi₂⟩ := deriv_step_mem (t - radius)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem e_s_second_derivative_abs_le (t : ℝ) : |deriv (deriv e_s) t| ≤ 2 := by
  rw [e_s_eq_identityExtension]
  exact identityExtension_second_derivative_abs_le 2 t

theorem e_nu_second_derivative_abs_le (t : ℝ) : |deriv (deriv e_nu) t| ≤ 2 := by
  rw [e_nu_eq_identityExtension]
  exact identityExtension_second_derivative_abs_le 21 t

end

end NCC.Construction
