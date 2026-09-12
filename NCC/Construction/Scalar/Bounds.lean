import NCC.Construction.Scalar

/-! Consequences of the exact scalar formulas: bounded extensions, endpoint
flatness, compact derivative support, and bounded higher derivatives. -/

namespace NCC.Construction

noncomputable section

open Set

theorem identityExtension_monotone {radius : ℝ} (hr : 0 ≤ radius) :
    Monotone (identityExtension radius) :=
  monotone_of_deriv_nonneg
    (fun t ↦ (hasDerivAt_identityExtension radius t).differentiableAt)
    (fun t ↦ (deriv_identityExtension_mem hr t).1)

theorem identityExtension_abs_le {radius : ℝ} (hr : 0 ≤ radius) (t : ℝ) :
    |identityExtension radius t| ≤ radius + 1 / 2 := by
  apply abs_le.mpr
  constructor
  · by_cases ht : t ≤ -(radius + 1)
    · rw [identityExtension_eq_left hr ht]
    · have h := identityExtension_monotone hr (le_of_not_ge ht)
      rw [identityExtension_eq_left hr (le_refl (-(radius + 1)))] at h
      exact h
  · by_cases ht : radius + 1 ≤ t
    · rw [identityExtension_eq_right hr ht]
    · have h := identityExtension_monotone hr (le_of_not_ge ht)
      rw [identityExtension_eq_right hr (le_refl (radius + 1))] at h
      exact h

theorem deriv_identityExtension_eq_one {radius t : ℝ}
    (hlo : -radius ≤ t) (hhi : t ≤ radius) :
    deriv (identityExtension radius) t = 1 := by
  rw [deriv_identityExtension, step_eq_one (by linarith : 1 ≤ t + (radius + 1)),
    step_eq_zero (by linarith : t - radius ≤ 0)]
  ring

theorem deriv_identityExtension_eq_zero_left {radius t : ℝ}
    (hr : 0 ≤ radius) (ht : t ≤ -(radius + 1)) :
    deriv (identityExtension radius) t = 0 := by
  rw [deriv_identityExtension, step_eq_zero (by linarith : t + (radius + 1) ≤ 0),
    step_eq_zero (by linarith : t - radius ≤ 0)]
  ring

theorem deriv_identityExtension_eq_zero_right {radius t : ℝ}
    (hr : 0 ≤ radius) (ht : radius + 1 ≤ t) :
    deriv (identityExtension radius) t = 0 := by
  rw [deriv_identityExtension, step_eq_one (by linarith : 1 ≤ t + (radius + 1)),
    step_eq_one (by linarith : 1 ≤ t - radius)]
  ring

theorem e_s_contDiff : ContDiff ℝ (⊤ : ℕ∞) e_s := by
  rw [e_s_eq_identityExtension]
  exact identityExtension_contDiff 2

theorem e_nu_contDiff : ContDiff ℝ (⊤ : ℕ∞) e_nu := by
  rw [e_nu_eq_identityExtension]
  exact identityExtension_contDiff 21

theorem e_s_abs_le (t : ℝ) : |e_s t| ≤ 5 / 2 := by
  rw [e_s_eq_identityExtension]
  convert identityExtension_abs_le (by norm_num : (0 : ℝ) ≤ 2) t using 1
  norm_num

theorem e_nu_abs_le (t : ℝ) : |e_nu t| ≤ 43 / 2 := by
  rw [e_nu_eq_identityExtension]
  convert identityExtension_abs_le (by norm_num : (0 : ℝ) ≤ 21) t using 1
  norm_num

theorem deriv_e_s_mem (t : ℝ) : deriv e_s t ∈ Icc (0 : ℝ) 1 := by
  rw [e_s_eq_identityExtension]
  exact deriv_identityExtension_mem (by norm_num) t

theorem deriv_e_nu_mem (t : ℝ) : deriv e_nu t ∈ Icc (0 : ℝ) 1 := by
  rw [e_nu_eq_identityExtension]
  exact deriv_identityExtension_mem (by norm_num) t

theorem deriv_e_s_eq_one {t : ℝ} (ht : |t| ≤ 2) : deriv e_s t = 1 := by
  rw [e_s_eq_identityExtension]
  exact deriv_identityExtension_eq_one (abs_le.mp ht).1 (abs_le.mp ht).2

theorem deriv_e_nu_eq_one {t : ℝ} (ht : |t| ≤ 21) : deriv e_nu t = 1 := by
  rw [e_nu_eq_identityExtension]
  exact deriv_identityExtension_eq_one (abs_le.mp ht).1 (abs_le.mp ht).2

theorem deriv_q_eq_zero_left {t : ℝ} (ht : t ≤ 1 / 5) : deriv q t = 0 := by
  refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Iic (1 / 5) t ht)
  refine (hasDerivWithinAt_const t (Iic (1 / 5)) 0).congr_of_mem (fun x hx ↦ ?_) ht
  exact q_eq_zero hx

theorem deriv_q_eq_zero_right {t : ℝ} (ht : 1 ≤ t) : deriv q t = 0 := by
  refine HasDerivWithinAt.deriv_eq_zero ?_ (uniqueDiffOn_Ici 1 t ht)
  refine (hasDerivWithinAt_const t (Ici 1) 1).congr_of_mem (fun x hx ↦ ?_) ht
  exact q_eq_one hx

/-- A proved analytic helper for smooth functions with constant tails. -/
theorem iteratedDeriv_eq_zero_of_constant_tails
    {f : ℝ → ℝ} {a b left right : ℝ}
    (hleft : ∀ t, t ≤ a → f t = left)
    (hright : ∀ t, b ≤ t → f t = right)
    {k : ℕ} (hk : 0 < k) {t : ℝ} (ht : t ∉ Icc a b) :
    iteratedDeriv k f t = 0 := by
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · have heq : EqOn f (fun _ ↦ left) (Iio a) := fun x hx ↦ hleft x hx.le
    have h := (heq.iteratedDeriv_of_isOpen isOpen_Iio k) ht
    simpa only [iteratedDeriv_const, hk.ne', ↓reduceIte] using h
  · have heq : EqOn f (fun _ ↦ right) (Ioi b) := fun x hx ↦ hright x hx.le
    have h := (heq.iteratedDeriv_of_isOpen isOpen_Ioi k) ht
    simpa only [iteratedDeriv_const, hk.ne', ↓reduceIte] using h

theorem iteratedDeriv_hasCompactSupport_of_constant_tails
    {f : ℝ → ℝ} {a b left right : ℝ}
    (hleft : ∀ t, t ≤ a → f t = left)
    (hright : ∀ t, b ≤ t → f t = right)
    {k : ℕ} (hk : 0 < k) : HasCompactSupport (iteratedDeriv k f) := by
  exact HasCompactSupport.intro' isCompact_Icc isClosed_Icc
    (fun t ht ↦ iteratedDeriv_eq_zero_of_constant_tails hleft hright hk ht)

theorem iteratedDeriv_bounded_of_constant_tails
    {f : ℝ → ℝ} {a b left right : ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hleft : ∀ t, t ≤ a → f t = left)
    (hright : ∀ t, b ≤ t → f t = right)
    {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv k f t| ≤ C := by
  have hcont : Continuous (fun t ↦ |iteratedDeriv k f t|) :=
    ((hf.of_le (WithTop.coe_le_coe.mpr le_top)).continuous_iteratedDeriv' k).abs
  obtain ⟨C, hC⟩ := bddAbove_def.mp (isCompact_Icc.bddAbove_image hcont.continuousOn)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Icc a b
  · exact (hC _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  · rw [iteratedDeriv_eq_zero_of_constant_tails hleft hright hk ht, abs_zero]
    exact le_max_right _ _

theorem q_iteratedDeriv_bounded {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv k q t| ≤ C :=
  iteratedDeriv_bounded_of_constant_tails q_contDiff
    (fun _ ht ↦ q_eq_zero ht) (fun _ ht ↦ q_eq_one ht) hk

theorem identityExtension_iteratedDeriv_bounded {radius : ℝ} (hr : 0 ≤ radius)
    {k : ℕ} (hk : 0 < k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |iteratedDeriv k (identityExtension radius) t| ≤ C :=
  iteratedDeriv_bounded_of_constant_tails (identityExtension_contDiff radius)
    (fun _ ht ↦ identityExtension_eq_left hr ht)
    (fun _ ht ↦ identityExtension_eq_right hr ht) hk

theorem q_deriv_hasCompactSupport : HasCompactSupport (deriv q) := by
  simpa using iteratedDeriv_hasCompactSupport_of_constant_tails
    (fun _ ht ↦ q_eq_zero ht) (fun _ ht ↦ q_eq_one ht) (by norm_num : 0 < (1 : ℕ))

theorem e_s_deriv_hasCompactSupport : HasCompactSupport (deriv e_s) := by
  rw [e_s_eq_identityExtension]
  simpa using iteratedDeriv_hasCompactSupport_of_constant_tails
    (fun _ ht ↦ identityExtension_eq_left (by norm_num : (0 : ℝ) ≤ 2) ht)
    (fun _ ht ↦ identityExtension_eq_right (by norm_num : (0 : ℝ) ≤ 2) ht)
    (by norm_num : 0 < (1 : ℕ))

theorem e_nu_deriv_hasCompactSupport : HasCompactSupport (deriv e_nu) := by
  rw [e_nu_eq_identityExtension]
  simpa using iteratedDeriv_hasCompactSupport_of_constant_tails
    (fun _ ht ↦ identityExtension_eq_left (by norm_num : (0 : ℝ) ≤ 21) ht)
    (fun _ ht ↦ identityExtension_eq_right (by norm_num : (0 : ℝ) ≤ 21) ht)
    (by norm_num : 0 < (1 : ℕ))

theorem deriv_R_abs_le {c : ℝ} (hc : -1 ≤ c) (t : ℝ) :
    |deriv (R c) t| ≤ c + 25 := by
  rw [abs_of_nonpos (deriv_R_nonpos hc t), deriv_R]
  have hdiff : step (10 * t - 1) - step (10 * t - 10) ≤ 1 := by
    linarith [step_le_one (10 * t - 1), step_nonneg (10 * t - 10)]
  have hmul := mul_le_mul_of_nonneg_left hdiff (show 0 ≤ c + 1 by linarith)
  linarith [step_le_one (-10 * t)]

theorem R_second_derivative_bounded (c : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv (deriv (R c)) t| ≤ C := by
  have hcont := (contDiff_infty_iff_deriv.mp (R_contDiff c)).2
  simpa using iteratedDeriv_bounded_of_constant_tails hcont
    (fun _ ht ↦ deriv_R_left ht) (fun _ ht ↦ deriv_R_right ht)
    (by norm_num : 0 < (1 : ℕ))

end

end NCC.Construction
