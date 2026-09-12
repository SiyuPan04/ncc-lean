import NCCLowerBoundVerification.Basic
import NCPLVerification.CarmonGates
import NCPLVerification.CarmonSmoothness

/-!
# The activation family

This module formalizes Definition `def:Psi-family` from
`Upper+Lower_unified_lower.tex`.  The paper's first activation is exactly the
flat exponential gate already verified in `NCPLVerification.CarmonGates`;
the second activation is its translation by `1/2`.
-/

namespace NCCLowerBoundVerification

noncomputable section

/-- The reward activation `Ψ₁` from Definition `def:Psi-family`. -/
def Psi1 (t : ℝ) : ℝ :=
  NCPLVerification.carmonPsi t

/-- The translated high-regime detector `Ψ₂`. -/
def Psi2 (t : ℝ) : ℝ :=
  Psi1 (t - 1 / 2)

/-- The verified first-derivative field of `Ψ₁`. -/
def Psi1Deriv (t : ℝ) : ℝ :=
  NCPLVerification.carmonPsiDeriv t

/-- The first-derivative field of the translated activation `Ψ₂`. -/
def Psi2Deriv (t : ℝ) : ℝ :=
  Psi1Deriv (t - 1 / 2)

def Psi1Second (t : ℝ) : ℝ :=
  NCPLVerification.carmonPsiSecond t

def Psi2Second (t : ℝ) : ℝ :=
  Psi1Second (t - 1 / 2)

/-- The definition of `Ψ₁` in exactly the piecewise form displayed in the paper. -/
theorem Psi1_eq_piecewise (t : ℝ) :
    Psi1 t = if t ≤ 1 / 2 then 0 else
      Real.exp (1 - 1 / (2 * t - 1) ^ 2) := by
  exact NCPLVerification.carmonPsi_eq_piecewise t

theorem Psi1_eq_zero_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) : Psi1 t = 0 := by
  exact NCPLVerification.carmonPsi_of_le_half ht

theorem Psi1_pos_of_half_lt {t : ℝ} (ht : 1 / 2 < t) : 0 < Psi1 t := by
  unfold Psi1 NCPLVerification.carmonPsi
  exact mul_pos (Real.exp_pos 1)
    (NCPLVerification.expNegInvSqGlue_pos_of_pos (by linarith))

theorem Psi1_nonneg (t : ℝ) : 0 ≤ Psi1 t := by
  exact NCPLVerification.carmonPsi_nonneg t

theorem Psi1_le_exp_one (t : ℝ) : Psi1 t ≤ Real.exp 1 := by
  exact NCPLVerification.carmonPsi_le_exp_one t

theorem Psi1_mem_range (t : ℝ) : Psi1 t ∈ Set.Icc (0 : ℝ) (Real.exp 1) := by
  exact ⟨Psi1_nonneg t, Psi1_le_exp_one t⟩

theorem Psi1_monotone : Monotone Psi1 := by
  exact NCPLVerification.carmonPsi_monotone

theorem Psi1_zero : Psi1 0 = 0 := by
  exact Psi1_eq_zero_of_le_half (by norm_num)

theorem Psi1_one : Psi1 1 = 1 := by
  exact NCPLVerification.carmonPsi_one

theorem hasDerivAt_Psi1 (t : ℝ) : HasDerivAt Psi1 (Psi1Deriv t) t := by
  have h := (NCPLVerification.differentiable_carmonPsi t).hasDerivAt
  rw [NCPLVerification.deriv_carmonPsi] at h
  unfold Psi1 Psi1Deriv
  convert h using 1

theorem deriv_Psi1 (t : ℝ) : deriv Psi1 t = Psi1Deriv t :=
  (hasDerivAt_Psi1 t).deriv

theorem differentiable_Psi1 : Differentiable ℝ Psi1 :=
  fun t ↦ (hasDerivAt_Psi1 t).differentiableAt

theorem Psi1Deriv_eq_zero_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) :
    Psi1Deriv t = 0 := by
  unfold Psi1Deriv NCPLVerification.carmonPsiDeriv
  rw [NCPLVerification.expNegInvSqGlueDeriv]
  simp [show 2 * t - 1 ≤ 0 by linarith]

theorem Psi1Deriv_pos_of_half_lt {t : ℝ} (ht : 1 / 2 < t) :
    0 < Psi1Deriv t := by
  unfold Psi1Deriv NCPLVerification.carmonPsiDeriv
  rw [NCPLVerification.expNegInvSqGlueDeriv, if_neg (by linarith)]
  have hx : 0 < (2 * t - 1)⁻¹ := inv_pos.mpr (by linarith)
  positivity

theorem Psi1Deriv_nonneg (t : ℝ) : 0 ≤ Psi1Deriv t := by
  exact NCPLVerification.carmonPsiDeriv_nonneg t

/-- A quotient form of the positive-tail derivative, convenient for estimates. -/
theorem Psi1Deriv_eq_mul_Psi1 {t : ℝ} (ht : 1 / 2 < t) :
    Psi1Deriv t = 4 / (2 * t - 1) ^ 3 * Psi1 t := by
  have hx : 2 * t - 1 ≠ 0 := ne_of_gt (by linarith)
  unfold Psi1Deriv Psi1 NCPLVerification.carmonPsiDeriv
    NCPLVerification.carmonPsi NCPLVerification.expNegInvSqGlueDeriv
    NCPLVerification.expNegInvSqGlue
  rw [if_neg (by linarith), if_neg (by linarith)]
  field_simp [hx]
  ring

/-- The derivative formula displayed in the proof of `lem:Psi-family-properties`. -/
theorem Psi1Deriv_eq_exp_formula {t : ℝ} (ht : 1 / 2 < t) :
    Psi1Deriv t =
      4 / (2 * t - 1) ^ 3 * Real.exp (1 - 1 / (2 * t - 1) ^ 2) := by
  rw [Psi1Deriv_eq_mul_Psi1 ht, Psi1_eq_piecewise, if_neg (not_le.mpr ht)]

theorem hasDerivAt_Psi2 (t : ℝ) : HasDerivAt Psi2 (Psi2Deriv t) t := by
  have hshift : HasDerivAt (fun s : ℝ ↦ s - 1 / 2) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (1 / 2)
  have hcomp := (hasDerivAt_Psi1 (t - 1 / 2)).comp t hshift
  unfold Psi2 Psi2Deriv
  convert hcomp using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · ring

theorem deriv_Psi2 (t : ℝ) : deriv Psi2 t = Psi2Deriv t :=
  (hasDerivAt_Psi2 t).deriv

theorem differentiable_Psi2 : Differentiable ℝ Psi2 :=
  fun t ↦ (hasDerivAt_Psi2 t).differentiableAt

theorem Psi2_eq_zero_of_le_one {t : ℝ} (ht : t ≤ 1) : Psi2 t = 0 := by
  unfold Psi2
  apply Psi1_eq_zero_of_le_half
  linarith

theorem Psi2Deriv_eq_zero_of_le_one {t : ℝ} (ht : t ≤ 1) :
    Psi2Deriv t = 0 := by
  unfold Psi2Deriv
  apply Psi1Deriv_eq_zero_of_le_half
  linarith

theorem Psi2_pos_of_one_lt {t : ℝ} (ht : 1 < t) : 0 < Psi2 t := by
  unfold Psi2
  apply Psi1_pos_of_half_lt
  linarith

theorem Psi2Deriv_pos_of_one_lt {t : ℝ} (ht : 1 < t) :
    0 < Psi2Deriv t := by
  unfold Psi2Deriv
  apply Psi1Deriv_pos_of_half_lt
  linarith

theorem Psi2_nonneg (t : ℝ) : 0 ≤ Psi2 t := by
  exact Psi1_nonneg (t - 1 / 2)

theorem Psi2_le_exp_one (t : ℝ) : Psi2 t ≤ Real.exp 1 := by
  exact Psi1_le_exp_one (t - 1 / 2)

theorem Psi2_mem_range (t : ℝ) : Psi2 t ∈ Set.Icc (0 : ℝ) (Real.exp 1) := by
  exact ⟨Psi2_nonneg t, Psi2_le_exp_one t⟩

theorem Psi2Deriv_nonneg (t : ℝ) : 0 ≤ Psi2Deriv t := by
  exact Psi1Deriv_nonneg (t - 1 / 2)

theorem Psi2_monotone : Monotone Psi2 := by
  intro s t hst
  exact Psi1_monotone (by linarith)

theorem Psi2_zero : Psi2 0 = 0 := by
  exact Psi2_eq_zero_of_le_one (by norm_num)

theorem Psi2Deriv_zero : Psi2Deriv 0 = 0 := by
  exact Psi2Deriv_eq_zero_of_le_one (by norm_num)

theorem abs_Psi1Deriv_le_twentyFour (t : ℝ) :
    |Psi1Deriv t| ≤ 24 := by
  exact NCPLVerification.abs_carmonPsiDeriv_le_twentyFour t

theorem hasDerivAt_Psi1Deriv (t : ℝ) :
    HasDerivAt Psi1Deriv (Psi1Second t) t := by
  exact NCPLVerification.hasDerivAt_carmonPsiDeriv t

theorem abs_Psi1Second_le_fourHundredThirtyTwo (t : ℝ) :
    |Psi1Second t| ≤ 432 := by
  exact NCPLVerification.abs_carmonPsiSecond_le_fourHundredThirtyTwo t

theorem hasDerivAt_Psi2Deriv (t : ℝ) :
    HasDerivAt Psi2Deriv (Psi2Second t) t := by
  have hshift : HasDerivAt (fun s : ℝ ↦ s - 1 / 2) 1 t := by
    simpa using (hasDerivAt_id t).sub_const (1 / 2)
  have hcomp := (hasDerivAt_Psi1Deriv (t - 1 / 2)).comp t hshift
  unfold Psi2Deriv Psi2Second
  convert hcomp using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · ring

theorem abs_Psi2Deriv_le_twentyFour (t : ℝ) :
    |Psi2Deriv t| ≤ 24 :=
  abs_Psi1Deriv_le_twentyFour (t - 1 / 2)

theorem abs_Psi2Second_le_fourHundredThirtyTwo (t : ℝ) :
    |Psi2Second t| ≤ 432 :=
  abs_Psi1Second_le_fourHundredThirtyTwo (t - 1 / 2)

/-- A fully explicit version of the paper's compact-interval constant
`ψ₀`: the derivative is at least `2` throughout every requested interval. -/
theorem two_le_Psi1Deriv_on {theta t : ℝ}
    (htheta_pos : 0 < theta) (htheta : theta < 1 / 10)
    (ht_low : 1 ≤ t) (ht_high : t ≤ 1 + theta) :
    2 ≤ Psi1Deriv t := by
  have hhalf : 1 / 2 < t := by linarith
  rw [Psi1Deriv_eq_exp_formula hhalf]
  let x : ℝ := 2 * t - 1
  have hx1 : 1 ≤ x := by dsimp [x]; linarith
  have hxu : x ≤ 6 / 5 := by dsimp [x]; linarith
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hx2pos : 0 < x ^ 2 := sq_pos_of_pos hx0
  have hx2one : 1 ≤ x ^ 2 := by nlinarith
  have hinv : 1 / x ^ 2 ≤ 1 := by
    apply (div_le_iff₀ hx2pos).2
    simpa using hx2one
  have hexp : 1 ≤ Real.exp (1 - 1 / x ^ 2) := by
    exact Real.one_le_exp (by linarith)
  have hpoly : 0 ≤ (6 / 5 : ℝ) ^ 2 + (6 / 5 : ℝ) * x + x ^ 2 := by
    positivity
  have hcube : x ^ 3 ≤ (6 / 5 : ℝ) ^ 3 := by
    have hm := mul_nonneg (sub_nonneg.mpr hxu) hpoly
    nlinarith
  have hx3pos : 0 < x ^ 3 := pow_pos hx0 3
  have hfrac : 2 ≤ 4 / x ^ 3 := by
    apply (le_div_iff₀ hx3pos).2
    nlinarith
  change 2 ≤ 4 / x ^ 3 * Real.exp (1 - 1 / x ^ 2)
  exact hfrac.trans (le_mul_of_one_le_right (by positivity) hexp)

/-- The positive high-regime lower bound can be chosen at the threshold. -/
def xi0 (theta : ℝ) : ℝ :=
  Psi2 (1 + theta)

theorem xi0_pos {theta : ℝ} (htheta : 0 < theta) : 0 < xi0 theta := by
  unfold xi0
  exact Psi2_pos_of_one_lt (by linarith)

theorem xi0_le_Psi2 {theta t : ℝ} (ht : 1 + theta ≤ t) :
    xi0 theta ≤ Psi2 t := by
  unfold xi0
  exact Psi2_monotone ht

end

end NCCLowerBoundVerification
