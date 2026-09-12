import NCPLVerification.InnerValue

/-!
# Terminal certificate

This file formalizes Lemma 3.2.  The numerical constant can be chosen as
`C_γ = 192` for the explicit gates used by the construction.
-/

namespace NCPLVerification

noncomputable section

def innerGamma {N : ℕ} (z : EVec N) : ℝ :=
  if hN : 0 < N then sigma (z ⟨N - 1, Nat.sub_lt hN (by omega)⟩) else 0

theorem innerGamma_eq {N : ℕ} (hN : 0 < N) (z : EVec N) :
    innerGamma z = sigma (z ⟨N - 1, Nat.sub_lt hN (by omega)⟩) := by
  simp [innerGamma, hN]

theorem innerGamma_nonneg {N : ℕ} (z : EVec N) : 0 ≤ innerGamma z := by
  unfold innerGamma
  split_ifs
  · exact sigma_nonneg _
  · rfl

theorem innerGamma_le_one {N : ℕ} (z : EVec N) : innerGamma z ≤ 1 := by
  unfold innerGamma
  split_ifs
  · exact sigma_le_one _
  · norm_num

private theorem terminal_gap_le_three_residual_sq {N : ℕ} (hN : 0 < N)
    (z : EVec N)
    (hopen : (1 : ℝ) / 2 ≤ sigma
      (innerPrev z ⟨N - 1, Nat.sub_lt hN (by omega)⟩)) :
    1 - innerGamma z ≤
      3 * innerResidual z ⟨N - 1, Nat.sub_lt hN (by omega)⟩ ^ 2 := by
  let i : Fin N := ⟨N - 1, Nat.sub_lt hN (by omega)⟩
  have hgamma : innerGamma z = sigma (z i) := by
    simpa [i] using innerGamma_eq hN z
  by_cases h1 : 1 ≤ z i
  · have hsigma : sigma (z i) = 1 := sigma_of_one_le h1
    rw [hgamma, hsigma]
    have hnonneg : 0 ≤ (3 : ℝ) *
        innerResidual z ⟨N - 1, Nat.sub_lt hN (by omega)⟩ ^ 2 :=
      mul_nonneg (by norm_num)
        (sq_nonneg (innerResidual z ⟨N - 1, Nat.sub_lt hN (by omega)⟩))
    simpa only [sub_self] using hnonneg
  by_cases h0 : 0 ≤ z i
  · have hz1 : z i ≤ 1 := le_of_not_ge h1
    have hsig := one_sub_sigma_le_three_sq h0 hz1
    have hbeta : beta (z i) = z i := beta_eq_self h0 hz1
    have hprod : sigma (innerPrev z i) * z i ≤ z i :=
      mul_le_of_le_one_left h0 (sigma_le_one _)
    have hr : 1 - z i ≤ innerResidual z i := by
      rw [innerResidual, gateResidual, hbeta, posPart]
      exact (by linarith : 1 - z i ≤
        1 - sigma (innerPrev z i) * z i) |>.trans (le_max_left _ _)
    have hr0 := innerResidual_nonneg z i
    rw [hgamma]
    nlinarith [sq_nonneg (innerResidual z i - (1 - z i))]
  · have hz0 : z i ≤ 0 := le_of_not_ge h0
    have hbeta : beta (z i) ≤ 0 := beta_nonpos_of_nonpos hz0
    have hmul : sigma (innerPrev z i) * beta (z i) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sigma_nonneg _) hbeta
    have hr : 1 ≤ innerResidual z i := by
      rw [innerResidual, gateResidual, posPart]
      exact (by linarith : 1 ≤ 1 - sigma (innerPrev z i) * beta (z i)) |>.trans
        (le_max_left _ _)
    have hsigma : sigma (z i) = 0 := sigma_of_nonpos hz0
    rw [hgamma, hsigma]
    nlinarith [sq_nonneg (innerResidual z i - 1)]

/-- Lemma 3.2 with the explicit constant `C_γ = 192`. -/
theorem terminal_certificate_estimate {N : ℕ} (hN2 : 2 ≤ N)
    {lambdaWall : ℝ} (hlambda : 12 ≤ lambdaWall) (z : EVec N) :
    (1 - innerGamma z) / (N : ℝ) ≤
      192 * innerCertificate N lambdaWall z := by
  have hN : 0 < N := by omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  let i : Fin N := ⟨N - 1, Nat.sub_lt hN (by omega)⟩
  by_cases hopen : (1 : ℝ) / 2 ≤ sigma (innerPrev z i)
  · have hgap := terminal_gap_le_three_residual_sq hN z (by simpa [i] using hopen)
    have hlocal := open_residual_value_le_local hN2
      (by linarith : (1 : ℝ) ≤ lambdaWall) z i hopen
    have halpha : innerAlpha N i = 1 := by
      simpa [i] using innerAlpha_terminal hN
    rw [halpha, one_mul] at hlocal
    have hlocalGlobal := innerResidualLocalCertificate_le hN lambdaWall z i
    calc
      (1 - innerGamma z) / (N : ℝ) ≤
          (3 * innerResidual z i ^ 2) / (N : ℝ) :=
        div_le_div_of_nonneg_right (by simpa [i] using hgap) hNreal.le
      _ ≤ (3 * (64 * (N : ℝ) *
          innerResidualLocalCertificate N lambdaWall z i)) / (N : ℝ) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlocal (by norm_num)) hNreal.le
      _ = 192 * innerResidualLocalCertificate N lambdaWall z i := by
        field_simp
        ring
      _ ≤ 192 * innerCertificate N lambdaWall z :=
        mul_le_mul_of_nonneg_left hlocalGlobal (by norm_num)
  · have hnot : ¬∀ j : Fin N, (1 : ℝ) / 2 ≤ sigma (innerPrev z j) := by
      intro hall
      exact hopen (hall i)
    have hcert := innerCertificate_lower_of_not_all_open hN2 hlambda z hnot
    have hgap : 1 - innerGamma z ≤ 1 := by
      have := innerGamma_nonneg z
      linarith
    calc
      (1 - innerGamma z) / (N : ℝ) ≤ 1 / (N : ℝ) :=
        div_le_div_of_nonneg_right hgap hNreal.le
      _ = 16 * (((1 : ℝ) / 16) / (N : ℝ)) := by ring
      _ ≤ 16 * innerCertificate N lambdaWall z :=
        mul_le_mul_of_nonneg_left hcert (by norm_num)
      _ ≤ 192 * innerCertificate N lambdaWall z := by
        have hc := innerCertificate_nonneg hN lambdaWall z
        nlinarith

end

end NCPLVerification
