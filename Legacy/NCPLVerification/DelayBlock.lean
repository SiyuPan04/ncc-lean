import NCPLVerification.TerminalCertificate

/-!
# The uniform maximization-PL delay block

This file formalizes the algebraic core of Lemma 4.1, including attainment of
the maximum and the sign argument which prevents cancellation between the
terminal gate gradient and the inner-chain gradient.
-/

namespace NCPLVerification

noncomputable section

def delayG (N : ℕ) (lambdaWall eta a : ℝ) (z : EVec N) : ℝ :=
  a * innerGamma z - eta * innerH N lambdaWall z

def innerGammaField (N : ℕ) (z : EVec N) : EVec N :=
  fun i ↦ if hN : 0 < N then
    if i = (⟨N - 1, Nat.sub_lt hN (by omega)⟩ : Fin N) then
      sigmaDeriv (z i)
    else 0
  else 0

def delayGradient (N : ℕ) (lambdaWall eta a : ℝ) (z : EVec N) : EVec N :=
  fun i ↦ a * innerGammaField N z i - eta * innerGradient N lambdaWall z i

/-- The terminal reward does not destroy the one-step support rule: its only
possible coordinate is the last one, and its derivative is flat at zero. -/
theorem delayGradient_is_zeroChain (N : ℕ) (lambdaWall eta a : ℝ) :
    IsFirstOrderZeroChain (delayGradient N lambdaWall eta a) := by
  intro r z hz i hir
  have hinner := innerGradient_is_zeroChain N lambdaWall r z hz i hir
  have hzi : z i = 0 := hz i (by omega)
  unfold delayGradient innerGammaField
  rw [hinner]
  split
  · split
    · simp [hzi, sigmaDeriv_zero]
    · ring
  · ring

def innerAllOnes (N : ℕ) : EVec N := fun _ ↦ 1

theorem innerPrev_allOnes {N : ℕ} (i : Fin N) :
    innerPrev (innerAllOnes N) i = 1 := by
  unfold innerPrev innerAllOnes
  split_ifs
  · rfl
  · rfl

theorem innerResidual_allOnes {N : ℕ} (i : Fin N) :
    innerResidual (innerAllOnes N) i = 0 := by
  rw [innerResidual, innerPrev_allOnes]
  change gateResidual 1 1 = 0
  rw [gateResidual, sigma_one,
    beta_eq_self (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (1 : ℝ) ≤ 1)]
  norm_num [posPart]

theorem innerH_allOnes {N : ℕ} (lambdaWall : ℝ) :
    innerH N lambdaWall (innerAllOnes N) = 0 := by
  unfold innerH
  simp [innerResidual_allOnes, innerAllOnes, negPart]

theorem innerGamma_allOnes {N : ℕ} (hN : 0 < N) :
    innerGamma (innerAllOnes N) = 1 := by
  rw [innerGamma_eq hN]
  norm_num [innerAllOnes, sigma]

/-- The point `(1,…,1)` attains value `a`. -/
theorem delayG_allOnes {N : ℕ} (hN : 0 < N)
    (lambdaWall eta a : ℝ) :
    delayG N lambdaWall eta a (innerAllOnes N) = a := by
  simp [delayG, innerGamma_allOnes hN, innerH_allOnes]

/-- Every point has value at most `a`; together with `delayG_allOnes`, this
is the exact maximum assertion without introducing a noncomputable argmax. -/
theorem delayG_le_a {N : ℕ} (hN : 0 < N) {lambdaWall eta a : ℝ}
    (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta) (ha : 0 ≤ a)
    (z : EVec N) : delayG N lambdaWall eta a z ≤ a := by
  have hgamma := innerGamma_le_one z
  have hH := innerH_nonneg hN hlambda z
  unfold delayG
  nlinarith

theorem delayG_gap (N : ℕ) (lambdaWall eta a : ℝ) (z : EVec N) :
    a - delayG N lambdaWall eta a z =
      a * (1 - innerGamma z) + eta * innerH N lambdaWall z := by
  unfold delayG
  ring

theorem innerGammaField_nonneg {N : ℕ} (z : EVec N) (i : Fin N) :
    0 ≤ innerGammaField N z i := by
  unfold innerGammaField
  split_ifs
  · exact sigmaDeriv_nonneg _
  · rfl
  · rfl

theorem innerGradient_terminal_nonpos {N : ℕ} (hN : 0 < N)
    {lambdaWall : ℝ} (hlambda : 0 ≤ lambdaWall) (z : EVec N) :
    innerGradient N lambdaWall z ⟨N - 1, Nat.sub_lt hN (by omega)⟩ ≤ 0 := by
  let i : Fin N := ⟨N - 1, Nat.sub_lt hN (by omega)⟩
  have hnot : ¬i.1 + 1 < N := by dsimp [i]; omega
  have hforward : innerForward N z i = 0 := by simp [innerForward, hnot]
  have hin := innerIncoming_nonneg hN z i
  have hv : 0 ≤ lambdaWall * innerD N i * negPart (z i) :=
    mul_nonneg (mul_nonneg hlambda (innerD_pos hN i).le) (negPart_nonneg _)
  rw [innerGradient, hforward]
  nlinarith

theorem gammaField_mul_innerGradient_nonpos {N : ℕ} (hN : 0 < N)
    {lambdaWall : ℝ} (hlambda : 0 ≤ lambdaWall) (z : EVec N) (i : Fin N) :
    innerGammaField N z i * innerGradient N lambdaWall z i ≤ 0 := by
  unfold innerGammaField
  simp only [dif_pos hN]
  by_cases hi : i = (⟨N - 1, Nat.sub_lt hN (by omega)⟩ : Fin N)
  · rw [if_pos hi, hi]
    exact mul_nonpos_of_nonneg_of_nonpos (sigmaDeriv_nonneg _)
      (innerGradient_terminal_nonpos hN hlambda z)
  · rw [if_neg hi, zero_mul]

/-- The terminal gate term cannot cancel the negative terminal component of
the inner gradient. -/
theorem eta_sq_innerDualSq_le_delay {N : ℕ} (hN : 0 < N)
    {lambdaWall eta a : ℝ} (hlambda : 0 ≤ lambdaWall)
    (heta : 0 ≤ eta) (ha : 0 ≤ a) (z : EVec N) :
    eta ^ 2 * innerDualSq N (innerGradient N lambdaWall z) ≤
      innerDualSq N (delayGradient N lambdaWall eta a z) := by
  unfold innerDualSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [delayGradient]
  have hd := (innerD_pos hN i).le
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hd
  have hcross := gammaField_mul_innerGradient_nonpos hN hlambda z i
  have hg := innerGammaField_nonneg z i
  have haeta : 0 ≤ a * eta := mul_nonneg ha heta
  have hcrossScaled : a * eta *
      (innerGammaField N z i * innerGradient N lambdaWall z i) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos haeta hcross
  nlinarith [sq_nonneg (a * innerGammaField N z i)]

theorem delayG_gap_le_certificate {N : ℕ} (hN2 : 2 ≤ N)
    {lambdaWall eta a Amax : ℝ} (hlambda : 12 ≤ lambdaWall)
    (heta : 0 ≤ eta) (ha : 0 ≤ a) (haMax : a ≤ Amax)
    (z : EVec N) :
    a - delayG N lambdaWall eta a z ≤
      (192 * Amax + 193 * eta) * (N : ℝ) *
        innerCertificate N lambdaWall z := by
  have hN : 0 < N := by omega
  have hterminal := terminal_certificate_estimate hN2 hlambda z
  have hvalue := innerH_le_certificate hN2 hlambda z
  have hgammaNonneg : 0 ≤ 1 - innerGamma z := by
    linarith [innerGamma_le_one z]
  have hH := innerH_nonneg hN (by linarith : 0 ≤ lambdaWall) z
  have htermScaled : a * (1 - innerGamma z) ≤
      192 * Amax * (N : ℝ) * innerCertificate N lambdaWall z := by
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have hfromTerminal : 1 - innerGamma z ≤
        192 * (N : ℝ) * innerCertificate N lambdaWall z := by
      have hmul := (div_le_iff₀ hNreal).mp hterminal
      calc
        1 - innerGamma z ≤
            192 * innerCertificate N lambdaWall z * (N : ℝ) := hmul
        _ = 192 * (N : ℝ) * innerCertificate N lambdaWall z := by ring
    calc
      a * (1 - innerGamma z) ≤ Amax * (1 - innerGamma z) :=
        mul_le_mul_of_nonneg_right haMax hgammaNonneg
      _ ≤ Amax * (192 * (N : ℝ) * innerCertificate N lambdaWall z) :=
        mul_le_mul_of_nonneg_left hfromTerminal (ha.trans haMax)
      _ = 192 * Amax * (N : ℝ) * innerCertificate N lambdaWall z := by ring
  rw [delayG_gap]
  have hvalueScaled : eta * innerH N lambdaWall z ≤
      193 * eta * (N : ℝ) * innerCertificate N lambdaWall z := by
    calc
      eta * innerH N lambdaWall z ≤
          eta * (193 * (N : ℝ) * innerCertificate N lambdaWall z) :=
        mul_le_mul_of_nonneg_left hvalue heta
      _ = 193 * eta * (N : ℝ) * innerCertificate N lambdaWall z := by ring
  calc
    a * (1 - innerGamma z) + eta * innerH N lambdaWall z ≤
        192 * Amax * (N : ℝ) * innerCertificate N lambdaWall z +
          193 * eta * (N : ℝ) * innerCertificate N lambdaWall z :=
      add_le_add htermScaled hvalueScaled
    _ = (192 * Amax + 193 * eta) * (N : ℝ) *
        innerCertificate N lambdaWall z := by ring

/-- Lemma 4.1(c), expressed using the already verified gradient fields.  The
constant is explicit and uniform in `N`. -/
theorem delay_block_PL_field {N : ℕ} (hN2 : 2 ≤ N)
    {lambdaWall eta a Amax : ℝ} (hlambda : 12 ≤ lambdaWall)
    (heta : 0 < eta) (ha : 0 ≤ a) (haMax : a ≤ Amax)
    (z : EVec N) :
    (1 : ℝ) / 2 * innerDualSq N (delayGradient N lambdaWall eta a z) ≥
      (eta ^ 2 / (2 * (192 * Amax + 193 * eta))) / (N : ℝ) *
        (a - delayG N lambdaWall eta a z) := by
  have hN : 0 < N := by omega
  have hAmax : 0 ≤ Amax := ha.trans haMax
  have hden : 0 < 192 * Amax + 193 * eta := by positivity
  have hgap := delayG_gap_le_certificate hN2 hlambda heta.le ha haMax z
  have hdelay := eta_sq_innerDualSq_le_delay hN
    (by linarith : 0 ≤ lambdaWall) heta.le ha z
  have hcertGrad := innerCertificate_le_gradient hN hlambda z
  have hetaCert : eta ^ 2 * innerCertificate N lambdaWall z ≤
      innerDualSq N (delayGradient N lambdaWall eta a z) :=
    (mul_le_mul_of_nonneg_left hcertGrad (sq_nonneg eta)).trans hdelay
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    (eta ^ 2 / (2 * (192 * Amax + 193 * eta))) / (N : ℝ) *
        (a - delayG N lambdaWall eta a z) =
      (eta ^ 2 * (a - delayG N lambdaWall eta a z)) /
        (2 * (192 * Amax + 193 * eta) * (N : ℝ)) := by
          field_simp
    _ ≤ (eta ^ 2 *
        ((192 * Amax + 193 * eta) * (N : ℝ) *
          innerCertificate N lambdaWall z)) /
        (2 * (192 * Amax + 193 * eta) * (N : ℝ)) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hgap (sq_nonneg eta)) (by positivity)
    _ = eta ^ 2 * innerCertificate N lambdaWall z / 2 := by
      field_simp
    _ ≤ innerDualSq N (delayGradient N lambdaWall eta a z) / 2 :=
      div_le_div_of_nonneg_right hetaCert (by norm_num)
    _ = (1 : ℝ) / 2 * innerDualSq N (delayGradient N lambdaWall eta a z) := by ring

end

end NCPLVerification
