import NCPLVerification.GateDerivatives
import NCPLVerification.InnerChain

/-!
# Gradient certificate for the inner PL chain

This file formalizes the `Pᵢ-eᵢ` decomposition in the proof of the inner PL
inequality.  The certificate is written coordinatewise, which is definitionally
equivalent to the two residual sums and the wall sum displayed in the paper.
-/

namespace NCPLVerification

noncomputable section

def innerForwardPos (N : ℕ) (z : EVec N) (i : Fin N) : ℝ :=
  if hi : i.1 + 1 < N then
    innerAlpha N ⟨i.1 + 1, hi⟩ * sigmaDeriv (z i) *
      posPart (beta (z ⟨i.1 + 1, hi⟩)) * innerResidual z ⟨i.1 + 1, hi⟩
  else 0

def innerError (N : ℕ) (z : EVec N) (i : Fin N) : ℝ :=
  if hi : i.1 + 1 < N then
    innerAlpha N ⟨i.1 + 1, hi⟩ * sigmaDeriv (z i) *
      negPart (beta (z ⟨i.1 + 1, hi⟩)) * innerResidual z ⟨i.1 + 1, hi⟩
  else 0

def innerWallPart (N : ℕ) (lambdaWall : ℝ) (z : EVec N) (i : Fin N) : ℝ :=
  lambdaWall * innerD N i * negPart (z i)

def innerP (N : ℕ) (lambdaWall : ℝ) (z : EVec N) (i : Fin N) : ℝ :=
  innerIncoming N z i + innerForwardPos N z i + innerWallPart N lambdaWall z i

/-- The weighted dual square `Σᵢ vᵢ²/dᵢ`. -/
def innerDualSq (N : ℕ) (v : EVec N) : ℝ :=
  ∑ i : Fin N, v i ^ 2 / innerD N i

/-- Certificate `S_N`, grouped by the gradient coordinate in which each
incoming, forward-positive, and wall term occurs. -/
def innerCertificate (N : ℕ) (lambdaWall : ℝ) (z : EVec N) : ℝ :=
  ∑ i : Fin N,
    (innerIncoming N z i ^ 2 + innerForwardPos N z i ^ 2 +
      innerWallPart N lambdaWall z i ^ 2) / innerD N i

def innerWallEnergy (N : ℕ) (z : EVec N) : ℝ :=
  ∑ i : Fin N, innerD N i * negPart (z i) ^ 2

theorem innerIncoming_nonneg {N : ℕ} (hN : 0 < N) (z : EVec N) (i : Fin N) :
    0 ≤ innerIncoming N z i := by
  unfold innerIncoming
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (innerAlpha_pos hN i).le (sigma_nonneg _)) (betaDeriv_nonneg _))
    (innerResidual_nonneg z i)

theorem innerForwardPos_nonneg {N : ℕ} (hN : 0 < N) (z : EVec N) (i : Fin N) :
    0 ≤ innerForwardPos N z i := by
  unfold innerForwardPos
  split_ifs with hi
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (innerAlpha_pos hN _).le (sigmaDeriv_nonneg _))
          (posPart_nonneg _))
      (innerResidual_nonneg z _)
  · rfl

theorem innerError_nonneg {N : ℕ} (hN : 0 < N) (z : EVec N) (i : Fin N) :
    0 ≤ innerError N z i := by
  unfold innerError
  split_ifs with hi
  · exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (innerAlpha_pos hN _).le (sigmaDeriv_nonneg _))
          (negPart_nonneg _))
      (innerResidual_nonneg z _)
  · rfl

theorem innerWallPart_nonneg {N : ℕ} (hN : 0 < N) {lambdaWall : ℝ}
    (hlambda : 0 ≤ lambdaWall) (z : EVec N) (i : Fin N) :
    0 ≤ innerWallPart N lambdaWall z i := by
  unfold innerWallPart
  exact mul_nonneg (mul_nonneg hlambda (innerD_pos hN i).le) (negPart_nonneg _)

/-- Splitting `β = β⁺-β⁻` gives exactly the sole cancellation term in the
paper. -/
theorem innerForward_eq_pos_sub_error (N : ℕ) (z : EVec N) (i : Fin N) :
    innerForward N z i = innerForwardPos N z i - innerError N z i := by
  unfold innerForward innerForwardPos innerError
  by_cases hi : i.1 + 1 < N
  · simp only [dif_pos hi]
    calc
      innerAlpha N ⟨i.1 + 1, hi⟩ * sigmaDeriv (z i) *
          beta (z ⟨i.1 + 1, hi⟩) * innerResidual z ⟨i.1 + 1, hi⟩ =
        innerAlpha N ⟨i.1 + 1, hi⟩ * sigmaDeriv (z i) *
          (posPart (beta (z ⟨i.1 + 1, hi⟩)) -
            negPart (beta (z ⟨i.1 + 1, hi⟩))) *
          innerResidual z ⟨i.1 + 1, hi⟩ := by
            rw [posPart_sub_negPart]
      _ = innerAlpha N ⟨i.1 + 1, hi⟩ * sigmaDeriv (z i) *
            posPart (beta (z ⟨i.1 + 1, hi⟩)) * innerResidual z ⟨i.1 + 1, hi⟩ -
          innerAlpha N ⟨i.1 + 1, hi⟩ * sigmaDeriv (z i) *
            negPart (beta (z ⟨i.1 + 1, hi⟩)) * innerResidual z ⟨i.1 + 1, hi⟩ := by
            ring
  · simp [hi]

/-- Coordinate identity `∂ᵢH_N = -2(Pᵢ-eᵢ)`, including the terminal case. -/
theorem innerGradient_eq_P_sub_error (N : ℕ) (lambdaWall : ℝ)
    (z : EVec N) (i : Fin N) :
    innerGradient N lambdaWall z i =
      -2 * (innerP N lambdaWall z i - innerError N z i) := by
  rw [innerGradient, innerP, innerWallPart, innerForward_eq_pos_sub_error]
  ring

theorem innerP_nonneg {N : ℕ} (hN : 0 < N) {lambdaWall : ℝ}
    (hlambda : 0 ≤ lambdaWall) (z : EVec N) (i : Fin N) :
    0 ≤ innerP N lambdaWall z i := by
  unfold innerP
  exact add_nonneg
    (add_nonneg (innerIncoming_nonneg hN z i) (innerForwardPos_nonneg hN z i))
    (innerWallPart_nonneg hN hlambda z i)

theorem innerCertificate_nonneg {N : ℕ} (hN : 0 < N)
    (lambdaWall : ℝ) (z : EVec N) : 0 ≤ innerCertificate N lambdaWall z := by
  unfold innerCertificate
  apply Finset.sum_nonneg
  intro i _
  exact div_nonneg (by positivity) (innerD_pos hN i).le

/-- Because every summand in `Pᵢ` is nonnegative, `ΣPᵢ²/dᵢ` controls the
certificate without a dimension-dependent loss. -/
theorem innerCertificate_le_P_dual {N : ℕ} (hN : 0 < N)
    {lambdaWall : ℝ} (hlambda : 0 ≤ lambdaWall) (z : EVec N) :
    innerCertificate N lambdaWall z ≤
      ∑ i : Fin N, innerP N lambdaWall z i ^ 2 / innerD N i := by
  unfold innerCertificate
  apply Finset.sum_le_sum
  intro i _
  have ha := innerIncoming_nonneg hN z i
  have hb := innerForwardPos_nonneg hN z i
  have hc := innerWallPart_nonneg hN hlambda z i
  have hsq : innerIncoming N z i ^ 2 + innerForwardPos N z i ^ 2 +
      innerWallPart N lambdaWall z i ^ 2 ≤ innerP N lambdaWall z i ^ 2 := by
    unfold innerP
    nlinarith [mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc]
  exact div_le_div_of_nonneg_right hsq (innerD_pos hN i).le

theorem innerDualSq_gradient_eq (N : ℕ) (lambdaWall : ℝ) (z : EVec N) :
    innerDualSq N (innerGradient N lambdaWall z) =
      4 * ∑ i : Fin N,
        (innerP N lambdaWall z i - innerError N z i) ^ 2 / innerD N i := by
  unfold innerDualSq
  simp_rw [innerGradient_eq_P_sub_error]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem half_P_sq_sub_error_sq_le (p e d : ℝ) (hd : 0 ≤ d) :
    (p ^ 2 / 2 - e ^ 2) / d ≤ (p - e) ^ 2 / d := by
  apply div_le_div_of_nonneg_right _ hd
  nlinarith [sq_nonneg (p - 2 * e)]

/-- Absorption step in the paper.  Once the squared error is at most one
quarter of `S_N`, the actual gradient controls `S_N`. -/
theorem innerCertificate_le_gradient_of_error {N : ℕ} (hN : 0 < N)
    {lambdaWall : ℝ} (hlambda : 0 ≤ lambdaWall) (z : EVec N)
    (herror : (∑ i : Fin N, innerError N z i ^ 2 / innerD N i) ≤
      innerCertificate N lambdaWall z / 4) :
    innerCertificate N lambdaWall z ≤
      innerDualSq N (innerGradient N lambdaWall z) := by
  have hpoint :
      (∑ i : Fin N, (innerP N lambdaWall z i ^ 2 / 2 -
        innerError N z i ^ 2) / innerD N i) ≤
      ∑ i : Fin N, (innerP N lambdaWall z i - innerError N z i) ^ 2 /
        innerD N i := by
    apply Finset.sum_le_sum
    intro i _
    exact half_P_sq_sub_error_sq_le _ _ _ (innerD_pos hN i).le
  have hP := innerCertificate_le_P_dual hN hlambda z
  rw [innerDualSq_gradient_eq]
  have hrewrite :
      (∑ i : Fin N, (innerP N lambdaWall z i ^ 2 / 2 -
        innerError N z i ^ 2) / innerD N i) =
      (∑ i : Fin N, innerP N lambdaWall z i ^ 2 / innerD N i) / 2 -
        ∑ i : Fin N, innerError N z i ^ 2 / innerD N i := by
    have hhalf :
        (∑ i : Fin N, innerP N lambdaWall z i ^ 2 /
          (2 * innerD N i)) =
        (∑ i : Fin N, innerP N lambdaWall z i ^ 2 / innerD N i) / 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [sub_div, div_div]
    rw [Finset.sum_sub_distrib, hhalf]
  rw [hrewrite] at hpoint
  nlinarith

/-- Explicit pointwise estimate for the sole cancellation term. -/
theorem innerError_le {N : ℕ} (hN : 0 < N) (z : EVec N) (i : Fin N)
    (hi : i.1 + 1 < N) :
    innerError N z i ≤
      6 * innerAlpha N ⟨i.1 + 1, hi⟩ * negPart (z ⟨i.1 + 1, hi⟩) := by
  rw [innerError, dif_pos hi]
  let j : Fin N := ⟨i.1 + 1, hi⟩
  have hα : 0 ≤ innerAlpha N j := (innerAlpha_pos hN j).le
  have hD0 : 0 ≤ sigmaDeriv (z i) := sigmaDeriv_nonneg _
  have hD : sigmaDeriv (z i) ≤ 3 / 2 := sigmaDeriv_le_three_halves _
  have hB0 : 0 ≤ negPart (beta (z j)) := negPart_nonneg _
  have hB : negPart (beta (z j)) ≤ 2 * negPart (z j) :=
    negPart_beta_le_two_mul_negPart _
  have hv : 0 ≤ negPart (z j) := negPart_nonneg _
  have hr0 : 0 ≤ innerResidual z j := innerResidual_nonneg z j
  have hr : innerResidual z j ≤ 2 := innerResidual_le_two z j
  have hDB : sigmaDeriv (z i) * negPart (beta (z j)) ≤ 3 * negPart (z j) := by
    have := mul_le_mul hD hB hB0 (by norm_num : (0 : ℝ) ≤ 3 / 2)
    nlinarith
  calc
    innerAlpha N j * sigmaDeriv (z i) * negPart (beta (z j)) * innerResidual z j =
        innerAlpha N j * (sigmaDeriv (z i) * negPart (beta (z j))) *
          innerResidual z j := by ring
    _ ≤ innerAlpha N j * (3 * negPart (z j)) * innerResidual z j :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDB hα) hr0
    _ ≤ innerAlpha N j * (3 * negPart (z j)) * 2 :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg hα (mul_nonneg (by norm_num) hv))
    _ = 6 * innerAlpha N j * negPart (z j) := by ring

theorem innerError_sq_div_le {N : ℕ} (hN : 0 < N) (z : EVec N) (i : Fin N)
    (hi : i.1 + 1 < N) :
    innerError N z i ^ 2 / innerD N i ≤
      36 * innerD N ⟨i.1 + 1, hi⟩ * negPart (z ⟨i.1 + 1, hi⟩) ^ 2 := by
  let j : Fin N := ⟨i.1 + 1, hi⟩
  have he0 := innerError_nonneg hN z i
  have hb := innerError_le hN z i hi
  have hα0 : 0 ≤ innerAlpha N j := (innerAlpha_pos hN j).le
  have hv0 : 0 ≤ negPart (z j) := negPart_nonneg _
  have hsq : innerError N z i ^ 2 ≤
      (6 * innerAlpha N j * negPart (z j)) ^ 2 :=
    (sq_le_sq₀ he0 (mul_nonneg (mul_nonneg (by norm_num) hα0) hv0)).2 hb
  rw [innerD_castSucc hN i hi]
  calc
    innerError N z i ^ 2 / innerAlpha N j ≤
        (6 * innerAlpha N j * negPart (z j)) ^ 2 / innerAlpha N j :=
      div_le_div_of_nonneg_right hsq hα0
    _ = 36 * innerAlpha N j * negPart (z j) ^ 2 := by
      field_simp [ne_of_gt (innerAlpha_pos hN j)]
      <;> ring
    _ ≤ 36 * innerD N j * negPart (z j) ^ 2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (innerAlpha_le_innerD hN j) (by norm_num))
        (sq_nonneg _)

/-- Summed error estimate from the paper, with an explicit constant `36`. -/
theorem innerError_dual_le_wall {N : ℕ} (hN : 0 < N) (z : EVec N) :
    (∑ i : Fin N, innerError N z i ^ 2 / innerD N i) ≤
      36 * innerWallEnergy N z := by
  cases N with
  | zero => omega
  | succ k =>
      rw [Fin.sum_univ_castSucc]
      have hlast : innerError (k + 1) z (Fin.last k) ^ 2 /
          innerD (k + 1) (Fin.last k) = 0 := by
        simp [innerError]
      rw [hlast, add_zero]
      have hterm :
          (∑ i : Fin k, innerError (k + 1) z i.castSucc ^ 2 /
            innerD (k + 1) i.castSucc) ≤
          ∑ i : Fin k, 36 * innerD (k + 1) i.succ * negPart (z i.succ) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hil := i.isLt
        have hi : i.castSucc.1 + 1 < k + 1 := by simp
        have hj : (⟨i.castSucc.1 + 1, hi⟩ : Fin (k + 1)) = i.succ := by
          apply Fin.ext
          simp
        rw [← hj]
        exact innerError_sq_div_le hN z i.castSucc hi
      have hshift :
          (∑ i : Fin k, innerD (k + 1) i.succ * negPart (z i.succ) ^ 2) ≤
            innerWallEnergy (k + 1) z := by
        rw [innerWallEnergy, Fin.sum_univ_succ]
        have hzero : 0 ≤ innerD (k + 1) 0 * negPart (z 0) ^ 2 :=
          mul_nonneg (innerD_pos hN 0).le (sq_nonneg _)
        linarith
      calc
        (∑ i : Fin k, innerError (k + 1) z i.castSucc ^ 2 /
            innerD (k + 1) i.castSucc)
            ≤ ∑ i : Fin k, 36 * innerD (k + 1) i.succ *
              negPart (z i.succ) ^ 2 := hterm
        _ = 36 * ∑ i : Fin k, innerD (k + 1) i.succ *
              negPart (z i.succ) ^ 2 := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                ring
        _ ≤ 36 * innerWallEnergy (k + 1) z :=
          mul_le_mul_of_nonneg_left hshift (by norm_num)

theorem lambda_sq_wall_le_certificate {N : ℕ} (hN : 0 < N)
    (lambdaWall : ℝ) (z : EVec N) :
    lambdaWall ^ 2 * innerWallEnergy N z ≤ innerCertificate N lambdaWall z := by
  unfold innerWallEnergy innerCertificate
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hd := innerD_pos hN i
  have hwall : lambdaWall ^ 2 * (innerD N i * negPart (z i) ^ 2) =
      innerWallPart N lambdaWall z i ^ 2 / innerD N i := by
    unfold innerWallPart
    field_simp [ne_of_gt hd]
  rw [hwall]
  apply div_le_div_of_nonneg_right _ hd.le
  nlinarith [sq_nonneg (innerIncoming N z i), sq_nonneg (innerForwardPos N z i)]

theorem innerCertificate_coord_le {N : ℕ} (hN : 0 < N)
    (lambdaWall : ℝ) (z : EVec N) (i : Fin N) :
    (innerIncoming N z i ^ 2 + innerForwardPos N z i ^ 2 +
      innerWallPart N lambdaWall z i ^ 2) / innerD N i ≤
      innerCertificate N lambdaWall z := by
  unfold innerCertificate
  change
    (innerIncoming N z i ^ 2 + innerForwardPos N z i ^ 2 +
      innerWallPart N lambdaWall z i ^ 2) / innerD N i ≤
    Finset.univ.sum (fun j ↦
      (innerIncoming N z j ^ 2 + innerForwardPos N z j ^ 2 +
        innerWallPart N lambdaWall z j ^ 2) / innerD N j)
  simpa only using
    (Finset.single_le_sum
      (s := (Finset.univ : Finset (Fin N)))
      (f := fun j ↦
        (innerIncoming N z j ^ 2 + innerForwardPos N z j ^ 2 +
          innerWallPart N lambdaWall z j ^ 2) / innerD N j)
      (fun j _ ↦ div_nonneg (by positivity) (innerD_pos hN j).le)
      (Finset.mem_univ i))

private theorem incoming_sq_div_eq {N : ℕ} (hN : 0 < N)
    (z : EVec N) (i : Fin N) (hi : i.1 + 1 < N) :
    innerIncoming N z i ^ 2 / innerD N i =
      (N : ℝ)⁻¹ *
        (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 := by
  unfold innerIncoming
  rw [show
    (innerAlpha N i * sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 /
        innerD N i =
      (innerAlpha N i ^ 2 / innerD N i) *
        (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 by ring]
  rw [innerAlpha_sq_div_innerD hN i hi]

/-- The explicit crossing certificate used whenever the next residual is
closed.  The numerical lower bound is stronger than what the paper needs. -/
theorem crossing_certificate {N : ℕ} (hN : 0 < N) (z : EVec N)
    (i : Fin N) (hi : i.1 + 1 < N) {lambdaWall : ℝ}
    (hlambda : 12 ≤ lambdaWall)
    (hopen : (1 : ℝ) / 2 ≤ sigma (innerPrev z i))
    (hclosed : sigma (z i) < (1 : ℝ) / 2) :
    ((1 : ℝ) / 16) / (N : ℝ) ≤ innerCertificate N lambdaWall z := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hzlt : z i < (1 : ℝ) / 2 := sigma_lt_half_imp_lt_half hclosed
  have hcoord := innerCertificate_coord_le hN lambdaWall z i
  by_cases hz0 : 0 ≤ z i
  · have hbeta : beta (z i) = z i := beta_eq_self hz0 (by linarith)
    have hE : betaDeriv (z i) = 1 := by
      rcases hz0.eq_or_lt with hz | hz
      · rw [← hz]
        norm_num [betaDeriv]
      · simp [betaDeriv, show ¬z i ≤ -1 by linarith,
          show ¬z i ≤ 0 by linarith, show z i ≤ 1 by linarith]
    have hprod : sigma (innerPrev z i) * z i ≤ z i :=
      mul_le_of_le_one_left hz0 (sigma_le_one _)
    have hins : (1 : ℝ) / 2 ≤ 1 - sigma (innerPrev z i) * beta (z i) := by
      rw [hbeta]
      linarith
    have hr : innerResidual z i = 1 - sigma (innerPrev z i) * beta (z i) := by
      rw [innerResidual, gateResidual, posPart,
        max_eq_left (by linarith : 0 ≤ 1 - sigma (innerPrev z i) * beta (z i))]
    have hc : (1 : ℝ) / 4 ≤
        sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i := by
      rw [hE, hr]
      have := mul_le_mul hopen hins (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (sigma_nonneg _)
      nlinarith
    have hcsq : (1 : ℝ) / 16 ≤
        (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 := by
      nlinarith [sq_nonneg
        (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i - 1 / 4)]
    have hinc : ((1 : ℝ) / 16) / (N : ℝ) ≤
        innerIncoming N z i ^ 2 / innerD N i := by
      rw [incoming_sq_div_eq hN z i hi]
      rw [div_le_iff₀ hNreal]
      field_simp
      nlinarith
    have hlocal : innerIncoming N z i ^ 2 / innerD N i ≤
        (innerIncoming N z i ^ 2 + innerForwardPos N z i ^ 2 +
          innerWallPart N lambdaWall z i ^ 2) / innerD N i := by
      apply div_le_div_of_nonneg_right _ (innerD_pos hN i).le
      nlinarith [sq_nonneg (innerForwardPos N z i),
        sq_nonneg (innerWallPart N lambdaWall z i)]
    exact hinc.trans (hlocal.trans hcoord)
  · have hzneg : z i < 0 := lt_of_not_ge hz0
    by_cases hzfar : z i ≤ -(1 : ℝ) / 2
    · have hv : (1 : ℝ) / 2 ≤ negPart (z i) :=
        (by linarith : (1 : ℝ) / 2 ≤ -z i) |>.trans (le_max_left _ _)
      have hd : (N : ℝ)⁻¹ ≤ innerD N i := one_div_N_le_innerD hN i
      have hwallEq : innerWallPart N lambdaWall z i ^ 2 / innerD N i =
          lambdaWall ^ 2 * innerD N i * negPart (z i) ^ 2 := by
        unfold innerWallPart
        field_simp [ne_of_gt (innerD_pos hN i)]
      have hwall : ((1 : ℝ) / 16) / (N : ℝ) ≤
          innerWallPart N lambdaWall z i ^ 2 / innerD N i := by
        rw [hwallEq]
        have hl : 144 ≤ lambdaWall ^ 2 := by nlinarith
        have hv2 : (1 : ℝ) / 4 ≤ negPart (z i) ^ 2 := by
          nlinarith [sq_nonneg (negPart (z i) - 1 / 2)]
        have hmul := mul_le_mul hl hd (inv_nonneg.mpr hNreal.le) (sq_nonneg lambdaWall)
        have hnonneg : 0 ≤ lambdaWall ^ 2 * innerD N i :=
          mul_nonneg (sq_nonneg _) (innerD_pos hN i).le
        have hmul2 := mul_le_mul_of_nonneg_left hv2 hnonneg
        have hbase : ((1 : ℝ) / 16) / (N : ℝ) ≤
            (144 * (N : ℝ)⁻¹) * (1 / 4) := by
          field_simp
          norm_num
        have hmul3 : (144 * (N : ℝ)⁻¹) * (1 / 4) ≤
            (lambdaWall ^ 2 * innerD N i) * (1 / 4) :=
          mul_le_mul_of_nonneg_right hmul (by norm_num)
        exact hbase.trans (hmul3.trans hmul2)
      have hlocal : innerWallPart N lambdaWall z i ^ 2 / innerD N i ≤
          (innerIncoming N z i ^ 2 + innerForwardPos N z i ^ 2 +
            innerWallPart N lambdaWall z i ^ 2) / innerD N i := by
        apply div_le_div_of_nonneg_right _ (innerD_pos hN i).le
        nlinarith [sq_nonneg (innerIncoming N z i),
          sq_nonneg (innerForwardPos N z i)]
      exact hwall.trans (hlocal.trans hcoord)
    · have hm1 : ¬z i ≤ -1 := by linarith
      have hzle : z i ≤ 0 := hzneg.le
      have hE : (1 : ℝ) / 2 ≤ betaDeriv (z i) := by
        rw [betaDeriv, if_neg hm1, if_pos hzle]
        have hu0 : (1 : ℝ) / 2 < z i + 1 := by linarith
        have hu1 : z i + 1 ≤ 1 := by linarith
        have hf : 1 ≤ 4 - 3 * (z i + 1) := by linarith
        have := mul_le_mul hu0.le hf (by norm_num : (0 : ℝ) ≤ 1)
          (by linarith : 0 ≤ z i + 1)
        nlinarith
      have hbetaNonpos : beta (z i) ≤ 0 := by
        rw [beta]
        simp only [if_neg hm1, if_pos hzle]
        have hu0 : 0 ≤ z i + 1 := by linarith
        have hu1 : z i + 1 ≤ 1 := by linarith
        have hp : 0 ≤ (1 - (z i + 1)) *
            (1 + (z i + 1) - (z i + 1) ^ 2) := by
          apply mul_nonneg (by linarith)
          nlinarith [sq_nonneg (z i + 1)]
        nlinarith
      have hins : 1 ≤ 1 - sigma (innerPrev z i) * beta (z i) := by
        have := mul_nonpos_of_nonneg_of_nonpos
          (sigma_nonneg (innerPrev z i)) hbetaNonpos
        linarith
      have hr : innerResidual z i = 1 - sigma (innerPrev z i) * beta (z i) := by
        rw [innerResidual, gateResidual, posPart,
          max_eq_left (by linarith : 0 ≤ 1 - sigma (innerPrev z i) * beta (z i))]
      have hc : (1 : ℝ) / 4 ≤
          sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i := by
        rw [hr]
        have hAE := mul_le_mul hopen hE (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (sigma_nonneg _)
        have hAEnonneg : 0 ≤
            sigma (innerPrev z i) * betaDeriv (z i) :=
          mul_nonneg (sigma_nonneg (innerPrev z i)) (betaDeriv_nonneg (z i))
        have := mul_le_mul_of_nonneg_left hins hAEnonneg
        nlinarith
      have hcsq : (1 : ℝ) / 16 ≤
          (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 := by
        nlinarith [sq_nonneg
          (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i - 1 / 4)]
      have hinc : ((1 : ℝ) / 16) / (N : ℝ) ≤
          innerIncoming N z i ^ 2 / innerD N i := by
        rw [incoming_sq_div_eq hN z i hi]
        rw [div_le_iff₀ hNreal]
        field_simp
        nlinarith
      have hlocal : innerIncoming N z i ^ 2 / innerD N i ≤
          (innerIncoming N z i ^ 2 + innerForwardPos N z i ^ 2 +
            innerWallPart N lambdaWall z i ^ 2) / innerD N i := by
        apply div_le_div_of_nonneg_right _ (innerD_pos hN i).le
        nlinarith [sq_nonneg (innerForwardPos N z i),
          sq_nonneg (innerWallPart N lambdaWall z i)]
      exact hinc.trans (hlocal.trans hcoord)

/-- Choosing the paper's wall coefficient at least `12` absorbs all possible
cancellation and makes the gradient dominate the certificate. -/
theorem innerCertificate_le_gradient {N : ℕ} (hN : 0 < N)
    {lambdaWall : ℝ} (hlambda : 12 ≤ lambdaWall) (z : EVec N) :
    innerCertificate N lambdaWall z ≤
      innerDualSq N (innerGradient N lambdaWall z) := by
  apply innerCertificate_le_gradient_of_error hN (by linarith) z
  have herr := innerError_dual_le_wall hN z
  have hwall := lambda_sq_wall_le_certificate hN lambdaWall z
  have henergy : 0 ≤ innerWallEnergy N z := by
    unfold innerWallEnergy
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (innerD_pos hN i).le (sq_nonneg _)
  have hlambdaSq : 144 ≤ lambdaWall ^ 2 := by nlinarith
  nlinarith

end

end NCPLVerification
