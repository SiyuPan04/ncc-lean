import NCPLVerification.InnerCertificate

/-!
# Value control for the inner PL chain

This file proves the second half of the PL argument: the value of the inner
chain is controlled by `N` times the gradient certificate.  All constants are
explicit.  In particular, no compactness argument is left implicit.
-/

namespace NCPLVerification

noncomputable section

def innerResidualEnergy (N : ℕ) (z : EVec N) : ℝ :=
  ∑ i : Fin N, innerAlpha N i * innerResidual z i ^ 2

/-- The part of the global certificate naturally charged to residual `i`.
For a noninitial residual, its predecessor derivative is stored in the
preceding gradient coordinate. -/
def innerResidualLocalCertificate (N : ℕ) (lambdaWall : ℝ)
    (z : EVec N) (i : Fin N) : ℝ :=
  innerIncoming N z i ^ 2 / innerD N i +
    (if hi : 0 < i.1 then
      innerForwardPos N z ⟨i.1 - 1, by omega⟩ ^ 2 /
        innerD N ⟨i.1 - 1, by omega⟩
    else 0) +
    innerWallPart N lambdaWall z i ^ 2 / innerD N i

theorem innerResidualEnergy_le_twelve {N : ℕ} (hN : 0 < N)
    (z : EVec N) : innerResidualEnergy N z ≤ 12 := by
  unfold innerResidualEnergy
  calc
    (∑ i : Fin N, innerAlpha N i * innerResidual z i ^ 2) ≤
        ∑ i : Fin N, 4 * innerAlpha N i := by
          apply Finset.sum_le_sum
          intro i _
          have hr0 := innerResidual_nonneg z i
          have hr2 := innerResidual_le_two z i
          have ha := (innerAlpha_pos hN i).le
          have hrsq : innerResidual z i ^ 2 ≤ 4 := by nlinarith
          simpa [mul_comm] using mul_le_mul_of_nonneg_left hrsq ha
    _ = 4 * ∑ i : Fin N, innerAlpha N i := by
          rw [Finset.mul_sum]
    _ ≤ 4 * 3 := mul_le_mul_of_nonneg_left (sum_innerAlpha_le_three hN) (by norm_num)
    _ = 12 := by norm_num

theorem innerResidualLocalCertificate_nonneg {N : ℕ} (hN : 0 < N)
    (lambdaWall : ℝ) (z : EVec N) (i : Fin N) :
    0 ≤ innerResidualLocalCertificate N lambdaWall z i := by
  unfold innerResidualLocalCertificate
  split_ifs with hi
  · exact add_nonneg
      (add_nonneg
        (div_nonneg (sq_nonneg _) (innerD_pos hN i).le)
        (div_nonneg (sq_nonneg _) (innerD_pos hN _).le))
      (div_nonneg (sq_nonneg _) (innerD_pos hN i).le)
  · exact add_nonneg
      (add_nonneg (div_nonneg (sq_nonneg _) (innerD_pos hN i).le) (by norm_num))
      (div_nonneg (sq_nonneg _) (innerD_pos hN i).le)

private theorem incoming_sq_div_formula {N : ℕ} (hN : 0 < N)
    (z : EVec N) (i : Fin N) :
    innerIncoming N z i ^ 2 / innerD N i =
      (innerAlpha N i ^ 2 / innerD N i) *
        (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 := by
  unfold innerIncoming
  ring

/-- The incoming observable has enough coefficient at every coordinate,
including the separately treated terminal coordinate. -/
theorem alpha_incoming_observable_le {N : ℕ} (hN2 : 2 ≤ N)
    (z : EVec N) (i : Fin N) :
    innerAlpha N i *
        (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 ≤
      (N : ℝ) * (innerIncoming N z i ^ 2 / innerD N i) := by
  have hN : 0 < N := by omega
  rw [incoming_sq_div_formula hN]
  by_cases hi : i.1 + 1 < N
  · rw [innerAlpha_sq_div_innerD hN i hi]
    have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
    have ha := innerAlpha_le_one hN i
    have hsq : 0 ≤
        (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 :=
      sq_nonneg _
    calc
      innerAlpha N i *
          (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 ≤
        1 * (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 :=
          mul_le_mul_of_nonneg_right ha hsq
      _ = (N : ℝ) * ((N : ℝ)⁻¹ *
          (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2) := by
            field_simp
  · have hiterm : i.1 = N - 1 := by omega
    have halpha : innerAlpha N i = 1 := by
      unfold innerAlpha
      simp [hiterm]
    have hd : innerD N i = 1 := by
      have hk : N - 2 - i.1 = 0 := by omega
      simp [innerD, hk]
    rw [halpha, hd]
    have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    nlinarith [sq_nonneg
      (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i)]

private theorem predecessor_forward_formula {N : ℕ} (hN : 0 < N)
    (z : EVec N) (i : Fin N) (hi : 0 < i.1) :
    innerForwardPos N z ⟨i.1 - 1, by omega⟩ ^ 2 /
        innerD N ⟨i.1 - 1, by omega⟩ =
      innerAlpha N i *
        (sigmaDeriv (innerPrev z i) * posPart (beta (z i)) *
          innerResidual z i) ^ 2 := by
  have hnext : (i.1 - 1) + 1 < N := by omega
  have hprev : innerPrev z i = z ⟨i.1 - 1, by omega⟩ := by
    simp [innerPrev, ne_of_gt hi]
  have hidx : (⟨(i.1 - 1) + 1, hnext⟩ : Fin N) = i := by
    apply Fin.ext
    exact Nat.sub_add_cancel hi
  rw [innerForwardPos, dif_pos hnext]
  simp only [hidx]
  rw [show
    (innerAlpha N i * sigmaDeriv (z ⟨i.1 - 1, by omega⟩) *
        posPart (beta (z i)) * innerResidual z i) ^ 2 /
          innerD N ⟨i.1 - 1, by omega⟩ =
      (innerAlpha N i ^ 2 / innerD N ⟨i.1 - 1, by omega⟩) *
        (sigmaDeriv (z ⟨i.1 - 1, by omega⟩) * posPart (beta (z i)) *
          innerResidual z i) ^ 2 by ring]
  rw [innerAlpha_sq_div_innerD_prev hN i hi, hprev]

private theorem initial_predecessor_observable_zero {N : ℕ}
    (z : EVec N) (i : Fin N) (hi : ¬0 < i.1) :
    sigmaDeriv (innerPrev z i) * posPart (beta (z i)) *
        innerResidual z i = 0 := by
  have hi0 : i.1 = 0 := by omega
  simp [innerPrev, hi0, sigmaDeriv]

private theorem wall_observable_le {N : ℕ} (hN : 0 < N)
    {lambdaWall : ℝ} (hlambda : 1 ≤ lambdaWall) (z : EVec N) (i : Fin N) :
    innerAlpha N i * negPart (z i) ^ 2 ≤
      innerWallPart N lambdaWall z i ^ 2 / innerD N i := by
  have ha := innerAlpha_le_innerD hN i
  have hd := innerD_pos hN i
  have hl : 1 ≤ lambdaWall ^ 2 := by nlinarith
  rw [innerWallPart]
  field_simp [ne_of_gt hd]
  have hv := sq_nonneg (negPart (z i))
  nlinarith [mul_nonneg hd.le hv]

/-- Open-gate observability with all coefficient conversions made explicit. -/
theorem open_residual_value_le_local {N : ℕ} (hN2 : 2 ≤ N)
    {lambdaWall : ℝ} (hlambda : 1 ≤ lambdaWall) (z : EVec N) (i : Fin N)
    (hopen : (1 : ℝ) / 2 ≤ sigma (innerPrev z i)) :
    innerAlpha N i * innerResidual z i ^ 2 ≤
      64 * (N : ℝ) * innerResidualLocalCertificate N lambdaWall z i := by
  have hN : 0 < N := by omega
  have hobs := open_gate_observability (innerPrev z i) (z i) hopen
  change innerResidual z i ^ 2 ≤ 64 *
    ((sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 +
      (sigmaDeriv (innerPrev z i) * posPart (beta (z i)) * innerResidual z i) ^ 2 +
      negPart (z i) ^ 2) at hobs
  have ha0 := (innerAlpha_pos hN i).le
  have hscaled := mul_le_mul_of_nonneg_left hobs ha0
  have hscaled' : innerAlpha N i * innerResidual z i ^ 2 ≤ 64 *
      (innerAlpha N i *
          (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 +
       innerAlpha N i *
          (sigmaDeriv (innerPrev z i) * posPart (beta (z i)) *
            innerResidual z i) ^ 2 +
       innerAlpha N i * negPart (z i) ^ 2) := by
    calc
      innerAlpha N i * innerResidual z i ^ 2 ≤
          innerAlpha N i * (64 *
            ((sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 +
             (sigmaDeriv (innerPrev z i) * posPart (beta (z i)) *
                innerResidual z i) ^ 2 + negPart (z i) ^ 2)) := hscaled
      _ = _ := by ring
  have hin := alpha_incoming_observable_le hN2 z i
  have hwall := wall_observable_le hN hlambda z i
  by_cases hi : 0 < i.1
  · have hfor := predecessor_forward_formula hN z i hi
    rw [innerResidualLocalCertificate, dif_pos hi]
    have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hfor0 : 0 ≤ innerForwardPos N z ⟨i.1 - 1, by omega⟩ ^ 2 /
        innerD N ⟨i.1 - 1, by omega⟩ :=
      div_nonneg (sq_nonneg _) (innerD_pos hN _).le
    have hforBound : innerAlpha N i *
        (sigmaDeriv (innerPrev z i) * posPart (beta (z i)) *
          innerResidual z i) ^ 2 ≤
        (N : ℝ) * (innerForwardPos N z ⟨i.1 - 1, by omega⟩ ^ 2 /
          innerD N ⟨i.1 - 1, by omega⟩) := by
      rw [← hfor]
      exact le_mul_of_one_le_left hfor0 hNreal
    have hwall0 : 0 ≤ innerWallPart N lambdaWall z i ^ 2 / innerD N i :=
      div_nonneg (sq_nonneg _) (innerD_pos hN i).le
    have hwallBound : innerAlpha N i * negPart (z i) ^ 2 ≤
        (N : ℝ) * (innerWallPart N lambdaWall z i ^ 2 / innerD N i) :=
      hwall.trans (le_mul_of_one_le_left hwall0 hNreal)
    have hsum :
        innerAlpha N i *
            (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 +
          innerAlpha N i *
            (sigmaDeriv (innerPrev z i) * posPart (beta (z i)) *
              innerResidual z i) ^ 2 +
          innerAlpha N i * negPart (z i) ^ 2 ≤
        (N : ℝ) *
          (innerIncoming N z i ^ 2 / innerD N i +
           innerForwardPos N z ⟨i.1 - 1, by omega⟩ ^ 2 /
             innerD N ⟨i.1 - 1, by omega⟩ +
           innerWallPart N lambdaWall z i ^ 2 / innerD N i) := by
      linarith
    exact hscaled'.trans (by nlinarith)
  · have hzero := initial_predecessor_observable_zero z i hi
    rw [innerResidualLocalCertificate, dif_neg hi]
    have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
    have hwall0 : 0 ≤ innerWallPart N lambdaWall z i ^ 2 / innerD N i :=
      div_nonneg (sq_nonneg _) (innerD_pos hN i).le
    have hwallBound : innerAlpha N i * negPart (z i) ^ 2 ≤
        (N : ℝ) * (innerWallPart N lambdaWall z i ^ 2 / innerD N i) :=
      hwall.trans (le_mul_of_one_le_left hwall0 hNreal)
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hscaled'
    have hsum :
        innerAlpha N i *
            (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i) ^ 2 +
          0 + innerAlpha N i * negPart (z i) ^ 2 ≤
        (N : ℝ) *
          (innerIncoming N z i ^ 2 / innerD N i + 0 +
           innerWallPart N lambdaWall z i ^ 2 / innerD N i) := by
      linarith
    exact hscaled'.trans (by nlinarith)

private theorem sum_predecessor_shift {n : ℕ} (f : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), if hi : 0 < i.1 then
        f ⟨i.1 - 1, by omega⟩ else 0) =
      ∑ j : Fin n, f j.castSucc := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, lt_self_iff_false, ↓reduceDIte, Fin.val_succ,
    Nat.zero_lt_succ, zero_add]
  apply Fintype.sum_congr
  intro j
  congr 1

private theorem sum_predecessor_forward_eq {N : ℕ} (z : EVec N) :
    (∑ i : Fin N, if hi : 0 < i.1 then
        innerForwardPos N z ⟨i.1 - 1, by omega⟩ ^ 2 /
          innerD N ⟨i.1 - 1, by omega⟩ else 0) =
      ∑ j : Fin N, innerForwardPos N z j ^ 2 / innerD N j := by
  cases N with
  | zero => simp
  | succ n =>
      have hshift := sum_predecessor_shift
        (fun j : Fin (n + 1) ↦
          innerForwardPos (n + 1) z j ^ 2 / innerD (n + 1) j)
      rw [hshift]
      rw [Fin.sum_univ_castSucc]
      have hterminal : innerForwardPos (n + 1) z (Fin.last n) = 0 := by
        unfold innerForwardPos
        simp
      rw [hterminal]
      simp

/-- Charging every residual once recovers exactly the global certificate. -/
theorem sum_innerResidualLocalCertificate {N : ℕ} (lambdaWall : ℝ)
    (z : EVec N) :
    (∑ i : Fin N, innerResidualLocalCertificate N lambdaWall z i) =
      innerCertificate N lambdaWall z := by
  unfold innerResidualLocalCertificate innerCertificate
  calc
    (∑ i : Fin N, (
        innerIncoming N z i ^ 2 / innerD N i +
          (if hi : 0 < i.1 then
            innerForwardPos N z ⟨i.1 - 1, by omega⟩ ^ 2 /
              innerD N ⟨i.1 - 1, by omega⟩ else 0) +
          innerWallPart N lambdaWall z i ^ 2 / innerD N i)) =
        (∑ i : Fin N, innerIncoming N z i ^ 2 / innerD N i) +
        (∑ i : Fin N, innerForwardPos N z i ^ 2 / innerD N i) +
        (∑ i : Fin N, innerWallPart N lambdaWall z i ^ 2 / innerD N i) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            sum_predecessor_forward_eq]
    _ = ∑ i : Fin N,
        (innerIncoming N z i ^ 2 + innerForwardPos N z i ^ 2 +
          innerWallPart N lambdaWall z i ^ 2) / innerD N i := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          ring

theorem innerResidualLocalCertificate_le {N : ℕ} (hN : 0 < N)
    (lambdaWall : ℝ) (z : EVec N) (i : Fin N) :
    innerResidualLocalCertificate N lambdaWall z i ≤
      innerCertificate N lambdaWall z := by
  rw [← sum_innerResidualLocalCertificate]
  exact Finset.single_le_sum
    (fun j _ ↦ innerResidualLocalCertificate_nonneg hN lambdaWall z j)
    (Finset.mem_univ i)

theorem innerResidualEnergy_le_certificate_of_all_open {N : ℕ}
    (hN2 : 2 ≤ N) {lambdaWall : ℝ} (hlambda : 1 ≤ lambdaWall)
    (z : EVec N)
    (hopen : ∀ i : Fin N, (1 : ℝ) / 2 ≤ sigma (innerPrev z i)) :
    innerResidualEnergy N z ≤
      64 * (N : ℝ) * innerCertificate N lambdaWall z := by
  unfold innerResidualEnergy
  calc
    (∑ i : Fin N, innerAlpha N i * innerResidual z i ^ 2) ≤
        ∑ i : Fin N,
          64 * (N : ℝ) * innerResidualLocalCertificate N lambdaWall z i := by
            apply Finset.sum_le_sum
            intro i _
            exact open_residual_value_le_local hN2 hlambda z i (hopen i)
    _ = 64 * (N : ℝ) *
        (∑ i : Fin N, innerResidualLocalCertificate N lambdaWall z i) := by
          simp only [Finset.mul_sum]
    _ = 64 * (N : ℝ) * innerCertificate N lambdaWall z := by
          rw [sum_innerResidualLocalCertificate]

private theorem exists_crossing_before {N : ℕ} (z : EVec N) (k : Fin N)
    (hk : k.1 + 1 < N) (hclosed : sigma (z k) < (1 : ℝ) / 2) :
    ∃ j : Fin N, j.1 ≤ k.1 ∧ j.1 + 1 < N ∧
      (1 : ℝ) / 2 ≤ sigma (innerPrev z j) ∧
      sigma (z j) < (1 : ℝ) / 2 := by
  have aux : ∀ n : ℕ, (hnN : n + 1 < N) →
      sigma (z ⟨n, by omega⟩) < (1 : ℝ) / 2 →
      ∃ j : Fin N, j.1 ≤ n ∧ j.1 + 1 < N ∧
        (1 : ℝ) / 2 ≤ sigma (innerPrev z j) ∧
        sigma (z j) < (1 : ℝ) / 2 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro hnN hnclosed
        by_cases hn0 : n = 0
        · let j : Fin N := ⟨n, by omega⟩
          refine ⟨j, le_rfl, hnN, ?_, hnclosed⟩
          have hjprev : innerPrev z j = 1 := by simp [j, innerPrev, hn0]
          rw [hjprev]
          norm_num [sigma]
        · let p : Fin N := ⟨n - 1, by omega⟩
          by_cases hopen : (1 : ℝ) / 2 ≤ sigma (z p)
          · let j : Fin N := ⟨n, by omega⟩
            refine ⟨j, le_rfl, hnN, ?_, hnclosed⟩
            have hprev : innerPrev z j = z p := by
              simp [innerPrev, j, p, hn0]
            simpa [hprev] using hopen
          · have hpclosed : sigma (z p) < (1 : ℝ) / 2 := lt_of_not_ge hopen
            obtain ⟨j, hjn, hjN, hjopen, hjclosed⟩ :=
              ih (n - 1) (by omega) (by omega) hpclosed
            exact ⟨j, by omega, hjN, hjopen, hjclosed⟩
  simpa only using aux k.1 hk hclosed

/-- If even one residual is closed, a preceding open-to-closed crossing gives
a fixed `1/(16N)` amount of certificate. -/
theorem innerCertificate_lower_of_not_all_open {N : ℕ} (hN2 : 2 ≤ N)
    {lambdaWall : ℝ} (hlambda : 12 ≤ lambdaWall) (z : EVec N)
    (hnot : ¬∀ i : Fin N, (1 : ℝ) / 2 ≤ sigma (innerPrev z i)) :
    ((1 : ℝ) / 16) / (N : ℝ) ≤ innerCertificate N lambdaWall z := by
  have hN : 0 < N := by omega
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  have hi0 : i.1 ≠ 0 := by
    intro heq
    have hprev : innerPrev z i = 1 := by simp [innerPrev, heq]
    have : sigma (innerPrev z i) = 1 := by rw [hprev]; norm_num [sigma]
    linarith
  let k : Fin N := ⟨i.1 - 1, by omega⟩
  have hkN : k.1 + 1 < N := by
    dsimp [k]
    omega
  have hkclosed : sigma (z k) < (1 : ℝ) / 2 := by
    have hprev : innerPrev z i = z k := by
      simp [innerPrev, k, hi0]
    simpa [hprev] using hi
  obtain ⟨j, hjle, hjN, hjopen, hjclosed⟩ :=
    exists_crossing_before z k hkN hkclosed
  exact crossing_certificate hN z j hjN hlambda hjopen hjclosed

theorem innerResidualEnergy_le_certificate_of_closed {N : ℕ}
    (hN2 : 2 ≤ N) {lambdaWall : ℝ} (hlambda : 12 ≤ lambdaWall)
    (z : EVec N)
    (hnot : ¬∀ i : Fin N, (1 : ℝ) / 2 ≤ sigma (innerPrev z i)) :
    innerResidualEnergy N z ≤
      192 * (N : ℝ) * innerCertificate N lambdaWall z := by
  have hN : 0 < N := by omega
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hcert := innerCertificate_lower_of_not_all_open hN2 hlambda z hnot
  calc
    innerResidualEnergy N z ≤ 12 := innerResidualEnergy_le_twelve hN z
    _ = 192 * (N : ℝ) * (((1 : ℝ) / 16) / (N : ℝ)) := by
          field_simp
          norm_num
    _ ≤ 192 * (N : ℝ) * innerCertificate N lambdaWall z := by
          exact mul_le_mul_of_nonneg_left hcert (by positivity)

/-- Uniform residual-value control, combining the all-open estimate with the
explicit crossing estimate. -/
theorem innerResidualEnergy_le_certificate {N : ℕ} (hN2 : 2 ≤ N)
    {lambdaWall : ℝ} (hlambda : 12 ≤ lambdaWall) (z : EVec N) :
    innerResidualEnergy N z ≤
      192 * (N : ℝ) * innerCertificate N lambdaWall z := by
  by_cases hopen : ∀ i : Fin N, (1 : ℝ) / 2 ≤ sigma (innerPrev z i)
  · have h64 := innerResidualEnergy_le_certificate_of_all_open hN2
      (by linarith : (1 : ℝ) ≤ lambdaWall) z hopen
    have hN : 0 < N := by omega
    have hcert := innerCertificate_nonneg hN lambdaWall z
    nlinarith
  · exact innerResidualEnergy_le_certificate_of_closed hN2 hlambda z hopen

theorem innerWallValue_le_certificate {N : ℕ} (hN : 0 < N)
    {lambdaWall : ℝ} (hlambda : 1 ≤ lambdaWall) (z : EVec N) :
    lambdaWall * innerWallEnergy N z ≤ innerCertificate N lambdaWall z := by
  have henergy : 0 ≤ innerWallEnergy N z := by
    unfold innerWallEnergy
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (innerD_pos hN i).le (sq_nonneg _)
  have hlinear : lambdaWall * innerWallEnergy N z ≤
      lambdaWall ^ 2 * innerWallEnergy N z := by
    have : lambdaWall ≤ lambdaWall ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this henergy
  exact hlinear.trans (lambda_sq_wall_le_certificate hN lambdaWall z)

/-- Explicit value-certificate inequality `H_N ≤ 193 N S_N`. -/
theorem innerH_le_certificate {N : ℕ} (hN2 : 2 ≤ N)
    {lambdaWall : ℝ} (hlambda : 12 ≤ lambdaWall) (z : EVec N) :
    innerH N lambdaWall z ≤
      193 * (N : ℝ) * innerCertificate N lambdaWall z := by
  have hN : 0 < N := by omega
  have hres := innerResidualEnergy_le_certificate hN2 hlambda z
  have hwall := innerWallValue_le_certificate hN
    (by linarith : (1 : ℝ) ≤ lambdaWall) z
  have hcert := innerCertificate_nonneg hN lambdaWall z
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  change innerResidualEnergy N z + lambdaWall * innerWallEnergy N z ≤ _
  nlinarith

/-- Part (b) of Lemma 3.1 for the explicit gradient field, with
`c_H = 1/386`. -/
theorem inner_PL_field {N : ℕ} (hN2 : 2 ≤ N)
    {lambdaWall : ℝ} (hlambda : 12 ≤ lambdaWall) (z : EVec N) :
    (1 : ℝ) / 2 * innerDualSq N (innerGradient N lambdaWall z) ≥
      ((1 : ℝ) / 386) / (N : ℝ) * innerH N lambdaWall z := by
  have hN : 0 < N := by omega
  have hvalue := innerH_le_certificate hN2 hlambda z
  have hgrad := innerCertificate_le_gradient hN hlambda z
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    ((1 : ℝ) / 386) / (N : ℝ) * innerH N lambdaWall z =
        innerH N lambdaWall z / (386 * (N : ℝ)) := by ring
    _ ≤ (193 * (N : ℝ) * innerCertificate N lambdaWall z) /
        (386 * (N : ℝ)) := by
          exact div_le_div_of_nonneg_right hvalue (by positivity)
    _ = innerCertificate N lambdaWall z / 2 := by
          field_simp
          ring
    _ ≤ innerDualSq N (innerGradient N lambdaWall z) / 2 := by
          exact div_le_div_of_nonneg_right hgrad (by norm_num)
    _ = (1 : ℝ) / 2 * innerDualSq N (innerGradient N lambdaWall z) := by ring

end

end NCPLVerification
