import NCPLVerification.GateSmoothness
import NCPLVerification.InnerCertificate

/-!
# Dimension-free weighted smoothness of the inner chain

The metric weights used in the PL certificate also control the variation of
the true gradient.  This file makes the paper's uniform smoothness assertion
quantitative: the constant below is independent of the chain length `N`.
-/

namespace NCPLVerification

noncomputable section

/-- The squared primal norm dual to `innerDualSq`. -/
def innerPrimalSq (N : Nat) (h : EVec N) : ℝ :=
  ∑ i : Fin N, innerD N i * h i ^ 2

theorem innerPrimalSq_nonneg {N : Nat} (hN : 0 < N) (h : EVec N) :
    0 ≤ innerPrimalSq N h := by
  unfold innerPrimalSq
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (innerD_pos hN i).le (sq_nonneg _)

private theorem abs_triple_sub_le (a b c a' b' c' : ℝ) :
    |a * b * c - a' * b' * c'| ≤
      |a - a'| * |b| * |c| + |a'| * |b - b'| * |c| +
        |a'| * |b'| * |c - c'| := by
  have heq : a * b * c - a' * b' * c' =
      (a - a') * b * c + a' * (b - b') * c +
        a' * b' * (c - c') := by ring
  rw [heq]
  calc
    |(a - a') * b * c + a' * (b - b') * c +
        a' * b' * (c - c')| ≤
        |(a - a') * b * c + a' * (b - b') * c| +
          |a' * b' * (c - c')| := abs_add_le _ _
    _ ≤ (|(a - a') * b * c| + |a' * (b - b') * c|) +
          |a' * b' * (c - c')| := by
            gcongr
            exact abs_add_le _ _
    _ = _ := by repeat' rw [abs_mul]

theorem innerPrev_abs_sub_le {N : Nat} (z w : EVec N) (i : Fin N) :
    |innerPrev z i - innerPrev w i| ≤
      if hi : i.1 = 0 then 0 else |z ⟨i.1 - 1, by omega⟩ - w ⟨i.1 - 1, by omega⟩| := by
  by_cases hi : i.1 = 0 <;> simp [innerPrev, hi]

theorem innerResidual_abs_sub_le {N : Nat} (z w : EVec N) (i : Fin N) :
    |innerResidual z i - innerResidual w i| ≤
      4 * |innerPrev z i - innerPrev w i| + 2 * |z i - w i| := by
  exact gateResidual_abs_sub_le _ _ _ _

/-- Coordinatewise Lipschitz estimate for the incoming residual term. -/
theorem innerIncoming_abs_sub_le {N : Nat} (hN : 0 < N)
    (z w : EVec N) (i : Fin N) :
    |innerIncoming N z i - innerIncoming N w i| ≤
      innerAlpha N i *
        (16 * |innerPrev z i - innerPrev w i| + 20 * |z i - w i|) := by
  let p := |innerPrev z i - innerPrev w i|
  let q := |z i - w i|
  let r := innerResidual z i
  let r' := innerResidual w i
  have hp : 0 ≤ p := abs_nonneg _
  have hq : 0 ≤ q := abs_nonneg _
  have hs := sigma_abs_sub_le (innerPrev z i) (innerPrev w i)
  have hb := betaDeriv_abs_sub_le (z i) (w i)
  have hr := innerResidual_abs_sub_le z w i
  have hsig : |sigma (innerPrev w i)| ≤ 1 := sigma_abs_le_one _
  have hbd : |betaDeriv (z i)| ≤ 2 := by
    rw [abs_of_nonneg (betaDeriv_nonneg _)]
    exact betaDeriv_le_two _
  have hbd' : |betaDeriv (w i)| ≤ 2 := by
    rw [abs_of_nonneg (betaDeriv_nonneg _)]
    exact betaDeriv_le_two _
  have hres : |r| ≤ 2 := by
    rw [abs_of_nonneg (innerResidual_nonneg z i)]
    exact innerResidual_le_two z i
  have htri := abs_triple_sub_le
    (sigma (innerPrev z i)) (betaDeriv (z i)) r
    (sigma (innerPrev w i)) (betaDeriv (w i)) r'
  have ht1 :
      |sigma (innerPrev z i) - sigma (innerPrev w i)| *
          |betaDeriv (z i)| * |r| ≤ 8 * p := by
    calc
      _ ≤ (2 * p) * 2 * 2 := by gcongr
      _ = 8 * p := by ring
  have ht2 :
      |sigma (innerPrev w i)| * |betaDeriv (z i) - betaDeriv (w i)| *
          |r| ≤ 16 * q := by
    calc
      _ ≤ 1 * (8 * q) * 2 := by gcongr
      _ = 16 * q := by ring
  have ht3 :
      |sigma (innerPrev w i)| * |betaDeriv (w i)| * |r - r'| ≤
        8 * p + 4 * q := by
    calc
      _ ≤ 1 * 2 * (4 * p + 2 * q) := by gcongr
      _ = 8 * p + 4 * q := by ring
  have hcore :
      |sigma (innerPrev z i) * betaDeriv (z i) * r -
          sigma (innerPrev w i) * betaDeriv (w i) * r'| ≤
        16 * p + 20 * q := by
    exact htri.trans (by linarith)
  have ha0 : 0 ≤ innerAlpha N i := (innerAlpha_pos hN i).le
  unfold innerIncoming
  rw [show innerAlpha N i *
      sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i -
      innerAlpha N i * sigma (innerPrev w i) * betaDeriv (w i) *
        innerResidual w i =
      innerAlpha N i *
      (sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i -
       sigma (innerPrev w i) * betaDeriv (w i) * innerResidual w i) by ring,
    abs_mul, abs_of_nonneg ha0]
  exact mul_le_mul_of_nonneg_left hcore ha0

/-- Coordinatewise Lipschitz estimate for the forward residual term. -/
theorem innerForward_abs_sub_le {N : Nat} (hN : 0 < N)
    (z w : EVec N) (i : Fin N) :
    |innerForward N z i - innerForward N w i| ≤
      if hi : i.1 + 1 < N then
        innerAlpha N ⟨i.1 + 1, hi⟩ *
          (36 * |z i - w i| +
            12 * |z ⟨i.1 + 1, hi⟩ - w ⟨i.1 + 1, hi⟩|)
      else 0 := by
  by_cases hi : i.1 + 1 < N
  · rw [dif_pos hi]
    let j : Fin N := ⟨i.1 + 1, hi⟩
    let p := |z i - w i|
    let q := |z j - w j|
    let r := innerResidual z j
    let r' := innerResidual w j
    have hp : 0 ≤ p := abs_nonneg _
    have hq : 0 ≤ q := abs_nonneg _
    have hs := sigmaDeriv_abs_sub_le (z i) (w i)
    have hb := beta_abs_sub_le (z j) (w j)
    have hr0 := innerResidual_abs_sub_le z w j
    have hprevj : innerPrev z j = z i := by
      simp [innerPrev, j]
    have hprevj' : innerPrev w j = w i := by
      simp [innerPrev, j]
    have hr : |r - r'| ≤ 4 * p + 2 * q := by
      simpa [r, r', p, q, hprevj, hprevj'] using hr0
    have hsd' : |sigmaDeriv (w i)| ≤ 3 / 2 := by
      rw [abs_of_nonneg (sigmaDeriv_nonneg _)]
      exact sigmaDeriv_le_three_halves _
    have hbeta : |beta (z j)| ≤ 2 := beta_abs_le_two _
    have hbeta' : |beta (w j)| ≤ 2 := beta_abs_le_two _
    have hres : |r| ≤ 2 := by
      rw [abs_of_nonneg (innerResidual_nonneg z j)]
      exact innerResidual_le_two z j
    have htri := abs_triple_sub_le
      (sigmaDeriv (z i)) (beta (z j)) r
      (sigmaDeriv (w i)) (beta (w j)) r'
    have ht1 :
        |sigmaDeriv (z i) - sigmaDeriv (w i)| * |beta (z j)| * |r| ≤
          24 * p := by
      calc
        _ ≤ (6 * p) * 2 * 2 := by gcongr
        _ = 24 * p := by ring
    have ht2 :
        |sigmaDeriv (w i)| * |beta (z j) - beta (w j)| * |r| ≤
          6 * q := by
      calc
        _ ≤ (3 / 2 : ℝ) * (2 * q) * 2 := by gcongr
        _ = 6 * q := by ring
    have ht3 :
        |sigmaDeriv (w i)| * |beta (w j)| * |r - r'| ≤
          12 * p + 6 * q := by
      calc
        _ ≤ (3 / 2 : ℝ) * 2 * (4 * p + 2 * q) := by gcongr
        _ = 12 * p + 6 * q := by ring
    have hcore :
        |sigmaDeriv (z i) * beta (z j) * r -
            sigmaDeriv (w i) * beta (w j) * r'| ≤
          36 * p + 12 * q := by
      exact htri.trans (by linarith)
    have ha0 : 0 ≤ innerAlpha N j := (innerAlpha_pos hN j).le
    rw [innerForward, dif_pos hi, innerForward, dif_pos hi]
    rw [show innerAlpha N ⟨i.1 + 1, hi⟩ * sigmaDeriv (z i) *
        beta (z ⟨i.1 + 1, hi⟩) * innerResidual z ⟨i.1 + 1, hi⟩ -
        innerAlpha N ⟨i.1 + 1, hi⟩ * sigmaDeriv (w i) *
        beta (w ⟨i.1 + 1, hi⟩) * innerResidual w ⟨i.1 + 1, hi⟩ =
        innerAlpha N ⟨i.1 + 1, hi⟩ *
        (sigmaDeriv (z i) * beta (z ⟨i.1 + 1, hi⟩) *
          innerResidual z ⟨i.1 + 1, hi⟩ -
         sigmaDeriv (w i) * beta (w ⟨i.1 + 1, hi⟩) *
          innerResidual w ⟨i.1 + 1, hi⟩) by ring,
      abs_mul, abs_of_nonneg ha0]
    exact mul_le_mul_of_nonneg_left (by simpa [j, p, q, r, r'] using hcore) ha0
  · simp [innerForward, hi]

/-- Energy at the predecessor of `i`; it vanishes at the initial index. -/
def innerPredecessorDiffEnergy {N : Nat} (z w : EVec N) (i : Fin N) : ℝ :=
  if hi : i.1 = 0 then 0 else
    innerD N ⟨i.1 - 1, by omega⟩ *
      (z ⟨i.1 - 1, by omega⟩ - w ⟨i.1 - 1, by omega⟩) ^ 2

/-- Energy at the successor of `i`; it vanishes at the terminal index. -/
def innerSuccessorDiffEnergy {N : Nat} (z w : EVec N) (i : Fin N) : ℝ :=
  if hi : i.1 + 1 < N then
    innerD N ⟨i.1 + 1, hi⟩ *
      (z ⟨i.1 + 1, hi⟩ - w ⟨i.1 + 1, hi⟩) ^ 2
  else 0

theorem innerPredecessorDiffEnergy_nonneg {N : Nat} (hN : 0 < N)
    (z w : EVec N) (i : Fin N) :
    0 ≤ innerPredecessorDiffEnergy z w i := by
  by_cases hi : i.1 = 0
  · simp [innerPredecessorDiffEnergy, hi]
  · simp only [innerPredecessorDiffEnergy, dif_neg hi]
    exact mul_nonneg (innerD_pos hN _).le (sq_nonneg _)

theorem innerSuccessorDiffEnergy_nonneg {N : Nat} (hN : 0 < N)
    (z w : EVec N) (i : Fin N) :
    0 ≤ innerSuccessorDiffEnergy z w i := by
  by_cases hi : i.1 + 1 < N
  · simp only [innerSuccessorDiffEnergy, dif_pos hi]
    exact mul_nonneg (innerD_pos hN _).le (sq_nonneg _)
  · simp [innerSuccessorDiffEnergy, hi]

theorem innerAlpha_sq_div_innerD_le_self {N : Nat} (hN : 0 < N)
    (i : Fin N) :
    innerAlpha N i ^ 2 / innerD N i ≤ innerD N i := by
  have hd := innerD_pos hN i
  have ha0 := (innerAlpha_pos hN i).le
  have had := innerAlpha_le_innerD hN i
  rw [div_le_iff₀ hd]
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr had)]

theorem innerAlpha_sq_div_innerD_le_predecessor {N : Nat} (hN : 0 < N)
    (i : Fin N) (hi : i.1 ≠ 0) :
    innerAlpha N i ^ 2 / innerD N i ≤
      innerD N ⟨i.1 - 1, by omega⟩ := by
  have hdprev : innerD N ⟨i.1 - 1, by omega⟩ = innerAlpha N i := by
    have hsum : 2 + (i.1 - 1) = 1 + i.1 := by omega
    simp only [innerD, innerAlpha, Nat.sub_sub, hsum]
  rw [hdprev]
  have hd := innerD_pos hN i
  have ha0 := (innerAlpha_pos hN i).le
  have had := innerAlpha_le_innerD hN i
  rw [div_le_iff₀ hd]
  nlinarith [mul_nonneg ha0 (sub_nonneg.mpr had)]

theorem innerAlpha_next_sq_div_innerD_eq {N : Nat} (hN : 0 < N)
    (i : Fin N) (hi : i.1 + 1 < N) :
    innerAlpha N ⟨i.1 + 1, hi⟩ ^ 2 / innerD N i = innerD N i := by
  rw [innerD_castSucc hN i hi]
  field_simp [ne_of_gt (innerAlpha_pos hN ⟨i.1 + 1, hi⟩)]

/-- Weighted pointwise square bound for the incoming term. -/
theorem innerIncoming_sq_div_le {N : Nat} (hN : 0 < N)
    (z w : EVec N) (i : Fin N) :
    (innerIncoming N z i - innerIncoming N w i) ^ 2 / innerD N i ≤
      512 * innerPredecessorDiffEnergy z w i +
        800 * innerD N i * (z i - w i) ^ 2 := by
  let A := innerIncoming N z i - innerIncoming N w i
  let p := |innerPrev z i - innerPrev w i|
  let q := |z i - w i|
  let a := innerAlpha N i
  have hp : 0 ≤ p := abs_nonneg _
  have hq : 0 ≤ q := abs_nonneg _
  have ha0 : 0 ≤ a := (innerAlpha_pos hN i).le
  have hLip := innerIncoming_abs_sub_le hN z w i
  have hB0 : 0 ≤ a * (16 * p + 20 * q) := by positivity
  have hsq0 : A ^ 2 ≤ (a * (16 * p + 20 * q)) ^ 2 := by
    rw [← sq_abs A]
    exact (sq_le_sq₀ (abs_nonneg A) hB0).2 (by simpa [A, a, p, q] using hLip)
  have hquad : (16 * p + 20 * q) ^ 2 ≤ 512 * p ^ 2 + 800 * q ^ 2 := by
    nlinarith [sq_nonneg (16 * p - 20 * q)]
  have hsq : A ^ 2 ≤ a ^ 2 * (512 * p ^ 2 + 800 * q ^ 2) := by
    calc
      A ^ 2 ≤ (a * (16 * p + 20 * q)) ^ 2 := hsq0
      _ = a ^ 2 * (16 * p + 20 * q) ^ 2 := by ring
      _ ≤ a ^ 2 * (512 * p ^ 2 + 800 * q ^ 2) :=
        mul_le_mul_of_nonneg_left hquad (sq_nonneg a)
  have hd0 := (innerD_pos hN i).le
  have hdiv : A ^ 2 / innerD N i ≤
      (a ^ 2 / innerD N i) * (512 * p ^ 2 + 800 * q ^ 2) := by
    calc
      A ^ 2 / innerD N i ≤
          (a ^ 2 * (512 * p ^ 2 + 800 * q ^ 2)) / innerD N i :=
        div_le_div_of_nonneg_right hsq hd0
      _ = _ := by ring
  by_cases hi : i.1 = 0
  · have hc := innerAlpha_sq_div_innerD_le_self hN i
    calc
      (innerIncoming N z i - innerIncoming N w i) ^ 2 / innerD N i =
          A ^ 2 / innerD N i := rfl
      _ ≤ (a ^ 2 / innerD N i) * (800 * q ^ 2) := by
        simpa [p, innerPrev, hi] using hdiv
      _ ≤ innerD N i * (800 * q ^ 2) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 512 * innerPredecessorDiffEnergy z w i +
          800 * innerD N i * (z i - w i) ^ 2 := by
        simp [innerPredecessorDiffEnergy, hi, q, sq_abs]
        ring
  · have hpcoef := innerAlpha_sq_div_innerD_le_predecessor hN i hi
    have hccoef := innerAlpha_sq_div_innerD_le_self hN i
    calc
      (innerIncoming N z i - innerIncoming N w i) ^ 2 / innerD N i =
          A ^ 2 / innerD N i := rfl
      _ ≤ (a ^ 2 / innerD N i) * (512 * p ^ 2 + 800 * q ^ 2) := hdiv
      _ = 512 * (a ^ 2 / innerD N i) * p ^ 2 +
          800 * (a ^ 2 / innerD N i) * q ^ 2 := by ring
      _ ≤ 512 * innerD N ⟨i.1 - 1, by omega⟩ * p ^ 2 +
          800 * innerD N i * q ^ 2 := by
        gcongr
      _ = 512 * innerPredecessorDiffEnergy z w i +
          800 * innerD N i * (z i - w i) ^ 2 := by
        simp only [innerPredecessorDiffEnergy, dif_neg hi]
        simp only [p, q, sq_abs, innerPrev, dif_neg hi]
        ring

/-- Weighted pointwise square bound for the forward term. -/
theorem innerForward_sq_div_le {N : Nat} (hN : 0 < N)
    (z w : EVec N) (i : Fin N) :
    (innerForward N z i - innerForward N w i) ^ 2 / innerD N i ≤
      2592 * innerD N i * (z i - w i) ^ 2 +
        288 * innerSuccessorDiffEnergy z w i := by
  by_cases hi : i.1 + 1 < N
  · let j : Fin N := ⟨i.1 + 1, hi⟩
    let A := innerForward N z i - innerForward N w i
    let p := |z i - w i|
    let q := |z j - w j|
    let a := innerAlpha N j
    have hp : 0 ≤ p := abs_nonneg _
    have hq : 0 ≤ q := abs_nonneg _
    have ha0 : 0 ≤ a := (innerAlpha_pos hN j).le
    have hLip := innerForward_abs_sub_le hN z w i
    rw [dif_pos hi] at hLip
    have hB0 : 0 ≤ a * (36 * p + 12 * q) := by positivity
    have hsq0 : A ^ 2 ≤ (a * (36 * p + 12 * q)) ^ 2 := by
      rw [← sq_abs A]
      exact (sq_le_sq₀ (abs_nonneg A) hB0).2
        (by simpa [A, a, p, q, j] using hLip)
    have hquad : (36 * p + 12 * q) ^ 2 ≤ 2592 * p ^ 2 + 288 * q ^ 2 := by
      nlinarith [sq_nonneg (36 * p - 12 * q)]
    have hsq : A ^ 2 ≤ a ^ 2 * (2592 * p ^ 2 + 288 * q ^ 2) := by
      calc
        A ^ 2 ≤ (a * (36 * p + 12 * q)) ^ 2 := hsq0
        _ = a ^ 2 * (36 * p + 12 * q) ^ 2 := by ring
        _ ≤ a ^ 2 * (2592 * p ^ 2 + 288 * q ^ 2) :=
          mul_le_mul_of_nonneg_left hquad (sq_nonneg a)
    have hd0 := (innerD_pos hN i).le
    have hdiv : A ^ 2 / innerD N i ≤
        (a ^ 2 / innerD N i) * (2592 * p ^ 2 + 288 * q ^ 2) := by
      calc
        A ^ 2 / innerD N i ≤
            (a ^ 2 * (2592 * p ^ 2 + 288 * q ^ 2)) / innerD N i :=
          div_le_div_of_nonneg_right hsq hd0
        _ = _ := by ring
    have heq := innerAlpha_next_sq_div_innerD_eq hN i hi
    have hnext : innerD N i ≤ innerD N j := by
      rw [innerD_castSucc hN i hi]
      exact innerAlpha_le_innerD hN j
    calc
      (innerForward N z i - innerForward N w i) ^ 2 / innerD N i =
          A ^ 2 / innerD N i := rfl
      _ ≤ (a ^ 2 / innerD N i) * (2592 * p ^ 2 + 288 * q ^ 2) := hdiv
      _ = innerD N i * (2592 * p ^ 2 + 288 * q ^ 2) := by
        rw [show a ^ 2 / innerD N i = innerD N i by simpa [a, j] using heq]
      _ = 2592 * innerD N i * p ^ 2 + 288 * innerD N i * q ^ 2 := by ring
      _ ≤ 2592 * innerD N i * p ^ 2 + 288 * innerD N j * q ^ 2 := by
        gcongr
      _ = 2592 * innerD N i * (z i - w i) ^ 2 +
          288 * innerSuccessorDiffEnergy z w i := by
        simp only [innerSuccessorDiffEnergy, dif_pos hi]
        simp only [p, q, j, sq_abs]
        ring
  · have hd0 := (innerD_pos hN i).le
    have hcur0 := mul_nonneg hd0 (sq_nonneg (z i - w i))
    simp [innerForward, hi, innerSuccessorDiffEnergy]
    positivity

private theorem sum_predecessor_shift {n : Nat} (f : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1),
      if hi : i.1 = 0 then 0 else f ⟨i.1 - 1, by omega⟩) =
      ∑ j : Fin n, f j.castSucc := by
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, dite_true, Fin.val_succ, Nat.succ_ne_zero,
    dite_false, zero_add]
  apply Fintype.sum_congr
  intro j
  congr 1

private theorem sum_successor_shift {n : Nat} (f : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1),
      if hi : i.1 + 1 < n + 1 then f ⟨i.1 + 1, hi⟩ else 0) =
      ∑ j : Fin n, f j.succ := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, lt_self_iff_false, dite_false, add_zero]
  apply Fintype.sum_congr
  intro j
  rw [dif_pos (by simp)]
  congr 1

theorem sum_innerPredecessorDiffEnergy_le_primal {N : Nat} (hN : 0 < N)
    (z w : EVec N) :
    (∑ i : Fin N, innerPredecessorDiffEnergy z w i) ≤
      innerPrimalSq N (z - w) := by
  cases N with
  | zero => omega
  | succ n =>
      let f : Fin (n + 1) → ℝ := fun j ↦
        innerD (n + 1) j * (z j - w j) ^ 2
      have hshift := sum_predecessor_shift f
      have hlast : 0 ≤ f (Fin.last n) := by
        exact mul_nonneg (innerD_pos hN _).le (sq_nonneg _)
      unfold innerPredecessorDiffEnergy
      rw [hshift]
      unfold innerPrimalSq
      rw [Fin.sum_univ_castSucc]
      have hle : (∑ j : Fin n, f j.castSucc) ≤
          (∑ j : Fin n, f j.castSucc) + f (Fin.last n) :=
        le_add_of_nonneg_right hlast
      simpa [f] using hle

theorem sum_innerSuccessorDiffEnergy_le_primal {N : Nat} (hN : 0 < N)
    (z w : EVec N) :
    (∑ i : Fin N, innerSuccessorDiffEnergy z w i) ≤
      innerPrimalSq N (z - w) := by
  cases N with
  | zero => omega
  | succ n =>
      let f : Fin (n + 1) → ℝ := fun j ↦
        innerD (n + 1) j * (z j - w j) ^ 2
      have hshift := sum_successor_shift f
      have hzero : 0 ≤ f 0 := by
        exact mul_nonneg (innerD_pos hN _).le (sq_nonneg _)
      unfold innerSuccessorDiffEnergy
      rw [hshift]
      unfold innerPrimalSq
      rw [Fin.sum_univ_succ]
      have hle : (∑ j : Fin n, f j.succ) ≤
          f 0 + ∑ j : Fin n, f j.succ :=
        le_add_of_nonneg_left hzero
      simpa [f] using hle

theorem innerIncoming_diff_dual_le {N : Nat} (hN : 0 < N)
    (z w : EVec N) :
    (∑ i : Fin N,
      (innerIncoming N z i - innerIncoming N w i) ^ 2 / innerD N i) ≤
      1312 * innerPrimalSq N (z - w) := by
  have hlocal :
      (∑ i : Fin N,
        (innerIncoming N z i - innerIncoming N w i) ^ 2 / innerD N i) ≤
      ∑ i : Fin N,
        (512 * innerPredecessorDiffEnergy z w i +
          800 * innerD N i * (z i - w i) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    exact innerIncoming_sq_div_le hN z w i
  have hpred := sum_innerPredecessorDiffEnergy_le_primal hN z w
  have hP0 := innerPrimalSq_nonneg hN (z - w)
  calc
    (∑ i : Fin N,
      (innerIncoming N z i - innerIncoming N w i) ^ 2 / innerD N i) ≤
        ∑ i : Fin N,
          (512 * innerPredecessorDiffEnergy z w i +
            800 * innerD N i * (z i - w i) ^ 2) := hlocal
    _ = 512 * (∑ i : Fin N, innerPredecessorDiffEnergy z w i) +
        800 * innerPrimalSq N (z - w) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · rw [Finset.mul_sum]
      · unfold innerPrimalSq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pi.sub_apply]
        ring
    _ ≤ 512 * innerPrimalSq N (z - w) +
        800 * innerPrimalSq N (z - w) := by gcongr
    _ = 1312 * innerPrimalSq N (z - w) := by ring

theorem innerForward_diff_dual_le {N : Nat} (hN : 0 < N)
    (z w : EVec N) :
    (∑ i : Fin N,
      (innerForward N z i - innerForward N w i) ^ 2 / innerD N i) ≤
      2880 * innerPrimalSq N (z - w) := by
  have hlocal :
      (∑ i : Fin N,
        (innerForward N z i - innerForward N w i) ^ 2 / innerD N i) ≤
      ∑ i : Fin N,
        (2592 * innerD N i * (z i - w i) ^ 2 +
          288 * innerSuccessorDiffEnergy z w i) := by
    apply Finset.sum_le_sum
    intro i _
    exact innerForward_sq_div_le hN z w i
  have hsucc := sum_innerSuccessorDiffEnergy_le_primal hN z w
  have hP0 := innerPrimalSq_nonneg hN (z - w)
  calc
    (∑ i : Fin N,
      (innerForward N z i - innerForward N w i) ^ 2 / innerD N i) ≤
        ∑ i : Fin N,
          (2592 * innerD N i * (z i - w i) ^ 2 +
            288 * innerSuccessorDiffEnergy z w i) := hlocal
    _ = 2592 * innerPrimalSq N (z - w) +
        288 * (∑ i : Fin N, innerSuccessorDiffEnergy z w i) := by
      rw [Finset.sum_add_distrib]
      congr 1
      · unfold innerPrimalSq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pi.sub_apply]
        ring
      · rw [Finset.mul_sum]
    _ ≤ 2592 * innerPrimalSq N (z - w) +
        288 * innerPrimalSq N (z - w) := by gcongr
    _ = 2880 * innerPrimalSq N (z - w) := by ring

theorem innerWallPart_sq_div_le {N : Nat} (hN : 0 < N)
    (lambdaWall : ℝ) (z w : EVec N) (i : Fin N) :
    (innerWallPart N lambdaWall z i - innerWallPart N lambdaWall w i) ^ 2 /
        innerD N i ≤
      lambdaWall ^ 2 * innerD N i * (z i - w i) ^ 2 := by
  let A := innerWallPart N lambdaWall z i - innerWallPart N lambdaWall w i
  have hd := innerD_pos hN i
  have hn := negPart_abs_sub_le (z i) (w i)
  have hA : |A| ≤ |lambdaWall| * innerD N i * |z i - w i| := by
    calc
      |A| = |lambdaWall * innerD N i *
          (negPart (z i) - negPart (w i))| := by
        apply congrArg abs
        simp only [A, innerWallPart]
        ring
      _ = |lambdaWall| * innerD N i *
          |negPart (z i) - negPart (w i)| := by
        rw [abs_mul, abs_mul, abs_of_pos hd]
      _ ≤ |lambdaWall| * innerD N i * |z i - w i| := by
        gcongr
  have hB0 : 0 ≤ |lambdaWall| * innerD N i * |z i - w i| := by positivity
  have hsq : A ^ 2 ≤
      (|lambdaWall| * innerD N i * |z i - w i|) ^ 2 := by
    rw [← sq_abs A]
    exact (sq_le_sq₀ (abs_nonneg A) hB0).2 hA
  calc
    (innerWallPart N lambdaWall z i - innerWallPart N lambdaWall w i) ^ 2 /
        innerD N i = A ^ 2 / innerD N i := rfl
    _ ≤ (|lambdaWall| * innerD N i * |z i - w i|) ^ 2 /
        innerD N i := div_le_div_of_nonneg_right hsq hd.le
    _ = lambdaWall ^ 2 * innerD N i * (z i - w i) ^ 2 := by
      rw [show (|lambdaWall| * innerD N i * |z i - w i|) ^ 2 =
          |lambdaWall| ^ 2 * innerD N i ^ 2 * |z i - w i| ^ 2 by ring,
        sq_abs, sq_abs]
      field_simp [ne_of_gt hd]

theorem innerWallPart_diff_dual_le {N : Nat} (hN : 0 < N)
    (lambdaWall : ℝ) (z w : EVec N) :
    (∑ i : Fin N,
      (innerWallPart N lambdaWall z i - innerWallPart N lambdaWall w i) ^ 2 /
        innerD N i) ≤
      lambdaWall ^ 2 * innerPrimalSq N (z - w) := by
  calc
    (∑ i : Fin N,
      (innerWallPart N lambdaWall z i - innerWallPart N lambdaWall w i) ^ 2 /
        innerD N i) ≤
      ∑ i : Fin N, lambdaWall ^ 2 * innerD N i * (z i - w i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact innerWallPart_sq_div_le hN lambdaWall z w i
    _ = lambdaWall ^ 2 * innerPrimalSq N (z - w) := by
      unfold innerPrimalSq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.sub_apply]
      ring

private theorem three_term_gradient_sq_le (a b c : ℝ) :
    (-2 * a - 2 * b - 2 * c) ^ 2 ≤ 12 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]

theorem innerGradient_pointwise_div_le {N : Nat} (hN : 0 < N)
    (lambdaWall : ℝ) (z w : EVec N) (i : Fin N) :
    (innerGradient N lambdaWall z i - innerGradient N lambdaWall w i) ^ 2 /
        innerD N i ≤
      12 *
        ((innerIncoming N z i - innerIncoming N w i) ^ 2 / innerD N i +
         (innerForward N z i - innerForward N w i) ^ 2 / innerD N i +
         (innerWallPart N lambdaWall z i - innerWallPart N lambdaWall w i) ^ 2 /
            innerD N i) := by
  let a := innerIncoming N z i - innerIncoming N w i
  let b := innerForward N z i - innerForward N w i
  let c := innerWallPart N lambdaWall z i - innerWallPart N lambdaWall w i
  have heq : innerGradient N lambdaWall z i - innerGradient N lambdaWall w i =
      -2 * a - 2 * b - 2 * c := by
    simp only [innerGradient, innerWallPart, a, b, c]
    ring
  have hs := three_term_gradient_sq_le a b c
  have hd0 := (innerD_pos hN i).le
  rw [heq]
  calc
    (-2 * a - 2 * b - 2 * c) ^ 2 / innerD N i ≤
        (12 * (a ^ 2 + b ^ 2 + c ^ 2)) / innerD N i :=
      div_le_div_of_nonneg_right hs hd0
    _ = 12 *
        ((innerIncoming N z i - innerIncoming N w i) ^ 2 / innerD N i +
         (innerForward N z i - innerForward N w i) ^ 2 / innerD N i +
         (innerWallPart N lambdaWall z i - innerWallPart N lambdaWall w i) ^ 2 /
            innerD N i) := by
      simp only [a, b, c]
      ring

/-- Raw dimension-free weighted smoothness estimate. -/
theorem innerGradient_weighted_lipschitz_raw {N : Nat} (hN : 0 < N)
    (lambdaWall : ℝ) (z w : EVec N) :
    innerDualSq N (innerGradient N lambdaWall z - innerGradient N lambdaWall w) ≤
      12 * (4192 + lambdaWall ^ 2) * innerPrimalSq N (z - w) := by
  let SI := ∑ i : Fin N,
    (innerIncoming N z i - innerIncoming N w i) ^ 2 / innerD N i
  let SF := ∑ i : Fin N,
    (innerForward N z i - innerForward N w i) ^ 2 / innerD N i
  let SW := ∑ i : Fin N,
    (innerWallPart N lambdaWall z i - innerWallPart N lambdaWall w i) ^ 2 /
      innerD N i
  have hlocal :
      innerDualSq N (innerGradient N lambdaWall z - innerGradient N lambdaWall w) ≤
        12 * (SI + SF + SW) := by
    unfold innerDualSq
    calc
      (∑ i : Fin N,
        (innerGradient N lambdaWall z - innerGradient N lambdaWall w) i ^ 2 /
          innerD N i) ≤
        ∑ i : Fin N, 12 *
          ((innerIncoming N z i - innerIncoming N w i) ^ 2 / innerD N i +
           (innerForward N z i - innerForward N w i) ^ 2 / innerD N i +
           (innerWallPart N lambdaWall z i - innerWallPart N lambdaWall w i) ^ 2 /
              innerD N i) := by
          apply Finset.sum_le_sum
          intro i _
          simpa only [Pi.sub_apply] using
            innerGradient_pointwise_div_le hN lambdaWall z w i
      _ = 12 * (SI + SF + SW) := by
        simp only [SI, SF, SW]
        rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hI : SI ≤ 1312 * innerPrimalSq N (z - w) := by
    simpa only [SI] using innerIncoming_diff_dual_le hN z w
  have hF : SF ≤ 2880 * innerPrimalSq N (z - w) := by
    simpa only [SF] using innerForward_diff_dual_le hN z w
  have hW : SW ≤ lambdaWall ^ 2 * innerPrimalSq N (z - w) := by
    simpa only [SW] using innerWallPart_diff_dual_le hN lambdaWall z w
  calc
    innerDualSq N (innerGradient N lambdaWall z - innerGradient N lambdaWall w) ≤
        12 * (SI + SF + SW) := hlocal
    _ ≤ 12 *
        (1312 * innerPrimalSq N (z - w) +
         2880 * innerPrimalSq N (z - w) +
         lambdaWall ^ 2 * innerPrimalSq N (z - w)) := by
      gcongr
    _ = 12 * (4192 + lambdaWall ^ 2) * innerPrimalSq N (z - w) := by ring

/-- A convenient explicit Lipschitz constant.  In particular, for the fixed
wall coefficient `12` the inner chain is `273`-smooth in its weighted metric. -/
theorem innerGradient_weighted_lipschitz {N : Nat} (hN : 0 < N)
    (lambdaWall : ℝ) (z w : EVec N) :
    innerDualSq N (innerGradient N lambdaWall z - innerGradient N lambdaWall w) ≤
      (225 + 4 * |lambdaWall|) ^ 2 * innerPrimalSq N (z - w) := by
  have hraw := innerGradient_weighted_lipschitz_raw hN lambdaWall z w
  have hcoef : 12 * (4192 + lambdaWall ^ 2) ≤
      (225 + 4 * |lambdaWall|) ^ 2 := by
    nlinarith [sq_abs lambdaWall, abs_nonneg lambdaWall, sq_nonneg lambdaWall]
  have hP0 := innerPrimalSq_nonneg hN (z - w)
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoef hP0)

theorem innerGradient_weighted_lipschitz_twelve {N : Nat} (hN : 0 < N)
    (z w : EVec N) :
    innerDualSq N (innerGradient N 12 z - innerGradient N 12 w) ≤
      273 ^ 2 * innerPrimalSq N (z - w) := by
  have h := innerGradient_weighted_lipschitz hN (12 : ℝ) z w
  norm_num at h ⊢
  exact h

end

end NCPLVerification
