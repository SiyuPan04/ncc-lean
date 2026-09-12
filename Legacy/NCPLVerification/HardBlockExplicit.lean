import NCPLVerification.HardInstance
import NCPLVerification.OuterActivation
import NCPLVerification.TerminalPerspectiveComposition
import NCPLVerification.ResidualPerspectiveComposition
import NCPLVerification.PerspectivePrimalDifferentiability

/-!
# Explicit local fields for one hard-instance block
-/

namespace NCPLVerification

noncomputable section

def carmonBlockPrev {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  if hi : i.1 = 0 then 1 else x ⟨i.1 - 1, by omega⟩

theorem carmonSqrtPsi_one : carmonSqrtPsi 1 = 1 := by
  have hs := carmonSqrtPsi_sq 1
  rw [carmonPsi_one] at hs
  nlinarith [carmonSqrtPsi_nonneg 1]

theorem carmonSqrtPsi_neg_one : carmonSqrtPsi (-1) = 0 := by
  apply carmonSqrtPsi_of_le_half
  norm_num

theorem carmonRhoProfile_one : carmonRhoProfile 1 = 1 := by
  simp [carmonRhoProfile, carmonSqrtPsi_one, carmonSqrtPsi_neg_one]

theorem carmonRho_eq_blockProfile {T : Nat} (x : EVec T) (i : Fin T) :
    carmonRho x i = carmonRhoProfile (carmonBlockPrev x i) := by
  rw [carmonRho_eq_profile]
  by_cases hi : i.1 = 0
  · simp [hi, carmonBlockPrev, carmonRhoProfile_one]
  · simp [hi, carmonBlockPrev]

theorem carmonOuterA_eq_terminalSplit {T : Nat} (x : EVec T) (i : Fin T) :
    carmonOuterA x i =
      terminalPlusCoeff (x i) * carmonSqrtPsi (carmonBlockPrev x i) ^ 2 +
        terminalMinusCoeff (x i) *
          carmonSqrtPsi (-carmonBlockPrev x i) ^ 2 := by
  by_cases hi : i.1 = 0
  · simp [carmonOuterA, carmonRhoSq, carmonTerm, carmonBlockPrev, hi,
      carmonPsi_one, carmonSqrtPsi_one, carmonSqrtPsi_neg_one,
      terminalPlusCoeff]
    ring
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    simp only [carmonOuterA, carmonRhoSq, carmonTerm, carmonBlockPrev]
    simp only [dif_neg hi]
    rw [carmonSqrtPsi_sq (x p), carmonSqrtPsi_sq (-x p)]
    unfold terminalPlusCoeff terminalMinusCoeff
    ring

private theorem splitTerminalGradU
    {a b c d u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = 0) :
    c * sigmaConeGradU a u + d * sigmaConeGradU b u =
      if 0 < a + b then
        (c * a ^ 2 + d * b ^ 2) / (a + b) *
          sigmaDeriv (u / (a + b))
      else 0 := by
  rcases mul_eq_zero.mp hab with haz | hbz
  · subst a
    rcases hb.eq_or_lt with rfl | hbpos
    · simp [sigmaConeGradU]
    · rw [if_pos (by simpa using hbpos)]
      simp [sigmaConeGradU, hbpos]
      field_simp [hbpos.ne']
  · subst b
    rcases ha.eq_or_lt with rfl | hapos
    · simp [sigmaConeGradU]
    · rw [if_pos (by simpa using hapos)]
      simp [sigmaConeGradU, hapos]
      field_simp [hapos.ne']

def hardBlockTerminalGradU (p q u : ℝ) : ℝ :=
  terminalPlusGradU p q u + terminalMinusGradU p q u

theorem hardBlockTerminalGradU_eq {T : Nat} (x : EVec T) (i : Fin T)
    (u : ℝ) :
    hardBlockTerminalGradU (carmonBlockPrev x i) (x i) u =
      if 0 < carmonRho x i then
        carmonOuterA x i / carmonRho x i *
          sigmaDeriv (u / carmonRho x i)
      else 0 := by
  let p := carmonBlockPrev x i
  have hsplit := splitTerminalGradU
    (c := terminalPlusCoeff (x i)) (d := terminalMinusCoeff (x i))
    (u := u) (carmonSqrtPsi_nonneg p) (carmonSqrtPsi_nonneg (-p))
    (carmonSqrtPsi_mul_neg p)
  rw [carmonRho_eq_blockProfile]
  unfold carmonRhoProfile
  rw [carmonOuterA_eq_terminalSplit]
  simpa [hardBlockTerminalGradU, terminalPlusGradU, terminalMinusGradU,
    terminalConeGradU] using hsplit

def hardResidualPrev {N : Nat} (rho : ℝ) (u : EVec N) (j : Fin N) : ℝ :=
  if hj : j.1 = 0 then rho else u ⟨j.1 - 1, by omega⟩

def hardResidualGradHere {N : Nat} (rho : ℝ) (u : EVec N)
    (j : Fin N) : ℝ :=
  residualConeGradV rho (hardResidualPrev rho u j) (u j)

def hardResidualGradPrev {N : Nat} (rho : ℝ) (u : EVec N)
    (j : Fin N) : ℝ :=
  residualConeGradU rho (hardResidualPrev rho u j) (u j)

def hardResidualDualComponent (N : Nat) (rho : ℝ) (u : EVec N)
    (k : Fin N) : ℝ :=
  innerAlpha N k * hardResidualGradHere rho u k +
    if hk : k.1 + 1 < N then
      innerAlpha N ⟨k.1 + 1, hk⟩ *
        hardResidualGradPrev rho u ⟨k.1 + 1, hk⟩
    else 0

theorem hardResidualPrev_div {N : Nat} {rho : ℝ} (hrho : 0 < rho)
    (u : EVec N) (j : Fin N) :
    hardResidualPrev rho u j / rho = innerPrev (rescaleEVec rho u) j := by
  by_cases hj : j.1 = 0
  · simp [hardResidualPrev, innerPrev, hj, hrho.ne']
  · simp [hardResidualPrev, innerPrev, rescaleEVec, hj]

theorem hardResidualGradHere_pos {N : Nat} {rho : ℝ} (hrho : 0 < rho)
    (u : EVec N) (j : Fin N) :
    hardResidualGradHere rho u j =
      rho * residualGradT (innerPrev (rescaleEVec rho u) j)
        ((rescaleEVec rho u) j) := by
  unfold hardResidualGradHere residualConeGradV twoConeGradient
  rw [if_pos hrho, hardResidualPrev_div hrho]
  rfl

theorem hardResidualGradPrev_pos {N : Nat} {rho : ℝ} (hrho : 0 < rho)
    (u : EVec N) (j : Fin N) :
    hardResidualGradPrev rho u j =
      rho * residualGradS (innerPrev (rescaleEVec rho u) j)
        ((rescaleEVec rho u) j) := by
  unfold hardResidualGradPrev residualConeGradU twoConeGradient
  rw [if_pos hrho, hardResidualPrev_div hrho]
  rfl

theorem hardResidualDualComponent_pos {N : Nat} {rho : ℝ}
    (hrho : 0 < rho) (u : EVec N) (k : Fin N) :
    hardResidualDualComponent N rho u k =
      rho * (-2 * innerIncoming N (rescaleEVec rho u) k -
        2 * innerForward N (rescaleEVec rho u) k) := by
  unfold hardResidualDualComponent
  rw [hardResidualGradHere_pos hrho]
  by_cases hk : k.1 + 1 < N
  · rw [dif_pos hk, hardResidualGradPrev_pos hrho]
    simp [innerIncoming, innerForward, hk, residualGradT,
      residualGradS, innerResidual, innerPrev]
    ring
  · rw [dif_neg hk]
    simp only [innerIncoming, innerForward, dif_neg hk, residualGradT,
      innerResidual]
    ring

theorem hardResidualDualComponent_zero (N : Nat) (u : EVec N) (k : Fin N) :
    hardResidualDualComponent N 0 u k = 0 := by
  simp [hardResidualDualComponent, hardResidualGradHere,
    hardResidualGradPrev, residualConeGradU, residualConeGradV,
    twoConeGradient]

def hardBlockExplicitGradU (N : Nat) (lambdaWall eta p q : ℝ)
    (u : EVec N) : EVec N := fun k ↦
  (if hN : 0 < N then
      if k = (⟨N - 1, Nat.sub_lt hN (by omega)⟩ : Fin N) then
        hardBlockTerminalGradU p q (u k)
      else 0
    else 0) -
    eta * hardResidualDualComponent N (carmonRhoProfile p) u k +
    2 * eta * lambdaWall * innerD N k * negPart (u k)

theorem hardBlockExplicitGradU_eq {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (i : Fin T) (u : EVec N) :
    hardBlockExplicitGradU N lambdaWall eta (carmonBlockPrev x i) (x i) u =
      perspectiveGradient N lambdaWall eta (carmonRho x i)
        (carmonOuterA x i) u := by
  funext k
  let p := carmonBlockPrev x i
  rw [carmonRho_eq_blockProfile]
  change hardBlockExplicitGradU N lambdaWall eta p (x i) u k =
    perspectiveGradient N lambdaWall eta (carmonRhoProfile p)
      (carmonOuterA x i) u k
  have hterm0 := hardBlockTerminalGradU_eq x i (u k)
  have hterm : hardBlockTerminalGradU p (x i) (u k) =
      if 0 < carmonRhoProfile p then
        carmonOuterA x i / carmonRhoProfile p *
          sigmaDeriv (u k / carmonRhoProfile p)
      else 0 := by
    simpa [p, carmonRho_eq_blockProfile] using hterm0
  by_cases hpos : 0 < carmonRhoProfile p
  · rw [perspectiveGradient, if_pos hpos]
    unfold hardBlockExplicitGradU
    rw [hardResidualDualComponent_pos hpos]
    unfold delayGradient innerGradient
    simp only [hN, ↓reduceDIte]
    rw [hterm, if_pos hpos]
    by_cases hk : k = (⟨N - 1, Nat.sub_lt hN (by omega)⟩ : Fin N)
    · subst k
      rw [if_pos rfl]
      simp only [innerGammaField, hN, ↓reduceDIte, if_pos,
        rescaleEVec]
      rw [negPart_div_pos
        (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) (carmonRhoProfile p) hpos]
      field_simp [hpos.ne']
      ring
    · rw [if_neg hk]
      simp only [innerGammaField, hN, ↓reduceDIte, hk,
        rescaleEVec]
      simp only [if_false]
      rw [negPart_div_pos (u k) (carmonRhoProfile p) hpos]
      field_simp [hpos.ne']
      ring
  · have hrho0 : carmonRhoProfile p = 0 :=
      le_antisymm (le_of_not_gt hpos) (carmonRhoProfile_nonneg p)
    rw [perspectiveGradient, if_neg hpos]
    unfold hardBlockExplicitGradU
    rw [hrho0, hardResidualDualComponent_zero]
    simp only [mul_zero, sub_zero]
    have ht0 : hardBlockTerminalGradU p (x i) (u k) = 0 := by
      have ht := hterm
      rw [hrho0, if_neg (by norm_num)] at ht
      exact ht
    simp [hN, ht0, p]

theorem sum_innerD_le_four {N : Nat} (hN : 0 < N) :
    ∑ i : Fin N, innerD N i ≤ 4 := by
  cases N with
  | zero => simp at hN
  | succ n =>
      have hlast : innerD (n + 1)
          (Fin.last n) = 1 := by
        have heq : Fin.last n =
            (⟨n, by omega⟩ : Fin (n + 1)) := by ext; rfl
        rw [heq]
        simpa using innerD_terminal (N := n + 1) (by omega)
      have hcast (i : Fin n) :
          innerD (n + 1) i.castSucc = innerAlpha (n + 1) i.succ := by
        have hi : i.castSucc.1 + 1 < n + 1 := by simp
        have heq : (⟨i.castSucc.1 + 1, hi⟩ : Fin (n + 1)) = i.succ := by
          ext
          rfl
        rw [← heq]
        exact innerD_castSucc (N := n + 1) (by omega) i.castSucc hi
      rw [Fin.sum_univ_castSucc]
      simp_rw [hcast]
      rw [hlast]
      have ha := sum_innerAlpha_le_three (N := n + 1) (by omega)
      rw [Fin.sum_univ_succ] at ha
      have ha0 := (innerAlpha_pos (N := n + 1) (by omega) 0).le
      linarith

theorem hardResidualGradHere_profile_abs_sub_le {N : Nat}
    (p p' : ℝ) (u : EVec N) (j : Fin N) :
    |hardResidualGradHere (carmonRhoProfile p) u j -
        hardResidualGradHere (carmonRhoProfile p') u j| ≤
      66 * residualProfileSmoothC * |p - p'| := by
  by_cases hj : j.1 = 0
  · unfold hardResidualGradHere hardResidualPrev
    rw [dif_pos hj, dif_pos hj]
    have h := residualProfileGradV_abs_sub_le p (carmonRhoProfile p) (u j)
      p' (carmonRhoProfile p') (u j)
    have hr := carmonRhoProfile_abs_sub_le p p'
    unfold residualProfileGradV at h
    simp only [sub_self, abs_zero, add_zero] at h
    have hadd : |p - p'| + |carmonRhoProfile p - carmonRhoProfile p'| ≤
        65 * |p - p'| := by linarith
    calc
      _ ≤ residualProfileSmoothC *
          (|p - p'| + |carmonRhoProfile p - carmonRhoProfile p'|) := h
      _ ≤ residualProfileSmoothC * (65 * |p - p'|) :=
        mul_le_mul_of_nonneg_left hadd residualProfileSmoothC_nonneg
      _ ≤ 66 * residualProfileSmoothC * |p - p'| := by
        have hp0 := abs_nonneg (p - p')
        nlinarith [mul_nonneg residualProfileSmoothC_nonneg hp0]
  · unfold hardResidualGradHere hardResidualPrev
    rw [dif_neg hj, dif_neg hj]
    have h := residualProfileGradV_abs_sub_le
      p (u ⟨j.1 - 1, by omega⟩) (u j)
      p' (u ⟨j.1 - 1, by omega⟩) (u j)
    unfold residualProfileGradV at h
    simp only [sub_self, abs_zero, add_zero] at h
    exact h.trans <| by
      have hprod := mul_nonneg residualProfileSmoothC_nonneg (abs_nonneg (p - p'))
      nlinarith

theorem hardResidualGradPrev_profile_abs_sub_le {N : Nat}
    (p p' : ℝ) (u : EVec N) (j : Fin N) :
    |hardResidualGradPrev (carmonRhoProfile p) u j -
        hardResidualGradPrev (carmonRhoProfile p') u j| ≤
      66 * residualProfileSmoothC * |p - p'| := by
  by_cases hj : j.1 = 0
  · unfold hardResidualGradPrev hardResidualPrev
    rw [dif_pos hj, dif_pos hj]
    have h := residualProfileGradU_abs_sub_le p (carmonRhoProfile p) (u j)
      p' (carmonRhoProfile p') (u j)
    have hr := carmonRhoProfile_abs_sub_le p p'
    unfold residualProfileGradU at h
    simp only [sub_self, abs_zero, add_zero] at h
    have hadd : |p - p'| + |carmonRhoProfile p - carmonRhoProfile p'| ≤
        65 * |p - p'| := by linarith
    calc
      _ ≤ residualProfileSmoothC *
          (|p - p'| + |carmonRhoProfile p - carmonRhoProfile p'|) := h
      _ ≤ residualProfileSmoothC * (65 * |p - p'|) :=
        mul_le_mul_of_nonneg_left hadd residualProfileSmoothC_nonneg
      _ ≤ 66 * residualProfileSmoothC * |p - p'| := by
        have hp0 := abs_nonneg (p - p')
        nlinarith [mul_nonneg residualProfileSmoothC_nonneg hp0]
  · unfold hardResidualGradPrev hardResidualPrev
    rw [dif_neg hj, dif_neg hj]
    have h := residualProfileGradU_abs_sub_le
      p (u ⟨j.1 - 1, by omega⟩) (u j)
      p' (u ⟨j.1 - 1, by omega⟩) (u j)
    unfold residualProfileGradU at h
    simp only [sub_self, abs_zero, add_zero] at h
    exact h.trans <| by
      have hprod := mul_nonneg residualProfileSmoothC_nonneg (abs_nonneg (p - p'))
      nlinarith

theorem hardResidualDualComponent_profile_abs_sub_le {N : Nat}
    (hN : 0 < N) (p p' : ℝ) (u : EVec N) (k : Fin N) :
    |hardResidualDualComponent N (carmonRhoProfile p) u k -
        hardResidualDualComponent N (carmonRhoProfile p') u k| ≤
      132 * residualProfileSmoothC * innerD N k * |p - p'| := by
  unfold hardResidualDualComponent
  have hh := hardResidualGradHere_profile_abs_sub_le p p' u k
  have ha0 := (innerAlpha_pos hN k).le
  have had := innerAlpha_le_innerD hN k
  by_cases hk : k.1 + 1 < N
  · rw [dif_pos hk, dif_pos hk]
    have hp := hardResidualGradPrev_profile_abs_sub_le p p' u
      ⟨k.1 + 1, hk⟩
    have hd := innerD_castSucc hN k hk
    have htri := abs_add_le
      (innerAlpha N k *
        (hardResidualGradHere (carmonRhoProfile p) u k -
          hardResidualGradHere (carmonRhoProfile p') u k))
      (innerAlpha N ⟨k.1 + 1, hk⟩ *
        (hardResidualGradPrev (carmonRhoProfile p) u ⟨k.1 + 1, hk⟩ -
          hardResidualGradPrev (carmonRhoProfile p') u ⟨k.1 + 1, hk⟩))
    rw [show
      innerAlpha N k * hardResidualGradHere (carmonRhoProfile p) u k +
          innerAlpha N ⟨k.1 + 1, hk⟩ *
            hardResidualGradPrev (carmonRhoProfile p) u ⟨k.1 + 1, hk⟩ -
        (innerAlpha N k * hardResidualGradHere (carmonRhoProfile p') u k +
          innerAlpha N ⟨k.1 + 1, hk⟩ *
            hardResidualGradPrev (carmonRhoProfile p') u ⟨k.1 + 1, hk⟩) =
        innerAlpha N k *
          (hardResidualGradHere (carmonRhoProfile p) u k -
            hardResidualGradHere (carmonRhoProfile p') u k) +
        innerAlpha N ⟨k.1 + 1, hk⟩ *
          (hardResidualGradPrev (carmonRhoProfile p) u ⟨k.1 + 1, hk⟩ -
            hardResidualGradPrev (carmonRhoProfile p') u ⟨k.1 + 1, hk⟩) by ring]
    have h1 :
        |innerAlpha N k *
          (hardResidualGradHere (carmonRhoProfile p) u k -
            hardResidualGradHere (carmonRhoProfile p') u k)| ≤
          innerAlpha N k * (66 * residualProfileSmoothC * |p - p'|) := by
      rw [abs_mul, abs_of_nonneg ha0]
      exact mul_le_mul_of_nonneg_left hh ha0
    have haNext0 := (innerAlpha_pos hN ⟨k.1 + 1, hk⟩).le
    have h2 :
        |innerAlpha N ⟨k.1 + 1, hk⟩ *
          (hardResidualGradPrev (carmonRhoProfile p) u ⟨k.1 + 1, hk⟩ -
            hardResidualGradPrev (carmonRhoProfile p') u ⟨k.1 + 1, hk⟩)| ≤
          innerAlpha N ⟨k.1 + 1, hk⟩ *
            (66 * residualProfileSmoothC * |p - p'|) := by
      rw [abs_mul, abs_of_nonneg haNext0]
      exact mul_le_mul_of_nonneg_left hp haNext0
    calc
      _ ≤ |innerAlpha N k *
            (hardResidualGradHere (carmonRhoProfile p) u k -
              hardResidualGradHere (carmonRhoProfile p') u k)| +
          |innerAlpha N ⟨k.1 + 1, hk⟩ *
            (hardResidualGradPrev (carmonRhoProfile p) u ⟨k.1 + 1, hk⟩ -
              hardResidualGradPrev (carmonRhoProfile p') u ⟨k.1 + 1, hk⟩)| :=
        abs_add_le _ _
      _ ≤ innerAlpha N k * (66 * residualProfileSmoothC * |p - p'|) +
          innerAlpha N ⟨k.1 + 1, hk⟩ *
            (66 * residualProfileSmoothC * |p - p'|) := add_le_add h1 h2
      _ ≤ 132 * residualProfileSmoothC * innerD N k * |p - p'| := by
        rw [← hd]
        have hbase := mul_nonneg residualProfileSmoothC_nonneg
          (abs_nonneg (p - p'))
        nlinarith
  · rw [dif_neg hk, dif_neg hk, add_zero, add_zero, ← mul_sub, abs_mul,
      abs_of_nonneg ha0]
    have hbase := mul_nonneg residualProfileSmoothC_nonneg
      (abs_nonneg (p - p'))
    have hm := mul_le_mul_of_nonneg_left hh ha0
    nlinarith [innerD_pos hN k]

def hardBlockDualParamC : ℝ :=
  200 + 132 * residualProfileSmoothC + 2 * terminalConeSmoothC

theorem hardBlockDualParamC_nonneg : 0 ≤ hardBlockDualParamC := by
  unfold hardBlockDualParamC
  nlinarith [residualProfileSmoothC_nonneg, terminalConeSmoothC_nonneg]

theorem hardBlockExplicitGradU_param_component_abs_sub_le {N : Nat}
    (hN : 0 < N) (lambdaWall eta p q p' q' : ℝ) (u : EVec N)
    (k : Fin N) (heta : |eta| ≤ 1) :
    |hardBlockExplicitGradU N lambdaWall eta p q u k -
        hardBlockExplicitGradU N lambdaWall eta p' q' u k| ≤
      hardBlockDualParamC * innerD N k * (|p - p'| + |q - q'|) := by
  unfold hardBlockExplicitGradU
  have hr := hardResidualDualComponent_profile_abs_sub_le hN p p' u k
  have hd0 := (innerD_pos hN k).le
  have hres :
      |eta * hardResidualDualComponent N (carmonRhoProfile p) u k -
        eta * hardResidualDualComponent N (carmonRhoProfile p') u k| ≤
      132 * residualProfileSmoothC * innerD N k * |p - p'| := by
    rw [← mul_sub, abs_mul]
    let B := 132 * residualProfileSmoothC * innerD N k * |p - p'|
    have hB0 : 0 ≤ B := by
      dsimp [B, residualProfileSmoothC]
      positivity
    calc
      |eta| * |hardResidualDualComponent N (carmonRhoProfile p) u k -
          hardResidualDualComponent N (carmonRhoProfile p') u k| ≤
          |eta| * B := mul_le_mul_of_nonneg_left hr (abs_nonneg eta)
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right heta hB0
      _ = B := one_mul B
  by_cases hk : k = (⟨N - 1, Nat.sub_lt hN (by omega)⟩ : Fin N)
  · subst k
    simp only [hN, ↓reduceDIte]
    rw [innerD_terminal hN]
    rw [innerD_terminal hN] at hres
    simp only [if_true, mul_one]
    have hp := terminalPlusGradU_abs_sub_le p q
      (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) p' q'
      (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)
    have hm := terminalMinusGradU_abs_sub_le p q
      (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) p' q'
      (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)
    simp only [sub_self, abs_zero, add_zero] at hp hm
    have ht := abs_add_le
      (terminalPlusGradU p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
        terminalPlusGradU p' q' (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩))
      (terminalMinusGradU p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
        terminalMinusGradU p' q' (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩))
    unfold hardBlockTerminalGradU
    rw [show
      terminalPlusGradU p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) +
          terminalMinusGradU p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
          eta * hardResidualDualComponent N (carmonRhoProfile p) u
            ⟨N - 1, Nat.sub_lt hN (by omega)⟩ +
          2 * eta * lambdaWall *
            negPart (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
        (terminalPlusGradU p' q' (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) +
          terminalMinusGradU p' q' (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
          eta * hardResidualDualComponent N (carmonRhoProfile p') u
            ⟨N - 1, Nat.sub_lt hN (by omega)⟩ +
          2 * eta * lambdaWall *
            negPart (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)) =
        (terminalPlusGradU p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
          terminalPlusGradU p' q' (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)) +
        (terminalMinusGradU p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
          terminalMinusGradU p' q' (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)) -
        (eta * hardResidualDualComponent N (carmonRhoProfile p) u
            ⟨N - 1, Nat.sub_lt hN (by omega)⟩ -
          eta * hardResidualDualComponent N (carmonRhoProfile p') u
            ⟨N - 1, Nat.sub_lt hN (by omega)⟩) by ring]
    have htri := abs_sub
      ((terminalPlusGradU p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
          terminalPlusGradU p' q' (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)) +
        (terminalMinusGradU p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
          terminalMinusGradU p' q' (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)))
      (eta * hardResidualDualComponent N (carmonRhoProfile p) u
          ⟨N - 1, Nat.sub_lt hN (by omega)⟩ -
        eta * hardResidualDualComponent N (carmonRhoProfile p') u
          ⟨N - 1, Nat.sub_lt hN (by omega)⟩)
    calc
      _ ≤ |(terminalPlusGradU p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
              terminalPlusGradU p' q' (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)) +
            (terminalMinusGradU p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
              terminalMinusGradU p' q' (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩))| +
          |eta * hardResidualDualComponent N (carmonRhoProfile p) u
              ⟨N - 1, Nat.sub_lt hN (by omega)⟩ -
            eta * hardResidualDualComponent N (carmonRhoProfile p') u
              ⟨N - 1, Nat.sub_lt hN (by omega)⟩| := htri
      _ ≤ (|terminalPlusGradU p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
              terminalPlusGradU p' q' (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)| +
            |terminalMinusGradU p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) -
              terminalMinusGradU p' q' (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)|) +
          |eta * hardResidualDualComponent N (carmonRhoProfile p) u
              ⟨N - 1, Nat.sub_lt hN (by omega)⟩ -
            eta * hardResidualDualComponent N (carmonRhoProfile p') u
              ⟨N - 1, Nat.sub_lt hN (by omega)⟩| := add_le_add ht le_rfl
      _ ≤ (terminalConeSmoothC * (|p - p'| + |q - q'|) +
            terminalConeSmoothC * (|p - p'| + |q - q'|)) +
          132 * residualProfileSmoothC * 1 * |p - p'| :=
        add_le_add (add_le_add hp hm) hres
      _ ≤ hardBlockDualParamC * (|p - p'| + |q - q'|) := by
        unfold hardBlockDualParamC
        have hdp := abs_nonneg (p - p')
        have hdq := abs_nonneg (q - q')
        have hRC := residualProfileSmoothC_nonneg
        have hTC := terminalConeSmoothC_nonneg
        nlinarith [mul_nonneg hRC hdq,
          mul_nonneg hTC (add_nonneg hdp hdq)]
  · simp only [hN, ↓reduceDIte, if_neg hk]
    rw [show
      (0 - eta * hardResidualDualComponent N (carmonRhoProfile p) u k +
          2 * eta * lambdaWall * innerD N k * negPart (u k)) -
        (0 - eta * hardResidualDualComponent N (carmonRhoProfile p') u k +
          2 * eta * lambdaWall * innerD N k * negPart (u k)) =
        -(eta * hardResidualDualComponent N (carmonRhoProfile p) u k -
          eta * hardResidualDualComponent N (carmonRhoProfile p') u k) by ring,
      abs_neg]
    unfold hardBlockDualParamC
    have hdp := abs_nonneg (p - p')
    have hdq := abs_nonneg (q - q')
    have hRC := residualProfileSmoothC_nonneg
    have hTC := terminalConeSmoothC_nonneg
    nlinarith [mul_nonneg hd0 hdp, mul_nonneg hd0 hdq,
      mul_nonneg hRC (mul_nonneg hd0 hdp)]

theorem hardBlockExplicitGradU_param_weighted_le {N : Nat}
    (hN : 0 < N) (lambdaWall eta p q p' q' : ℝ) (u : EVec N)
    (heta : |eta| ≤ 1) :
    innerDualSq N
        (hardBlockExplicitGradU N lambdaWall eta p q u -
          hardBlockExplicitGradU N lambdaWall eta p' q' u) ≤
      8 * hardBlockDualParamC ^ 2 *
        ((p - p') ^ 2 + (q - q') ^ 2) := by
  let s : ℝ := |p - p'| + |q - q'|
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  have hC0 := hardBlockDualParamC_nonneg
  have hpoint (k : Fin N) :
      (hardBlockExplicitGradU N lambdaWall eta p q u k -
          hardBlockExplicitGradU N lambdaWall eta p' q' u k) ^ 2 /
          innerD N k ≤
        hardBlockDualParamC ^ 2 * innerD N k * s ^ 2 := by
    have hd := innerD_pos hN k
    have h := hardBlockExplicitGradU_param_component_abs_sub_le hN
      lambdaWall eta p q p' q' u k heta
    change |hardBlockExplicitGradU N lambdaWall eta p q u k -
        hardBlockExplicitGradU N lambdaWall eta p' q' u k| ≤
      hardBlockDualParamC * innerD N k * s at h
    have hright0 : 0 ≤ hardBlockDualParamC * innerD N k * s := by positivity
    have hsq :
        (hardBlockExplicitGradU N lambdaWall eta p q u k -
          hardBlockExplicitGradU N lambdaWall eta p' q' u k) ^ 2 ≤
        (hardBlockDualParamC * innerD N k * s) ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hright0).2 h
    rw [div_le_iff₀ hd]
    calc
      (hardBlockExplicitGradU N lambdaWall eta p q u k -
          hardBlockExplicitGradU N lambdaWall eta p' q' u k) ^ 2 ≤
          (hardBlockDualParamC * innerD N k * s) ^ 2 := hsq
      _ = (hardBlockDualParamC ^ 2 * innerD N k * s ^ 2) *
          innerD N k := by ring
  unfold innerDualSq
  simp only [Pi.sub_apply]
  have hsum :
      (∑ k : Fin N,
        (hardBlockExplicitGradU N lambdaWall eta p q u k -
          hardBlockExplicitGradU N lambdaWall eta p' q' u k) ^ 2 /
            innerD N k) ≤
      ∑ k : Fin N, hardBlockDualParamC ^ 2 * innerD N k * s ^ 2 := by
    apply Finset.sum_le_sum
    intro k _
    exact hpoint k
  have hsumEq :
      (∑ k : Fin N, hardBlockDualParamC ^ 2 * innerD N k * s ^ 2) =
        hardBlockDualParamC ^ 2 * s ^ 2 * ∑ k : Fin N, innerD N k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsumEq] at hsum
  have hdSum := sum_innerD_le_four hN
  have hcoef0 : 0 ≤ hardBlockDualParamC ^ 2 * s ^ 2 := by positivity
  have hsum' :
      (∑ k : Fin N,
        (hardBlockExplicitGradU N lambdaWall eta p q u k -
          hardBlockExplicitGradU N lambdaWall eta p' q' u k) ^ 2 /
            innerD N k) ≤
        hardBlockDualParamC ^ 2 * s ^ 2 * 4 :=
    hsum.trans (mul_le_mul_of_nonneg_left hdSum hcoef0)
  have hsSq : s ^ 2 ≤ 2 * ((p - p') ^ 2 + (q - q') ^ 2) := by
    dsimp [s]
    have hpSq : |p - p'| ^ 2 = (p - p') ^ 2 := sq_abs _
    have hqSq : |q - q'| ^ 2 = (q - q') ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|p - p'| - |q - q'|)]
  calc
    _ ≤ hardBlockDualParamC ^ 2 * s ^ 2 * 4 := hsum'
    _ ≤ hardBlockDualParamC ^ 2 *
          (2 * ((p - p') ^ 2 + (q - q') ^ 2)) * 4 := by
      gcongr
    _ = 8 * hardBlockDualParamC ^ 2 *
        ((p - p') ^ 2 + (q - q') ^ 2) := by ring

end

end NCPLVerification
