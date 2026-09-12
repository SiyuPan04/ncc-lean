import NCPLVerification.SigmaPerspectiveSmoothness
import NCPLVerification.CarmonActivation

/-!
# Composing the terminal perspective with the outer flat gates

The noninitial outer gate splits into two disjoint square-root half-gates.
This module establishes uniform Lipschitz bounds for the three scalar
gradient components of either half-gate terminal contribution.
-/

namespace NCPLVerification

noncomputable section

theorem deriv_carmonSqrtPsi (t : ℝ) :
    deriv carmonSqrtPsi t = carmonSqrtPsiDeriv t :=
  (hasDerivAt_carmonSqrtPsi t).deriv

theorem differentiable_carmonSqrtPsi : Differentiable ℝ carmonSqrtPsi :=
  fun t ↦ (hasDerivAt_carmonSqrtPsi t).differentiableAt

theorem deriv_carmonSqrtPsiDeriv (t : ℝ) :
    deriv carmonSqrtPsiDeriv t = carmonSqrtPsiSecond t :=
  (hasDerivAt_carmonSqrtPsiDeriv t).deriv

theorem differentiable_carmonSqrtPsiDeriv :
    Differentiable ℝ carmonSqrtPsiDeriv :=
  fun t ↦ (hasDerivAt_carmonSqrtPsiDeriv t).differentiableAt

theorem carmonSqrtPsi_lipschitz :
    LipschitzWith (32 : NNReal) carmonSqrtPsi := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_carmonSqrtPsi
  intro t
  rw [deriv_carmonSqrtPsi, ← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using abs_carmonSqrtPsiDeriv_le_thirtyTwo t

theorem carmonSqrtPsi_abs_sub_le (s t : ℝ) :
    |carmonSqrtPsi s - carmonSqrtPsi t| ≤ 32 * |s - t| := by
  simpa [Real.norm_eq_abs] using carmonSqrtPsi_lipschitz.norm_sub_le s t

theorem carmonSqrtPsiDeriv_lipschitz :
    LipschitzWith (576 : NNReal) carmonSqrtPsiDeriv := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_carmonSqrtPsiDeriv
  intro t
  rw [deriv_carmonSqrtPsiDeriv, ← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using abs_carmonSqrtPsiSecond_le_fiveSeventySix t

theorem carmonSqrtPsiDeriv_abs_sub_le (s t : ℝ) :
    |carmonSqrtPsiDeriv s - carmonSqrtPsiDeriv t| ≤ 576 * |s - t| := by
  simpa [Real.norm_eq_abs] using
    carmonSqrtPsiDeriv_lipschitz.norm_sub_le s t

def terminalConeGradP (c dcScale rho u : ℝ) : ℝ :=
  c * dcScale * sigmaConeGradRho rho u

def terminalConeGradQ (dc rho u : ℝ) : ℝ :=
  dc * sigmaConeValue rho u

def terminalConeGradU (c rho u : ℝ) : ℝ :=
  c * sigmaConeGradU rho u

def terminalConeSmoothC : ℝ := 100000 * (1 + carmonPhiCap)

theorem terminalConeSmoothC_nonneg : 0 ≤ terminalConeSmoothC := by
  unfold terminalConeSmoothC
  exact mul_nonneg (by norm_num) (by linarith [carmonPhiCap_nonneg])

private theorem abs_pair_sub_le (a b a' b' : ℝ) :
    |a * b - a' * b'| ≤ |a - a'| * |b| + |a'| * |b - b'| := by
  have heq : a * b - a' * b' = (a - a') * b + a' * (b - b') := by ring
  rw [heq]
  exact (abs_add_le _ _).trans_eq (by repeat' rw [abs_mul])

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

theorem terminalConeGradP_abs_sub_le
    {rho rho' dRho dRho' c c' u u' dp dq : ℝ}
    (hrho : 0 ≤ rho) (hrho' : 0 ≤ rho')
    (hrho2 : rho ≤ 2) (hrho2' : rho' ≤ 2)
    (hRhoDiff : |rho - rho'| ≤ 32 * dp)
    (hdRho : |dRho| ≤ 32) (hdRho' : |dRho'| ≤ 32)
    (hdRhoDiff : |dRho - dRho'| ≤ 576 * dp)
    (hc : |c| ≤ 2 * carmonPhiCap)
    (hc' : |c'| ≤ 2 * carmonPhiCap)
    (hcDiff : |c - c'| ≤ 2 * dq)
    (hdp : 0 ≤ dp) (hdq : 0 ≤ dq) :
    |terminalConeGradP c dRho rho u -
        terminalConeGradP c' dRho' rho' u'| ≤
      terminalConeSmoothC * (dp + dq + |u - u'|) := by
  unfold terminalConeGradP
  have htri := abs_triple_sub_le c dRho (sigmaConeGradRho rho u)
    c' dRho' (sigmaConeGradRho rho' u')
  have hk := sigmaConeGradRho_abs_le (u := u) hrho
  have hk' := sigmaConeGradRho_abs_le (u := u') hrho'
  have hk8 : |sigmaConeGradRho rho u| ≤ 8 := by nlinarith
  have hk8' : |sigmaConeGradRho rho' u'| ≤ 8 := by nlinarith
  have hkDiff0 := sigmaConeGradRho_abs_sub_le hrho hrho'
    (u := u) (v := u')
  have hkDiff :
      |sigmaConeGradRho rho u - sigmaConeGradRho rho' u'| ≤
        40 * (32 * dp + |u - u'|) := by
    nlinarith [abs_nonneg (rho - rho'), abs_nonneg (u - u')]
  have hcap2 : 0 ≤ 2 * carmonPhiCap :=
    mul_nonneg (by norm_num) carmonPhiCap_nonneg
  have hdp576 : 0 ≤ 576 * dp := mul_nonneg (by norm_num) hdp
  have hcapdp : 0 ≤ (2 * carmonPhiCap) * (576 * dp) :=
    mul_nonneg hcap2 hdp576
  have hcap32 : 0 ≤ (2 * carmonPhiCap) * 32 :=
    mul_nonneg hcap2 (by norm_num)
  have hkDiffRhs0 : 0 ≤ 40 * (32 * dp + |u - u'|) := by positivity
  have h1 : |c - c'| * |dRho| * |sigmaConeGradRho rho u| ≤
      (2 * dq) * 32 * 8 := by gcongr
  have h2 : |c'| * |dRho - dRho'| * |sigmaConeGradRho rho u| ≤
      (2 * carmonPhiCap) * (576 * dp) * 8 := by
    gcongr
  have h3 : |c'| * |dRho'| *
      |sigmaConeGradRho rho u - sigmaConeGradRho rho' u'| ≤
      (2 * carmonPhiCap) * 32 *
        (40 * (32 * dp + |u - u'|)) := by
    gcongr
  calc
    |c * dRho * sigmaConeGradRho rho u -
        c' * dRho' * sigmaConeGradRho rho' u'| ≤
      |c - c'| * |dRho| * |sigmaConeGradRho rho u| +
        |c'| * |dRho - dRho'| * |sigmaConeGradRho rho u| +
          |c'| * |dRho'| *
            |sigmaConeGradRho rho u - sigmaConeGradRho rho' u'| := htri
    _ ≤ (2 * dq) * 32 * 8 +
        (2 * carmonPhiCap) * (576 * dp) * 8 +
          (2 * carmonPhiCap) * 32 *
            (40 * (32 * dp + |u - u'|)) := by gcongr
    _ ≤ terminalConeSmoothC * (dp + dq + |u - u'|) := by
      unfold terminalConeSmoothC
      nlinarith [carmonPhiCap_nonneg, abs_nonneg (u - u')]

theorem terminalConeGradQ_abs_sub_le
    {rho rho' dc dc' u u' dp dq : ℝ}
    (hrho : 0 ≤ rho) (hrho' : 0 ≤ rho')
    (hrho2 : rho ≤ 2) (hrho2' : rho' ≤ 2)
    (hRhoDiff : |rho - rho'| ≤ 32 * dp)
    (hdc : |dc| ≤ 2) (hdc' : |dc'| ≤ 2)
    (hdcDiff : |dc - dc'| ≤ 4 * dq)
    (hdp : 0 ≤ dp) (hdq : 0 ≤ dq) :
    |terminalConeGradQ dc rho u - terminalConeGradQ dc' rho' u'| ≤
      terminalConeSmoothC * (dp + dq + |u - u'|) := by
  unfold terminalConeGradQ
  have htri := abs_pair_sub_le dc (sigmaConeValue rho u)
    dc' (sigmaConeValue rho' u')
  have hv := sigmaConeValue_abs_le_sq (rho := rho) (u := u) hrho
  have hv4 : |sigmaConeValue rho u| ≤ 4 := by nlinarith [sq_nonneg rho]
  have hvDiff0 := sigmaConeValue_abs_sub_le hrho hrho' hrho2 hrho2'
    (u := u) (v := u') (R := 2)
  have hvDiff :
      |sigmaConeValue rho u - sigmaConeValue rho' u'| ≤
        8 * (32 * dp + |u - u'|) := by
    nlinarith [abs_nonneg (rho - rho'), abs_nonneg (u - u')]
  have h1 : |dc - dc'| * |sigmaConeValue rho u| ≤
      (4 * dq) * 4 := by gcongr
  have h2 : |dc'| * |sigmaConeValue rho u - sigmaConeValue rho' u'| ≤
      2 * (8 * (32 * dp + |u - u'|)) := by gcongr
  calc
    |dc * sigmaConeValue rho u - dc' * sigmaConeValue rho' u'| ≤
        |dc - dc'| * |sigmaConeValue rho u| +
          |dc'| * |sigmaConeValue rho u - sigmaConeValue rho' u'| := htri
    _ ≤ (4 * dq) * 4 + 2 * (8 * (32 * dp + |u - u'|)) :=
      add_le_add h1 h2
    _ ≤ terminalConeSmoothC * (dp + dq + |u - u'|) := by
      unfold terminalConeSmoothC
      nlinarith [carmonPhiCap_nonneg, abs_nonneg (u - u')]

theorem terminalConeGradU_abs_sub_le
    {rho rho' c c' u u' dp dq : ℝ}
    (hrho : 0 ≤ rho) (hrho' : 0 ≤ rho')
    (hrho2 : rho ≤ 2) (hrho2' : rho' ≤ 2)
    (hRhoDiff : |rho - rho'| ≤ 32 * dp)
    (hc : |c| ≤ 2 * carmonPhiCap)
    (hc' : |c'| ≤ 2 * carmonPhiCap)
    (hcDiff : |c - c'| ≤ 2 * dq)
    (hdp : 0 ≤ dp) (hdq : 0 ≤ dq) :
    |terminalConeGradU c rho u - terminalConeGradU c' rho' u'| ≤
      terminalConeSmoothC * (dp + dq + |u - u'|) := by
  unfold terminalConeGradU
  have htri := abs_pair_sub_le c (sigmaConeGradU rho u)
    c' (sigmaConeGradU rho' u')
  have hg := sigmaConeGradU_abs_le (u := u) hrho
  have hg4 : |sigmaConeGradU rho u| ≤ 4 := by nlinarith
  have hgDiff0 := sigmaConeGradU_abs_sub_le hrho hrho'
    (u := u) (v := u')
  have hgDiff :
      |sigmaConeGradU rho u - sigmaConeGradU rho' u'| ≤
        8 * (32 * dp + |u - u'|) := by
    nlinarith [abs_nonneg (rho - rho'), abs_nonneg (u - u')]
  have hcap2 : 0 ≤ 2 * carmonPhiCap :=
    mul_nonneg (by norm_num) carmonPhiCap_nonneg
  have hgDiffRhs0 : 0 ≤ 8 * (32 * dp + |u - u'|) := by positivity
  have h1 : |c - c'| * |sigmaConeGradU rho u| ≤
      (2 * dq) * 4 := by gcongr
  have h2 : |c'| * |sigmaConeGradU rho u - sigmaConeGradU rho' u'| ≤
      (2 * carmonPhiCap) * (8 * (32 * dp + |u - u'|)) := by gcongr
  calc
    |c * sigmaConeGradU rho u - c' * sigmaConeGradU rho' u'| ≤
        |c - c'| * |sigmaConeGradU rho u| +
          |c'| * |sigmaConeGradU rho u - sigmaConeGradU rho' u'| := htri
    _ ≤ (2 * dq) * 4 +
        (2 * carmonPhiCap) * (8 * (32 * dp + |u - u'|)) :=
      add_le_add h1 h2
    _ ≤ terminalConeSmoothC * (dp + dq + |u - u'|) := by
      unfold terminalConeSmoothC
      nlinarith [carmonPhiCap_nonneg, abs_nonneg (u - u')]

def terminalPlusCoeff (q : ℝ) : ℝ := carmonPhiCap - carmonPhi q
def terminalPlusCoeffDeriv (q : ℝ) : ℝ := -carmonPhiDeriv q
def terminalMinusCoeff (q : ℝ) : ℝ := carmonPhiCap + carmonPhi (-q)
def terminalMinusCoeffDeriv (q : ℝ) : ℝ := -carmonPhiDeriv (-q)

theorem hasDerivAt_terminalPlusCoeff (q : ℝ) :
    HasDerivAt terminalPlusCoeff (terminalPlusCoeffDeriv q) q := by
  have h := (hasDerivAt_const q carmonPhiCap).sub (hasDerivAt_carmonPhi q)
  change HasDerivAt terminalPlusCoeff _ q at h
  exact h.congr_deriv (by simp [terminalPlusCoeffDeriv])

theorem hasDerivAt_terminalMinusCoeff (q : ℝ) :
    HasDerivAt terminalMinusCoeff (terminalMinusCoeffDeriv q) q := by
  have hneg : HasDerivAt (fun s : ℝ ↦ -s) (-1) q :=
    (hasDerivAt_id q).neg
  have hphi := (hasDerivAt_carmonPhi (-q)).comp q hneg
  have h := (hasDerivAt_const q carmonPhiCap).add hphi
  change HasDerivAt terminalMinusCoeff _ q at h
  exact h.congr_deriv (by simp [terminalMinusCoeffDeriv])

theorem terminalPlusCoeff_abs_le (q : ℝ) :
    |terminalPlusCoeff q| ≤ 2 * carmonPhiCap := by
  unfold terminalPlusCoeff
  have h := abs_sub carmonPhiCap (carmonPhi q)
  rw [abs_of_nonneg carmonPhiCap_nonneg] at h
  nlinarith [abs_carmonPhi_le_cap q]

theorem terminalMinusCoeff_abs_le (q : ℝ) :
    |terminalMinusCoeff q| ≤ 2 * carmonPhiCap := by
  unfold terminalMinusCoeff
  have h := abs_add_le carmonPhiCap (carmonPhi (-q))
  rw [abs_of_nonneg carmonPhiCap_nonneg] at h
  nlinarith [abs_carmonPhi_le_cap (-q)]

theorem terminalPlusCoeff_abs_sub_le (q q' : ℝ) :
    |terminalPlusCoeff q - terminalPlusCoeff q'| ≤ 2 * |q - q'| := by
  simpa [terminalPlusCoeff, abs_sub_comm] using carmonPhi_abs_sub_le q q'

theorem terminalMinusCoeff_abs_sub_le (q q' : ℝ) :
    |terminalMinusCoeff q - terminalMinusCoeff q'| ≤ 2 * |q - q'| := by
  have h := carmonPhi_abs_sub_le (-q) (-q')
  unfold terminalMinusCoeff
  rw [show (carmonPhiCap + carmonPhi (-q)) -
      (carmonPhiCap + carmonPhi (-q')) =
        carmonPhi (-q) - carmonPhi (-q') by ring]
  simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using h

theorem terminalPlusCoeffDeriv_abs_le (q : ℝ) :
    |terminalPlusCoeffDeriv q| ≤ 2 := by
  simpa [terminalPlusCoeffDeriv] using abs_carmonPhiDeriv_le_two q

theorem terminalMinusCoeffDeriv_abs_le (q : ℝ) :
    |terminalMinusCoeffDeriv q| ≤ 2 := by
  simpa [terminalMinusCoeffDeriv] using abs_carmonPhiDeriv_le_two (-q)

theorem terminalPlusCoeffDeriv_abs_sub_le (q q' : ℝ) :
    |terminalPlusCoeffDeriv q - terminalPlusCoeffDeriv q'| ≤
      4 * |q - q'| := by
  have h := carmonPhiDeriv_abs_sub_le q q'
  simpa only [terminalPlusCoeffDeriv, neg_sub_neg, abs_neg,
    abs_sub_comm] using h

theorem terminalMinusCoeffDeriv_abs_sub_le (q q' : ℝ) :
    |terminalMinusCoeffDeriv q - terminalMinusCoeffDeriv q'| ≤
      4 * |q - q'| := by
  have h := carmonPhiDeriv_abs_sub_le (-q) (-q')
  simp only [terminalMinusCoeffDeriv, neg_sub_neg]
  simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using h

theorem carmonSqrtPsi_le_two (p : ℝ) : carmonSqrtPsi p ≤ 2 := by
  have h := carmonRhoProfile_le_two p
  unfold carmonRhoProfile at h
  nlinarith [carmonSqrtPsi_nonneg (-p)]

theorem carmonSqrtPsi_neg_abs_sub_le (p p' : ℝ) :
    |carmonSqrtPsi (-p) - carmonSqrtPsi (-p')| ≤ 32 * |p - p'| := by
  have h := carmonSqrtPsi_abs_sub_le (-p) (-p')
  simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using h

theorem neg_carmonSqrtPsiDeriv_abs_le (p : ℝ) :
    |-carmonSqrtPsiDeriv (-p)| ≤ 32 := by
  simpa using abs_carmonSqrtPsiDeriv_le_thirtyTwo (-p)

theorem neg_carmonSqrtPsiDeriv_abs_sub_le (p p' : ℝ) :
    |-carmonSqrtPsiDeriv (-p) - -carmonSqrtPsiDeriv (-p')| ≤
      576 * |p - p'| := by
  have h := carmonSqrtPsiDeriv_abs_sub_le (-p) (-p')
  simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using h

def terminalPlusGradP (p q u : ℝ) : ℝ :=
  terminalConeGradP (terminalPlusCoeff q) (carmonSqrtPsiDeriv p)
    (carmonSqrtPsi p) u

def terminalPlusGradQ (p q u : ℝ) : ℝ :=
  terminalConeGradQ (terminalPlusCoeffDeriv q) (carmonSqrtPsi p) u

def terminalPlusGradU (p q u : ℝ) : ℝ :=
  terminalConeGradU (terminalPlusCoeff q) (carmonSqrtPsi p) u

def terminalMinusGradP (p q u : ℝ) : ℝ :=
  terminalConeGradP (terminalMinusCoeff q) (-carmonSqrtPsiDeriv (-p))
    (carmonSqrtPsi (-p)) u

def terminalMinusGradQ (p q u : ℝ) : ℝ :=
  terminalConeGradQ (terminalMinusCoeffDeriv q) (carmonSqrtPsi (-p)) u

def terminalMinusGradU (p q u : ℝ) : ℝ :=
  terminalConeGradU (terminalMinusCoeff q) (carmonSqrtPsi (-p)) u

def terminalPlusValue (p q u : ℝ) : ℝ :=
  terminalPlusCoeff q * sigmaConeValue (carmonSqrtPsi p) u

def terminalMinusValue (p q u : ℝ) : ℝ :=
  terminalMinusCoeff q * sigmaConeValue (carmonSqrtPsi (-p)) u

theorem hasDerivAt_terminalPlusValue_p (p q u : ℝ) :
    HasDerivAt (fun s ↦ terminalPlusValue s q u)
      (terminalPlusGradP p q u) p := by
  have hr := (hasDerivAt_sigmaConeValue_rho
    (u := u) (carmonSqrtPsi_nonneg p)).comp p (hasDerivAt_carmonSqrtPsi p)
  have hmul := (hasDerivAt_const p (terminalPlusCoeff q)).mul hr
  have hfun :
      (fun s : ℝ ↦ terminalPlusValue s q u) =
        (fun _ : ℝ ↦ terminalPlusCoeff q) *
          ((fun r : ℝ ↦ sigmaConeValue r u) ∘ carmonSqrtPsi) := by
    funext s
    change terminalPlusValue s q u =
      terminalPlusCoeff q * sigmaConeValue (carmonSqrtPsi s) u
    rfl
  have hderiv :
      terminalPlusGradP p q u =
        0 * sigmaConeValue (carmonSqrtPsi p) u +
          terminalPlusCoeff q *
            (sigmaConeGradRho (carmonSqrtPsi p) u * carmonSqrtPsiDeriv p) := by
    unfold terminalPlusGradP terminalConeGradP
    ring
  rw [hfun, hderiv]
  exact hmul

theorem hasDerivAt_terminalPlusValue_q (p q u : ℝ) :
    HasDerivAt (fun s ↦ terminalPlusValue p s u)
      (terminalPlusGradQ p q u) q := by
  have hmul := (hasDerivAt_terminalPlusCoeff q).mul
    (hasDerivAt_const q (sigmaConeValue (carmonSqrtPsi p) u))
  change HasDerivAt (fun s : ℝ ↦ terminalPlusValue p s u) _ q at hmul
  apply hmul.congr_deriv
  simp [terminalPlusGradQ, terminalConeGradQ]

theorem hasDerivAt_terminalPlusValue_u (p q u : ℝ) :
    HasDerivAt (fun s ↦ terminalPlusValue p q s)
      (terminalPlusGradU p q u) u := by
  have hu := hasDerivAt_sigmaConeValue_u
    (u := u) (carmonSqrtPsi_nonneg p)
  have hmul := (hasDerivAt_const u (terminalPlusCoeff q)).mul hu
  change HasDerivAt (fun s : ℝ ↦ terminalPlusValue p q s) _ u at hmul
  apply hmul.congr_deriv
  simp [terminalPlusGradU, terminalConeGradU]

theorem hasDerivAt_terminalMinusValue_p (p q u : ℝ) :
    HasDerivAt (fun s ↦ terminalMinusValue s q u)
      (terminalMinusGradP p q u) p := by
  have hneg : HasDerivAt (fun s : ℝ ↦ -s) (-1) p :=
    (hasDerivAt_id p).neg
  have hsqrt := (hasDerivAt_carmonSqrtPsi (-p)).comp p hneg
  have hr := (hasDerivAt_sigmaConeValue_rho
    (u := u) (carmonSqrtPsi_nonneg (-p))).comp p hsqrt
  have hmul := (hasDerivAt_const p (terminalMinusCoeff q)).mul hr
  have hfun :
      (fun s : ℝ ↦ terminalMinusValue s q u) =
        (fun _ : ℝ ↦ terminalMinusCoeff q) *
          ((fun r : ℝ ↦ sigmaConeValue r u) ∘
            (carmonSqrtPsi ∘ fun s : ℝ ↦ -s)) := by
    funext s
    change terminalMinusValue s q u =
      terminalMinusCoeff q * sigmaConeValue (carmonSqrtPsi (-s)) u
    rfl
  have hderiv :
      terminalMinusGradP p q u =
        0 * sigmaConeValue (carmonSqrtPsi (-p)) u +
          terminalMinusCoeff q *
            (sigmaConeGradRho (carmonSqrtPsi (-p)) u *
              (carmonSqrtPsiDeriv (-p) * -1)) := by
    unfold terminalMinusGradP terminalConeGradP
    ring
  rw [hfun, hderiv]
  exact hmul

theorem hasDerivAt_terminalMinusValue_q (p q u : ℝ) :
    HasDerivAt (fun s ↦ terminalMinusValue p s u)
      (terminalMinusGradQ p q u) q := by
  have hmul := (hasDerivAt_terminalMinusCoeff q).mul
    (hasDerivAt_const q (sigmaConeValue (carmonSqrtPsi (-p)) u))
  change HasDerivAt (fun s : ℝ ↦ terminalMinusValue p s u) _ q at hmul
  apply hmul.congr_deriv
  simp [terminalMinusGradQ, terminalConeGradQ]

theorem hasDerivAt_terminalMinusValue_u (p q u : ℝ) :
    HasDerivAt (fun s ↦ terminalMinusValue p q s)
      (terminalMinusGradU p q u) u := by
  have hu := hasDerivAt_sigmaConeValue_u
    (u := u) (carmonSqrtPsi_nonneg (-p))
  have hmul := (hasDerivAt_const u (terminalMinusCoeff q)).mul hu
  change HasDerivAt (fun s : ℝ ↦ terminalMinusValue p q s) _ u at hmul
  apply hmul.congr_deriv
  simp [terminalMinusGradU, terminalConeGradU]

theorem terminalPlusGradP_abs_sub_le (p q u p' q' u' : ℝ) :
    |terminalPlusGradP p q u - terminalPlusGradP p' q' u'| ≤
      terminalConeSmoothC * (|p - p'| + |q - q'| + |u - u'|) := by
  unfold terminalPlusGradP
  exact terminalConeGradP_abs_sub_le
    (dp := |p - p'|) (dq := |q - q'|)
    (carmonSqrtPsi_nonneg p) (carmonSqrtPsi_nonneg p')
    (carmonSqrtPsi_le_two p) (carmonSqrtPsi_le_two p')
    (carmonSqrtPsi_abs_sub_le p p')
    (abs_carmonSqrtPsiDeriv_le_thirtyTwo p)
    (abs_carmonSqrtPsiDeriv_le_thirtyTwo p')
    (carmonSqrtPsiDeriv_abs_sub_le p p')
    (terminalPlusCoeff_abs_le q) (terminalPlusCoeff_abs_le q')
    (terminalPlusCoeff_abs_sub_le q q')
    (abs_nonneg _) (abs_nonneg _)

theorem terminalPlusGradQ_abs_sub_le (p q u p' q' u' : ℝ) :
    |terminalPlusGradQ p q u - terminalPlusGradQ p' q' u'| ≤
      terminalConeSmoothC * (|p - p'| + |q - q'| + |u - u'|) := by
  unfold terminalPlusGradQ
  exact terminalConeGradQ_abs_sub_le
    (dp := |p - p'|) (dq := |q - q'|)
    (carmonSqrtPsi_nonneg p) (carmonSqrtPsi_nonneg p')
    (carmonSqrtPsi_le_two p) (carmonSqrtPsi_le_two p')
    (carmonSqrtPsi_abs_sub_le p p')
    (terminalPlusCoeffDeriv_abs_le q)
    (terminalPlusCoeffDeriv_abs_le q')
    (terminalPlusCoeffDeriv_abs_sub_le q q')
    (abs_nonneg _) (abs_nonneg _)

theorem terminalPlusGradU_abs_sub_le (p q u p' q' u' : ℝ) :
    |terminalPlusGradU p q u - terminalPlusGradU p' q' u'| ≤
      terminalConeSmoothC * (|p - p'| + |q - q'| + |u - u'|) := by
  unfold terminalPlusGradU
  exact terminalConeGradU_abs_sub_le
    (dp := |p - p'|) (dq := |q - q'|)
    (carmonSqrtPsi_nonneg p) (carmonSqrtPsi_nonneg p')
    (carmonSqrtPsi_le_two p) (carmonSqrtPsi_le_two p')
    (carmonSqrtPsi_abs_sub_le p p')
    (terminalPlusCoeff_abs_le q) (terminalPlusCoeff_abs_le q')
    (terminalPlusCoeff_abs_sub_le q q')
    (abs_nonneg _) (abs_nonneg _)

theorem terminalMinusGradP_abs_sub_le (p q u p' q' u' : ℝ) :
    |terminalMinusGradP p q u - terminalMinusGradP p' q' u'| ≤
      terminalConeSmoothC * (|p - p'| + |q - q'| + |u - u'|) := by
  unfold terminalMinusGradP
  exact terminalConeGradP_abs_sub_le
    (dp := |p - p'|) (dq := |q - q'|)
    (carmonSqrtPsi_nonneg (-p)) (carmonSqrtPsi_nonneg (-p'))
    (carmonSqrtPsi_le_two (-p)) (carmonSqrtPsi_le_two (-p'))
    (carmonSqrtPsi_neg_abs_sub_le p p')
    (neg_carmonSqrtPsiDeriv_abs_le p)
    (neg_carmonSqrtPsiDeriv_abs_le p')
    (neg_carmonSqrtPsiDeriv_abs_sub_le p p')
    (terminalMinusCoeff_abs_le q) (terminalMinusCoeff_abs_le q')
    (terminalMinusCoeff_abs_sub_le q q')
    (abs_nonneg _) (abs_nonneg _)

theorem terminalMinusGradQ_abs_sub_le (p q u p' q' u' : ℝ) :
    |terminalMinusGradQ p q u - terminalMinusGradQ p' q' u'| ≤
      terminalConeSmoothC * (|p - p'| + |q - q'| + |u - u'|) := by
  unfold terminalMinusGradQ
  exact terminalConeGradQ_abs_sub_le
    (dp := |p - p'|) (dq := |q - q'|)
    (carmonSqrtPsi_nonneg (-p)) (carmonSqrtPsi_nonneg (-p'))
    (carmonSqrtPsi_le_two (-p)) (carmonSqrtPsi_le_two (-p'))
    (carmonSqrtPsi_neg_abs_sub_le p p')
    (terminalMinusCoeffDeriv_abs_le q)
    (terminalMinusCoeffDeriv_abs_le q')
    (terminalMinusCoeffDeriv_abs_sub_le q q')
    (abs_nonneg _) (abs_nonneg _)

theorem terminalMinusGradU_abs_sub_le (p q u p' q' u' : ℝ) :
    |terminalMinusGradU p q u - terminalMinusGradU p' q' u'| ≤
      terminalConeSmoothC * (|p - p'| + |q - q'| + |u - u'|) := by
  unfold terminalMinusGradU
  exact terminalConeGradU_abs_sub_le
    (dp := |p - p'|) (dq := |q - q'|)
    (carmonSqrtPsi_nonneg (-p)) (carmonSqrtPsi_nonneg (-p'))
    (carmonSqrtPsi_le_two (-p)) (carmonSqrtPsi_le_two (-p'))
    (carmonSqrtPsi_neg_abs_sub_le p p')
    (terminalMinusCoeff_abs_le q) (terminalMinusCoeff_abs_le q')
    (terminalMinusCoeff_abs_sub_le q q')
    (abs_nonneg _) (abs_nonneg _)

end

end NCPLVerification
