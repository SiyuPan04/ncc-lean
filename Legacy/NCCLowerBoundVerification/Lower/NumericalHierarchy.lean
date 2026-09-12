import Mathlib

/-!
# Explicit compatible numerical constants

The proof of `lem:constants` repeatedly says to choose the next numerical
constant sufficiently small or large.  Here the gate and threshold part of
that dependency chain is realized by closed formulas and checked exactly.
-/

namespace NCCLowerBoundVerification

/-- The constants and all inequalities in groups (i)--(ii) of
`lem:constants`. -/
structure GateThresholdConstants (theta xi0 xi1 xi2 : ℝ) where
  gamma : ℝ
  mu : ℝ
  beta : ℝ
  alpha : ℝ
  abar : ℝ
  deltaS : ℝ
  Bs : ℝ
  gamma_pos : 0 < gamma
  gamma_le_half : gamma ≤ 1 / 2
  mu_pos : 0 < mu
  beta_pos : 0 < beta
  alpha_pos : 0 < alpha
  abar_gt_one : 1 < abar
  deltaS_pos : 0 < deltaS
  deltaS_lt_one : deltaS < 1
  Bs_gt_three : 3 < Bs
  gate_curvature : -3 * (1 - theta) + 2 * gamma * (1 + theta) ≤ -1
  order_margin : 1 ≤ mu * xi0
  exit_margin : 1 ≤ beta * xi0 ^ 2
  entrance_margin :
    -alpha * xi0 + 2 * gamma + 4 * gamma * (1 + theta) ≤ -1
  threshold_margin :
    1 ≤ -alpha * xi1 + (12 + 2 * gamma) * abar - 6 * (1 + theta)
  clip_width_margin : 2 * beta * xi1 * xi2 * deltaS ≤ 1 / 2

/-- Explicit witnesses for the gate and threshold hierarchy. -/
theorem gateThresholdConstants_nonempty
    {theta xi0 xi1 xi2 : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1 / 10)
    (hxi0 : 0 < xi0) (hxi1 : 0 < xi1) (hxi2 : 0 < xi2) :
    Nonempty (GateThresholdConstants theta xi0 xi1 xi2) := by
  let gamma : ℝ := (2 - 3 * theta) / (4 * (1 + theta))
  have htheta_lt_two_thirds : theta < 2 / 3 := by linarith
  have hnum : 0 < 2 - 3 * theta := by linarith
  have hone : 0 < 1 + theta := by linarith
  have hden : 0 < 4 * (1 + theta) := mul_pos (by norm_num) hone
  have hgamma : 0 < gamma := div_pos hnum hden
  have hgamma_mul : gamma * (4 * (1 + theta)) = 2 - 3 * theta := by
    dsimp [gamma]
    field_simp [ne_of_gt hone]
  have hgamma_le : gamma ≤ 1 / 2 := by
    rw [div_le_iff₀ hden]
    field_simp [ne_of_gt hone]
    nlinarith
  have hgate : -3 * (1 - theta) + 2 * gamma * (1 + theta) ≤ -1 := by
    nlinarith
  let mu : ℝ := 1 / xi0
  let beta : ℝ := 1 / xi0 ^ 2
  have hmu : 0 < mu := div_pos zero_lt_one hxi0
  have hxi0sq : 0 < xi0 ^ 2 := sq_pos_of_pos hxi0
  have hbeta : 0 < beta := div_pos zero_lt_one hxi0sq
  have hmu_eq : mu * xi0 = 1 := by
    dsimp [mu]
    field_simp [ne_of_gt hxi0]
  have hbeta_eq : beta * xi0 ^ 2 = 1 := by
    dsimp [beta]
    field_simp [ne_of_gt hxi0sq]
  let alpha : ℝ :=
    (1 + 2 * gamma + 4 * gamma * (1 + theta)) / xi0
  have halpha_num : 0 < 1 + 2 * gamma + 4 * gamma * (1 + theta) := by
    positivity
  have halpha : 0 < alpha := div_pos halpha_num hxi0
  have halpha_eq :
      alpha * xi0 = 1 + 2 * gamma + 4 * gamma * (1 + theta) := by
    dsimp [alpha]
    field_simp [ne_of_gt hxi0]
  have hentrance :
      -alpha * xi0 + 2 * gamma + 4 * gamma * (1 + theta) ≤ -1 := by
    nlinarith [halpha_eq]
  have hcoef : 0 < 12 + 2 * gamma := by positivity
  let abar : ℝ :=
    1 + (1 + alpha * xi1 + 6 * (1 + theta)) / (12 + 2 * gamma)
  have habar_num : 0 < 1 + alpha * xi1 + 6 * (1 + theta) := by
    positivity
  have habar : 1 < abar := by
    dsimp [abar]
    have := div_pos habar_num hcoef
    linarith
  have habar_mul :
      (12 + 2 * gamma) *
          ((1 + alpha * xi1 + 6 * (1 + theta)) / (12 + 2 * gamma)) =
        1 + alpha * xi1 + 6 * (1 + theta) := by
    field_simp [ne_of_gt hcoef]
  have hthreshold :
      1 ≤ -alpha * xi1 + (12 + 2 * gamma) * abar - 6 * (1 + theta) := by
    dsimp [abar]
    rw [mul_add, mul_one, habar_mul]
    linarith
  have hprod : 0 < 4 * beta * xi1 * xi2 := by positivity
  let deltaS : ℝ := min (1 / 2) (1 / (4 * beta * xi1 * xi2))
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  have hinv : 0 < 1 / (4 * beta * xi1 * xi2) := div_pos zero_lt_one hprod
  have hdelta : 0 < deltaS := lt_min hhalf hinv
  have hdelta_le_half : deltaS ≤ 1 / 2 := min_le_left _ _
  have hdelta_lt_one : deltaS < 1 := hdelta_le_half.trans_lt (by norm_num)
  have hdelta_le_inv : deltaS ≤ 1 / (4 * beta * xi1 * xi2) := min_le_right _ _
  have hclip : 2 * beta * xi1 * xi2 * deltaS ≤ 1 / 2 := by
    have hscale : 0 ≤ 2 * beta * xi1 * xi2 := by positivity
    have h := mul_le_mul_of_nonneg_left hdelta_le_inv hscale
    calc
      2 * beta * xi1 * xi2 * deltaS ≤
          2 * beta * xi1 * xi2 * (1 / (4 * beta * xi1 * xi2)) := h
      _ = 1 / 2 := by
        field_simp [ne_of_gt hbeta, ne_of_gt hxi1, ne_of_gt hxi2]
        norm_num
  refine ⟨{
    gamma := gamma
    mu := mu
    beta := beta
    alpha := alpha
    abar := abar
    deltaS := deltaS
    Bs := 4
    gamma_pos := hgamma
    gamma_le_half := hgamma_le
    mu_pos := hmu
    beta_pos := hbeta
    alpha_pos := halpha
    abar_gt_one := habar
    deltaS_pos := hdelta
    deltaS_lt_one := hdelta_lt_one
    Bs_gt_three := by norm_num
    gate_curvature := hgate
    order_margin := by rw [hmu_eq]
    exit_margin := by rw [hbeta_eq]
    entrance_margin := hentrance
    threshold_margin := hthreshold
    clip_width_margin := hclip
  }⟩

/-- Explicit witnesses for the radial and transition part of group (iii).
The quantities `cp`, `cq`, and `cs` are the already established uniform
component bounds from the preceding construction. -/
structure RadialTransitionConstants
    (gamma cp cq cs psi0 deltaS Bs : ℝ) where
  P0 : ℝ
  K : ℝ
  P1 : ℝ
  eta : ℝ
  P0_gt_one : 1 < P0
  P0_lt_P1 : P0 < P1
  K_gt : cq + 1 < K
  eta_pos : 0 < eta
  clip_range :
    let hs := (3 + deltaS / 2) / 2
    hs / (2 * (P0 + 2)) ≤ min (deltaS / 2) (Bs - 3)
  P0_margin : ∀ r ≥ P0,
    gamma * r ^ 2 ≤ 2 * gamma * r ^ 2 - cp * r
  P1_margin : ∀ r ≥ P1,
    (1 / 2 : ℝ) * r ^ 2 ≤ 2 * (K - cq) * r ^ 2 - cp * r
  transition_margin : cs + 1 ≤ eta * psi0

/-- The genuinely earlier spatial part of group (iii).  In the TeX proof
`P₀,K,P₁` are fixed before the memory remainder `c_s` is bounded. -/
structure RadialSpatialConstants
    (gamma cp cq deltaS Bs : ℝ) where
  P0 : ℝ
  K : ℝ
  P1 : ℝ
  P0_gt_one : 1 < P0
  P0_lt_P1 : P0 < P1
  K_gt : cq + 1 < K
  clip_range :
    let hs := (3 + deltaS / 2) / 2
    hs / (2 * (P0 + 2)) ≤ min (deltaS / 2) (Bs - 3)
  P0_margin : ∀ r ≥ P0,
    gamma * r ^ 2 ≤ 2 * gamma * r ^ 2 - cp * r
  P1_margin : ∀ r ≥ P1,
    (1 / 2 : ℝ) * r ^ 2 ≤ 2 * (K - cq) * r ^ 2 - cp * r

/-- The final dependency: after a genuine memory bound `c_s` is known,
choose only `eta`. -/
structure TransitionEtaConstants (cs psi0 : ℝ) where
  eta : ℝ
  eta_pos : 0 < eta
  transition_margin : cs + 1 ≤ eta * psi0

theorem radialTransitionConstants_nonempty
    {gamma cp cq cs psi0 deltaS Bs : ℝ}
    (hgamma : 0 < gamma) (hcp : 0 < cp) (hcq : 0 < cq)
    (hcs : 0 < cs) (hpsi0 : 0 < psi0)
    (hdelta : 0 < deltaS) (hBs : 3 < Bs) :
    Nonempty (RadialTransitionConstants gamma cp cq cs psi0 deltaS Bs) := by
  let hs : ℝ := (3 + deltaS / 2) / 2
  have hhs : 0 < hs := by dsimp [hs]; positivity
  let P0 : ℝ := max 2
    (max (cp / gamma + 1)
      (max (hs / deltaS - 2 + 1) (hs / (2 * (Bs - 3)) - 2 + 1)))
  have hP0two : 2 ≤ P0 := le_max_left _ _
  have hP0one : 1 < P0 := lt_of_lt_of_le (by norm_num) hP0two
  have houter :
      max (cp / gamma + 1)
        (max (hs / deltaS - 2 + 1) (hs / (2 * (Bs - 3)) - 2 + 1)) ≤ P0 :=
    le_max_right _ _
  have hP0cp : cp / gamma + 1 ≤ P0 :=
    (le_max_left _ _).trans houter
  have hP0delta : hs / deltaS - 2 + 1 ≤ P0 :=
    (le_max_left _ _).trans ((le_max_right _ _).trans houter)
  have hP0Bs : hs / (2 * (Bs - 3)) - 2 + 1 ≤ P0 :=
    (le_max_right _ _).trans ((le_max_right _ _).trans houter)
  have hP0pos2 : 0 < P0 + 2 := by linarith
  have hdelta_product : hs ≤ deltaS * (P0 + 2) := by
    have hquot : hs / deltaS < P0 + 2 := by linarith
    have := (div_lt_iff₀ hdelta).1 hquot
    linarith
  have hBspos : 0 < Bs - 3 := sub_pos.mpr hBs
  have hBsden : 0 < 2 * (Bs - 3) := mul_pos (by norm_num) hBspos
  have hBs_product : hs ≤ (Bs - 3) * (2 * (P0 + 2)) := by
    have hquot : hs / (2 * (Bs - 3)) < P0 + 2 := by linarith
    have hmul := (div_lt_iff₀ hBsden).1 hquot
    nlinarith
  have hclipDelta : hs / (2 * (P0 + 2)) ≤ deltaS / 2 := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hP0pos2) (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hclipBs : hs / (2 * (P0 + 2)) ≤ Bs - 3 := by
    rw [div_le_iff₀ (mul_pos (by norm_num) hP0pos2)]
    nlinarith
  have hclip : hs / (2 * (P0 + 2)) ≤ min (deltaS / 2) (Bs - 3) :=
    le_min hclipDelta hclipBs
  have hP0ratio : cp / gamma < P0 := by linarith
  have hP0gamma : cp < gamma * P0 := by
    simpa [mul_comm] using (div_lt_iff₀ hgamma).1 hP0ratio
  have hP0margin : ∀ r ≥ P0,
      gamma * r ^ 2 ≤ 2 * gamma * r ^ 2 - cp * r := by
    intro r hr
    have hP0pos : 0 < P0 := zero_lt_one.trans hP0one
    have hrpos : 0 ≤ r := le_trans hP0pos.le hr
    have hgr : cp ≤ gamma * r :=
      (le_of_lt hP0gamma).trans (mul_le_mul_of_nonneg_left hr hgamma.le)
    nlinarith [mul_nonneg hrpos (sub_nonneg.mpr hgr)]
  let K : ℝ := cq + 2
  have hK : cq + 1 < K := by dsimp [K]; linarith
  let den : ℝ := 2 * (K - cq) - 1 / 2
  have hden : 0 < den := by dsimp [den, K]; norm_num
  let P1 : ℝ := max (P0 + 1) (cp / den + 1)
  have hP1P0 : P0 < P1 :=
    lt_of_lt_of_le (lt_add_one P0) (le_max_left _ _)
  have hP1ratioPlus : cp / den + 1 ≤ P1 := le_max_right _ _
  have hP1ratio : cp / den < P1 := by linarith
  have hP1den : cp < den * P1 := by
    simpa [mul_comm] using (div_lt_iff₀ hden).1 hP1ratio
  have hP1pos : 0 < P1 := zero_lt_one.trans (hP0one.trans hP1P0)
  have hP1margin : ∀ r ≥ P1,
      (1 / 2 : ℝ) * r ^ 2 ≤ 2 * (K - cq) * r ^ 2 - cp * r := by
    intro r hr
    have hrnonneg : 0 ≤ r := le_trans hP1pos.le hr
    have hdr : cp ≤ den * r :=
      (le_of_lt hP1den).trans (mul_le_mul_of_nonneg_left hr hden.le)
    dsimp [den] at hdr
    nlinarith [mul_nonneg hrnonneg (sub_nonneg.mpr hdr)]
  let eta : ℝ := (cs + 1) / psi0
  have heta : 0 < eta := div_pos (by linarith) hpsi0
  have hetamargin : cs + 1 ≤ eta * psi0 := by
    dsimp [eta]
    field_simp [ne_of_gt hpsi0]
    norm_num
  refine ⟨{
    P0 := P0
    K := K
    P1 := P1
    eta := eta
    P0_gt_one := hP0one
    P0_lt_P1 := hP1P0
    K_gt := hK
    eta_pos := heta
    clip_range := by simpa only [hs] using hclip
    P0_margin := hP0margin
    P1_margin := hP1margin
    transition_margin := hetamargin
  }⟩

/-- The spatial witnesses can be selected before any memory-remainder bound
is known.  This is the dependency order used in the TeX construction. -/
theorem radialSpatialConstants_nonempty
    {gamma cp cq deltaS Bs : ℝ}
    (hgamma : 0 < gamma) (hcp : 0 < cp) (hcq : 0 < cq)
    (hdelta : 0 < deltaS) (hBs : 3 < Bs) :
    Nonempty (RadialSpatialConstants gamma cp cq deltaS Bs) := by
  obtain ⟨R⟩ := radialTransitionConstants_nonempty
    hgamma hcp hcq (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1) hdelta hBs
  exact ⟨{
    P0 := R.P0
    K := R.K
    P1 := R.P1
    P0_gt_one := R.P0_gt_one
    P0_lt_P1 := R.P0_lt_P1
    K_gt := R.K_gt
    clip_range := R.clip_range
    P0_margin := R.P0_margin
    P1_margin := R.P1_margin
  }⟩

/-- Once `c_s` has actually been proved finite, `eta` is the only remaining
constant in the hierarchy. -/
theorem transitionEtaConstants_nonempty
    {cs psi0 : ℝ} (hcs : 0 ≤ cs) (hpsi0 : 0 < psi0) :
    Nonempty (TransitionEtaConstants cs psi0) := by
  let eta : ℝ := (cs + 1) / psi0
  have heta : 0 < eta := div_pos (by linarith) hpsi0
  refine ⟨{
    eta := eta
    eta_pos := heta
    transition_margin := ?_
  }⟩
  dsimp [eta]
  rw [div_mul_cancel₀]
  exact ne_of_gt hpsi0

/-- Assemble the two dependency-correct stages into the record consumed by
the later radial estimates. -/
def assembleRadialTransition
    {gamma cp cq cs psi0 deltaS Bs : ℝ}
    (S : RadialSpatialConstants gamma cp cq deltaS Bs)
    (E : TransitionEtaConstants cs psi0) :
    RadialTransitionConstants gamma cp cq cs psi0 deltaS Bs := {
  P0 := S.P0
  K := S.K
  P1 := S.P1
  eta := E.eta
  P0_gt_one := S.P0_gt_one
  P0_lt_P1 := S.P0_lt_P1
  K_gt := S.K_gt
  eta_pos := E.eta_pos
  clip_range := S.clip_range
  P0_margin := S.P0_margin
  P1_margin := S.P1_margin
  transition_margin := E.transition_margin
}

/-- Uniform coefficient bounds produce the `c_q` inequality in
`eq:Cq`.  This is stated pointwise so it applies immediately to the concrete
families `c₁,n` and `c₂,n`. -/
theorem quadraticCorrection_remainder_bound
    {c1 c2 gamma C a b : ℝ}
    (hC : 0 ≤ C) (hgamma : 0 ≤ gamma)
    (hc1 : |c1| ≤ C) (hc2 : |c2| ≤ C) :
    -2 * (C + gamma) * (a ^ 2 + b ^ 2) ≤
      2 * (c1 + gamma) * a ^ 2 + 2 * (c2 + gamma) * b ^ 2 := by
  have hc1lower : -C ≤ c1 := (abs_le.mp hc1).1
  have hc2lower : -C ≤ c2 := (abs_le.mp hc2).1
  have ha : 0 ≤ a ^ 2 := sq_nonneg a
  have hb : 0 ≤ b ^ 2 := sq_nonneg b
  have h1 : 0 ≤ (c1 + C) * a ^ 2 :=
    mul_nonneg (by linarith) ha
  have h2 : 0 ≤ (c2 + C) * b ^ 2 :=
    mul_nonneg (by linarith) hb
  nlinarith

theorem numericalCq_pos {C gamma : ℝ} (hC : 0 < C) (hgamma : 0 ≤ gamma) :
    0 < C + gamma := by linarith

end NCCLowerBoundVerification
