import NCPLVerification.GateDerivatives
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Global Lipschitz estimates for the scalar gates
-/

namespace NCPLVerification

noncomputable section

theorem sigma_lipschitz : LipschitzWith (3 / 2 : NNReal) sigma := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_sigma
  intro x
  rw [deriv_sigma, ← NNReal.coe_le_coe]
  simp only [coe_nnnorm, NNReal.coe_div, NNReal.coe_ofNat]
  rw [Real.norm_eq_abs, abs_of_nonneg (sigmaDeriv_nonneg x)]
  exact sigmaDeriv_le_three_halves x

theorem beta_lipschitz : LipschitzWith (2 : NNReal) beta := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_beta
  intro x
  rw [deriv_beta, ← NNReal.coe_le_coe]
  simp only [coe_nnnorm, NNReal.coe_ofNat]
  rw [Real.norm_eq_abs, abs_of_nonneg (betaDeriv_nonneg x)]
  exact betaDeriv_le_two x

theorem sigma_abs_sub_le (x y : ℝ) :
    |sigma x - sigma y| ≤ 2 * |x - y| := by
  have h := sigma_lipschitz.norm_sub_le x y
  simp only [Real.norm_eq_abs, NNReal.coe_div, NNReal.coe_ofNat] at h
  nlinarith [abs_nonneg (x - y)]

theorem beta_abs_sub_le (x y : ℝ) :
    |beta x - beta y| ≤ 2 * |x - y| := by
  simpa [Real.norm_eq_abs] using beta_lipschitz.norm_sub_le x y

theorem sigmaDeriv_abs_sub_le (x y : ℝ) :
    |sigmaDeriv x - sigmaDeriv y| ≤ 6 * |x - y| := by
  wlog hxy : x ≤ y generalizing x y
  · have hyx : y ≤ x := le_of_not_ge hxy
    simpa [abs_sub_comm] using this y x hyx
  by_cases hy0 : y ≤ 0
  · have hx0 : x ≤ 0 := hxy.trans hy0
    simp [sigmaDeriv, hx0, hy0]
  by_cases hx0 : x ≤ 0
  · by_cases hy1 : y ≤ 1
    · have hypos : 0 < y := lt_of_not_ge hy0
      rw [sigmaDeriv, if_pos hx0, sigmaDeriv, if_neg (not_le.mpr hypos),
        if_pos hy1]
      have hp : 0 ≤ 6 * y - 6 * y ^ 2 := by
        nlinarith [mul_nonneg hypos.le (sub_nonneg.mpr hy1)]
      rw [zero_sub, abs_neg, abs_of_nonneg hp,
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      nlinarith [sq_nonneg y]
    · have hyone : 1 < y := lt_of_not_ge hy1
      rw [sigmaDeriv, if_pos hx0, sigmaDeriv,
        if_neg (not_le.mpr (lt_trans (by norm_num) hyone)),
        if_neg (not_le.mpr hyone)]
      simp
  · have hxpos : 0 < x := lt_of_not_ge hx0
    by_cases hx1 : x ≤ 1
    · by_cases hy1 : y ≤ 1
      · rw [sigmaDeriv, if_neg (not_le.mpr hxpos), if_pos hx1,
          sigmaDeriv, if_neg (not_le.mpr (hxpos.trans_le hxy)), if_pos hy1]
        have heq :
            (6 * x - 6 * x ^ 2) - (6 * y - 6 * y ^ 2) =
              6 * (x - y) * (1 - x - y) := by ring
        have hs : |1 - x - y| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith
        rw [heq, abs_mul, abs_mul,
          abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
        nlinarith [abs_nonneg (x - y)]
      · have hyone : 1 < y := lt_of_not_ge hy1
        rw [sigmaDeriv, if_neg (not_le.mpr hxpos), if_pos hx1,
          sigmaDeriv, if_neg (not_le.mpr (lt_trans (by norm_num) hyone)),
          if_neg (not_le.mpr hyone)]
        have hp : 0 ≤ 6 * x - 6 * x ^ 2 := by
          nlinarith [mul_nonneg hxpos.le (sub_nonneg.mpr hx1)]
        rw [sub_zero, abs_of_nonneg hp,
          abs_of_nonpos (sub_nonpos.mpr hxy)]
        nlinarith [sq_nonneg (1 - x)]
    · have hxone : 1 < x := lt_of_not_ge hx1
      have hyone : 1 < y := hxone.trans_le hxy
      rw [sigmaDeriv, if_neg (not_le.mpr hxpos), if_neg (not_le.mpr hxone),
        sigmaDeriv, if_neg (not_le.mpr (lt_trans (by norm_num) hyone)),
        if_neg (not_le.mpr hyone)]
      simp

def unitClamp (t : ℝ) : ℝ := min (max t 0) 1

def betaLeftSlope (u : ℝ) : ℝ := 4 * u - 3 * u ^ 2

def betaRightSlope (u : ℝ) : ℝ := 1 + 2 * u - 3 * u ^ 2

theorem unitClamp_zero {t : ℝ} (h : t ≤ 0) : unitClamp t = 0 := by
  simp [unitClamp, h]

theorem unitClamp_self {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    unitClamp t = t := by simp [unitClamp, h0, h1]

theorem unitClamp_one {t : ℝ} (h : 1 ≤ t) : unitClamp t = 1 := by
  have h0 : 0 ≤ t := by linarith
  simp [unitClamp, h, h0]

theorem unitClamp_nonneg (t : ℝ) : 0 ≤ unitClamp t := by
  simp [unitClamp]

theorem unitClamp_le_one (t : ℝ) : unitClamp t ≤ 1 := by
  simp [unitClamp]

theorem unitClamp_lipschitz : LipschitzWith (1 : NNReal) unitClamp := by
  unfold unitClamp
  exact (LipschitzWith.id.max_const (0 : ℝ)).min_const 1

theorem unitClamp_abs_sub_le (x y : ℝ) :
    |unitClamp x - unitClamp y| ≤ |x - y| := by
  simpa [Real.norm_eq_abs] using unitClamp_lipschitz.norm_sub_le x y

theorem betaDeriv_clamp_repr (t : ℝ) : betaDeriv t =
    betaLeftSlope (unitClamp (t + 1)) +
      betaRightSlope (unitClamp (t - 1)) - 1 := by
  by_cases hm1 : t ≤ -1
  · rw [unitClamp_zero (by linarith : t + 1 ≤ 0),
      unitClamp_zero (by linarith : t - 1 ≤ 0)]
    simp [betaDeriv, hm1, betaLeftSlope, betaRightSlope]
  · have hgtm1 : -1 < t := lt_of_not_ge hm1
    by_cases h0 : t ≤ 0
    · rw [unitClamp_self (by linarith : 0 ≤ t + 1)
          (by linarith : t + 1 ≤ 1),
        unitClamp_zero (by linarith : t - 1 ≤ 0)]
      simp [betaDeriv, hm1, h0, betaLeftSlope, betaRightSlope]
    · have hgt0 : 0 < t := lt_of_not_ge h0
      by_cases h1 : t ≤ 1
      · rw [unitClamp_one (by linarith : 1 ≤ t + 1),
          unitClamp_zero (by linarith : t - 1 ≤ 0)]
        simp [betaDeriv, hm1, h0, h1, betaLeftSlope, betaRightSlope] <;> ring
      · have hgt1 : 1 < t := lt_of_not_ge h1
        by_cases h2 : t ≤ 2
        · rw [unitClamp_one (by linarith : 1 ≤ t + 1),
            unitClamp_self (by linarith : 0 ≤ t - 1)
              (by linarith : t - 1 ≤ 1)]
          simp [betaDeriv, hm1, h0, h1, h2,
            betaLeftSlope, betaRightSlope] <;> ring
        · have hgt2 : 2 < t := lt_of_not_ge h2
          rw [unitClamp_one (by linarith : 1 ≤ t + 1),
            unitClamp_one (by linarith : 1 ≤ t - 1)]
          simp [betaDeriv, hm1, h0, h1, h2,
            betaLeftSlope, betaRightSlope] <;> ring

private theorem betaLeftSlope_abs_sub_le {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    |betaLeftSlope u - betaLeftSlope v| ≤ 4 * |u - v| := by
  have hfac : |4 - 3 * (u + v)| ≤ 4 := by
    rw [abs_le]
    constructor <;> linarith
  have heq : betaLeftSlope u - betaLeftSlope v =
      (u - v) * (4 - 3 * (u + v)) := by
    unfold betaLeftSlope
    ring
  rw [heq, abs_mul]
  nlinarith [abs_nonneg (u - v)]

private theorem betaRightSlope_abs_sub_le {u v : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    |betaRightSlope u - betaRightSlope v| ≤ 4 * |u - v| := by
  have hfac : |2 - 3 * (u + v)| ≤ 4 := by
    rw [abs_le]
    constructor <;> linarith
  have heq : betaRightSlope u - betaRightSlope v =
      (u - v) * (2 - 3 * (u + v)) := by
    unfold betaRightSlope
    ring
  rw [heq, abs_mul]
  nlinarith [abs_nonneg (u - v)]

theorem betaDeriv_abs_sub_le (x y : ℝ) :
    |betaDeriv x - betaDeriv y| ≤ 8 * |x - y| := by
  let ux := unitClamp (x + 1)
  let uy := unitClamp (y + 1)
  let vx := unitClamp (x - 1)
  let vy := unitClamp (y - 1)
  have hp := betaLeftSlope_abs_sub_le
    (unitClamp_nonneg (x + 1)) (unitClamp_le_one (x + 1))
    (unitClamp_nonneg (y + 1)) (unitClamp_le_one (y + 1))
  have hq := betaRightSlope_abs_sub_le
    (unitClamp_nonneg (x - 1)) (unitClamp_le_one (x - 1))
    (unitClamp_nonneg (y - 1)) (unitClamp_le_one (y - 1))
  have hu := unitClamp_abs_sub_le (x + 1) (y + 1)
  have hv := unitClamp_abs_sub_le (x - 1) (y - 1)
  rw [betaDeriv_clamp_repr, betaDeriv_clamp_repr]
  have htri :
      |(betaLeftSlope (unitClamp (x + 1)) -
          betaLeftSlope (unitClamp (y + 1))) +
        (betaRightSlope (unitClamp (x - 1)) -
          betaRightSlope (unitClamp (y - 1)))| ≤
        |betaLeftSlope (unitClamp (x + 1)) -
          betaLeftSlope (unitClamp (y + 1))| +
        |betaRightSlope (unitClamp (x - 1)) -
          betaRightSlope (unitClamp (y - 1))| := abs_add_le _ _
  have heq :
      (betaLeftSlope (unitClamp (x + 1)) +
          betaRightSlope (unitClamp (x - 1)) - 1) -
        (betaLeftSlope (unitClamp (y + 1)) +
          betaRightSlope (unitClamp (y - 1)) - 1) =
      (betaLeftSlope (unitClamp (x + 1)) -
          betaLeftSlope (unitClamp (y + 1))) +
        (betaRightSlope (unitClamp (x - 1)) -
          betaRightSlope (unitClamp (y - 1))) := by ring
  rw [heq]
  have hu' : |unitClamp (x + 1) - unitClamp (y + 1)| ≤ |x - y| := by
    simpa only [add_sub_add_right_eq_sub] using hu
  have hv' : |unitClamp (x - 1) - unitClamp (y - 1)| ≤ |x - y| := by
    simpa only [sub_sub_sub_cancel_right] using hv
  nlinarith

theorem negPart_abs_sub_le (x y : ℝ) :
    |negPart x - negPart y| ≤ |x - y| := by
  have hpos : LipschitzWith (1 : NNReal) (fun t : ℝ => max t 0) :=
    LipschitzWith.id.max_const 0
  have h := hpos.norm_sub_le (-x) (-y)
  have h' : |max (-x) 0 - max (-y) 0| ≤ |-x - -y| := by
    simpa only [Real.norm_eq_abs, NNReal.coe_one, one_mul] using h
  have habs : |-x - -y| = |x - y| := by
    rw [show -x - -y = -(x - y) by ring, abs_neg]
  rw [habs] at h'
  simpa only [negPart, posPart] using h'

theorem posPart_abs_sub_le (x y : ℝ) :
    |posPart x - posPart y| ≤ |x - y| := by
  have hpos : LipschitzWith (1 : NNReal) (fun t : ℝ => max t 0) :=
    LipschitzWith.id.max_const 0
  simpa only [posPart, Real.norm_eq_abs, NNReal.coe_one, one_mul] using
    hpos.norm_sub_le x y

theorem sigma_abs_le_one (s : ℝ) : |sigma s| ≤ 1 := by
  rw [abs_of_nonneg (sigma_nonneg s)]
  exact sigma_le_one s

theorem beta_abs_le_two (t : ℝ) : |beta t| ≤ 2 := by
  rw [abs_le]
  constructor
  · linarith [beta_lower t]
  · exact beta_upper t

theorem gateResidual_abs_sub_le (s t s' t' : ℝ) :
    |gateResidual s t - gateResidual s' t'| ≤
      4 * |s - s'| + 2 * |t - t'| := by
  have hout := posPart_abs_sub_le
    (1 - sigma s * beta t) (1 - sigma s' * beta t')
  have hprod : |sigma s * beta t - sigma s' * beta t'| ≤
      4 * |s - s'| + 2 * |t - t'| := by
    have htri :
        |sigma s * (beta t - beta t') +
          (sigma s - sigma s') * beta t'| ≤
        |sigma s * (beta t - beta t')| +
          |(sigma s - sigma s') * beta t'| := abs_add_le _ _
    have heq : sigma s * beta t - sigma s' * beta t' =
        sigma s * (beta t - beta t') +
          (sigma s - sigma s') * beta t' := by ring
    rw [heq]
    rw [abs_mul, abs_mul] at htri
    have hs := sigma_abs_le_one s
    have hb := beta_abs_le_two t'
    have hdt := beta_abs_sub_le t t'
    have hds := sigma_abs_sub_le s s'
    nlinarith [abs_nonneg (beta t - beta t'),
      abs_nonneg (sigma s - sigma s')]
  unfold gateResidual
  have heq :
      (1 - sigma s * beta t) - (1 - sigma s' * beta t') =
        -(sigma s * beta t - sigma s' * beta t') := by ring
  rw [heq, abs_neg] at hout
  exact hout.trans hprod

end

end NCPLVerification
