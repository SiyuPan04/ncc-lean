import NCPLVerification.GateSmoothness
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# The scalar terminal-gate perspective is globally C1,1

The terminal contribution is a two-homogeneous conic lift of `sigma`.
This file proves global Lipschitz estimates for its two gradient components,
including comparisons across the zero-scale boundary.
-/

namespace NCPLVerification

noncomputable section

theorem sigmaDeriv_of_nonpos {t : ℝ} (ht : t ≤ 0) : sigmaDeriv t = 0 := by
  simp [sigmaDeriv, ht]

theorem sigmaDeriv_of_one_le {t : ℝ} (ht : 1 ≤ t) : sigmaDeriv t = 0 := by
  rcases ht.eq_or_lt with rfl | ht
  · exact sigmaDeriv_one
  · simp [sigmaDeriv, not_le.mpr (by linarith : 0 < t),
      not_le.mpr ht]

theorem sigmaDeriv_abs_le_two (t : ℝ) : |sigmaDeriv t| ≤ 2 := by
  rw [abs_of_nonneg (sigmaDeriv_nonneg t)]
  linarith [sigmaDeriv_le_three_halves t]

theorem sigmaDeriv_clamp_repr (t : ℝ) :
    sigmaDeriv t =
      6 * unitClamp t - 6 * unitClamp t ^ 2 := by
  by_cases h0 : t ≤ 0
  · rw [unitClamp_zero h0, sigmaDeriv_of_nonpos h0]
    ring
  · have ht0 : 0 < t := lt_of_not_ge h0
    by_cases h1 : t ≤ 1
    · rw [unitClamp_self ht0.le h1]
      simp [sigmaDeriv, h0, h1]
    · have ht1 : 1 < t := lt_of_not_ge h1
      rw [unitClamp_one ht1.le, sigmaDeriv_of_one_le ht1.le]
      ring

def sigmaWeightedDeriv (t : ℝ) : ℝ := t * sigmaDeriv t

theorem sigmaWeightedDeriv_clamp_repr (t : ℝ) :
    sigmaWeightedDeriv t =
      unitClamp t *
        (6 * unitClamp t - 6 * unitClamp t ^ 2) := by
  unfold sigmaWeightedDeriv
  rw [sigmaDeriv_clamp_repr]
  by_cases h0 : t ≤ 0
  · rw [unitClamp_zero h0]
    ring
  · have ht0 : 0 < t := lt_of_not_ge h0
    by_cases h1 : t ≤ 1
    · rw [unitClamp_self ht0.le h1]
    · rw [unitClamp_one (le_of_not_ge h1)]
      ring

theorem sigmaWeightedDeriv_abs_le_two (t : ℝ) :
    |sigmaWeightedDeriv t| ≤ 2 := by
  rw [sigmaWeightedDeriv_clamp_repr]
  let c := unitClamp t
  have hc0 : 0 ≤ c := unitClamp_nonneg t
  have hc1 : c ≤ 1 := unitClamp_le_one t
  have hd0 : 0 ≤ 6 * c - 6 * c ^ 2 := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  rw [abs_of_nonneg (mul_nonneg hc0 hd0)]
  nlinarith [sigmaDeriv_le_three_halves c]

private theorem sigmaWeightedPoly_abs_sub_le {c d : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    |c * (6 * c - 6 * c ^ 2) -
        d * (6 * d - 6 * d ^ 2)| ≤ 30 * |c - d| := by
  have heq :
      c * (6 * c - 6 * c ^ 2) - d * (6 * d - 6 * d ^ 2) =
        (c - d) * (6 * (c + d) - 6 * (c ^ 2 + c * d + d ^ 2)) := by
    ring
  have hfac :
      |6 * (c + d) - 6 * (c ^ 2 + c * d + d ^ 2)| ≤ 30 := by
    rw [abs_le]
    constructor <;>
      nlinarith [sq_nonneg c, sq_nonneg d, mul_nonneg hc0 hd0,
        mul_le_mul hc1 hc1 hc0 (by norm_num : (0 : ℝ) ≤ 1),
        mul_le_mul hd1 hd1 hd0 (by norm_num : (0 : ℝ) ≤ 1),
        mul_le_mul hc1 hd1 hd0 (by norm_num : (0 : ℝ) ≤ 1)]
  rw [heq, abs_mul]
  nlinarith [abs_nonneg (c - d)]

theorem sigmaWeightedDeriv_abs_sub_le (x y : ℝ) :
    |sigmaWeightedDeriv x - sigmaWeightedDeriv y| ≤ 30 * |x - y| := by
  rw [sigmaWeightedDeriv_clamp_repr, sigmaWeightedDeriv_clamp_repr]
  have hp := sigmaWeightedPoly_abs_sub_le
    (unitClamp_nonneg x) (unitClamp_le_one x)
    (unitClamp_nonneg y) (unitClamp_le_one y)
  have hc := unitClamp_abs_sub_le x y
  nlinarith [abs_nonneg (unitClamp x - unitClamp y)]

def sigmaRadialField (t : ℝ) : ℝ :=
  2 * sigma t - sigmaWeightedDeriv t

theorem sigmaRadialField_abs_le_four (t : ℝ) :
    |sigmaRadialField t| ≤ 4 := by
  unfold sigmaRadialField
  have htri := abs_sub (2 * sigma t) (sigmaWeightedDeriv t)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at htri
  have hs := sigma_abs_le_one t
  have hw := sigmaWeightedDeriv_abs_le_two t
  nlinarith

theorem sigmaRadialField_abs_sub_le (x y : ℝ) :
    |sigmaRadialField x - sigmaRadialField y| ≤ 34 * |x - y| := by
  unfold sigmaRadialField
  have hs := sigma_abs_sub_le x y
  have hw := sigmaWeightedDeriv_abs_sub_le x y
  have htri := abs_sub
    (2 * (sigma x - sigma y))
    (sigmaWeightedDeriv x - sigmaWeightedDeriv y)
  have heq :
      (2 * sigma x - sigmaWeightedDeriv x) -
          (2 * sigma y - sigmaWeightedDeriv y) =
        2 * (sigma x - sigma y) -
          (sigmaWeightedDeriv x - sigmaWeightedDeriv y) := by ring
  rw [heq]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at htri
  nlinarith [abs_nonneg (sigma x - sigma y)]

theorem ratio_abs_sub {r s v : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    |v / r - v / s| = |v| * (s - r) / (r * s) := by
  have hs : 0 < s := hr.trans_le hrs
  rw [show v / r - v / s = v * (s - r) / (r * s) by
    field_simp [hr.ne', hs.ne']]
  rw [abs_div, abs_mul, abs_of_nonneg (sub_nonneg.mpr hrs),
    abs_of_pos (mul_pos hr hs)]

theorem sigmaDeriv_scale_abs_sub_le {r s v : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) :
    r * |sigmaDeriv (v / r) - sigmaDeriv (v / s)| ≤
      6 * (s - r) := by
  have hs : 0 < s := hr.trans_le hrs
  by_cases hv0 : v ≤ 0
  · have hvr : v / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv0 hr.le
    have hvs : v / s ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv0 hs.le
    simp [sigmaDeriv_of_nonpos hvr, sigmaDeriv_of_nonpos hvs,
      sub_nonneg.mpr hrs]
  by_cases hsv : s ≤ v
  · have hvr : 1 ≤ v / r := by
      apply (le_div_iff₀ hr).2
      simpa using hrs.trans hsv
    have hvs : 1 ≤ v / s := by
      apply (le_div_iff₀ hs).2
      simpa using hsv
    simp [sigmaDeriv_of_one_le hvr, sigmaDeriv_of_one_le hvs,
      sub_nonneg.mpr hrs]
  · have hvpos : 0 < v := lt_of_not_ge hv0
    have hvlt : v < s := lt_of_not_ge hsv
    have hlip := sigmaDeriv_abs_sub_le (v / r) (v / s)
    rw [ratio_abs_sub hr hrs, abs_of_pos hvpos] at hlip
    have hvsle : v / s ≤ 1 := (div_le_one hs).2 hvlt.le
    have hvs0 : 0 ≤ v / s := div_nonneg hvpos.le hs.le
    calc
      r * |sigmaDeriv (v / r) - sigmaDeriv (v / s)| ≤
          r * (6 * (v * (s - r) / (r * s))) :=
        mul_le_mul_of_nonneg_left hlip hr.le
      _ = 6 * (v / s) * (s - r) := by field_simp [hr.ne', hs.ne']
      _ ≤ 6 * 1 * (s - r) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hvsle (by norm_num))
          (sub_nonneg.mpr hrs)
      _ = 6 * (s - r) := by ring

theorem sigmaWeightedDeriv_scale_abs_sub_le {r s v : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) :
    r * |sigmaWeightedDeriv (v / r) -
      sigmaWeightedDeriv (v / s)| ≤ 30 * (s - r) := by
  have hs : 0 < s := hr.trans_le hrs
  by_cases hv0 : v ≤ 0
  · have hvr : v / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv0 hr.le
    have hvs : v / s ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv0 hs.le
    simp [sigmaWeightedDeriv, sigmaDeriv_of_nonpos hvr,
      sigmaDeriv_of_nonpos hvs, sub_nonneg.mpr hrs]
  by_cases hsv : s ≤ v
  · have hvr : 1 ≤ v / r := by
      apply (le_div_iff₀ hr).2
      simpa using hrs.trans hsv
    have hvs : 1 ≤ v / s := by
      apply (le_div_iff₀ hs).2
      simpa using hsv
    simp [sigmaWeightedDeriv, sigmaDeriv_of_one_le hvr,
      sigmaDeriv_of_one_le hvs, sub_nonneg.mpr hrs]
  · have hvpos : 0 < v := lt_of_not_ge hv0
    have hvlt : v < s := lt_of_not_ge hsv
    have hlip := sigmaWeightedDeriv_abs_sub_le (v / r) (v / s)
    rw [ratio_abs_sub hr hrs, abs_of_pos hvpos] at hlip
    have hvsle : v / s ≤ 1 := (div_le_one hs).2 hvlt.le
    calc
      r * |sigmaWeightedDeriv (v / r) - sigmaWeightedDeriv (v / s)| ≤
          r * (30 * (v * (s - r) / (r * s))) :=
        mul_le_mul_of_nonneg_left hlip hr.le
      _ = 30 * (v / s) * (s - r) := by field_simp [hr.ne', hs.ne']
      _ ≤ 30 * 1 * (s - r) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hvsle (by norm_num))
          (sub_nonneg.mpr hrs)
      _ = 30 * (s - r) := by ring

theorem sigmaRadial_scale_abs_sub_le {r s v : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) :
    r * |sigmaRadialField (v / r) - sigmaRadialField (v / s)| ≤
      34 * (s - r) := by
  have hs : 0 < s := hr.trans_le hrs
  by_cases hv0 : v ≤ 0
  · have hvr : v / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv0 hr.le
    have hvs : v / s ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv0 hs.le
    simp [sigmaRadialField, sigmaWeightedDeriv,
      sigma_of_nonpos hvr, sigma_of_nonpos hvs,
      sigmaDeriv_of_nonpos hvr, sigmaDeriv_of_nonpos hvs,
      sub_nonneg.mpr hrs]
  by_cases hsv : s ≤ v
  · have hvr : 1 ≤ v / r := by
      apply (le_div_iff₀ hr).2
      simpa using hrs.trans hsv
    have hvs : 1 ≤ v / s := by
      apply (le_div_iff₀ hs).2
      simpa using hsv
    simp [sigmaRadialField, sigmaWeightedDeriv,
      sigma_of_one_le hvr, sigma_of_one_le hvs,
      sigmaDeriv_of_one_le hvr, sigmaDeriv_of_one_le hvs,
      sub_nonneg.mpr hrs]
  · have hvpos : 0 < v := lt_of_not_ge hv0
    have hvlt : v < s := lt_of_not_ge hsv
    have hlip := sigmaRadialField_abs_sub_le (v / r) (v / s)
    rw [ratio_abs_sub hr hrs, abs_of_pos hvpos] at hlip
    have hvsle : v / s ≤ 1 := (div_le_one hs).2 hvlt.le
    calc
      r * |sigmaRadialField (v / r) - sigmaRadialField (v / s)| ≤
          r * (34 * (v * (s - r) / (r * s))) :=
        mul_le_mul_of_nonneg_left hlip hr.le
      _ = 34 * (v / s) * (s - r) := by field_simp [hr.ne', hs.ne']
      _ ≤ 34 * 1 * (s - r) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hvsle (by norm_num))
          (sub_nonneg.mpr hrs)
      _ = 34 * (s - r) := by ring

theorem sigma_scale_abs_sub_le {r s v : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) :
    r * |sigma (v / r) - sigma (v / s)| ≤ 2 * (s - r) := by
  have hs : 0 < s := hr.trans_le hrs
  by_cases hv0 : v ≤ 0
  · have hvr : v / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv0 hr.le
    have hvs : v / s ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv0 hs.le
    simp [sigma_of_nonpos hvr, sigma_of_nonpos hvs,
      sub_nonneg.mpr hrs]
  by_cases hsv : s ≤ v
  · have hvr : 1 ≤ v / r := by
      apply (le_div_iff₀ hr).2
      simpa using hrs.trans hsv
    have hvs : 1 ≤ v / s := by
      apply (le_div_iff₀ hs).2
      simpa using hsv
    simp [sigma_of_one_le hvr, sigma_of_one_le hvs,
      sub_nonneg.mpr hrs]
  · have hvpos : 0 < v := lt_of_not_ge hv0
    have hvlt : v < s := lt_of_not_ge hsv
    have hlip := sigma_abs_sub_le (v / r) (v / s)
    rw [ratio_abs_sub hr hrs, abs_of_pos hvpos] at hlip
    have hvsle : v / s ≤ 1 := (div_le_one hs).2 hvlt.le
    calc
      r * |sigma (v / r) - sigma (v / s)| ≤
          r * (2 * (v * (s - r) / (r * s))) :=
        mul_le_mul_of_nonneg_left hlip hr.le
      _ = 2 * (v / s) * (s - r) := by field_simp [hr.ne', hs.ne']
      _ ≤ 2 * 1 * (s - r) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hvsle (by norm_num))
          (sub_nonneg.mpr hrs)
      _ = 2 * (s - r) := by ring

def sigmaConeValue (rho u : ℝ) : ℝ :=
  if 0 < rho then rho ^ 2 * sigma (u / rho) else 0

theorem sigmaConeValue_abs_le_sq {rho u : ℝ} (hrho : 0 ≤ rho) :
    |sigmaConeValue rho u| ≤ rho ^ 2 := by
  rcases hrho.eq_or_lt with rfl | hpos
  · simp [sigmaConeValue]
  · rw [sigmaConeValue, if_pos hpos, abs_mul,
      abs_of_nonneg (sq_nonneg rho)]
    have hs := sigma_abs_le_one (u / rho)
    nlinarith [sq_nonneg rho]

private theorem sigmaConeValue_abs_sub_le_ordered {r s u v R : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) (hsR : s ≤ R) :
    |sigmaConeValue r u - sigmaConeValue s v| ≤
      4 * R * (|r - s| + |u - v|) := by
  have hR0 : 0 ≤ R := hr.trans (hrs.trans hsR)
  rcases hr.eq_or_lt with rfl | hrpos
  · have hs0 : 0 ≤ s := hrs
    simp only [sigmaConeValue, lt_self_iff_false, if_false,
      zero_sub, abs_neg]
    by_cases hspos : 0 < s
    · rw [if_pos hspos]
      have hv := sigmaConeValue_abs_le_sq (rho := s) (u := v) hs0
      rw [sigmaConeValue, if_pos hspos] at hv
      rw [abs_of_nonneg hs0]
      nlinarith [sq_nonneg s, abs_nonneg (u - v)]
    · have hsEq : s = 0 := le_antisymm (le_of_not_gt hspos) hs0
      simp [hsEq]
      positivity
  · have hspos : 0 < s := hrpos.trans_le hrs
    simp only [sigmaConeValue, if_pos hrpos, if_pos hspos]
    have hduv := sigma_abs_sub_le (u / r) (v / r)
    have hscale := sigma_scale_abs_sub_le hrpos hrs (v := v)
    have hratio : |u / r - v / r| = |u - v| / r := by
      rw [show u / r - v / r = (u - v) / r by ring,
        abs_div, abs_of_pos hrpos]
    rw [hratio] at hduv
    have hduvScaled :
        r * |sigma (u / r) - sigma (v / r)| ≤ 2 * |u - v| := by
      calc
        r * |sigma (u / r) - sigma (v / r)| ≤
            r * (2 * (|u - v| / r)) :=
          mul_le_mul_of_nonneg_left hduv hrpos.le
        _ = 2 * |u - v| := by field_simp [hrpos.ne']
    have htri := abs_add_le
      (sigma (u / r) - sigma (v / r))
      (sigma (v / r) - sigma (v / s))
    have heqSigma :
        sigma (u / r) - sigma (v / s) =
          (sigma (u / r) - sigma (v / r)) +
            (sigma (v / r) - sigma (v / s)) := by ring
    have hfirst :
        r ^ 2 * |sigma (u / r) - sigma (v / s)| ≤
          2 * R * |u - v| + 2 * R * (s - r) := by
      rw [heqSigma]
      calc
        r ^ 2 * |(sigma (u / r) - sigma (v / r)) +
            (sigma (v / r) - sigma (v / s))| ≤
            r ^ 2 * (|sigma (u / r) - sigma (v / r)| +
              |sigma (v / r) - sigma (v / s)|) :=
          mul_le_mul_of_nonneg_left htri (sq_nonneg r)
        _ = r * (r * |sigma (u / r) - sigma (v / r)|) +
            r * (r * |sigma (v / r) - sigma (v / s)|) := by ring
        _ ≤ R * (2 * |u - v|) + R * (2 * (s - r)) := by
          exact add_le_add
            (mul_le_mul (hrs.trans hsR) hduvScaled (by positivity) hR0)
            (mul_le_mul (hrs.trans hsR) hscale (by positivity) hR0)
        _ = 2 * R * |u - v| + 2 * R * (s - r) := by ring
    have hsv := sigma_abs_le_one (v / s)
    have hsqdiff : |r ^ 2 - s ^ 2| ≤ 2 * R * (s - r) := by
      rw [show r ^ 2 - s ^ 2 = -(s - r) * (s + r) by ring,
        abs_mul, abs_neg, abs_of_nonneg (sub_nonneg.mpr hrs),
        abs_of_nonneg (add_nonneg hspos.le hr)]
      have hsum : s + r ≤ 2 * R := by linarith
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hrs)
    have hdecomp :
        r ^ 2 * sigma (u / r) - s ^ 2 * sigma (v / s) =
          r ^ 2 * (sigma (u / r) - sigma (v / s)) +
            (r ^ 2 - s ^ 2) * sigma (v / s) := by ring
    rw [hdecomp]
    have hab := abs_add_le
      (r ^ 2 * (sigma (u / r) - sigma (v / s)))
      ((r ^ 2 - s ^ 2) * sigma (v / s))
    rw [abs_mul, abs_of_nonneg (sq_nonneg r), abs_mul] at hab
    rw [abs_of_nonpos (sub_nonpos.mpr hrs), neg_sub]
    have hsecond :
        |r ^ 2 - s ^ 2| * |sigma (v / s)| ≤ 2 * R * (s - r) := by
      calc
        |r ^ 2 - s ^ 2| * |sigma (v / s)| ≤
            |r ^ 2 - s ^ 2| * 1 :=
          mul_le_mul_of_nonneg_left hsv (abs_nonneg _)
        _ ≤ 2 * R * (s - r) := by simpa using hsqdiff
    calc
      |r ^ 2 * (sigma (u / r) - sigma (v / s)) +
          (r ^ 2 - s ^ 2) * sigma (v / s)| ≤
          r ^ 2 * |sigma (u / r) - sigma (v / s)| +
            |r ^ 2 - s ^ 2| * |sigma (v / s)| := hab
      _ ≤ (2 * R * |u - v| + 2 * R * (s - r)) +
          2 * R * (s - r) := add_le_add hfirst hsecond
      _ ≤ 4 * R * (s - r + |u - v|) := by
        nlinarith [mul_nonneg hR0 (abs_nonneg (u - v)),
          mul_nonneg hR0 (sub_nonneg.mpr hrs)]

theorem sigmaConeValue_abs_sub_le {r s u v R : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrR : r ≤ R) (hsR : s ≤ R) :
    |sigmaConeValue r u - sigmaConeValue s v| ≤
      4 * R * (|r - s| + |u - v|) := by
  by_cases hrs : r ≤ s
  · exact sigmaConeValue_abs_sub_le_ordered hr hrs hsR
  · have h := sigmaConeValue_abs_sub_le_ordered hs (le_of_not_ge hrs) hrR
      (u := v) (v := u)
    simpa [abs_sub_comm, add_comm] using h

def sigmaConeGradU (rho u : ℝ) : ℝ :=
  if 0 < rho then rho * sigmaDeriv (u / rho) else 0

def sigmaConeGradRho (rho u : ℝ) : ℝ :=
  if 0 < rho then rho * sigmaRadialField (u / rho) else 0

theorem hasDerivAt_sigmaConeValue_u {rho u : ℝ} (hrho : 0 ≤ rho) :
    HasDerivAt (fun q ↦ sigmaConeValue rho q) (sigmaConeGradU rho u) u := by
  rcases hrho.eq_or_lt with rfl | hpos
  · simpa only [sigmaConeValue, lt_self_iff_false, if_false,
      sigmaConeGradU] using hasDerivAt_const u 0
  · have hratio : HasDerivAt (fun q : ℝ ↦ q / rho) (1 / rho) u := by
      exact (hasDerivAt_id u).div_const rho
    have hs := (hasDerivAt_sigma (u / rho)).comp u hratio
    have hmul := (hasDerivAt_const u (rho ^ 2)).mul hs
    have hfun :
        (fun q : ℝ ↦ sigmaConeValue rho q) =
          (fun x : ℝ ↦ rho ^ 2) * (sigma ∘ fun q : ℝ ↦ q / rho) := by
      funext q
      change sigmaConeValue rho q = rho ^ 2 * sigma (q / rho)
      rw [sigmaConeValue, if_pos hpos]
    have hderiv :
        sigmaConeGradU rho u =
          0 * (sigma ∘ fun q : ℝ ↦ q / rho) u +
            rho ^ 2 * (sigmaDeriv (u / rho) * (1 / rho)) := by
      rw [sigmaConeGradU, if_pos hpos]
      field_simp [hpos.ne']
      ring
    rw [hfun, hderiv]
    exact hmul

private theorem sigmaConeValue_abs_le_all (rho u : ℝ) :
    |sigmaConeValue rho u| ≤ 1 * rho ^ 2 := by
  by_cases h : 0 ≤ rho
  · simpa only [one_mul] using sigmaConeValue_abs_le_sq h
  · have hn : ¬0 < rho := not_lt_of_ge (le_of_not_ge h)
    simpa [sigmaConeValue, hn] using sq_nonneg rho

theorem hasDerivAt_sigmaConeValue_rho_zero (u : ℝ) :
    HasDerivAt (fun q ↦ sigmaConeValue q u) 0 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hpow : (fun q : ℝ ↦ q ^ 2) =o[nhds 0] fun q ↦ q :=
    Asymptotics.isLittleO_pow_id (by norm_num)
  refine (Asymptotics.IsBigO.of_bound 1 ?_).trans_isLittleO hpow
  filter_upwards [] with q
  have h := sigmaConeValue_abs_le_all q u
  simpa [sigmaConeValue, Real.norm_eq_abs] using h

theorem hasDerivAt_sigmaConeValue_rho {rho u : ℝ} (hrho : 0 ≤ rho) :
    HasDerivAt (fun q ↦ sigmaConeValue q u) (sigmaConeGradRho rho u) rho := by
  rcases hrho.eq_or_lt with rfl | hpos
  · simpa [sigmaConeGradRho] using hasDerivAt_sigmaConeValue_rho_zero u
  · have hsq := (hasDerivAt_id rho).mul (hasDerivAt_id rho)
    have hratio :=
      (hasDerivAt_const rho u).div (hasDerivAt_id rho) hpos.ne'
    change HasDerivAt (fun q : ℝ ↦ u / q)
      ((0 * rho - u * 1) / rho ^ 2) rho at hratio
    have hratio' : HasDerivAt (fun q : ℝ ↦ u / q) (-u / rho ^ 2) rho := by
      convert hratio using 1
      ring
    have hs := (hasDerivAt_sigma (u / rho)).comp rho hratio'
    have hmul := hsq.mul hs
    have hderiv :
        2 * rho * sigma (u / rho) + rho ^ 2 *
          (sigmaDeriv (u / rho) * (-u / rho ^ 2)) =
        rho * sigmaRadialField (u / rho) := by
      unfold sigmaRadialField sigmaWeightedDeriv
      field_simp [hpos.ne']
      ring
    have hgrad :
        sigmaConeGradRho rho u =
          (1 * rho + rho * 1) * (sigma ∘ fun q : ℝ ↦ u / q) rho +
            (rho * rho) * (sigmaDeriv (u / rho) * (-u / rho ^ 2)) := by
      rw [sigmaConeGradRho, if_pos hpos, Function.comp_apply, ← hderiv]
      ring
    rw [hgrad]
    apply hmul.congr_of_eventuallyEq
    filter_upwards [(isOpen_Ioi.mem_nhds hpos)] with q hq
    change sigmaConeValue q u = (q * q) * sigma (u / q)
    have hq' : 0 < q := hq
    simp [sigmaConeValue, hq', pow_two]

theorem sigmaConeGradU_abs_le {rho u : ℝ} (hrho : 0 ≤ rho) :
    |sigmaConeGradU rho u| ≤ 2 * rho := by
  rcases hrho.eq_or_lt with rfl | hpos
  · simp [sigmaConeGradU]
  · rw [sigmaConeGradU, if_pos hpos, abs_mul, abs_of_pos hpos]
    have h := sigmaDeriv_abs_le_two (u / rho)
    nlinarith

theorem sigmaConeGradRho_abs_le {rho u : ℝ} (hrho : 0 ≤ rho) :
    |sigmaConeGradRho rho u| ≤ 4 * rho := by
  rcases hrho.eq_or_lt with rfl | hpos
  · simp [sigmaConeGradRho]
  · rw [sigmaConeGradRho, if_pos hpos, abs_mul, abs_of_pos hpos]
    have h := sigmaRadialField_abs_le_four (u / rho)
    nlinarith

private theorem sigmaConeGradU_abs_sub_le_ordered {r s u v : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    |sigmaConeGradU r u - sigmaConeGradU s v| ≤
      8 * (|r - s| + |u - v|) := by
  rcases hr.eq_or_lt with rfl | hrpos
  · have hs0 : 0 ≤ s := hrs
    simp only [sigmaConeGradU, lt_self_iff_false, if_false, zero_sub, abs_neg]
    by_cases hspos : 0 < s
    · rw [if_pos hspos, abs_mul, abs_of_pos hspos]
      have hd := sigmaDeriv_abs_le_two (v / s)
      nlinarith [abs_nonneg (u - v)]
    · have hsEq : s = 0 := le_antisymm (le_of_not_gt hspos) hs0
      simp [hsEq]
  · have hspos : 0 < s := hrpos.trans_le hrs
    simp only [sigmaConeGradU, if_pos hrpos, if_pos hspos]
    have hduv := sigmaDeriv_abs_sub_le (u / r) (v / r)
    have hscale := sigmaDeriv_scale_abs_sub_le hrpos hrs
      (v := v)
    have htri1 := abs_sub (sigmaDeriv (u / r)) (sigmaDeriv (v / s))
    have htri2 := abs_add_le
      (sigmaDeriv (u / r) - sigmaDeriv (v / r))
      (sigmaDeriv (v / r) - sigmaDeriv (v / s))
    have heq1 :
        sigmaDeriv (u / r) - sigmaDeriv (v / s) =
          (sigmaDeriv (u / r) - sigmaDeriv (v / r)) +
            (sigmaDeriv (v / r) - sigmaDeriv (v / s)) := by ring
    have hfirst :
        r * |sigmaDeriv (u / r) - sigmaDeriv (v / s)| ≤
          6 * |u - v| + 6 * (s - r) := by
      rw [heq1]
      have hratio : |u / r - v / r| = |u - v| / r := by
        rw [show u / r - v / r = (u - v) / r by ring,
          abs_div, abs_of_pos hrpos]
      rw [hratio] at hduv
      have hduvScaled :
          r * |sigmaDeriv (u / r) - sigmaDeriv (v / r)| ≤
            6 * |u - v| := by
        calc
          r * |sigmaDeriv (u / r) - sigmaDeriv (v / r)| ≤
              r * (6 * (|u - v| / r)) :=
            mul_le_mul_of_nonneg_left hduv hrpos.le
          _ = 6 * |u - v| := by field_simp [hrpos.ne']
      calc
        r * |(sigmaDeriv (u / r) - sigmaDeriv (v / r)) +
            (sigmaDeriv (v / r) - sigmaDeriv (v / s))| ≤
            r * (|sigmaDeriv (u / r) - sigmaDeriv (v / r)| +
              |sigmaDeriv (v / r) - sigmaDeriv (v / s)|) :=
          mul_le_mul_of_nonneg_left htri2 hrpos.le
        _ = r * |sigmaDeriv (u / r) - sigmaDeriv (v / r)| +
            r * |sigmaDeriv (v / r) - sigmaDeriv (v / s)| := by ring
        _ ≤ 6 * |u - v| + 6 * (s - r) :=
          add_le_add hduvScaled hscale
    have hdv := sigmaDeriv_abs_le_two (v / s)
    have hdecomp :
        r * sigmaDeriv (u / r) - s * sigmaDeriv (v / s) =
          r * (sigmaDeriv (u / r) - sigmaDeriv (v / s)) +
            (r - s) * sigmaDeriv (v / s) := by ring
    rw [hdecomp]
    have hab := abs_add_le
      (r * (sigmaDeriv (u / r) - sigmaDeriv (v / s)))
      ((r - s) * sigmaDeriv (v / s))
    rw [abs_mul, abs_of_pos hrpos, abs_mul] at hab
    rw [abs_of_nonpos (sub_nonpos.mpr hrs), neg_sub] at hab ⊢
    nlinarith [abs_nonneg (u - v)]

theorem sigmaConeGradU_abs_sub_le {r s u v : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |sigmaConeGradU r u - sigmaConeGradU s v| ≤
      8 * (|r - s| + |u - v|) := by
  by_cases hrs : r ≤ s
  · exact sigmaConeGradU_abs_sub_le_ordered hr hrs
  · have h := sigmaConeGradU_abs_sub_le_ordered hs (le_of_not_ge hrs)
      (u := v) (v := u)
    simpa [abs_sub_comm, add_comm] using h

private theorem sigmaConeGradRho_abs_sub_le_ordered {r s u v : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) :
    |sigmaConeGradRho r u - sigmaConeGradRho s v| ≤
      40 * (|r - s| + |u - v|) := by
  rcases hr.eq_or_lt with rfl | hrpos
  · have hs0 : 0 ≤ s := hrs
    simp only [sigmaConeGradRho, lt_self_iff_false, if_false, zero_sub, abs_neg]
    by_cases hspos : 0 < s
    · rw [if_pos hspos, abs_mul, abs_of_pos hspos]
      have hk := sigmaRadialField_abs_le_four (v / s)
      nlinarith [abs_nonneg (u - v)]
    · have hsEq : s = 0 := le_antisymm (le_of_not_gt hspos) hs0
      simp [hsEq]
  · have hspos : 0 < s := hrpos.trans_le hrs
    simp only [sigmaConeGradRho, if_pos hrpos, if_pos hspos]
    have hduv := sigmaRadialField_abs_sub_le (u / r) (v / r)
    have hscale := sigmaRadial_scale_abs_sub_le hrpos hrs (v := v)
    have htri := abs_add_le
      (sigmaRadialField (u / r) - sigmaRadialField (v / r))
      (sigmaRadialField (v / r) - sigmaRadialField (v / s))
    have heq :
        sigmaRadialField (u / r) - sigmaRadialField (v / s) =
          (sigmaRadialField (u / r) - sigmaRadialField (v / r)) +
            (sigmaRadialField (v / r) - sigmaRadialField (v / s)) := by ring
    have hfirst :
        r * |sigmaRadialField (u / r) - sigmaRadialField (v / s)| ≤
          34 * |u - v| + 34 * (s - r) := by
      rw [heq]
      have hratio : |u / r - v / r| = |u - v| / r := by
        rw [show u / r - v / r = (u - v) / r by ring,
          abs_div, abs_of_pos hrpos]
      rw [hratio] at hduv
      have hduvScaled :
          r * |sigmaRadialField (u / r) - sigmaRadialField (v / r)| ≤
            34 * |u - v| := by
        calc
          r * |sigmaRadialField (u / r) - sigmaRadialField (v / r)| ≤
              r * (34 * (|u - v| / r)) :=
            mul_le_mul_of_nonneg_left hduv hrpos.le
          _ = 34 * |u - v| := by field_simp [hrpos.ne']
      calc
        r * |(sigmaRadialField (u / r) - sigmaRadialField (v / r)) +
            (sigmaRadialField (v / r) - sigmaRadialField (v / s))| ≤
            r * (|sigmaRadialField (u / r) - sigmaRadialField (v / r)| +
              |sigmaRadialField (v / r) - sigmaRadialField (v / s)|) :=
          mul_le_mul_of_nonneg_left htri hrpos.le
        _ = r * |sigmaRadialField (u / r) - sigmaRadialField (v / r)| +
            r * |sigmaRadialField (v / r) - sigmaRadialField (v / s)| := by ring
        _ ≤ 34 * |u - v| + 34 * (s - r) :=
          add_le_add hduvScaled hscale
    have hkv := sigmaRadialField_abs_le_four (v / s)
    have hdecomp :
        r * sigmaRadialField (u / r) - s * sigmaRadialField (v / s) =
          r * (sigmaRadialField (u / r) - sigmaRadialField (v / s)) +
            (r - s) * sigmaRadialField (v / s) := by ring
    rw [hdecomp]
    have hab := abs_add_le
      (r * (sigmaRadialField (u / r) - sigmaRadialField (v / s)))
      ((r - s) * sigmaRadialField (v / s))
    rw [abs_mul, abs_of_pos hrpos, abs_mul] at hab
    rw [abs_of_nonpos (sub_nonpos.mpr hrs), neg_sub] at hab ⊢
    nlinarith [abs_nonneg (u - v)]

theorem sigmaConeGradRho_abs_sub_le {r s u v : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |sigmaConeGradRho r u - sigmaConeGradRho s v| ≤
      40 * (|r - s| + |u - v|) := by
  by_cases hrs : r ≤ s
  · exact sigmaConeGradRho_abs_sub_le_ordered hr hrs
  · have h := sigmaConeGradRho_abs_sub_le_ordered hs (le_of_not_ge hrs)
      (u := v) (v := u)
    simpa [abs_sub_comm, add_comm] using h

end

end NCPLVerification
