import NCPLVerification.GateSmoothness
import NCPLVerification.SigmaPerspectiveSmoothness

/-!
# Radial estimates for the clipped beta gate
-/

namespace NCPLVerification

noncomputable section

theorem beta_of_le_neg_one {t : ℝ} (ht : t ≤ -1) : beta t = -1 := by
  simp [beta, ht]

theorem betaDeriv_of_le_neg_one {t : ℝ} (ht : t ≤ -1) :
    betaDeriv t = 0 := by simp [betaDeriv, ht]

theorem betaDeriv_of_two_le {t : ℝ} (ht : 2 ≤ t) :
    betaDeriv t = 0 := by
  rcases ht.eq_or_lt with rfl | ht
  · norm_num [betaDeriv]
  · simp [betaDeriv, not_le.mpr (by linarith : -1 < t),
      not_le.mpr (by linarith : 0 < t),
      not_le.mpr (by linarith : 1 < t), not_le.mpr ht]

theorem betaDeriv_abs_le_two (t : ℝ) : |betaDeriv t| ≤ 2 := by
  rw [abs_of_nonneg (betaDeriv_nonneg t)]
  exact betaDeriv_le_two t

def betaRangeClamp (t : ℝ) : ℝ := min (max t (-1)) 2

theorem betaRangeClamp_self {t : ℝ} (hm : -1 ≤ t) (hp : t ≤ 2) :
    betaRangeClamp t = t := by simp [betaRangeClamp, hm, hp]

theorem betaRangeClamp_neg_one {t : ℝ} (ht : t ≤ -1) :
    betaRangeClamp t = -1 := by
  simp [betaRangeClamp, ht, show (-1 : ℝ) ≤ 2 by norm_num]

theorem betaRangeClamp_two {t : ℝ} (ht : 2 ≤ t) :
    betaRangeClamp t = 2 := by
  have hm : -1 ≤ t := by linarith
  simp [betaRangeClamp, ht, hm]

theorem betaRangeClamp_abs_le_two (t : ℝ) : |betaRangeClamp t| ≤ 2 := by
  unfold betaRangeClamp
  have hlo : -1 ≤ min (max t (-1)) 2 := by
    simp [show (-1 : ℝ) ≤ 2 by norm_num]
  have hhi : min (max t (-1)) 2 ≤ 2 := min_le_right _ _
  rw [abs_le]
  constructor <;> linarith

theorem betaRangeClamp_lipschitz :
    LipschitzWith (1 : NNReal) betaRangeClamp := by
  unfold betaRangeClamp
  exact (LipschitzWith.id.max_const (-1 : ℝ)).min_const 2

theorem betaRangeClamp_abs_sub_le (s t : ℝ) :
    |betaRangeClamp s - betaRangeClamp t| ≤ |s - t| := by
  simpa [Real.norm_eq_abs] using betaRangeClamp_lipschitz.norm_sub_le s t

def betaWeightedDeriv (t : ℝ) : ℝ := t * betaDeriv t

theorem betaWeightedDeriv_clamp (t : ℝ) :
    betaWeightedDeriv t = betaRangeClamp t * betaDeriv t := by
  unfold betaWeightedDeriv
  by_cases hm : t ≤ -1
  · rw [betaDeriv_of_le_neg_one hm]
    ring
  by_cases hp : 2 ≤ t
  · rw [betaDeriv_of_two_le hp]
    ring
  · rw [betaRangeClamp_self (by linarith) (by linarith)]

theorem betaWeightedDeriv_abs_le_four (t : ℝ) :
    |betaWeightedDeriv t| ≤ 4 := by
  rw [betaWeightedDeriv_clamp, abs_mul]
  have hc := betaRangeClamp_abs_le_two t
  have hd := betaDeriv_abs_le_two t
  nlinarith [abs_nonneg (betaRangeClamp t), abs_nonneg (betaDeriv t)]

theorem betaWeightedDeriv_abs_sub_le (s t : ℝ) :
    |betaWeightedDeriv s - betaWeightedDeriv t| ≤ 18 * |s - t| := by
  rw [betaWeightedDeriv_clamp, betaWeightedDeriv_clamp]
  have heq :
      betaRangeClamp s * betaDeriv s - betaRangeClamp t * betaDeriv t =
        betaRangeClamp s * (betaDeriv s - betaDeriv t) +
          (betaRangeClamp s - betaRangeClamp t) * betaDeriv t := by ring
  rw [heq]
  have htri := abs_add_le
    (betaRangeClamp s * (betaDeriv s - betaDeriv t))
    ((betaRangeClamp s - betaRangeClamp t) * betaDeriv t)
  rw [abs_mul, abs_mul] at htri
  have hc := betaRangeClamp_abs_le_two s
  have hd := betaDeriv_abs_sub_le s t
  have hcl := betaRangeClamp_abs_sub_le s t
  have hdt := betaDeriv_abs_le_two t
  nlinarith [abs_nonneg (s - t),
    abs_nonneg (betaDeriv s - betaDeriv t),
    abs_nonneg (betaRangeClamp s - betaRangeClamp t)]

private theorem beta_ratio_middle {r s v : ℝ} (hr : 0 < r)
    (hrs : r ≤ s) (hlow : ¬v ≤ -s) (hhigh : ¬2 * s ≤ v) :
    r * |v / r - v / s| ≤ 2 * (s - r) := by
  have hs : 0 < s := hr.trans_le hrs
  have hvabs : |v| ≤ 2 * s := by
    rw [abs_le]
    constructor <;> linarith
  rw [ratio_abs_sub hr hrs]
  have hrs0 : 0 ≤ s - r := sub_nonneg.mpr hrs
  have hden : 0 < r * s := mul_pos hr hs
  calc
    r * (|v| * (s - r) / (r * s)) = (|v| / s) * (s - r) := by
      field_simp [hr.ne', hs.ne']
    _ ≤ 2 * (s - r) := by
      have hvdiv : |v| / s ≤ 2 := (div_le_iff₀ hs).2 (by nlinarith)
      exact mul_le_mul_of_nonneg_right hvdiv hrs0

theorem beta_scale_abs_sub_le {r s v : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    r * |beta (v / r) - beta (v / s)| ≤ 4 * (s - r) := by
  have hs : 0 < s := hr.trans_le hrs
  by_cases hlow : v ≤ -s
  · have hvr : v / r ≤ -1 := by
      apply (div_le_iff₀ hr).2
      nlinarith
    have hvs : v / s ≤ -1 := by
      apply (div_le_iff₀ hs).2
      nlinarith
    simp [beta_of_le_neg_one hvr, beta_of_le_neg_one hvs,
      sub_nonneg.mpr hrs]
  by_cases hhigh : 2 * s ≤ v
  · have hvr : 2 ≤ v / r := by
      apply (le_div_iff₀ hr).2
      nlinarith
    have hvs : 2 ≤ v / s := by
      apply (le_div_iff₀ hs).2
      nlinarith
    simp [beta_of_two_le hvr, beta_of_two_le hvs, sub_nonneg.mpr hrs]
  · have hratio := beta_ratio_middle hr hrs hlow hhigh
    have hlip := beta_abs_sub_le (v / r) (v / s)
    nlinarith

theorem betaDeriv_scale_abs_sub_le {r s v : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) :
    r * |betaDeriv (v / r) - betaDeriv (v / s)| ≤ 16 * (s - r) := by
  have hs : 0 < s := hr.trans_le hrs
  by_cases hlow : v ≤ -s
  · have hvr : v / r ≤ -1 := by apply (div_le_iff₀ hr).2; nlinarith
    have hvs : v / s ≤ -1 := by apply (div_le_iff₀ hs).2; nlinarith
    simp [betaDeriv_of_le_neg_one hvr, betaDeriv_of_le_neg_one hvs,
      sub_nonneg.mpr hrs]
  by_cases hhigh : 2 * s ≤ v
  · have hvr : 2 ≤ v / r := by apply (le_div_iff₀ hr).2; nlinarith
    have hvs : 2 ≤ v / s := by apply (le_div_iff₀ hs).2; nlinarith
    simp [betaDeriv_of_two_le hvr, betaDeriv_of_two_le hvs,
      sub_nonneg.mpr hrs]
  · have hratio := beta_ratio_middle hr hrs hlow hhigh
    have hlip := betaDeriv_abs_sub_le (v / r) (v / s)
    nlinarith

theorem betaWeightedDeriv_scale_abs_sub_le {r s v : ℝ}
    (hr : 0 < r) (hrs : r ≤ s) :
    r * |betaWeightedDeriv (v / r) - betaWeightedDeriv (v / s)| ≤
      36 * (s - r) := by
  have hs : 0 < s := hr.trans_le hrs
  by_cases hlow : v ≤ -s
  · have hvr : v / r ≤ -1 := by apply (div_le_iff₀ hr).2; nlinarith
    have hvs : v / s ≤ -1 := by apply (div_le_iff₀ hs).2; nlinarith
    simp [betaWeightedDeriv, betaDeriv_of_le_neg_one hvr,
      betaDeriv_of_le_neg_one hvs, sub_nonneg.mpr hrs]
  by_cases hhigh : 2 * s ≤ v
  · have hvr : 2 ≤ v / r := by apply (le_div_iff₀ hr).2; nlinarith
    have hvs : 2 ≤ v / s := by apply (le_div_iff₀ hs).2; nlinarith
    simp [betaWeightedDeriv, betaDeriv_of_two_le hvr,
      betaDeriv_of_two_le hvs, sub_nonneg.mpr hrs]
  · have hratio := beta_ratio_middle hr hrs hlow hhigh
    have hlip := betaWeightedDeriv_abs_sub_le (v / r) (v / s)
    nlinarith

end

end NCPLVerification
