import NCPLVerification.Gates

/-!
# Algebra and formal derivatives of the scalar gates

This file records the exact piecewise derivative formulas used throughout the
inner-chain proof.  Analytic derivative and `C¹,¹` statements are kept
separate from the elementary sign and range facts, so every later gradient
calculation can cite a single canonical formula.
-/

namespace NCPLVerification

noncomputable section

def posPart (x : ℝ) : ℝ := max x 0

def negPart (x : ℝ) : ℝ := max (-x) 0

def sigmaDeriv (s : ℝ) : ℝ :=
  if s ≤ 0 then 0
  else if s ≤ 1 then 6 * s - 6 * s ^ 2
  else 0

def betaDeriv (t : ℝ) : ℝ :=
  if t ≤ -1 then 0
  else if t ≤ 0 then 4 * (t + 1) - 3 * (t + 1) ^ 2
  else if t ≤ 1 then 1
  else if t ≤ 2 then 1 + 2 * (t - 1) - 3 * (t - 1) ^ 2
  else 0

@[simp] theorem posPart_nonneg (x : ℝ) : 0 ≤ posPart x := by
  simp [posPart]

@[simp] theorem negPart_nonneg (x : ℝ) : 0 ≤ negPart x := by
  simp [negPart]

@[simp] theorem posPart_zero : posPart 0 = 0 := by simp [posPart]

@[simp] theorem negPart_zero : negPart 0 = 0 := by simp [negPart]

theorem posPart_sub_negPart (x : ℝ) : posPart x - negPart x = x := by
  by_cases hx : x ≤ 0
  · simp [posPart, negPart, hx]
  · have hx' : 0 ≤ x := le_of_lt (lt_of_not_ge hx)
    simp [posPart, negPart, hx']

theorem posPart_eq_zero {x : ℝ} (h : x ≤ 0) : posPart x = 0 := by
  simp [posPart, h]

theorem negPart_eq_zero {x : ℝ} (h : 0 ≤ x) : negPart x = 0 := by
  simp [negPart, h]

theorem posPart_sq_le_sq {x c : ℝ} (hc : 0 ≤ c) (hx : x ≤ c) :
    posPart x ^ 2 ≤ c ^ 2 := by
  have hp := posPart_nonneg x
  have hpc : posPart x ≤ c := max_le hx hc
  nlinarith

@[simp] theorem sigmaDeriv_zero : sigmaDeriv 0 = 0 := by
  norm_num [sigmaDeriv]

@[simp] theorem sigmaDeriv_one : sigmaDeriv 1 = 0 := by
  norm_num [sigmaDeriv]

theorem sigmaDeriv_nonneg (s : ℝ) : 0 ≤ sigmaDeriv s := by
  by_cases h0 : s ≤ 0
  · simp [sigmaDeriv, h0]
  by_cases h1 : s ≤ 1
  · rw [sigmaDeriv, if_neg h0, if_pos h1]
    have hs : 0 ≤ s := le_of_lt (lt_of_not_ge h0)
    nlinarith [mul_nonneg hs (sub_nonneg.mpr h1)]
  · simp [sigmaDeriv, h0, h1]

theorem sigmaDeriv_le_three_halves (s : ℝ) : sigmaDeriv s ≤ 3 / 2 := by
  by_cases h0 : s ≤ 0
  · norm_num [sigmaDeriv, h0]
  by_cases h1 : s ≤ 1
  · rw [sigmaDeriv, if_neg h0, if_pos h1]
    nlinarith [sq_nonneg (2 * s - 1)]
  · norm_num [sigmaDeriv, h0, h1]

theorem betaDeriv_nonneg (t : ℝ) : 0 ≤ betaDeriv t := by
  by_cases hm1 : t ≤ -1
  · simp [betaDeriv, hm1]
  by_cases h0 : t ≤ 0
  · rw [betaDeriv, if_neg hm1, if_pos h0]
    have hu0 : 0 ≤ t + 1 := by linarith
    have hu1 : t + 1 ≤ 1 := by linarith
    nlinarith [mul_nonneg hu0 (by linarith : 0 ≤ 4 - 3 * (t + 1))]
  by_cases h1 : t ≤ 1
  · norm_num [betaDeriv, hm1, h0, h1]
  by_cases h2 : t ≤ 2
  · rw [betaDeriv, if_neg hm1, if_neg h0, if_neg h1, if_pos h2]
    have hv0 : 0 ≤ t - 1 := by linarith
    have hv1 : t - 1 ≤ 1 := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hv1)
      (by linarith : 0 ≤ 1 + 3 * (t - 1))]
  · simp [betaDeriv, hm1, h0, h1, h2]

theorem betaDeriv_le_two (t : ℝ) : betaDeriv t ≤ 2 := by
  by_cases hm1 : t ≤ -1
  · norm_num [betaDeriv, hm1]
  by_cases h0 : t ≤ 0
  · rw [betaDeriv, if_neg hm1, if_pos h0]
    nlinarith [sq_nonneg (3 * (t + 1) - 2)]
  by_cases h1 : t ≤ 1
  · norm_num [betaDeriv, hm1, h0, h1]
  by_cases h2 : t ≤ 2
  · rw [betaDeriv, if_neg hm1, if_neg h0, if_neg h1, if_pos h2]
    nlinarith [sq_nonneg (3 * (t - 1) - 1)]
  · norm_num [betaDeriv, hm1, h0, h1, h2]

theorem beta_nonneg_of_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ beta t := by
  by_cases h1 : t ≤ 1
  · rw [beta_eq_self ht h1]
    exact ht
  by_cases h2 : t ≤ 2
  · rw [beta]
    simp only [if_neg (by linarith : ¬t ≤ -1), if_neg (by linarith : ¬t ≤ 0),
      if_neg h1, if_pos h2]
    have hv0 : 0 ≤ t - 1 := by linarith
    have hv1 : t - 1 ≤ 1 := by linarith
    have hprod : 0 ≤ (t - 1) * (1 + (t - 1) - (t - 1) ^ 2) := by
      apply mul_nonneg hv0
      nlinarith [sq_nonneg (t - 1)]
    nlinarith
  · rw [beta_of_two_le (by linarith)]
    norm_num

theorem beta_one_le_of_one_le {t : ℝ} (ht : 1 ≤ t) : 1 ≤ beta t := by
  rcases ht.eq_or_lt with rfl | ht
  · norm_num [beta]
  by_cases h2 : t ≤ 2
  · rw [beta]
    simp only [if_neg (by linarith : ¬t ≤ -1), if_neg (by linarith : ¬t ≤ 0),
      if_neg (by linarith : ¬t ≤ 1), if_pos h2]
    have hv0 : 0 ≤ t - 1 := by linarith
    have hv1 : t - 1 ≤ 1 := by linarith
    have hprod : 0 ≤ (t - 1) * (1 + (t - 1) - (t - 1) ^ 2) := by
      apply mul_nonneg hv0
      nlinarith [sq_nonneg (t - 1)]
    nlinarith
  · rw [beta_of_two_le (by linarith)]
    norm_num

/-- The negative part of `β(t)` is controlled by the lower wall with the
explicit numerical constant two. -/
theorem negPart_beta_le_two_mul_negPart (t : ℝ) :
    negPart (beta t) ≤ 2 * negPart t := by
  have hneg : -beta t ≤ 2 * negPart t := by
    by_cases hm1 : t ≤ -1
    · rw [beta]
      simp only [if_pos hm1]
      have ht : 1 ≤ -t := by linarith
      have hwall : -t ≤ negPart t := le_max_left _ _
      nlinarith [negPart_nonneg t]
    by_cases h0 : t ≤ 0
    · rw [beta]
      simp only [if_neg hm1, if_pos h0]
      rw [show negPart t = -t by simp [negPart, h0]]
      have hu0 : 0 ≤ t + 1 := by linarith
      have hu1 : t + 1 ≤ 1 := by linarith
      have hprod : 0 ≤ (1 - (t + 1)) *
          (1 - (t + 1) + (t + 1) ^ 2) := by
        apply mul_nonneg (by linarith)
        nlinarith [sq_nonneg (t + 1)]
      nlinarith
    · have hbeta : 0 ≤ beta t := beta_nonneg_of_nonneg (le_of_lt (lt_of_not_ge h0))
      have : -beta t ≤ 0 := neg_nonpos.mpr hbeta
      exact this.trans (mul_nonneg (by norm_num) (negPart_nonneg t))
  exact max_le hneg (mul_nonneg (by norm_num) (negPart_nonneg t))

/-- Residual used by the inner chain. -/
def gateResidual (s t : ℝ) : ℝ := posPart (1 - sigma s * beta t)

theorem gateResidual_nonneg (s t : ℝ) : 0 ≤ gateResidual s t :=
  posPart_nonneg _

theorem gateResidual_le_two (s t : ℝ) : gateResidual s t ≤ 2 := by
  have hA0 := sigma_nonneg s
  have hA1 := sigma_le_one s
  have hB := beta_lower t
  have hprod : 0 ≤ sigma s * (beta t + 1) :=
    mul_nonneg hA0 (by linarith)
  apply max_le
  · nlinarith
  · norm_num

/-- If the cubic gate is at least half open, its argument is at least `1/2`. -/
theorem half_le_of_half_le_sigma {s : ℝ} (h : (1 : ℝ) / 2 ≤ sigma s) :
    (1 : ℝ) / 2 ≤ s := by
  by_cases h0 : s ≤ 0
  · rw [sigma_of_nonpos h0] at h
    norm_num at h
  by_cases h1 : s ≤ 1
  · rw [sigma, if_neg h0, if_pos h1] at h
    by_contra hs
    have hs0 : 0 ≤ s := le_of_lt (lt_of_not_ge h0)
    have hq : 0 < -2 * s ^ 2 + 2 * s + 1 := by
      nlinarith [mul_nonneg hs0 (sub_nonneg.mpr h1)]
    have hp : (s - 1 / 2) * (-2 * s ^ 2 + 2 * s + 1) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hq
    nlinarith
  · linarith

theorem half_le_sigma_of_half_le {s : ℝ} (h : (1 : ℝ) / 2 ≤ s) :
    (1 : ℝ) / 2 ≤ sigma s := by
  by_cases h1 : s ≤ 1
  · have h0 : ¬s ≤ 0 := by linarith
    rw [sigma, if_neg h0, if_pos h1]
    have hq : 0 < -2 * s ^ 2 + 2 * s + 1 := by
      nlinarith [mul_nonneg (by linarith : 0 ≤ s) (sub_nonneg.mpr h1)]
    have hp : 0 ≤ (s - 1 / 2) * (-2 * s ^ 2 + 2 * s + 1) :=
      mul_nonneg (by linarith) hq.le
    nlinarith
  · rw [sigma_of_one_le (by linarith)]
    norm_num

theorem sigma_lt_half_imp_lt_half {s : ℝ} (h : sigma s < (1 : ℝ) / 2) :
    s < (1 : ℝ) / 2 := by
  exact lt_of_not_ge fun hs ↦ (not_le_of_gt h) (half_le_sigma_of_half_le hs)

/-- A coarse inverse estimate used in the explicit open-gate proof. -/
theorem sigma_lt_two_thirds_imp_lt_three_quarters {s : ℝ}
    (h : sigma s < (2 : ℝ) / 3) : s < (3 : ℝ) / 4 := by
  by_contra hs
  have hs34 : (3 : ℝ) / 4 ≤ s := le_of_not_gt hs
  by_cases h1 : s ≤ 1
  · have h0 : ¬s ≤ 0 := by linarith
    rw [sigma, if_neg h0, if_pos h1] at h
    have hq : 0 ≤ -2 * s ^ 2 + (3 / 2 : ℝ) * s + 9 / 8 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hs34) (sub_nonneg.mpr h1)]
    have hp : 0 ≤ (s - 3 / 4) *
        (-2 * s ^ 2 + (3 / 2 : ℝ) * s + 9 / 8) :=
      mul_nonneg (by linarith) hq
    nlinarith
  · rw [sigma_of_one_le (by linarith)] at h
    norm_num at h

private theorem residual_sq_le_of_eighth {r c : ℝ} (hr : 0 ≤ r)
    (hc : (1 : ℝ) / 8 ≤ c) : r ^ 2 ≤ 64 * (c * r) ^ 2 := by
  have hc0 : 0 ≤ c := by linarith
  have hmul : r / 8 ≤ c * r := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_of_nonneg_right hc hr
  have hsquare : (r / 8) ^ 2 ≤ (c * r) ^ 2 :=
    (sq_le_sq₀ (div_nonneg hr (by norm_num)) (mul_nonneg hc0 hr)).2 hmul
  nlinarith

private theorem residual_sq_le_from_wall {r v : ℝ} (hr0 : 0 ≤ r)
    (hr2 : r ≤ 2) (hv : (1 : ℝ) / 2 ≤ v) : r ^ 2 ≤ 64 * v ^ 2 := by
  nlinarith [sq_nonneg (r - 2), sq_nonneg (v - 1 / 2)]

/-- Quantitative version of the paper's open-gate observability lemma.  The
unspecified numerical constant can be chosen as `64`. -/
theorem open_gate_observability (s t : ℝ)
    (hopen : (1 : ℝ) / 2 ≤ sigma s) :
    let r := gateResidual s t
    r ^ 2 ≤ 64 *
      ((sigma s * betaDeriv t * r) ^ 2 +
       (sigmaDeriv s * posPart (beta t) * r) ^ 2 +
       negPart t ^ 2) := by
  dsimp only
  let r := gateResidual s t
  change r ^ 2 ≤ 64 *
    ((sigma s * betaDeriv t * r) ^ 2 +
     (sigmaDeriv s * posPart (beta t) * r) ^ 2 + negPart t ^ 2)
  have hr0 : 0 ≤ r := gateResidual_nonneg _ _
  have hr2 : r ≤ 2 := gateResidual_le_two _ _
  by_cases htwall : t ≤ -(1 : ℝ) / 2
  · have hv : (1 : ℝ) / 2 ≤ negPart t := by
      exact (by linarith : (1 : ℝ) / 2 ≤ -t) |>.trans (le_max_left _ _)
    have hsq := residual_sq_le_from_wall hr0 hr2 hv
    nlinarith [sq_nonneg (sigma s * betaDeriv t * r),
      sq_nonneg (sigmaDeriv s * posPart (beta t) * r)]
  by_cases ht0 : t < 0
  · have hm1 : ¬t ≤ -1 := by linarith
    have htle0 : t ≤ 0 := ht0.le
    have hE : (1 : ℝ) / 2 ≤ betaDeriv t := by
      rw [betaDeriv, if_neg hm1, if_pos htle0]
      have hu0 : (1 : ℝ) / 2 < t + 1 := by linarith
      have hu1 : t + 1 ≤ 1 := by linarith
      have hfactor : 1 ≤ 4 - 3 * (t + 1) := by linarith
      have hprod := mul_le_mul hu0.le hfactor (by norm_num : 0 ≤ (1 : ℝ))
        (by linarith : 0 ≤ t + 1)
      nlinarith
    have hcoef : (1 : ℝ) / 8 ≤ sigma s * betaDeriv t := by
      have := mul_le_mul hopen hE (by norm_num : 0 ≤ (1 : ℝ) / 2)
        (sigma_nonneg s)
      nlinarith
    have hsq := residual_sq_le_of_eighth hr0 hcoef
    nlinarith [sq_nonneg (sigmaDeriv s * posPart (beta t) * r),
      sq_nonneg (negPart t)]
  by_cases ht1 : t ≤ 1
  · have ht0' : 0 ≤ t := le_of_not_gt ht0
    have hE : betaDeriv t = 1 := by
      rcases ht0'.eq_or_lt with rfl | htpos
      · norm_num [betaDeriv]
      · rw [betaDeriv]
        simp [show ¬t ≤ -1 by linarith, show ¬t ≤ 0 by linarith, ht1]
    have hcoef : (1 : ℝ) / 8 ≤ sigma s * betaDeriv t := by
      rw [hE]
      nlinarith
    have hsq := residual_sq_le_of_eighth hr0 hcoef
    nlinarith [sq_nonneg (sigmaDeriv s * posPart (beta t) * r),
      sq_nonneg (negPart t)]
  · have htone : 1 < t := lt_of_not_ge ht1
    by_cases hr : r = 0
    · simp [hr]
    have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have ht2 : t < 2 := by
      by_contra h
      have hbeta : beta t = 2 := beta_of_two_le (le_of_not_gt h)
      have hinside : 1 - sigma s * beta t ≤ 0 := by nlinarith
      have : r = 0 := by
        simp [r, gateResidual, posPart, hinside]
      exact hr this
    have hm1 : ¬t ≤ -1 := by linarith
    have h0 : ¬t ≤ 0 := by linarith
    have h1 : ¬t ≤ 1 := by linarith
    have h2 : t ≤ 2 := ht2.le
    by_cases hEcase : (1 : ℝ) / 4 ≤ betaDeriv t
    · have hcoef : (1 : ℝ) / 8 ≤ sigma s * betaDeriv t := by
        have := mul_le_mul hopen hEcase (by norm_num : 0 ≤ (1 : ℝ) / 4)
          (sigma_nonneg s)
        nlinarith
      have hsq := residual_sq_le_of_eighth hr0 hcoef
      nlinarith [sq_nonneg (sigmaDeriv s * posPart (beta t) * r),
        sq_nonneg (negPart t)]
    · have hEformula : betaDeriv t =
          1 + 2 * (t - 1) - 3 * (t - 1) ^ 2 := by
        simp [betaDeriv, hm1, h0, h1, h2]
      have hv0 : 0 ≤ t - 1 := by linarith
      have hv1 : t - 1 ≤ 1 := by linarith
      have hEge : 1 - (t - 1) ≤ betaDeriv t := by
        rw [hEformula]
        nlinarith [mul_nonneg (sub_nonneg.mpr hv1)
          (by linarith : 0 ≤ 3 * (t - 1))]
      have hvlarge : (3 : ℝ) / 4 < t - 1 := by linarith
      have hbetaformula : beta t =
          1 + (t - 1) + (t - 1) ^ 2 - (t - 1) ^ 3 := by
        simp [beta, hm1, h0, h1, h2]
      have htail : 0 ≤ (t - 1) ^ 2 * (1 - (t - 1)) :=
        mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hv1)
      have hB : (3 : ℝ) / 2 < beta t := by
        rw [hbetaformula]
        nlinarith
      have hinside : 0 < 1 - sigma s * beta t := by
        by_contra hnot
        have hle : 1 - sigma s * beta t ≤ 0 := le_of_not_gt hnot
        have : r = 0 := by simp [r, gateResidual, posPart, hle]
        exact hr this
      have hAlt : sigma s < (2 : ℝ) / 3 := by
        by_contra hnot
        have hAge : (2 : ℝ) / 3 ≤ sigma s := le_of_not_gt hnot
        have hmul : 1 < sigma s * beta t := by
          have h₁ := mul_lt_mul_of_pos_left hB (by linarith : 0 < sigma s)
          nlinarith
        linarith
      have hslo : (1 : ℝ) / 2 ≤ s := half_le_of_half_le_sigma hopen
      have hshi : s < (3 : ℝ) / 4 :=
        sigma_lt_two_thirds_imp_lt_three_quarters hAlt
      have hDformula : sigmaDeriv s = 6 * s - 6 * s ^ 2 := by
        have hs0 : ¬s ≤ 0 := by linarith
        have hs1 : s ≤ 1 := by linarith
        simp [sigmaDeriv, hs0, hs1]
      have hprod : (1 : ℝ) / 8 ≤ s * (1 - s) := by
        have := mul_le_mul hslo (by linarith : (1 : ℝ) / 4 ≤ 1 - s)
          (by norm_num : 0 ≤ (1 : ℝ) / 4) (by linarith : 0 ≤ s)
        nlinarith
      have hD : (3 : ℝ) / 4 ≤ sigmaDeriv s := by
        rw [hDformula]
        nlinarith
      have hposbeta : posPart (beta t) = beta t := by
        simp [posPart, le_of_lt (by linarith : 0 < beta t)]
      have hcoef : (1 : ℝ) / 8 ≤ sigmaDeriv s * posPart (beta t) := by
        rw [hposbeta]
        have := mul_le_mul hD hB.le (by linarith : 0 ≤ (3 : ℝ) / 2)
          (sigmaDeriv_nonneg s)
        nlinarith
      have hsq := residual_sq_le_of_eighth hr0 hcoef
      nlinarith [sq_nonneg (sigma s * betaDeriv t * r), sq_nonneg (negPart t)]

/-- Frozen first-coordinate form of open-gate observability. -/
theorem frozen_open_gate_observability (t : ℝ) :
    let r := gateResidual 1 t
    r ^ 2 ≤ 64 * ((betaDeriv t * r) ^ 2 + negPart t ^ 2) := by
  dsimp only
  let r := gateResidual 1 t
  change r ^ 2 ≤ 64 * ((betaDeriv t * r) ^ 2 + negPart t ^ 2)
  have hr0 : 0 ≤ r := gateResidual_nonneg _ _
  have hr2 : r ≤ 2 := gateResidual_le_two _ _
  by_cases htwall : t ≤ -(1 : ℝ) / 2
  · have hv : (1 : ℝ) / 2 ≤ negPart t :=
      (by linarith : (1 : ℝ) / 2 ≤ -t) |>.trans (le_max_left _ _)
    have hsq := residual_sq_le_from_wall hr0 hr2 hv
    nlinarith [sq_nonneg (betaDeriv t * r)]
  by_cases ht0 : t < 0
  · have hm1 : ¬t ≤ -1 := by linarith
    have htle0 : t ≤ 0 := ht0.le
    have hE : (1 : ℝ) / 2 ≤ betaDeriv t := by
      rw [betaDeriv, if_neg hm1, if_pos htle0]
      have hu0 : (1 : ℝ) / 2 < t + 1 := by linarith
      have hu1 : t + 1 ≤ 1 := by linarith
      have hfactor : 1 ≤ 4 - 3 * (t + 1) := by linarith
      have := mul_le_mul hu0.le hfactor (by norm_num : 0 ≤ (1 : ℝ))
        (by linarith : 0 ≤ t + 1)
      nlinarith
    have hsq := residual_sq_le_of_eighth hr0 (by linarith : (1 : ℝ) / 8 ≤ betaDeriv t)
    nlinarith [sq_nonneg (negPart t)]
  by_cases ht1 : t ≤ 1
  · have hE : betaDeriv t = 1 := by
      have ht0' : 0 ≤ t := le_of_not_gt ht0
      rcases ht0'.eq_or_lt with rfl | htpos
      · norm_num [betaDeriv]
      · rw [betaDeriv]
        simp [show ¬t ≤ -1 by linarith, show ¬t ≤ 0 by linarith, ht1]
    rw [hE]
    nlinarith [sq_nonneg (negPart t)]
  · have hbeta : 1 ≤ beta t := beta_one_le_of_one_le (le_of_not_ge ht1)
    have hinside : 1 - sigma 1 * beta t ≤ 0 := by rw [sigma_one]; linarith
    have hr : r = 0 := by simp [r, gateResidual, posPart, hinside]
    simp [hr]

end

end NCPLVerification
