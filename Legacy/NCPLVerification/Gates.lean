import Mathlib

/-!
# Scalar gates

Exact executable definitions of the paper's scalar gates `σ` and `β`, with
their elementary range and interpolation properties.
-/

namespace NCPLVerification

noncomputable section

/-- The cubic opening gate from Section 2. -/
def sigma (s : ℝ) : ℝ :=
  if s ≤ 0 then 0
  else if s ≤ 1 then 3 * s ^ 2 - 2 * s ^ 3
  else 1

/-- The monotone clipped coordinate gate from Section 2. -/
def beta (t : ℝ) : ℝ :=
  if t ≤ -1 then -1
  else if t ≤ 0 then -1 + 2 * (t + 1) ^ 2 - (t + 1) ^ 3
  else if t ≤ 1 then t
  else if t ≤ 2 then 1 + (t - 1) + (t - 1) ^ 2 - (t - 1) ^ 3
  else 2

theorem sigma_of_nonpos {s : ℝ} (h : s ≤ 0) : sigma s = 0 := by
  simp [sigma, h]

theorem sigma_of_one_le {s : ℝ} (h : 1 ≤ s) : sigma s = 1 := by
  rcases h.eq_or_lt with rfl | h
  · norm_num [sigma]
  · simp [sigma, not_le.mpr (by linarith : 0 < s), not_le.mpr h]

theorem sigma_zero : sigma 0 = 0 := by norm_num [sigma]

theorem sigma_one : sigma 1 = 1 := by norm_num [sigma]

theorem sigma_nonneg (s : ℝ) : 0 ≤ sigma s := by
  by_cases h0 : s ≤ 0
  · simp [sigma, h0]
  by_cases h1 : s ≤ 1
  · rw [sigma, if_neg h0, if_pos h1]
    have hs : 0 ≤ s := le_of_lt (lt_of_not_ge h0)
    have hfactor : 0 ≤ s ^ 2 * (3 - 2 * s) :=
      mul_nonneg (sq_nonneg s) (by linarith)
    nlinarith
  · simp [sigma, h0, h1]

theorem sigma_le_one (s : ℝ) : sigma s ≤ 1 := by
  by_cases h0 : s ≤ 0
  · simp [sigma, h0]
  by_cases h1 : s ≤ 1
  · rw [sigma, if_neg h0, if_pos h1]
    have hs : 0 ≤ s := le_of_lt (lt_of_not_ge h0)
    have hfactor : 0 ≤ (1 - s) ^ 2 * (1 + 2 * s) :=
      mul_nonneg (sq_nonneg (1 - s)) (by linarith)
    nlinarith
  · simp [sigma, h0, h1]

theorem sigma_mem_unit (s : ℝ) : sigma s ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨sigma_nonneg s, sigma_le_one s⟩

theorem beta_zero : beta 0 = 0 := by norm_num [beta]

theorem beta_nonpos_of_nonpos {t : ℝ} (ht : t ≤ 0) : beta t ≤ 0 := by
  by_cases hm1 : t ≤ -1
  · simp [beta, hm1]
  · rw [beta, if_neg hm1, if_pos ht]
    have hu0 : 0 ≤ t + 1 := by linarith
    have hu1 : t + 1 ≤ 1 := by linarith
    have haux : 0 ≤ 1 + (t + 1) - (t + 1) ^ 2 := by
      nlinarith [sq_nonneg (t + 1)]
    have hprod : 0 ≤ (1 - (t + 1)) *
        (1 + (t + 1) - (t + 1) ^ 2) :=
      mul_nonneg (by linarith) haux
    nlinarith

theorem one_sub_sigma_le_three_sq {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    1 - sigma t ≤ 3 * (1 - t) ^ 2 := by
  rcases h0.eq_or_lt with rfl | ht
  · norm_num [sigma]
  · rw [sigma, if_neg (not_le.mpr ht), if_pos h1]
    nlinarith [sq_nonneg (1 - t)]

theorem beta_eq_self {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : beta t = t := by
  rcases h0.eq_or_lt with rfl | ht
  · exact beta_zero
  · simp [beta, not_le.mpr (by linarith : -1 < t), not_le.mpr ht, h1]

theorem beta_of_two_le {t : ℝ} (h : 2 ≤ t) : beta t = 2 := by
  rcases h.eq_or_lt with rfl | ht
  · norm_num [beta]
  · simp [beta, not_le.mpr (by linarith : -1 < t),
      not_le.mpr (by linarith : 0 < t), not_le.mpr (by linarith : 1 < t),
      not_le.mpr ht]

theorem beta_lower (t : ℝ) : -1 ≤ beta t := by
  by_cases h₁ : t ≤ -1
  · simp [beta, h₁]
  by_cases h₀ : t ≤ 0
  · rw [beta, if_neg h₁, if_pos h₀]
    let u : ℝ := t + 1
    have hu0 : 0 ≤ u := by dsimp [u]; linarith
    have hu1 : u ≤ 1 := by dsimp [u]; linarith
    have hprod : 0 ≤ u ^ 2 * (2 - u) :=
      mul_nonneg (sq_nonneg u) (by linarith)
    dsimp [u] at hprod
    nlinarith
  by_cases h1 : t ≤ 1
  · rw [beta, if_neg h₁, if_neg h₀, if_pos h1]
    linarith
  by_cases h2 : t ≤ 2
  · rw [beta, if_neg h₁, if_neg h₀, if_neg h1, if_pos h2]
    let v : ℝ := t - 1
    have hv0 : 0 ≤ v := by dsimp [v]; linarith
    have hv1 : v ≤ 1 := by dsimp [v]; linarith
    have haux : 0 ≤ 1 + v - v ^ 2 := by nlinarith [sq_nonneg v]
    have hprod : 0 ≤ v * (1 + v - v ^ 2) := mul_nonneg hv0 haux
    dsimp [v] at hprod
    nlinarith
  · norm_num [beta, h₁, h₀, h1, h2]

theorem beta_upper (t : ℝ) : beta t ≤ 2 := by
  by_cases h₁ : t ≤ -1
  · norm_num [beta, h₁]
  by_cases h₀ : t ≤ 0
  · rw [beta, if_neg h₁, if_pos h₀]
    let u : ℝ := t + 1
    have hu0 : 0 ≤ u := by dsimp [u]; linarith
    have hu1 : u ≤ 1 := by dsimp [u]; linarith
    have haux : 0 ≤ 1 + u - u ^ 2 := by nlinarith [sq_nonneg u]
    have hprod : 0 ≤ (1 - u) * (1 + u - u ^ 2) :=
      mul_nonneg (by linarith) haux
    dsimp [u] at hprod
    nlinarith
  by_cases h1 : t ≤ 1
  · rw [beta, if_neg h₁, if_neg h₀, if_pos h1]
    linarith
  by_cases h2 : t ≤ 2
  · rw [beta, if_neg h₁, if_neg h₀, if_neg h1, if_pos h2]
    let v : ℝ := t - 1
    have hv0 : 0 ≤ v := by dsimp [v]; linarith
    have hv1 : v ≤ 1 := by dsimp [v]; linarith
    have hprod : 0 ≤ (1 - v) * (1 - v ^ 2) :=
      mul_nonneg (by linarith) (by nlinarith [sq_nonneg v])
    dsimp [v] at hprod
    nlinarith
  · norm_num [beta, h₁, h₀, h1, h2]

theorem beta_mem (t : ℝ) : beta t ∈ Set.Icc (-1 : ℝ) 2 :=
  ⟨beta_lower t, beta_upper t⟩

end

end NCPLVerification
