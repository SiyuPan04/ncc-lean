import Mathlib

/-!
# Weights of the terminal-amplified inner chain

The paper writes

`αᵢ = N ^ (-1 + 2 ^ (-(N-i)))`.

It is more convenient for proofs to index the same sequence by the distance
`k` from the terminal coordinate.  The defining recurrence is

`w 0 = 1`, `w (k+1) = sqrt (w k / N)`.

The closed-form identity with the displayed formula in the paper is proved
below; subsequent algebra uses the recurrence, so no transcendental identity
is hidden in automation.
-/

namespace NCPLVerification

noncomputable section

/-- The inner-chain weight at distance `k` from the terminal coordinate. -/
def innerWeight (N : ℕ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => Real.sqrt (innerWeight N k / (N : ℝ))

@[simp] theorem innerWeight_zero (N : ℕ) : innerWeight N 0 = 1 := rfl

@[simp] theorem innerWeight_succ (N k : ℕ) :
    innerWeight N (k + 1) = Real.sqrt (innerWeight N k / (N : ℝ)) := rfl

theorem innerWeight_pos {N : ℕ} (hN : 0 < N) (k : ℕ) : 0 < innerWeight N k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [innerWeight_succ]
      exact Real.sqrt_pos.2 (div_pos ih (by positivity))

theorem innerWeight_nonneg {N : ℕ} (hN : 0 < N) (k : ℕ) :
    0 ≤ innerWeight N k := (innerWeight_pos hN k).le

theorem innerWeight_succ_sq {N : ℕ} (hN : 0 < N) (k : ℕ) :
    innerWeight N (k + 1) ^ 2 = innerWeight N k / (N : ℝ) := by
  rw [innerWeight_succ, Real.sq_sqrt]
  exact div_nonneg (innerWeight_nonneg hN k) (by positivity)

/-- Closed form used in the paper: at distance `k` from the end, the weight
is `N ^ (-1 + 2⁻ᵏ)`. -/
theorem innerWeight_eq_rpow {N : ℕ} (hN : 0 < N) (k : ℕ) :
    innerWeight N k =
      (N : ℝ) ^ ((-1 : ℝ) + ((1 : ℝ) / 2) ^ k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
      have hsq := innerWeight_succ_sq hN k
      have hexp :
          ((-1 : ℝ) + ((1 : ℝ) / 2) ^ (k + 1)) * 2 =
            ((-1 : ℝ) + ((1 : ℝ) / 2) ^ k) - 1 := by
        rw [pow_succ]
        norm_num
        ring
      have hrhs_sq :
          ((N : ℝ) ^ ((-1 : ℝ) + ((1 : ℝ) / 2) ^ (k + 1))) ^ 2 =
            innerWeight N k / (N : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hNreal.le]
        norm_num only [Nat.cast_ofNat]
        rw [hexp,
          Real.rpow_sub hNreal, Real.rpow_one, ← ih]
      have hleft : 0 ≤ innerWeight N (k + 1) := innerWeight_nonneg hN _
      have hright :
          0 ≤ (N : ℝ) ^ ((-1 : ℝ) + ((1 : ℝ) / 2) ^ (k + 1)) :=
        Real.rpow_nonneg hNreal.le _
      nlinarith

/-- Every weight lies in `[1/N, 1]`.  This is the key elementary estimate
behind both monotonicity and the uniform bound on the sum of the weights. -/
theorem innerWeight_mem {N : ℕ} (hN : 0 < N) (k : ℕ) :
    innerWeight N k ∈ Set.Icc ((N : ℝ)⁻¹) 1 := by
  induction k with
  | zero =>
      constructor
      · simpa using (inv_le_one₀ (by exact_mod_cast hN)).2 (by exact_mod_cast hN)
      · simp
  | succ k ih =>
      constructor
      · have hsquare := innerWeight_succ_sq hN k
        have hnonneg := innerWeight_nonneg hN (k + 1)
        have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
        have hinvnonneg : 0 ≤ (N : ℝ)⁻¹ := (inv_pos.mpr hNreal).le
        have hprev : (N : ℝ)⁻¹ ≤ innerWeight N k := ih.1
        have hsq : (N : ℝ)⁻¹ ^ 2 ≤ innerWeight N (k + 1) ^ 2 := by
          rw [hsquare]
          simpa [pow_two, div_eq_mul_inv] using
            mul_le_mul_of_nonneg_right hprev hinvnonneg
        nlinarith
      · have hsquare := innerWeight_succ_sq hN k
        have hnonneg := innerWeight_nonneg hN (k + 1)
        have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast hN
        have hquot : innerWeight N k / (N : ℝ) ≤ 1 := by
          have := ih.2
          apply (div_le_one (by positivity)).2
          linarith
        nlinarith

theorem innerWeight_antitone_step {N : ℕ} (hN : 0 < N) (k : ℕ) :
    innerWeight N (k + 1) ≤ innerWeight N k := by
  have hsquare := innerWeight_succ_sq hN k
  have hnext := innerWeight_nonneg hN (k + 1)
  have hprev := innerWeight_nonneg hN k
  have hlower := (innerWeight_mem hN k).1
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmul : 1 ≤ (N : ℝ) * innerWeight N k := by
    have hdiv : 1 / (N : ℝ) ≤ innerWeight N k := by
      simpa [one_div] using hlower
    have := (div_le_iff₀ hNreal).mp hdiv
    simpa [mul_comm] using this
  have hsq : innerWeight N (k + 1) ^ 2 ≤ innerWeight N k ^ 2 := by
    rw [hsquare]
    apply (div_le_iff₀ hNreal).2
    nlinarith
  nlinarith

/-- A convenient affine-geometric majorant. -/
theorem innerWeight_le_geometric {N : ℕ} (hN : 0 < N) (k : ℕ) :
    innerWeight N k ≤ (2 : ℝ)⁻¹ ^ k + (N : ℝ)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hsquare := innerWeight_succ_sq hN k
      have hnext := innerWeight_nonneg hN (k + 1)
      have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
      have hamgm :
          innerWeight N (k + 1) ≤
            (innerWeight N k + (N : ℝ)⁻¹) / 2 := by
        have hsqnonneg :
            0 ≤ (innerWeight N k - (N : ℝ)⁻¹) ^ 2 := sq_nonneg _
        have htarget :
            innerWeight N (k + 1) ^ 2 ≤
              ((innerWeight N k + (N : ℝ)⁻¹) / 2) ^ 2 := by
          rw [hsquare, div_eq_mul_inv]
          nlinarith
        have hrhs : 0 ≤ (innerWeight N k + (N : ℝ)⁻¹) / 2 :=
          div_nonneg
            (add_nonneg (innerWeight_nonneg hN k) (inv_nonneg.mpr hNreal.le))
            (by norm_num)
        nlinarith
      rw [pow_succ]
      have hhalf : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
      rw [hhalf] at ih ⊢
      nlinarith [inv_pos.mpr hNreal]

theorem sum_half_pow_eq (n : ℕ) :
    ∑ k ∈ Finset.range n, ((1 : ℝ) / 2) ^ k =
      2 - 2 * ((1 : ℝ) / 2) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      ring

theorem sum_innerWeight_range_le_three {N : ℕ} (hN : 0 < N) :
    ∑ k ∈ Finset.range N, innerWeight N k ≤ 3 := by
  have hmajor :
      (∑ k ∈ Finset.range N, innerWeight N k) ≤
        ∑ k ∈ Finset.range N, (((1 : ℝ) / 2) ^ k + (N : ℝ)⁻¹) := by
    exact Finset.sum_le_sum fun k _ ↦ by
      simpa [one_div] using innerWeight_le_geometric hN k
  have hgeom : (∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ k) ≤ 2 := by
    rw [sum_half_pow_eq]
    have : 0 ≤ ((1 : ℝ) / 2) ^ N := pow_nonneg (by norm_num) _
    linarith
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  calc
    (∑ k ∈ Finset.range N, innerWeight N k)
        ≤ ∑ k ∈ Finset.range N, (((1 : ℝ) / 2) ^ k + (N : ℝ)⁻¹) := hmajor
    _ = (∑ k ∈ Finset.range N, ((1 : ℝ) / 2) ^ k) +
          (N : ℝ) * (N : ℝ)⁻¹ := by
            rw [Finset.sum_add_distrib]
            simp
    _ ≤ 2 + 1 := add_le_add hgeom (le_of_eq (mul_inv_cancel₀ hNreal.ne'))
    _ = 3 := by norm_num

/-- The paper's one-based `αᵢ`, represented using a zero-based `Fin N` index. -/
def innerAlpha (N : ℕ) (i : Fin N) : ℝ :=
  innerWeight N (N - 1 - i.1)

/-- The paper's metric weight `dᵢ`; truncated subtraction makes the terminal
case exactly `d_N = 1`. -/
def innerD (N : ℕ) (i : Fin N) : ℝ :=
  innerWeight N (N - 2 - i.1)

theorem innerAlpha_pos {N : ℕ} (hN : 0 < N) (i : Fin N) :
    0 < innerAlpha N i := innerWeight_pos hN _

theorem innerAlpha_le_one {N : ℕ} (hN : 0 < N) (i : Fin N) :
    innerAlpha N i ≤ 1 := (innerWeight_mem hN _).2

theorem innerD_pos {N : ℕ} (hN : 0 < N) (i : Fin N) :
    0 < innerD N i := innerWeight_pos hN _

theorem innerD_terminal {N : ℕ} (hN : 0 < N) :
    innerD N ⟨N - 1, Nat.sub_lt hN (by omega)⟩ = 1 := by
  have hk : N - 2 - (N - 1) = 0 := by omega
  simp [innerD, hk]

theorem innerAlpha_terminal {N : ℕ} (hN : 0 < N) :
    innerAlpha N ⟨N - 1, Nat.sub_lt hN (by omega)⟩ = 1 := by
  simp [innerAlpha]

/-- For nonterminal indices, `dᵢ = αᵢ₊₁`. -/
theorem innerD_castSucc {N : ℕ} (hN : 0 < N) (i : Fin N) (hi : i.1 + 1 < N) :
    innerD N i = innerAlpha N ⟨i.1 + 1, hi⟩ := by
  have hsum : 2 + i.1 = 1 + (i.1 + 1) := by omega
  simp only [innerD, innerAlpha, Nat.sub_sub, hsum]

/-- Exact coefficient identity `αᵢ²/dᵢ = 1/N` away from the terminal
coordinate. -/
theorem innerAlpha_sq_div_innerD {N : ℕ} (hN : 0 < N)
    (i : Fin N) (hi : i.1 + 1 < N) :
    innerAlpha N i ^ 2 / innerD N i = (N : ℝ)⁻¹ := by
  have hk : N - 1 - i.1 = (N - 2 - i.1) + 1 := by omega
  rw [innerAlpha, innerD, hk, innerWeight_succ_sq hN]
  have hw : innerWeight N (N - 2 - i.1) ≠ 0 :=
    ne_of_gt (innerWeight_pos hN _)
  field_simp [hw]

/-- Exact identity `αᵢ²/dᵢ₋₁ = αᵢ` for noninitial indices. -/
theorem innerAlpha_sq_div_innerD_prev {N : ℕ} (hN : 0 < N)
    (i : Fin N) (hi : 0 < i.1) :
    innerAlpha N i ^ 2 / innerD N ⟨i.1 - 1, by omega⟩ = innerAlpha N i := by
  have hil := i.isLt
  have heq : innerD N ⟨i.1 - 1, by omega⟩ = innerAlpha N i := by
    have hsum : 2 + (i.1 - 1) = 1 + i.1 := by omega
    simp only [innerD, innerAlpha, Nat.sub_sub, hsum]
  rw [heq]
  field_simp [ne_of_gt (innerAlpha_pos hN i)]

theorem innerAlpha_le_innerD {N : ℕ} (hN : 0 < N) (i : Fin N) :
    innerAlpha N i ≤ innerD N i := by
  unfold innerAlpha innerD
  by_cases hi : i.1 + 1 < N
  · have hk : N - 1 - i.1 = (N - 2 - i.1) + 1 := by omega
    rw [hk]
    exact innerWeight_antitone_step hN _
  · have hterminal : i.1 = N - 1 := by omega
    have hk : N - 2 - (N - 1) = 0 := by omega
    simp [hterminal, hk]

theorem one_div_N_le_innerD {N : ℕ} (hN : 0 < N) (i : Fin N) :
    (N : ℝ)⁻¹ ≤ innerD N i := (innerWeight_mem hN _).1

/-- The unspecified numerical constant in the paper can be chosen as `3`. -/
theorem sum_innerAlpha_le_three {N : ℕ} (hN : 0 < N) :
    ∑ i : Fin N, innerAlpha N i ≤ 3 := by
  have halpha (i : Fin N) :
      innerAlpha N i = innerWeight N (Fin.rev i).1 := by
    unfold innerAlpha
    apply congrArg (innerWeight N)
    rw [Fin.val_rev]
    omega
  calc
    (∑ i : Fin N, innerAlpha N i)
        = ∑ i : Fin N, innerWeight N (Fin.rev i).1 := by
            apply Fintype.sum_congr
            exact halpha
    _ = ∑ i : Fin N, innerWeight N i.1 := by
          simpa using Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin N))
            (fun i : Fin N ↦ innerWeight N i.1)
    _ = ∑ k ∈ Finset.range N, innerWeight N k := by
          simpa using Fin.sum_univ_eq_sum_range (fun k ↦ innerWeight N k) N
    _ ≤ 3 := sum_innerWeight_range_le_three hN

end

end NCPLVerification
