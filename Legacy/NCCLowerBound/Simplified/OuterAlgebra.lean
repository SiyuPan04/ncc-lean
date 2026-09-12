import NCCLowerBound.Simplified.OuterInterfaces

/-!
# Discrete frontier and terminal algebra

This module isolates the exact finite-order and two-dimensional calculations
used in Lemma `lem:bounded-pulse` and Proposition `prop:terminal-gradient`.
They are independent of the analytic construction of the scalar interfaces.
-/

namespace NCCLowerBound
namespace Simplified

noncomputable section

/-- A high-prefix/low-suffix frontier at the first low state. -/
def IsFrontier (M : Nat) (s : Nat → ℝ) (j : Nat) : Prop :=
  j ≤ M ∧
    (∀ i, i < j → (1 : ℝ) ≤ s i) ∧
    (∀ i, j ≤ i → i ≤ M → s i ≤ (1 / 5 : ℝ))

/--
If every state is either low or high, the seed is high, the terminal state is
low, and a low-to-high adjacent pair is excluded, then the frontier exists
and is unique.
-/
theorem existsUnique_frontier
    {M : Nat} (hM : 1 ≤ M) (s : Nat → ℝ)
    (hseed : (1 : ℝ) ≤ s 0)
    (hterminal : s M ≤ (1 / 5 : ℝ))
    (hphase : ∀ i, i ≤ M →
      s i ≤ (1 / 5 : ℝ) ∨ (1 : ℝ) ≤ s i)
    (hnoLowHigh : ∀ i, i < M →
      s i ≤ (1 / 5 : ℝ) → ¬ (1 : ℝ) ≤ s (i + 1)) :
    ∃! j, 1 ≤ j ∧ IsFrontier M s j := by
  have hex : ∃ i : Nat, s i ≤ (1 / 5 : ℝ) := ⟨M, hterminal⟩
  let j : Nat := Nat.find hex
  have hjlow : s j ≤ (1 / 5 : ℝ) := Nat.find_spec hex
  have hjM : j ≤ M := Nat.find_le hterminal
  have hjpos : 1 ≤ j := by
    by_contra h
    have hj0 : j = 0 := by omega
    rw [hj0] at hjlow
    linarith
  have hbefore : ∀ i, i < j → (1 : ℝ) ≤ s i := by
    intro i hi
    rcases hphase i (by omega) with hilow | hihigh
    · exact False.elim ((Nat.find_min hex hi) hilow)
    · exact hihigh
  have hlowNext : ∀ i, i < M →
      s i ≤ (1 / 5 : ℝ) → s (i + 1) ≤ (1 / 5 : ℝ) := by
    intro i hiM hilow
    rcases hphase (i + 1) (by omega) with hnextLow | hnextHigh
    · exact hnextLow
    · exact False.elim (hnoLowHigh i hiM hilow hnextHigh)
  have hafter : ∀ i, j ≤ i → i ≤ M → s i ≤ (1 / 5 : ℝ) := by
    intro i
    induction i with
    | zero =>
        intro hji _hiM
        have hj0 : j = 0 := by omega
        simpa [hj0] using hjlow
    | succ i ih =>
        intro hji hiM
        by_cases hEq : j = i + 1
        · simpa [hEq] using hjlow
        · have hjPrev : j ≤ i := by omega
          exact hlowNext i (by omega) (ih hjPrev (by omega))
  have hjFrontier : IsFrontier M s j := ⟨hjM, hbefore, hafter⟩
  refine ⟨j, ⟨hjpos, hjFrontier⟩, ?_⟩
  intro k hk
  rcases hk with ⟨hkpos, hkM, hkbefore, hkafter⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with hjk | hkj
  · have hkHigh : (1 : ℝ) ≤ s k := hbefore k hjk
    have hkLow : s k ≤ (1 / 5 : ℝ) := hkafter k le_rfl hkM
    linarith
  · have hjHigh : (1 : ℝ) ≤ s j := hkbefore j hkj
    linarith

/-- The radial inequality in the pulse variables forces the uniform bound 20. -/
theorem pulse_norm_le_twenty
    {r tau : ℝ} (hr : 0 ≤ r) (htau0 : 0 ≤ tau)
    (htau : tau ≤ (1 / 4 : ℝ))
    (hradial : (2 / 5 : ℝ) * r ^ 2 - 7 * r ≤ tau * r) :
    r ≤ 20 := by
  by_cases hr0 : r = 0
  · simp [hr0]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    nlinarith

/-- Coordinate-wise consequence of a two-dimensional norm bound. -/
theorem coords_lower_of_sq_sum_le
    {ga gb tau : ℝ} (htau : 0 ≤ tau)
    (hsmall : ga ^ 2 + gb ^ 2 ≤ tau ^ 2) :
    -tau ≤ ga ∧ -tau ≤ gb := by
  constructor <;> nlinarith [sq_nonneg ga, sq_nonneg gb]

/--
Solving the two frontier pulse equations gives `b ≥ 1`.  The proof uses a
slightly coarser coordinate bound than the manuscript's `sqrt 5` estimate;
it is strictly strong enough at `tau ≤ 1/4`.
-/
theorem frontier_exit_pulse_ge_one
    {a b s ga gb tau : ℝ}
    (hsLower : -(1 / 10 : ℝ) ≤ s)
    (hsUpper : s ≤ (1 / 5 : ℝ))
    (htau0 : 0 ≤ tau) (htau : tau ≤ (1 / 4 : ℝ))
    (hsmall : ga ^ 2 + gb ^ 2 ≤ tau ^ 2)
    (hga : ga = 2 * a - b - 4)
    (hgb : gb = -a + 2 * b - s) :
    1 ≤ b := by
  have hcoords := coords_lower_of_sq_sum_le htau0 hsmall
  have hsolve : 3 * b = 4 + 2 * s + ga + 2 * gb := by
    rw [hga, hgb]
    ring
  nlinarith

/-- The active state derivative has magnitude at least one. -/
theorem terminal_state_gradient_abs_ge_one
    {uPrime b g : ℝ} (hu : uPrime ≤ 0) (hb : 1 ≤ b)
    (hg : g = uPrime - b) :
    1 ≤ |g| := by
  have hgneg : g ≤ -1 := by rw [hg]; linarith
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- A gradient norm below `tau ≤ 1/4` contradicts the active state derivative. -/
theorem terminal_gradient_contradiction
    {gradSq tau g : ℝ} (htau0 : 0 ≤ tau) (htau : tau ≤ (1 / 4 : ℝ))
    (hgcomponent : g ^ 2 ≤ gradSq) (hsmall : gradSq ≤ tau ^ 2)
    (hlarge : 1 ≤ |g|) : False := by
  nlinarith [sq_abs g]

end

end Simplified
end NCCLowerBound
