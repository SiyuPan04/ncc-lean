import NCCLowerBoundVerification.Lower.UnscaledSerialization
import NCCLowerBoundVerification.Lower.GreenMatrix

/-!
# The genuine blockwise maximizer of the unscaled lower-bound objective

The dual part of `unscaledObjective` is a sum of independent regularized path
chains.  This file assembles the verified Green-matrix maximizer of every
inner chain into one vector in `UnscaledDual T n`.  In particular, the result
below is about the literal objective, rather than an auxiliary quadratic
value formula.
-/

namespace NCCLowerBoundVerification

noncomputable section

open Set

/-- The product of the explicit unconstrained maximizers of all inner blocks. -/
def unscaledInnerMaximizer {T n : Nat} (hn : 0 < n)
    (x : UnscaledPrimal T) : UnscaledDual T n :=
  fun j =>
    let ik := dualBlockIndexPair j
    innerMaximizer hn (primalA x ik.1) (primalB x ik.1) ik.2

@[simp] theorem dualBlock_unscaledInnerMaximizer {T n : Nat} (hn : 0 < n)
    (x : UnscaledPrimal T) (i : Fin (T - 1)) :
    dualBlock (unscaledInnerMaximizer hn x) i =
      innerMaximizer hn (primalA x i) (primalB x i) := by
  funext k
  unfold dualBlock unscaledInnerMaximizer dualBlockIndexPair
  have hcast :
      Fin.cast (Nat.mul_comm n (T - 1)) (dualBlockIndex i k) =
        finProdFinEquiv (i, k) := by
    apply Fin.ext
    simp [dualBlockIndex, finProdFinEquiv]
    omega
  rw [hcast, Equiv.symm_apply_apply]

/-- The block-product equivalence in the literal storage order `n * (T-1)`. -/
def unscaledDualBlockEquiv (T n : Nat) :
    (Fin (T - 1) × Fin n) ≃ Fin (n * (T - 1)) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm (T - 1) n))

@[simp] theorem unscaledDualBlockEquiv_apply {T n : Nat}
    (i : Fin (T - 1)) (k : Fin n) :
    unscaledDualBlockEquiv T n (i, k) = dualBlockIndex i k := by
  apply Fin.ext
  simp [unscaledDualBlockEquiv, finProdFinEquiv, dualBlockIndex]
  omega

/-- Euclidean squared norm splits exactly over the inner blocks. -/
theorem vecSq_eq_sum_dualBlock {T n : Nat} (y : UnscaledDual T n) :
    vecSq y = ∑ i : Fin (T - 1), vecSq (dualBlock y i) := by
  unfold vecSq NCPLVerification.vecSq
  calc
    (∑ j : Fin (n * (T - 1)), y j ^ 2) =
        ∑ p : Fin (T - 1) × Fin n,
          y (unscaledDualBlockEquiv T n p) ^ 2 := by
      symm
      exact Equiv.sum_comp (unscaledDualBlockEquiv T n)
        (fun j : Fin (n * (T - 1)) => y j ^ 2)
    _ = ∑ p : Fin (T - 1) × Fin n, (dualBlock y p.1 p.2) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [unscaledDualBlockEquiv_apply]
      rfl
    _ = ∑ i : Fin (T - 1), ∑ k : Fin n, (dualBlock y i k) ^ 2 := by
      rw [Fintype.sum_prod_type]

/-- The verified Green-column bounds give a genuine norm estimate for the
assembled dual maximizer. -/
theorem unscaledInnerMaximizer_size {T n : Nat} (hn : 10 ≤ n)
    (x : UnscaledPrimal T) :
    vecSq (unscaledInnerMaximizer (by omega : 0 < n) x) ≤
      96000 * (n : ℝ) ^ 2 * pulseSq x := by
  rw [vecSq_eq_sum_dualBlock]
  calc
    _ ≤
        ∑ i : Fin (T - 1),
          96000 * (n : ℝ) ^ 2 *
            ((primalA x i) ^ 2 + (primalB x i) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [dualBlock_unscaledInnerMaximizer]
      exact innerMaximizer_size_verified hn (primalA x i) (primalB x i)
    _ = 96000 * (n : ℝ) ^ 2 *
        ∑ i : Fin (T - 1),
          ((primalA x i) ^ 2 + (primalB x i) ^ 2) := by
      rw [Finset.mul_sum]

/-- A squared-norm condition is an exact, assumption-free inactivity test for
the paper's diameter-normalized dual ball. -/
theorem unscaledInnerMaximizer_mem_diameterBall {T n : Nat} (hn : 10 ≤ n)
    {D : ℝ} (x : UnscaledPrimal T)
    (hsize : 96000 * (n : ℝ) ^ 2 * pulseSq x ≤ (D / 2) ^ 2) :
    unscaledInnerMaximizer (by omega : 0 < n) x ∈
      diameterBall (n * (T - 1)) D := by
  unfold diameterBall
  exact (unscaledInnerMaximizer_size hn x).trans hsize

/-- Each literal block is maximized by its Green-matrix candidate. -/
theorem unscaledBlock_le_at_innerMaximizer {T n : Nat} (hn : 10 ≤ n)
    (P : UnscaledParameters) (x : UnscaledPrimal T)
    (y : UnscaledDual T n) (i : Fin (T - 1)) :
    unscaledBlock (by omega : 0 < n) P x y i ≤
      unscaledBlock (by omega : 0 < n) P x
        (unscaledInnerMaximizer (by omega : 0 < n) x) i := by
  have hinner := innerChain_le_at_stationary (by omega : 0 < n)
    (innerC (by omega : 0 < n)) (primalA x i) (primalB x i)
    (innerMaximizer_stationary hn (primalA x i) (primalB x i))
    (dualBlock y i)
  unfold unscaledBlock
  rw [dualBlock_unscaledInnerMaximizer]
  linarith

/-- The assembled vector is a global unconstrained dual maximizer of the
actual hard objective. -/
theorem unscaledInnerMaximizer_isMaximizer_univ {T n : Nat} (hn : 10 ≤ n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) :
    IsMaximizerOn Set.univ (unscaledObjective (by omega : 0 < n) P) x
      (unscaledInnerMaximizer (by omega : 0 < n) x) := by
  constructor
  · exact Set.mem_univ _
  · intro y _hy
    unfold unscaledObjective
    have hsum :
        (∑ i : Fin (T - 1),
            unscaledBlock (by omega : 0 < n) P x y i) ≤
          ∑ i : Fin (T - 1),
            unscaledBlock (by omega : 0 < n) P x
              (unscaledInnerMaximizer (by omega : 0 < n) x) i := by
      exact Finset.sum_le_sum fun i _ =>
        unscaledBlock_le_at_innerMaximizer hn P x y i
    linarith

/-- The unconstrained value is the objective evaluated at the assembled
maximizer; this turns the `sSup` definition into a concrete equality. -/
theorem unscaledValue_univ_eq_at_innerMaximizer {T n : Nat} (hn : 10 ≤ n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) :
    ValueOn Set.univ (unscaledObjective (by omega : 0 < n) P) x =
      unscaledObjective (by omega : 0 < n) P x
        (unscaledInnerMaximizer (by omega : 0 < n) x) := by
  exact value_eq_of_isMaximizerOn
    (unscaledInnerMaximizer_isMaximizer_univ hn P x)

/-- If the explicit unconstrained maximizer lies in a chosen feasible set,
then that same vector maximizes the literal objective on the feasible set. -/
theorem unscaledInnerMaximizer_isMaximizerOn {T n : Nat} (hn : 10 ≤ n)
    (P : UnscaledParameters) (Y : Set (UnscaledDual T n))
    (x : UnscaledPrimal T)
    (hmem : unscaledInnerMaximizer (by omega : 0 < n) x ∈ Y) :
    IsMaximizerOn Y (unscaledObjective (by omega : 0 < n) P) x
      (unscaledInnerMaximizer (by omega : 0 < n) x) := by
  refine ⟨hmem, ?_⟩
  intro y hy
  exact (unscaledInnerMaximizer_isMaximizer_univ hn P x).2 y (Set.mem_univ _)

theorem unscaledValue_eq_at_innerMaximizer_of_mem {T n : Nat} (hn : 10 ≤ n)
    (P : UnscaledParameters) (Y : Set (UnscaledDual T n))
    (x : UnscaledPrimal T)
    (hmem : unscaledInnerMaximizer (by omega : 0 < n) x ∈ Y) :
    ValueOn Y (unscaledObjective (by omega : 0 < n) P) x =
      unscaledObjective (by omega : 0 < n) P x
        (unscaledInnerMaximizer (by omega : 0 < n) x) := by
  exact value_eq_of_isMaximizerOn
    (unscaledInnerMaximizer_isMaximizerOn hn P Y x hmem)

/-- Restricted dual-ball inactivity for the value itself, derived from the
literal maximizer rather than postulated as an identity. -/
theorem unscaledValue_diameterBall_eq_univ_of_size {T n : Nat} (hn : 10 ≤ n)
    (P : UnscaledParameters) {D : ℝ} (x : UnscaledPrimal T)
    (hsize : 96000 * (n : ℝ) ^ 2 * pulseSq x ≤ (D / 2) ^ 2) :
    ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (by omega : 0 < n) P) x =
      ValueOn Set.univ (unscaledObjective (by omega : 0 < n) P) x := by
  rw [unscaledValue_eq_at_innerMaximizer_of_mem hn P
      (diameterBall (n * (T - 1)) D) x
      (unscaledInnerMaximizer_mem_diameterBall hn x hsize),
    unscaledValue_univ_eq_at_innerMaximizer hn P x]

/-- Substitution of the true maximizer turns every inner block into the
paper's Li-link `6(a-b/2)^2`, while retaining all literal outer terms. -/
theorem unscaledBlock_at_innerMaximizer_eq {T n : Nat} (hn : 10 ≤ n)
    (P : UnscaledParameters) (x : UnscaledPrimal T)
    (i : Fin (T - 1)) :
    unscaledBlock (by omega : 0 < n) P x
        (unscaledInnerMaximizer (by omega : 0 < n) x) i =
      entrancePulse P.alpha P.theta P.P0 (clippedCurrent P x i)
          (clippedNext P x i) (primalA x i) +
        6 * (primalA x i - primalB x i / 2) ^ 2 +
        P.gamma * ((primalA x i) ^ 2 + (primalB x i) ^ 2) +
        exitPulse P.beta P.theta (clippedCurrent P x i) (primalB x i)
          (clippedNext P x i) := by
  rw [unscaledBlock, dualBlock_unscaledInnerMaximizer]
  have htransfer := innerChain_transfer_verified hn (primalA x i) (primalB x i)
  linarith

/-! ## Endpoint-gradient transfer at the genuine maximizer

These are the differentiated Li-link identities.  They are proved directly
from the verified Green matrix, so later value-gradient arguments do not need
to assume an envelope formula.
-/

theorem innerGradA_at_innerMaximizer {n : Nat} (hn : 10 ≤ n) (a b : ℝ) :
    innerGradA (by omega : 0 < n) (innerC (by omega : 0 < n))
        (innerMaximizer (by omega : 0 < n) a b) +
      2 * innerC1 (by omega : 0 < n) * a =
        12 * (a - b / 2) := by
  let hnpos : 0 < n := by omega
  let q := innerB n (innerLast hnpos) (innerFirst hnpos)
  let d := innerB n (innerFirst hnpos) (innerFirst hnpos)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hqpos : 0 < q := by
    dsimp [q]
    exact innerB_cross_pos hn
  have hcrossne :
      innerB n (innerLast hnpos) (innerFirst hnpos) ≠ 0 :=
    ne_of_gt (innerB_cross_pos hn)
  have hsquare : innerScale n (innerC hnpos) ^ 2 = innerC hnpos / (n : ℝ) := by
    unfold innerScale
    rw [Real.sq_sqrt]
    exact div_nonneg (innerC_pos hn).le hnreal.le
  change innerGradA hnpos (innerC hnpos) (innerMaximizer hnpos a b) +
      2 * innerC1 hnpos * a = 12 * (a - b / 2)
  unfold innerGradA innerMaximizer
  let E := innerB n (innerFirst hnpos) (innerFirst hnpos) * a -
    innerB n (innerFirst hnpos) (innerLast hnpos) * (b / 2)
  change innerScale n (innerC hnpos) *
      (innerScale n (innerC hnpos) * E) + 2 * innerC1 hnpos * a =
    12 * (a - b / 2)
  have hscaled : innerScale n (innerC hnpos) *
      (innerScale n (innerC hnpos) * E) =
        innerC hnpos / (n : ℝ) * E := by
    rw [← mul_assoc]
    rw [show innerScale n (innerC hnpos) * innerScale n (innerC hnpos) =
        innerC hnpos / (n : ℝ) by simpa [pow_two] using hsquare]
  rw [hscaled]
  dsimp [E]
  rw [innerB_apply_comm n (innerFirst hnpos) (innerLast hnpos)]
  change innerC hnpos / (n : ℝ) *
      (d * a - q * (b / 2)) + 2 * innerC1 hnpos * a =
    12 * (a - b / 2)
  unfold innerC1 innerC
  dsimp [q, d]
  field_simp [ne_of_gt hnreal, hcrossne]
  ring

theorem innerGradB_at_innerMaximizer {n : Nat} (hn : 10 ≤ n) (a b : ℝ) :
    innerGradB (by omega : 0 < n) (innerC (by omega : 0 < n))
        (innerMaximizer (by omega : 0 < n) a b) +
      2 * innerC2 (by omega : 0 < n) * b =
        -6 * (a - b / 2) := by
  let hnpos : 0 < n := by omega
  let q := innerB n (innerLast hnpos) (innerFirst hnpos)
  let d := innerB n (innerFirst hnpos) (innerFirst hnpos)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hqpos : 0 < q := by
    dsimp [q]
    exact innerB_cross_pos hn
  have hcrossne :
      innerB n (innerLast hnpos) (innerFirst hnpos) ≠ 0 :=
    ne_of_gt (innerB_cross_pos hn)
  have hdiag :
      innerB n (innerLast hnpos) (innerLast hnpos) = d := by
    simpa [d] using innerB_endpoint_diagonal_eq hnpos
  have hcross :
      innerB n (innerLast hnpos) (innerFirst hnpos) = q := rfl
  have hsquare : innerScale n (innerC hnpos) ^ 2 = innerC hnpos / (n : ℝ) := by
    unfold innerScale
    rw [Real.sq_sqrt]
    exact div_nonneg (innerC_pos hn).le hnreal.le
  change innerGradB hnpos (innerC hnpos) (innerMaximizer hnpos a b) +
      2 * innerC2 hnpos * b = -6 * (a - b / 2)
  unfold innerGradB innerMaximizer
  let E := innerB n (innerLast hnpos) (innerFirst hnpos) * a -
    innerB n (innerLast hnpos) (innerLast hnpos) * (b / 2)
  change -(1 / 2 : ℝ) * innerScale n (innerC hnpos) *
      (innerScale n (innerC hnpos) * E) + 2 * innerC2 hnpos * b =
    -6 * (a - b / 2)
  have hinnerScale : innerScale n (innerC hnpos) *
      (innerScale n (innerC hnpos) * E) =
        innerC hnpos / (n : ℝ) * E := by
    rw [← mul_assoc]
    rw [show innerScale n (innerC hnpos) * innerScale n (innerC hnpos) =
        innerC hnpos / (n : ℝ) by simpa [pow_two] using hsquare]
  have hscaled : -(1 / 2 : ℝ) * innerScale n (innerC hnpos) *
      (innerScale n (innerC hnpos) * E) =
        -(1 / 2 : ℝ) * (innerC hnpos / (n : ℝ) * E) := by
    calc
      _ = -(1 / 2 : ℝ) *
          (innerScale n (innerC hnpos) *
            (innerScale n (innerC hnpos) * E)) := by ring
      _ = -(1 / 2 : ℝ) * (innerC hnpos / (n : ℝ) * E) := by
        rw [hinnerScale]
  rw [hscaled]
  dsimp [E]
  rw [hdiag, hcross]
  change -(1 / 2 : ℝ) *
      (innerC hnpos / (n : ℝ) * (q * a - d * (b / 2))) +
      2 * innerC2 hnpos * b = -6 * (a - b / 2)
  unfold innerC2 innerC
  dsimp [q, d]
  field_simp [ne_of_gt hnreal, hcrossne]
  ring

end

end NCCLowerBoundVerification
