import NCCLowerBoundVerification.Basic

/-!
# The bounded dual ball

This module proves the elementary geometric properties of the paper's
diameter-normalized Euclidean ball.  Its defining radius is `D / 2`, so two
points in the ball are at squared Euclidean distance at most `D ^ 2`.
-/

namespace NCCLowerBoundVerification

noncomputable section

/-- The explicit coordinate-squared Euclidean norm is continuous. -/
theorem continuous_vecSq {n : Nat} : Continuous (@vecSq n) := by
  unfold vecSq NCPLVerification.vecSq
  fun_prop

/-- The full coordinate origin belongs to every diameter ball. -/
theorem zero_mem_diameterBall (n : Nat) (D : ℝ) (_hD : 0 ≤ D) :
    (0 : EVec n) ∈ diameterBall n D := by
  simp [diameterBall, vecSq, NCPLVerification.vecSq, sq_nonneg]

/-- Every diameter ball is nonempty. -/
theorem diameterBall_nonempty (n : Nat) (D : ℝ) (hD : 0 ≤ D) :
    (diameterBall n D).Nonempty :=
  ⟨0, zero_mem_diameterBall n D hD⟩

/-- A diameter ball is closed. -/
theorem diameterBall_closed (n : Nat) (D : ℝ) :
    IsClosed (diameterBall n D) := by
  exact isClosed_le continuous_vecSq continuous_const

/-- Squared Euclidean norm is convex, hence so is each of its sublevel balls. -/
theorem diameterBall_convex (n : Nat) (D : ℝ) :
    Convex ℝ (diameterBall n D) := by
  intro x hx y hy a b ha hb hab
  unfold diameterBall at hx hy ⊢
  unfold vecSq NCPLVerification.vecSq at hx hy ⊢
  calc
    ∑ i : Fin n, (a * x i + b * y i) ^ 2 ≤
        ∑ i : Fin n, (a * x i ^ 2 + b * y i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sq_nonneg (x i - y i))]
    _ = a * (∑ i : Fin n, x i ^ 2) + b * (∑ i : Fin n, y i ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ a * (D / 2) ^ 2 + b * (D / 2) ^ 2 := by
      exact add_le_add (mul_le_mul_of_nonneg_left hx ha)
        (mul_le_mul_of_nonneg_left hy hb)
    _ = (D / 2) ^ 2 := by
      rw [← add_mul, hab, one_mul]

/-- Coordinate form of `‖x - y‖² ≤ 2‖x‖² + 2‖y‖²`. -/
theorem vecSq_sub_le_two {n : Nat} (x y : EVec n) :
    vecSq (x - y) ≤ 2 * vecSq x + 2 * vecSq y := by
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (x i + y i)]

/-- The defining radius `D / 2` gives squared Euclidean diameter at most `D²`. -/
theorem diameterBall_vecSq_sub_le {n : Nat} {D : ℝ} (_hD : 0 ≤ D)
    {y y' : EVec n} (hy : y ∈ diameterBall n D)
    (hy' : y' ∈ diameterBall n D) :
    vecSq (y - y') ≤ D ^ 2 := by
  have hsub := vecSq_sub_le_two y y'
  change vecSq y ≤ (D / 2) ^ 2 at hy
  change vecSq y' ≤ (D / 2) ^ 2 at hy'
  nlinarith

/-- The four basic facts needed when instantiating the paper's dual domain. -/
theorem diameterBall_properties (n : Nat) (D : ℝ) (hD : 0 ≤ D) :
    (diameterBall n D).Nonempty ∧
      IsClosed (diameterBall n D) ∧
      Convex ℝ (diameterBall n D) ∧
      ∀ y ∈ diameterBall n D, ∀ y' ∈ diameterBall n D,
        vecSq (y - y') ≤ D ^ 2 := by
  exact ⟨diameterBall_nonempty n D hD, diameterBall_closed n D,
    diameterBall_convex n D, fun y hy y' hy' =>
      diameterBall_vecSq_sub_le hD hy hy'⟩

end

end NCCLowerBoundVerification
