import NCC.Basic
import Mathlib

/-!
# What the primal initial gap does not control in the NC-SC extension

This elementary family is not a counterexample to a rate with an explicit
dual initialization cost. It proves that such a cost cannot be bounded
from the primal value gap alone when the dual domain is unbounded.
-/
namespace NCC.Extensions.NCSCInitialization
noncomputable section

def objective (mu center : ℝ) (_x y : ℝ) : ℝ :=
  -(mu / 2) * (y - center) ^ 2

def dualGradient (mu center : ℝ) (_x y : ℝ) : ℝ := -mu * (y - center)

theorem derivative (mu center x y : ℝ) :
    HasDerivAt (objective mu center x) (dualGradient mu center x y) y := by
  have h := ((hasDerivAt_id y).sub_const center).pow 2 |>.const_mul (-(mu / 2))
  exact h.congr_deriv (by dsimp [dualGradient]; ring)

theorem primal_derivative (mu center x y : ℝ) :
    HasDerivAt (fun u => objective mu center u y) 0 x := hasDerivAt_const _ _

theorem gradient_lipschitz (mu center x y u v : ℝ) :
    (dualGradient mu center x y - dualGradient mu center u v) ^ 2 ≤
      mu ^ 2 * ((x - u) ^ 2 + (y - v) ^ 2) := by
  unfold dualGradient
  nlinarith [mul_nonneg (sq_nonneg mu) (sq_nonneg (x - u))]

/-- Exact strong-concavity identity, for every convex-combination weight. -/
theorem strong_concavity_identity (mu center x y v theta : ℝ) :
    objective mu center x (theta * y + (1 - theta) * v) =
      theta * objective mu center x y + (1 - theta) * objective mu center x v +
        mu / 2 * theta * (1 - theta) * (y - v) ^ 2 := by
  unfold objective
  ring

theorem maximum (mu center x : ℝ) (hmu : 0 < mu) :
    objective mu center x center = 0 ∧ ∀ y, objective mu center x y ≤ 0 := by
  refine ⟨by simp [objective], ?_⟩
  intro y
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg (y - center))

theorem maximizer_unique {mu center x y : ℝ} (hmu : 0 < mu)
    (hy : objective mu center x y = 0) : y = center := by
  have hs := sq_nonneg (y - center)
  have hsq : (y - center) ^ 2 = 0 := by
    unfold objective at hy
    nlinarith
  nlinarith [sq_eq_zero_iff.mp hsq]

theorem value_eq_zero {mu center : ℝ} (hmu : 0 < mu) (x : ℝ) :
    sSup (Set.range (objective mu center x)) = 0 := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro v ⟨y, rfl⟩
    exact (maximum mu center x hmu).2 y
  · apply le_csSup
    · exact ⟨0, by rintro v ⟨y, rfl⟩; exact (maximum mu center x hmu).2 y⟩
    · exact ⟨center, (maximum mu center x hmu).1⟩

theorem initial_value_gap_zero {mu center : ℝ} (hmu : 0 < mu) :
    sSup (Set.range (objective mu center 0)) -
      sInf (Set.range (fun x : ℝ => sSup (Set.range (objective mu center x)))) = 0 := by
  simp only [value_eq_zero hmu, Set.range_const, csInf_singleton, sub_self]

/-- Even with fixed smoothness, strong concavity, origin initialization
and zero primal value gap, the dual optimum and initial GS residual can
be arbitrarily far from zero. -/
theorem arbitrarily_large_dual_initialization {mu : ℝ} (hmu : 0 < mu) (K : ℝ) :
    ∃ center : ℝ,
      mu * center ^ 2 > K ∧
      |dualGradient mu center 0 0| > K ∧
      sSup (Set.range (objective mu center 0)) = 0 := by
  let center := (|K| + mu + 1) / mu
  have hc : 0 < center := by dsimp [center]; positivity
  have hprod : mu * center = |K| + mu + 1 := by dsimp [center]; field_simp
  have hc1 : 1 < center := by
    apply (lt_div_iff₀ hmu).2
    linarith [abs_nonneg K]
  refine ⟨center, ?_, ?_, value_eq_zero hmu 0⟩
  · have hs : mu * center < mu * center ^ 2 := by
      have hm := mul_lt_mul_of_pos_left hc1 (mul_pos hmu hc)
      nlinarith
    linarith [le_abs_self K]
  · have hg : dualGradient mu center 0 0 = mu * center := by simp [dualGradient]
    rw [hg, abs_of_pos (mul_pos hmu hc)]
    linarith [le_abs_self K]

end
end NCC.Extensions.NCSCInitialization
