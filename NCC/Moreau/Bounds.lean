import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# A norm bound from the proximal strong-convexity inequality

For an `ell`-weakly convex objective and proximal parameter `1 / (2 * ell)`,
strong convexity of the proximal objective gives the hypothesis `hprox` below.
This file proves its norm/algebra consequence, NOT existence of the proximal
point, the weak-convexity implication, or differentiability of the envelope.
Those analytical bridges are listed as pending in `STATUS.md`.

The `8/3` estimate was discussed during the manuscript audit; it is auxiliary,
not asserted to be a numbered theorem in the current paper.
-/

namespace NCC.Moreau

theorem initial_gradient_bound_of_proximal_inequality
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (phi : E → ℝ) (x u gradient : E) (ell delta : ℝ)
    (hell : 0 < ell)
    (hgap : phi x - phi u ≤ delta)
    (hprox : phi u + ell * ‖x - u‖ ^ 2 +
      (ell / 2) * ‖x - u‖ ^ 2 ≤ phi x)
    (hgradient : gradient = (2 * ell) • (x - u)) :
    ‖gradient‖ ^ 2 ≤ (8 / 3 : ℝ) * ell * delta := by
  have hbase : (3 / 2 : ℝ) * ell * ‖x - u‖ ^ 2 ≤ delta := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hbase (le_of_lt hell)
  rw [hgradient, norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < 2 * ell)]
  nlinarith only [hscaled]

end NCC.Moreau
