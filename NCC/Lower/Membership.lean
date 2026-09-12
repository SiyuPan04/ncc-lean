import NCC.Construction.Regularity
import NCC.Model.ConventionBridge
import NCCLowerBoundVerification.DiameterBall

/-!
# Function-class membership of the literal current hard instance

The domain is the whole primal space and one dual ball of diameter D.
All fields, including actual gradient representation, come from the current
construction, not an abstract certificate or an older terminal example.
-/

namespace NCC.Lower.Membership

noncomputable section

open NCCLowerBoundVerification
open NCC.Construction

def unscaled {m n : ℕ} (hn : 0 < n) (D : ℝ) : NCCInstance (m * 3) (m * n) where
  X := Set.univ
  Y := Inner.dualBall m n D
  f := Composite.objective hn
  gradX := Regularity.gradientX hn
  gradY := Regularity.gradientY hn
  x0 := 0

theorem dualBall_eq_diameterBall (m n : ℕ) (D : ℝ) :
    Inner.dualBall m n D = diameterBall (m * n) D := rfl

theorem withinClass {m n : ℕ} (hm : 0 < m) (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 < D) :
    Model.WithinClass Regularity.ell₀ D (Composite.c_Δ * (m : ℝ))
      (unscaled (m := m) (by omega : 0 < n) D) := by
  let hnp : 0 < n := by omega
  have hrep := Regularity.gradient_represents_fderiv (m := m) hnp
  refine {
    ell_pos := Regularity.ell₀_pos
    D_pos := hD
    Delta_pos := mul_pos Composite.c_Δ_pos (by exact_mod_cast hm)
    primal_origin := Set.mem_univ _
    dual_origin := Composite.zero_mem_dualBall m n D
    initialization := rfl
    X_closed := isClosed_univ
    X_convex := convex_univ
    Y_closed := diameterBall_closed (m * n) D
    Y_convex := diameterBall_convex (m * n) D
    gradient_representation := ?_
    jointly_smooth := ?_
    dual_concave := ?_
    dual_diameter := ?_
    initial_gap_pointwise := ?_ }
  · intro x _ y _
    have heq : fderiv ℝ (Function.uncurry (Composite.objective hnp)) (x, y) =
        Model.jointGradientCLM (Regularity.gradientX hnp x y)
          (Regularity.gradientY hnp x y) := by
      apply ContinuousLinearMap.ext
      intro d
      exact hrep.2 x y d.1 d.2
    dsimp only [unscaled]
    rw [← heq]
    exact hrep.1.differentiableAt.hasFDerivAt.hasFDerivWithinAt
  · intro x _ y _ x' _ y' _
    exact Regularity.gradients_jointlySmooth hn x y x' y'
  · intro x _
    exact (Regularity.objective_dual_concave hnp x).subset
      (Set.subset_univ _) (diameterBall_convex (m * n) D)
  · intro y hy y' hy'
    exact diameterBall_vecSq_sub_le hD.le hy hy'
  · intro x _
    change Composite.value hnp D 0 - Composite.value hnp D x ≤ _
    rw [Composite.value_origin]
    linarith [Composite.value_lower (m := m) hn hD.le x]

/-- The globally smooth hard instance also belongs to the legacy analytic
class used by the generic lower-oracle framework. This is proved only for
the explicit construction, not asserted for every WithinClass instance. -/
theorem analyticClass {m n : ℕ} (hm : 0 < m) (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 < D) :
    IsNCCClass Regularity.ell₀ D (Composite.c_Δ * (m : ℝ))
      (unscaled (m := m) (by omega : 0 < n) D) := by
  have h := withinClass hm hn hD
  refine {
    ell_pos := h.ell_pos
    D_pos := h.D_pos
    Delta_pos := h.Delta_pos
    x0_mem := Set.mem_univ _
    X_nonempty := Set.univ_nonempty
    X_closed := h.X_closed
    X_convex := h.X_convex
    Y_nonempty := ⟨0, h.dual_origin⟩
    Y_closed := h.Y_closed
    Y_convex := h.Y_convex
    gradient_representation := Regularity.gradient_represents_fderiv (by omega)
    jointly_smooth := h.jointly_smooth
    dual_concave := h.dual_concave
    maximum_attained := ?_
    value_bddBelow := h.value_bddBelow
    initial_gap := h.initial_gap
    dual_diameter := h.dual_diameter }
  intro x hx
  exact h.maximum_attained hx

end

end NCC.Lower.Membership
