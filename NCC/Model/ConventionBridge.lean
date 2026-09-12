import NCC.Model.FeasibleClass
import NCC.Moreau.Analytic
import NCC.Moreau.Within

/-!
# Compatibility of the two derivative conventions

A neighborhood derivative restricts to a derivative within the feasible
domain. The converse is not assumed. On a class member satisfying the
stronger convention, both analyses define the same prox, envelope and
gradient. Thus the direct within-domain development changes assumptions,
not the meaning of optimization stationarity.
-/

namespace NCC.Model

noncomputable section

open NCCLowerBoundVerification

variable {m n : Nat} {ell D Delta : ℝ} {P : NCCInstance m n}

theorem representsJointGradientWithin_of_near (h : RepresentsJointGradientNear P) :
    RepresentsJointGradientWithin P := by
  obtain ⟨U, hU, hXY, hC1, hgrad⟩ := h
  intro x hx y hy
  have hxy : (x, y) ∈ U := hXY ⟨hx, hy⟩
  have hd : DifferentiableAt ℝ (Function.uncurry P.f) (x, y) :=
    (hC1.differentiableOn (by norm_num) _ hxy).differentiableAt (hU.mem_nhds hxy)
  have heq : fderiv ℝ (Function.uncurry P.f) (x, y) =
      jointGradientCLM (P.gradX x y) (P.gradY x y) := by
    apply ContinuousLinearMap.ext
    intro d
    exact hgrad x hx y hy d.1 d.2
  rw [← heq]
  exact hd.hasFDerivAt.hasFDerivWithinAt

theorem InClass.toWithin (h : InClass ell D Delta P) : WithinClass ell D Delta P where
  ell_pos := h.ell_pos
  D_pos := h.D_pos
  Delta_pos := h.Delta_pos
  primal_origin := h.primal_origin
  dual_origin := h.dual_origin
  initialization := h.initialization
  X_closed := h.X_closed
  X_convex := h.X_convex
  Y_closed := h.Y_closed
  Y_convex := h.Y_convex
  gradient_representation := representsJointGradientWithin_of_near h.gradient_representation
  jointly_smooth := h.jointly_smooth
  dual_concave := h.dual_concave
  dual_diameter := h.dual_diameter
  initial_gap_pointwise := h.initial_gap_pointwise

theorem prox_conventions_eq (h : InClass ell D Delta P) :
    Moreau.prox h = Moreau.Within.prox h.toWithin := rfl

theorem envelope_conventions_eq (h : InClass ell D Delta P) :
    Moreau.envelope h = Moreau.Within.envelope h.toWithin := rfl

theorem gradient_conventions_eq (h : InClass ell D Delta P) :
    Moreau.gradient h = Moreau.Within.gradient h.toWithin := rfl

theorem os_conventions_iff (h : InClass ell D Delta P) (eps : ℝ) (z : EVec m) :
    Moreau.IsOS h eps z ↔ Moreau.Within.IsOS h.toWithin eps z := Iff.rfl

/-- A genuinely represented ambient gradient restricts to the feasible
domain. This direction adds no hypothesis about the values outside it. -/
theorem withinClass_of_analytic (h : IsNCCClass ell D Delta P)
    (hx0 : (0 : EVec m) ∈ P.X) (hy0 : (0 : EVec n) ∈ P.Y)
    (hinit : P.x0 = 0) : WithinClass ell D Delta P := by
  refine {
    ell_pos := h.ell_pos
    D_pos := h.D_pos
    Delta_pos := h.Delta_pos
    primal_origin := hx0
    dual_origin := hy0
    initialization := hinit
    X_closed := h.X_closed
    X_convex := h.X_convex
    Y_closed := h.Y_closed
    Y_convex := h.Y_convex
    gradient_representation := ?_
    jointly_smooth := h.jointly_smooth
    dual_concave := h.dual_concave
    dual_diameter := h.dual_diameter
    initial_gap_pointwise := ?_ }
  · intro x _ y _
    have heq : fderiv ℝ (Function.uncurry P.f) (x, y) =
        jointGradientCLM (P.gradX x y) (P.gradY x y) := by
      apply ContinuousLinearMap.ext
      intro d
      exact h.gradient_representation.2 x y d.1 d.2
    rw [← heq]
    exact h.gradient_representation.1.differentiableAt.hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    have hi := h.initial_gap
    rw [hinit] at hi
    have hl := csInf_le h.value_bddBelow (show ValueOn P.Y P.f x ∈ ValueOn P.Y P.f '' P.X
      from ⟨x, hx, rfl⟩)
    linarith

end

end NCC.Model
