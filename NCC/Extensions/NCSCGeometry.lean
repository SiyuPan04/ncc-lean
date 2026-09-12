import NCC.Extensions.NCSCAuxiliary

/-!
# Solver geometry without a dual-diameter hypothesis

This bounded interface isolates the actual derivative, support, attainment,
and pointwise-conjugate facts needed by the generic VI/FOAM assembly. Its
current NC-SC instantiation is proved from `NCSCClass` below. It is not an
unproved hard-instance or algorithm certificate.
-/

namespace NCC.Extensions.NCSCGeometry

noncomputable section

set_option maxHeartbeats 3000000

open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper

structure CoreClass {m n : ℕ} (ell r : ℝ) (P : NCCInstance m n) : Prop where
  ell_pos : 0 < ell
  X_nonempty : P.X.Nonempty
  Y_nonempty : P.Y.Nonempty
  X_closed : IsClosed P.X
  X_convex : Convex ℝ P.X
  Y_closed : IsClosed P.Y
  Y_convex : Convex ℝ P.Y
  gradient_representation : RepresentsJointGradientWithin P
  jointly_smooth : JointlySmoothWithin ell P
  dual_concave : ∀ x ∈ P.X, ConcaveOn ℝ P.Y (P.f x)
  gamma_bounded : ∀ z, PointwiseConjugate.GammaBddAbove P.X P.Y
    (PointwiseConjugate.decurved P.f ell r z)
  regularized_maximum_attained : ∀ x ∈ P.X,
    ∃ y, IsMaximizerOn P.Y (fun u v => P.f u v - r / 2 * vecSq v) x y

variable {m n : ℕ} {ell r : ℝ} {P : NCCInstance m n}

theorem CoreClass.shiftedSection_support (h : CoreClass ell r P)
    {x z : EVec m} (hx : x ∈ P.X) (hz : z ∈ P.X)
    {y : EVec n} (hy : y ∈ P.Y) :
    P.f x y + ell / 2 * vecSq x +
      (∑ i : Fin m, (P.gradX x y i + ell * x i) * (z i - x i)) ≤
      P.f z y + ell / 2 * vecSq z := by
  have hc := section_weaklyConvex_of_within h.ell_pos h.X_convex
    h.gradient_representation h.jointly_smooth hy
  have hs := convex_support_of_within hc hx hz
    (hasFDerivWithinAt_shiftedSection h.gradient_representation ell hx hy)
  simpa [quadraticCorrection, residualCLM_apply, eDot] using hs

theorem CoreClass.dualSection_support (h : CoreClass ell r P)
    {x : EVec m} (hx : x ∈ P.X) {y v : EVec n} (hy : y ∈ P.Y) (hv : v ∈ P.Y) :
    P.f x v ≤ P.f x y + ∑ j : Fin n, P.gradY x y j * (v j - y j) := by
  have hs := concave_support_of_within (h.dual_concave x hx) hy hv
    (hasFDerivWithinAt_dual_section h.gradient_representation hx hy)
  simpa [residualCLM_apply, eDot] using hs

theorem CoreClass.regularizedValue_weaklyConvex (h : CoreClass ell r P) :
    IsWeaklyConvexOn ell P.X (DualRegularizedValueOn P.Y P.f r) := by
  apply value_weaklyConvexOn_of_sections h.X_convex h.regularized_maximum_attained
  intro y hy
  have hc := (section_weaklyConvex_of_within h.ell_pos h.X_convex
    h.gradient_representation h.jointly_smooth hy).add_const (-(r / 2 * vecSq y))
  apply hc.congr
  intro x _
  change (P.f x y + quadraticCorrection ell x) + (-(r / 2 * vecSq y)) =
    P.f x y - r / 2 * vecSq y + quadraticCorrection ell x
  ring

theorem ofNCSC {ell mu Delta : ℝ} {P : NCCInstance m n} (h : NCSC.NCSCClass ell mu Delta P) :
    CoreClass (NCSC.internalSmoothness ell mu) mu (NCSC.auxiliary P mu) where
  ell_pos := NCSC.internalSmoothness_pos h
  X_nonempty := ⟨0, h.primal_origin⟩
  Y_nonempty := ⟨0, h.dual_origin⟩
  X_closed := h.X_closed
  X_convex := h.X_convex
  Y_closed := h.Y_closed
  Y_convex := h.Y_convex
  gradient_representation := NCSC.auxiliary_representation h
  jointly_smooth := NCSC.auxiliary_smooth h
  dual_concave := by
    intro x hx
    exact NCSC.auxiliary_dual_concave (x := x) h hx
  gamma_bounded := by
    intro z
    exact NCSC.auxiliary_gamma_bounded h z
  regularized_maximum_attained := by
    intro x hx
    rw [NCSC.auxiliary_regularized_objective]
    exact NCSC.maximum_attained h hx

end

end NCC.Extensions.NCSCGeometry
