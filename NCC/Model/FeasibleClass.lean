import NCC.Model.WithinConvexity

/-!
# The current class under feasible-domain differentiation

`WithinClass` keeps the manuscript's positive parameters, domains, prescribed
oracle gradients, Euclidean smoothness, dual concavity, diameter, and initial
gap. Differentiation on the closed feasible product means precisely
`RepresentsJointGradientWithin`: no neighborhood extension or behavior outside
the product is required. The prescribed gradient need not be the unique ambient
differential of a lower-dimensional domain.

This is an explicit boundary-differentiation convention. This file does not
assert equivalence to a neighborhood convention or provide a globalization.
The coordinate model admits zero dimensions; a dimension-indexed manuscript
class can separately impose its positive-dimension restrictions.
-/

namespace NCC.Model

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper

structure WithinClass {m n : Nat} (ell D Delta : ℝ)
    (P : NCCInstance m n) : Prop where
  ell_pos : 0 < ell
  D_pos : 0 < D
  Delta_pos : 0 < Delta
  primal_origin : (0 : EVec m) ∈ P.X
  dual_origin : (0 : EVec n) ∈ P.Y
  initialization : P.x0 = 0
  X_closed : IsClosed P.X
  X_convex : Convex ℝ P.X
  Y_closed : IsClosed P.Y
  Y_convex : Convex ℝ P.Y
  gradient_representation : RepresentsJointGradientWithin P
  jointly_smooth : JointlySmoothWithin ell P
  dual_concave : ∀ x ∈ P.X, ConcaveOn ℝ P.Y (P.f x)
  dual_diameter : ∀ y ∈ P.Y, ∀ y' ∈ P.Y, vecSq (y - y') ≤ D ^ 2
  initial_gap_pointwise : ∀ x ∈ P.X,
    ValueOn P.Y P.f 0 - ValueOn P.Y P.f x ≤ Delta

variable {m n : Nat} {ell D Delta : ℝ} {P : NCCInstance m n}

theorem WithinClass.dual_compact (h : WithinClass ell D Delta P) :
    IsCompact P.Y := by
  apply Metric.isCompact_of_isClosed_isBounded h.Y_closed
  rw [Metric.isBounded_iff_subset_closedBall (0 : EVec n)]
  refine ⟨D, ?_⟩
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  have hs : vecSq y ≤ D ^ 2 := by
    simpa only [sub_zero] using h.dual_diameter y hy 0 h.dual_origin
  have hnorm := norm_le_sqrt_vecSq y
  have hroot := Real.sq_sqrt (vecSq_nonneg y)
  have hnonneg := Real.sqrt_nonneg (vecSq y)
  have hD := h.D_pos
  nlinarith

theorem WithinClass.maximum_attained (h : WithinClass ell D Delta P)
    {x : EVec m} (hx : x ∈ P.X) :
    ∃ y, IsMaximizerOn P.Y P.f x y :=
  maximum_attained_of_within h.gradient_representation h.dual_compact
    ⟨0, h.dual_origin⟩ hx

theorem WithinClass.value_continuousOn (h : WithinClass ell D Delta P) :
    ContinuousOn (ValueOn P.Y P.f) P.X :=
  value_continuousOn_of_joint_continuousOn h.dual_compact
    h.gradient_representation.continuousOn

theorem WithinClass.value_bddBelow (h : WithinClass ell D Delta P) :
    BddBelow (ValueOn P.Y P.f '' P.X) := by
  refine ⟨ValueOn P.Y P.f 0 - Delta, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  linarith [h.initial_gap_pointwise x hx]

theorem WithinClass.initial_gap (h : WithinClass ell D Delta P) :
    ValueOn P.Y P.f 0 - sInf (ValueOn P.Y P.f '' P.X) ≤ Delta := by
  have hne : (ValueOn P.Y P.f '' P.X).Nonempty :=
    ⟨ValueOn P.Y P.f 0, 0, h.primal_origin, rfl⟩
  have hlower : ValueOn P.Y P.f 0 - Delta ≤
      sInf (ValueOn P.Y P.f '' P.X) := by
    apply le_csInf hne
    rintro _ ⟨x, hx, rfl⟩
    linarith [h.initial_gap_pointwise x hx]
  linarith

theorem WithinClass.value_weaklyConvex (h : WithinClass ell D Delta P) :
    IsWeaklyConvexOn ell P.X (ValueOn P.Y P.f) :=
  value_weaklyConvex_of_within h.ell_pos h.X_convex h.gradient_representation
    h.jointly_smooth h.dual_compact ⟨0, h.dual_origin⟩

theorem WithinClass.prox_exists (h : WithinClass ell D Delta P) :
    HasProxEverywhere P.X (ValueOn P.Y P.f) ell :=
  prox_exists_of_within h.gradient_representation h.dual_compact h.X_closed
    h.primal_origin h.ell_pos h.initial_gap_pointwise

theorem WithinClass.prox_existsUnique (h : WithinClass ell D Delta P) (z : EVec m) :
    ∃! u, IsProxPoint P.X (ValueOn P.Y P.f) ell z u :=
  existsUnique_prox_of_within h.ell_pos h.X_convex h.X_closed h.primal_origin
    h.gradient_representation h.jointly_smooth h.dual_compact ⟨0, h.dual_origin⟩
    h.initial_gap_pointwise z

end

end NCC.Model
