import NCCLowerBoundVerification.PaperClass
import NCCLowerBoundVerification.Upper.ClassAnalytic

/-!
# Current function class, with derived attainment

The coordinates in `EVec` use the usual finite product topology. All squared
norms below are the Euclidean sum of squares `vecSq`, not the product norm.

On a closed feasible domain we explicitly choose the conventional ambient
interpretation of differentiation: a C¹ representative on an open
neighborhood, whose derivatives give the supplied oracle gradient. This
convention is recorded, not silently inferred from an undefined boundary
gradient. No global smoothness outside the feasible domain is assumed.

The initial gap is written pointwise. For a real-valued function on a
nonempty set this is equivalent to a finite infimum and the paper's gap
inequality; the two consequences are proved below. In particular, maximum
attainment and a finite lower bound are not independent class assumptions.
-/

namespace NCC.Model

noncomputable section

open NCCLowerBoundVerification

structure InClass {m n : Nat} (ell D Delta : ℝ)
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
  gradient_representation : RepresentsJointGradientNear P
  jointly_smooth : ∀ x ∈ P.X, ∀ y ∈ P.Y,
    ∀ x' ∈ P.X, ∀ y' ∈ P.Y,
      jointSq (P.gradX x y - P.gradX x' y')
          (P.gradY x y - P.gradY x' y') ≤
        ell ^ 2 * jointSq (x - x') (y - y')
  dual_concave : ∀ x ∈ P.X, ConcaveOn ℝ P.Y (P.f x)
  dual_diameter : ∀ y ∈ P.Y, ∀ y' ∈ P.Y,
    vecSq (y - y') ≤ D ^ 2
  initial_gap_pointwise : ∀ x ∈ P.X,
    ValueOn P.Y P.f 0 - ValueOn P.Y P.f x ≤ Delta

variable {m n : Nat} {ell D Delta : ℝ} {P : NCCInstance m n}

theorem InClass.dual_compact (h : InClass ell D Delta P) :
    IsCompact P.Y := by
  apply Metric.isCompact_of_isClosed_isBounded h.Y_closed
  rw [Metric.isBounded_iff_subset_closedBall (0 : EVec n)]
  refine ⟨D, ?_⟩
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  have hs : vecSq y ≤ D ^ 2 := by
    simpa only [sub_zero] using h.dual_diameter y hy 0 h.dual_origin
  have hnorm := Upper.norm_le_sqrt_vecSq y
  have hroot := Real.sq_sqrt (vecSq_nonneg y)
  have hnonneg := Real.sqrt_nonneg (vecSq y)
  have hD := h.D_pos
  nlinarith

theorem InClass.maximum_attained (h : InClass ell D Delta P)
    {x : EVec m} (hx : x ∈ P.X) :
    ∃ y, IsMaximizerOn P.Y P.f x y := by
  obtain ⟨U, _, hXY, hC1, _⟩ := h.gradient_representation
  have hsection : ContinuousOn (P.f x) P.Y := by
    exact hC1.continuousOn.comp
      (continuous_const.prodMk continuous_id).continuousOn
      (fun y hy => hXY ⟨hx, hy⟩)
  obtain ⟨y, hy, hmax⟩ := h.dual_compact.exists_isMaxOn
    ⟨0, h.dual_origin⟩ hsection
  exact ⟨y, hy, fun v hv => hmax hv⟩

theorem InClass.value_bddBelow (h : InClass ell D Delta P) :
    BddBelow (ValueOn P.Y P.f '' P.X) := by
  refine ⟨ValueOn P.Y P.f 0 - Delta, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  linarith [h.initial_gap_pointwise x hx]

theorem InClass.initial_gap (h : InClass ell D Delta P) :
    ValueOn P.Y P.f 0 - sInf (ValueOn P.Y P.f '' P.X) ≤ Delta := by
  have hne : (ValueOn P.Y P.f '' P.X).Nonempty :=
    ⟨ValueOn P.Y P.f 0, 0, h.primal_origin, rfl⟩
  have hlower : ValueOn P.Y P.f 0 - Delta ≤
      sInf (ValueOn P.Y P.f '' P.X) := by
    apply le_csInf hne
    rintro _ ⟨x, hx, rfl⟩
    linarith [h.initial_gap_pointwise x hx]
  linarith

theorem pointwise_gap_of_inf_gap
    (hbdd : BddBelow (ValueOn P.Y P.f '' P.X))
    (hgap : ValueOn P.Y P.f 0 - sInf (ValueOn P.Y P.f '' P.X) ≤ Delta) :
    ∀ x ∈ P.X, ValueOn P.Y P.f 0 - ValueOn P.Y P.f x ≤ Delta := by
  intro x hx
  have hi := csInf_le hbdd (show ValueOn P.Y P.f x ∈
    ValueOn P.Y P.f '' P.X from ⟨x, hx, rfl⟩)
  linarith

/-- All extra fields of the analytic backend follow from the current class. -/
theorem InClass.toPaperClass (h : InClass ell D Delta P) :
    IsPaperNCCClass ell D Delta P := by
  refine
    { ell_pos := h.ell_pos
      D_pos := h.D_pos
      Delta_pos := h.Delta_pos
      x0_mem := by rw [h.initialization]; exact h.primal_origin
      X_nonempty := ⟨0, h.primal_origin⟩
      X_closed := h.X_closed
      X_convex := h.X_convex
      Y_nonempty := ⟨0, h.dual_origin⟩
      Y_closed := h.Y_closed
      Y_convex := h.Y_convex
      gradient_representation := h.gradient_representation
      jointly_smooth := h.jointly_smooth
      dual_concave := h.dual_concave
      maximum_attained := fun _ hx => h.maximum_attained hx
      value_bddBelow := h.value_bddBelow
      initial_gap := ?_
      dual_diameter := h.dual_diameter }
  rw [h.initialization]
  exact h.initial_gap

/-- Globalization preserves every feasible oracle reply and every value on X. -/
theorem InClass.globalization (h : InClass ell D Delta P) :
    Nonempty (PaperGlobalization ell D Delta P) :=
  exists_paperGlobalization h.toPaperClass

end

end NCC.Model
