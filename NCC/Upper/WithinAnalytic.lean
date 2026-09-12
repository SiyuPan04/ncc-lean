import NCC.Model.WithinSupport
import NCC.Upper.WithinRegularization

/-! Feasible-domain analytic facts for the concrete upper system. -/

namespace NCC.Model

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper

variable {m n : Nat} {ell D Delta r : ℝ} {P : NCCInstance m n}

theorem WithinClass.dual_isCompact (h : WithinClass ell D Delta P) :
    IsCompact P.Y := h.dual_compact

theorem WithinClass.exists_value_lower_bound (h : WithinClass ell D Delta P) :
    ∃ lower : ℝ, ∀ x ∈ P.X, lower ≤ ValueOn P.Y P.f x := by
  refine ⟨ValueOn P.Y P.f 0 - Delta, ?_⟩
  intro x hx
  linarith [h.initial_gap_pointwise x hx]

theorem WithinClass.value_hasProxEverywhere (h : WithinClass ell D Delta P) :
    HasProxEverywhere P.X (ValueOn P.Y P.f) ell := h.prox_exists

theorem WithinClass.regularized_maximum_attained (h : WithinClass ell D Delta P)
    (x : EVec m) (hx : x ∈ P.X) :
    ∃ y, IsMaximizerOn P.Y (fun u v => P.f u v - r / 2 * vecSq v) x y :=
  NCC.Upper.WithinRegularization.maximum_attained h hx

theorem WithinClass.regularizedValue_continuousOn (h : WithinClass ell D Delta P) :
    ContinuousOn (DualRegularizedValueOn P.Y P.f r) P.X :=
  NCC.Upper.WithinRegularization.value_continuousOn h

theorem WithinClass.regularizedValue_weaklyConvex (h : WithinClass ell D Delta P) :
    IsWeaklyConvexOn ell P.X (DualRegularizedValueOn P.Y P.f r) :=
  NCC.Upper.WithinRegularization.value_weaklyConvex h

theorem WithinClass.dual_vecSq_le (h : WithinClass ell D Delta P)
    {y : EVec n} (hy : y ∈ P.Y) : vecSq y ≤ D ^ 2 := by
  simpa only [sub_zero] using h.dual_diameter y hy 0 h.dual_origin

theorem WithinClass.exists_regularizedValue_lower_bound (h : WithinClass ell D Delta P)
    (hr : 0 ≤ r) :
    ∃ lowerR : ℝ, ∀ x ∈ P.X, lowerR ≤ DualRegularizedValueOn P.Y P.f r x := by
  refine ⟨ValueOn P.Y P.f 0 - Delta - r / 2 * D ^ 2, ?_⟩
  intro x hx
  linarith [h.initial_gap_pointwise x hx,
    (NCC.Upper.WithinRegularization.value_bias h hr hx).2]

theorem WithinClass.regularizedValue_hasProxEverywhere (h : WithinClass ell D Delta P)
    (hr : 0 ≤ r) : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell :=
  NCC.Upper.WithinRegularization.prox_exists h hr

end

end NCC.Model
