import NCCLowerBoundVerification.SmoothSectionWeakConvexity
import NCCLowerBoundVerification.Upper.ProxExistence
import NCCLowerBoundVerification.Upper.PerturbationBias

/-!
# Analytic interfaces derived from an `IsNCCClass` instance

This module closes the compactness, continuity, weak-convexity, and proximal
existence obligations used by the concrete upper trajectory.  In particular,
the Moreau proximal points are constructed from the actual class fields rather
than left as an independent assumption.
-/

namespace NCCLowerBoundVerification
namespace Upper

noncomputable section

theorem IsNCCClass.dual_isBounded {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P) :
    Bornology.IsBounded P.Y := by
  obtain ⟨y0, hy0⟩ := hP.Y_nonempty
  rw [Metric.isBounded_iff_subset_closedBall y0]
  refine ⟨D, ?_⟩
  intro y hy
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hnorm := norm_le_sqrt_vecSq (y - y0)
  have hsq := hP.dual_diameter y hy y0 hy0
  have hs0 := Real.sqrt_nonneg (vecSq (y - y0))
  have hs2 := Real.sq_sqrt (vecSq_nonneg (y - y0))
  have hsqrt : Real.sqrt (vecSq (y - y0)) ≤ D := by
    nlinarith [hP.D_pos]
  exact hnorm.trans hsqrt

theorem IsNCCClass.dual_isCompact {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P) :
    IsCompact P.Y :=
  Metric.isCompact_of_isClosed_isBounded hP.Y_closed (dual_isBounded hP)

theorem IsNCCClass.value_continuous {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P) :
    Continuous (ValueOn P.Y P.f) := by
  unfold ValueOn
  exact (dual_isCompact hP).continuous_sSup
    hP.gradient_representation.1.continuous

theorem IsNCCClass.exists_value_lower_bound {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) :
    ∃ lower : ℝ, ∀ x ∈ P.X, lower ≤ ValueOn P.Y P.f x := by
  obtain ⟨lower, hlower⟩ := hP.value_bddBelow
  refine ⟨lower, ?_⟩
  intro x hx
  exact hlower ⟨x, hx, rfl⟩

/-- The original value's proximal minimizer exists at every anchor. -/
theorem IsNCCClass.value_hasProxEverywhere {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) :
    HasProxEverywhere P.X (ValueOn P.Y P.f) ell := by
  obtain ⟨lower, hlower⟩ := exists_value_lower_bound hP
  exact hasProxEverywhere_of_continuousOn_bddBelow
    hP.X_nonempty hP.X_closed hP.ell_pos
    (value_continuous hP).continuousOn hlower

private theorem regularized_uncurry_continuous {m n : Nat}
    {f : EVec m → EVec n → ℝ} {r : ℝ}
    (hf : Continuous (Function.uncurry f)) :
    Continuous (Function.uncurry
      (fun x y => f x y - r / 2 * vecSq y)) := by
  have hquad : Continuous (fun p : EVec m × EVec n => r / 2 * vecSq p.2) :=
    continuous_const.mul (continuous_vecSq.comp continuous_snd)
  change Continuous
    (Function.uncurry f - fun p : EVec m × EVec n => r / 2 * vecSq p.2)
  exact hf.sub hquad

theorem IsNCCClass.regularized_maximum_attained {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) :
    ∀ x, ∃ y, IsMaximizerOn P.Y
      (fun u v => P.f u v - r / 2 * vecSq v) x y := by
  intro x
  let fR := fun u v => P.f u v - r / 2 * vecSq v
  have hjoint : Continuous (Function.uncurry fR) :=
    regularized_uncurry_continuous hP.gradient_representation.1.continuous
  have hsection : Continuous (fR x) :=
    hjoint.comp (continuous_const.prodMk continuous_id)
  obtain ⟨y, hy, hmax⟩ := (dual_isCompact hP).exists_isMaxOn
    hP.Y_nonempty hsection.continuousOn
  exact ⟨y, hy, fun v hv => hmax hv⟩

/-- Compactness of the dual domain and the fixed global differentiable
extension give attainment even at anchors outside `X`.  This is the uniform
form needed by the perturbation comparison between two selected prox points. -/
theorem IsNCCClass.maximum_attained_everywhere {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) :
    ∀ x, ∃ y, IsMaximizerOn P.Y P.f x y := by
  intro x
  have hjoint : Continuous (Function.uncurry P.f) :=
    hP.gradient_representation.1.continuous
  have hsection : Continuous (P.f x) :=
    hjoint.comp (continuous_const.prodMk continuous_id)
  obtain ⟨y, hy, hmax⟩ := (dual_isCompact hP).exists_isMaxOn
    hP.Y_nonempty hsection.continuousOn
  exact ⟨y, hy, fun v hv => hmax hv⟩

theorem IsNCCClass.regularizedValue_continuous {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) :
    Continuous (DualRegularizedValueOn P.Y P.f r) := by
  unfold DualRegularizedValueOn ValueOn
  exact (dual_isCompact hP).continuous_sSup
    (regularized_uncurry_continuous hP.gradient_representation.1.continuous)

/-- With the paper's dual-origin normalization, diameter control becomes the
uniform squared-radius bound used by the perturbation argument. -/
theorem IsNCCClass.dual_vecSq_le {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) :
    ∀ y ∈ P.Y, vecSq y ≤ D ^ 2 := by
  intro y hy
  simpa only [sub_zero] using hP.dual_diameter y hy 0 hzero

private theorem regularized_section_weak {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) {y : EVec n} (hy : y ∈ P.Y) :
    IsWeaklyConvexOn ell P.X
      (fun x => P.f x y - r / 2 * vecSq y) := by
  have hbase := hP.section_weakConvexity hy
  unfold IsWeaklyConvexOn at hbase ⊢
  unfold quadraticCorrection
  refine ⟨hbase.1, ?_⟩
  intro x hx z hz a b ha hb hab
  have h := hbase.2 hx hz ha hb hab
  simp only [smul_eq_mul] at h ⊢
  let c : ℝ := r / 2 * vecSq y
  calc
    P.f (a • x + b • z) y - c + ell / 2 * vecSq (a • x + b • z) =
        (P.f (a • x + b • z) y +
          ell / 2 * vecSq (a • x + b • z)) - c := by ring
    _ ≤ (a * (P.f x y + ell / 2 * vecSq x) +
          b * (P.f z y + ell / 2 * vecSq z)) - c :=
      sub_le_sub_right h c
    _ = (a * (P.f x y + ell / 2 * vecSq x) +
          b * (P.f z y + ell / 2 * vecSq z)) - (a + b) * c := by
      rw [hab]
      ring
    _ = a * (P.f x y - c + ell / 2 * vecSq x) +
        b * (P.f z y - c + ell / 2 * vecSq z) := by
      ring

theorem IsNCCClass.regularizedValue_weaklyConvex {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) :
    IsWeaklyConvexOn ell P.X (DualRegularizedValueOn P.Y P.f r) := by
  unfold DualRegularizedValueOn
  exact value_weaklyConvexOn_of_sections hP.X_convex
    (fun x _hx => regularized_maximum_attained hP x)
    (fun y hy => regularized_section_weak hP hy)

/-- The regularized value is lower bounded by the original value lower bound
minus the uniform dual quadratic bias. -/
theorem IsNCCClass.exists_regularizedValue_lower_bound {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    (hr : 0 ≤ r) :
    ∃ lowerR : ℝ,
      ∀ x ∈ P.X, lowerR ≤ DualRegularizedValueOn P.Y P.f r x := by
  obtain ⟨lower, hlower⟩ := exists_value_lower_bound hP
  refine ⟨lower - r / 2 * D ^ 2, ?_⟩
  intro x hx
  have hbias := dualRegularizedValue_bias hr (dual_vecSq_le hP hzero)
    (hP.maximum_attained x hx) (regularized_maximum_attained hP x)
  linarith [hlower x hx]

/-- The regularized value's proximal point is likewise an actual consequence
of the class assumptions and dual-origin normalization. -/
theorem IsNCCClass.regularizedValue_hasProxEverywhere {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    (hr : 0 ≤ r) :
    HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell := by
  obtain ⟨lowerR, hlowerR⟩ :=
    exists_regularizedValue_lower_bound hP hzero hr
  exact hasProxEverywhere_of_continuousOn_bddBelow
    hP.X_nonempty hP.X_closed hP.ell_pos
    (regularizedValue_continuous hP).continuousOn hlowerR

end

end Upper
end NCCLowerBoundVerification
