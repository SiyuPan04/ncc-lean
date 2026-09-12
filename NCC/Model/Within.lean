import NCC.Model.Class
import Mathlib.Analysis.Convex.Deriv

/-!
# Derivatives within a closed feasible domain

This module is independent of the neighborhood-extension interpretation in
`InClass`. A prescribed differential is required only within the feasible
set. No `UniqueDiffOn` assumption is made: lower-dimensional feasible sets
can have nonunique ambient normal components in their oracle gradients.
-/

namespace NCC.Model

noncomputable section

open Set
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper

/-- The Euclidean coordinate functional associated with a joint gradient. -/
def jointGradientCLM {m n : Nat} (gx : EVec m) (gy : EVec n) :
    (EVec m × EVec n) →L[ℝ] ℝ :=
  (residualCLM gx).comp (ContinuousLinearMap.fst ℝ (EVec m) (EVec n)) +
    (residualCLM gy).comp (ContinuousLinearMap.snd ℝ (EVec m) (EVec n))

theorem jointGradientCLM_apply {m n : Nat} (gx hx : EVec m) (gy hy : EVec n) :
    jointGradientCLM gx gy (hx, hy) =
      (∑ i : Fin m, gx i * hx i) + ∑ j : Fin n, gy j * hy j := rfl

/-- The feasible-domain derivative condition, stated without selecting
`fderivWithin`, which need not recover prescribed normal components. -/
def RepresentsJointGradientWithin {m n : Nat} (P : NCCInstance m n) : Prop :=
  ∀ x ∈ P.X, ∀ y ∈ P.Y,
    HasFDerivWithinAt (Function.uncurry P.f) (jointGradientCLM (P.gradX x y) (P.gradY x y))
      (P.X ×ˢ P.Y) (x, y)

theorem RepresentsJointGradientWithin.continuousOn {m n : Nat} {P : NCCInstance m n}
    (h : RepresentsJointGradientWithin P) :
    ContinuousOn (Function.uncurry P.f) (P.X ×ˢ P.Y) := by
  rintro ⟨x, y⟩ hxy
  exact (h x hxy.1 y hxy.2).continuousWithinAt

/-- Compact maximization is continuous on the primal feasible set; a global
continuous extension of the objective is unnecessary. -/
theorem value_continuousOn_of_joint_continuousOn {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ}
    (hY : IsCompact Y) (hf : ContinuousOn (Function.uncurry f) (X ×ˢ Y)) :
    ContinuousOn (ValueOn Y f) X := by
  letI : CompactSpace Y := isCompact_iff_compactSpace.mp hY
  have hrestricted : Continuous (fun p : X × Y ↦ f p.1.val p.2.val) := by
    exact hf.comp_continuous
      (continuous_subtype_val.comp continuous_fst |>.prodMk
        (continuous_subtype_val.comp continuous_snd))
      (fun p ↦ ⟨p.1.property, p.2.property⟩)
  have hs : Continuous (fun x : X ↦ sSup ((fun y : Y ↦ f x.val y.val) '' univ)) :=
    isCompact_univ.continuous_sSup hrestricted
  apply continuousOn_iff_continuous_restrict.mpr
  convert hs using 1
  funext x
  change sSup (f x.val '' Y) = sSup ((fun y : Y ↦ f x.val y.val) '' univ)
  congr 1
  ext a
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, mem_univ _, rfl⟩
  · rintro ⟨y, _, rfl⟩
    exact ⟨y.val, y.property, rfl⟩

/-- Existence of feasible dual maximizers needs only feasible continuity. -/
theorem maximum_attained_of_within {m n : Nat} {P : NCCInstance m n}
    (hrep : RepresentsJointGradientWithin P) (hY : IsCompact P.Y) (hYne : P.Y.Nonempty)
    {x : EVec m} (hx : x ∈ P.X) : ∃ y, IsMaximizerOn P.Y P.f x y := by
  have hsection : ContinuousOn (P.f x) P.Y :=
    hrep.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hy ↦ ⟨hx, hy⟩)
  obtain ⟨y, hy, hm⟩ := hY.exists_isMaxOn hYne hsection
  exact ⟨y, hy, fun _ hv ↦ hm hv⟩

/-- Every original Moreau proximal point exists under within-domain
derivatives, compactness, and the actual pointwise gap condition. -/
theorem prox_exists_of_within {m n : Nat} {P : NCCInstance m n} {ell Delta : ℝ}
    (hrep : RepresentsJointGradientWithin P) (hY : IsCompact P.Y)
    (hXclosed : IsClosed P.X) (hzero : (0 : EVec m) ∈ P.X) (hell : 0 < ell)
    (hgap : ∀ x ∈ P.X, ValueOn P.Y P.f 0 - ValueOn P.Y P.f x ≤ Delta) :
    HasProxEverywhere P.X (ValueOn P.Y P.f) ell := by
  apply hasProxEverywhere_of_continuousOn_bddBelow ⟨0, hzero⟩ hXclosed hell
    (value_continuousOn_of_joint_continuousOn hY hrep.continuousOn)
    (lower := ValueOn P.Y P.f 0 - Delta)
  intro x hx
  linarith [hgap x hx]

section MonotoneDifferential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A monotone prescribed differential within a convex set makes the
function convex. This does not assume a neighborhood derivative or that
the feasible set has nonempty interior. -/
theorem convexOn_of_monotone_within_derivative {S : Set E} {f : E → ℝ}
    {F : E → E →L[ℝ] ℝ} (hS : Convex ℝ S)
    (hF : ∀ x ∈ S, HasFDerivWithinAt f (F x) S x)
    (hmono : ∀ x ∈ S, ∀ z ∈ S, 0 ≤ (F x - F z) (x - z)) :
    ConvexOn ℝ S f := by
  refine ⟨hS, ?_⟩
  intro x hx z hz a b ha hb hab
  let path : ℝ → E := fun t ↦ t • (z - x) + x
  have hpath_mem : MapsTo path (Icc (0 : ℝ) 1) S := by
    intro t ht
    have heq : path t = (1 - t) • x + t • z := by dsimp [path]; module
    rw [heq]
    exact hS hx hz (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hpath_deriv (t : ℝ) : HasDerivAt path (z - x) t := by
    simpa [path] using ((hasDerivAt_id t).smul_const (z - x)).add_const x
  have hcurve (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt (f ∘ path) (F (path t) (z - x)) (Icc (0 : ℝ) 1) t :=
    (hF _ (hpath_mem ht)).comp_hasDerivWithinAt t
      (hpath_deriv t).hasDerivWithinAt hpath_mem
  have hinterior (t : ℝ) (ht : t ∈ interior (Icc (0 : ℝ) 1)) :
      HasDerivAt (f ∘ path) (F (path t) (z - x)) t :=
    (hcurve t (interior_subset ht)).hasDerivAt (mem_interior_iff_mem_nhds.mp ht)
  have hderiv_mono : MonotoneOn (deriv (f ∘ path)) (interior (Icc (0 : ℝ) 1)) := by
    intro s hs t ht hst
    rw [(hinterior s hs).deriv, (hinterior t ht).deriv]
    rcases hst.eq_or_lt with rfl | hst
    · exact le_rfl
    have hm := hmono _ (hpath_mem (interior_subset ht)) _ (hpath_mem (interior_subset hs))
    have heq : path t - path s = (t - s) • (z - x) := by dsimp [path]; module
    rw [heq, map_smul] at hm
    change 0 ≤ (t - s) * (F (path t) (z - x) - F (path s) (z - x)) at hm
    nlinarith
  have hc : ConvexOn ℝ (Icc (0 : ℝ) 1) (f ∘ path) :=
    hderiv_mono.convexOn_of_deriv (convex_Icc 0 1)
      (fun t ht ↦ (hcurve t ht).continuousWithinAt)
      (fun t ht ↦ (hinterior t ht).differentiableAt.differentiableWithinAt)
  have hj := hc.2 (show (0 : ℝ) ∈ Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Icc 0 1 by simp) ha hb hab
  have heq : path (a * 0 + b * 1) = a • x + b • z := by
    dsimp [path]
    have ha' : a = 1 - b := by linarith
    rw [ha']
    module
  simpa only [smul_eq_mul, Function.comp_apply, heq, path, zero_smul, zero_add,
    one_smul, sub_add_cancel] using hj

end MonotoneDifferential

end

end NCC.Model
