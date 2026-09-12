import NCC.Model.FeasibleClass

/-!
# First-order support on the closed feasible domains

These inequalities use only the prescribed derivatives within the feasible
product. They also hold on lower-dimensional domains: no ambient extension
or unique normal component of the gradient is required.
-/

namespace NCC.Model

noncomputable section

open Set NCCLowerBoundVerification NCCLowerBoundVerification.Upper

section Support

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The first-order supporting inequality uses a derivative within the
convex domain, including at its boundary. -/
theorem convex_support_of_within {S : Set E} {f : E → ℝ}
    (hconv : ConvexOn ℝ S f) {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    {F : E →L[ℝ] ℝ} (hF : HasFDerivWithinAt f F S x) :
    f x + F (y - x) ≤ f y := by
  let path : ℝ → E := fun t ↦ t • (y - x) + x
  have hmem : MapsTo path (Icc (0 : ℝ) 1) S := by
    intro t ht
    have heq : path t = (1 - t) • x + t • y := by dsimp [path]; module
    rw [heq]
    exact hconv.1 hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hcurve : ConvexOn ℝ (Icc (0 : ℝ) 1) (f ∘ path) := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro s hs t ht a b ha hb hab
    have hc := hconv.2 (hmem hs) (hmem ht) ha hb hab
    have heq : a • path s + b • path t = path (a * s + b * t) := by
      dsimp [path]
      have ha' : a = 1 - b := by linarith
      rw [ha']
      module
    simpa only [Function.comp_apply, smul_eq_mul, heq] using hc
  have hp : HasDerivAt path (y - x) 0 := by
    simpa [path] using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).add_const x
  have hx0 : path 0 = x := by simp [path]
  have hder : HasDerivWithinAt (f ∘ path) (F (y - x)) (Icc (0 : ℝ) 1) 0 := by
    have hf0 : HasFDerivWithinAt f F S (path 0) := hx0.symm ▸ hF
    exact hf0.comp_hasDerivWithinAt 0 hp.hasDerivWithinAt hmem
  have hslope := hcurve.le_slope_of_hasDerivWithinAt
    (show (0 : ℝ) ∈ Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Icc 0 1 by simp) zero_lt_one hder
  have hslope' : F (y - x) ≤ f y - f x := by
    simpa [slope, path] using hslope
  linarith

theorem concave_support_of_within {S : Set E} {f : E → ℝ}
    (hconc : ConcaveOn ℝ S f) {x y : E} (hx : x ∈ S) (hy : y ∈ S)
    {F : E →L[ℝ] ℝ} (hF : HasFDerivWithinAt f F S x) :
    f y ≤ f x + F (y - x) := by
  have h := convex_support_of_within hconc.neg hx hy hF.neg
  simp only [Pi.neg_apply, neg_apply] at h
  linarith

end Support

variable {m n : Nat} {ell D Delta : ℝ} {P : NCCInstance m n}

theorem WithinClass.X_nonempty (h : WithinClass ell D Delta P) : P.X.Nonempty :=
  ⟨0, h.primal_origin⟩

theorem WithinClass.Y_nonempty (h : WithinClass ell D Delta P) : P.Y.Nonempty :=
  ⟨0, h.dual_origin⟩

theorem WithinClass.x0_mem (h : WithinClass ell D Delta P) : P.x0 ∈ P.X := by
  rw [h.initialization]
  exact h.primal_origin

theorem hasFDerivWithinAt_dual_section
    (hrep : RepresentsJointGradientWithin P)
    {x : EVec m} (hx : x ∈ P.X) {y : EVec n} (hy : y ∈ P.Y) :
    HasFDerivWithinAt (P.f x) (residualCLM (P.gradY x y)) P.Y y := by
  have hinj := (hasFDerivAt_const (𝕜 := ℝ) x y).prodMk
    (hasFDerivAt_id (𝕜 := ℝ) y)
  have hcomp := (hrep x hx y hy).comp y hinj.hasFDerivWithinAt
    (show MapsTo (fun v : EVec n ↦ (x, v)) P.Y (P.X ×ˢ P.Y) from
      fun _ hv ↦ ⟨hx, hv⟩)
  convert! hcomp using 1
  ext d
  simp [jointGradientCLM, residualCLM_apply, eDot]

theorem WithinClass.shiftedSection_support (h : WithinClass ell D Delta P)
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

theorem WithinClass.dualSection_support (h : WithinClass ell D Delta P)
    {x : EVec m} (hx : x ∈ P.X) {y v : EVec n}
    (hy : y ∈ P.Y) (hv : v ∈ P.Y) :
    P.f x v ≤ P.f x y + ∑ j : Fin n, P.gradY x y j * (v j - y j) := by
  have hs := concave_support_of_within (h.dual_concave x hx) hy hv
    (hasFDerivWithinAt_dual_section h.gradient_representation hx hy)
  simpa [residualCLM_apply, eDot] using hs

end

end NCC.Model
