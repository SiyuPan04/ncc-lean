import NCC.Model.Within

/-!
# Weak convexity from prescribed feasible-domain derivatives

The source convention here interprets a gradient on `X × Y` as a prescribed
`HasFDerivWithinAt` differential, as defined in `Within.lean`. This file
does not assume `InClass`, neighborhood C¹ regularity, an ambient derivative
outside the feasible set, `UniqueDiffOn`, or a nonempty ambient interior.
Every quantitative norm below is the Euclidean sum of squares `vecSq`.

The final value theorem is exactly the `IsWeaklyConvexOn` input expected by
the existing Moreau-envelope backend. Its value is the actual `ValueOn`
supremum, with maximum attainment proved from within-domain continuity.
-/

namespace NCC.Model

noncomputable section

open Set
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper

/-- The manuscript's joint smoothness condition on feasible pairs. -/
def JointlySmoothWithin {m n : Nat} (ell : ℝ) (P : NCCInstance m n) : Prop :=
  ∀ x ∈ P.X, ∀ y ∈ P.Y, ∀ x' ∈ P.X, ∀ y' ∈ P.Y,
    jointSq (P.gradX x y - P.gradX x' y') (P.gradY x y - P.gradY x' y') ≤
      ell ^ 2 * jointSq (x - x') (y - y')

theorem section_gradient_squared_le_of_within {m n : Nat} {P : NCCInstance m n}
    {ell : ℝ} (hsmooth : JointlySmoothWithin ell P)
    {x z : EVec m} (hx : x ∈ P.X) (hz : z ∈ P.X)
    {y : EVec n} (hy : y ∈ P.Y) :
    vecSq (P.gradX x y - P.gradX z y) ≤ ell ^ 2 * vecSq (x - z) := by
  have h := hsmooth x hx y hy z hz y hy
  have hdual := vecSq_nonneg (P.gradY x y - P.gradY z y)
  simp only [jointSq, sub_self] at h
  have hzv : vecSq (0 : EVec n) = 0 := by simp [vecSq, NCPLVerification.vecSq]
  rw [hzv, add_zero] at h
  linarith

/-- Restricting a represented joint derivative to a fixed feasible dual
point gives the prescribed primal differential within `X`. -/
theorem hasFDerivWithinAt_section {m n : Nat} {P : NCCInstance m n}
    (hrep : RepresentsJointGradientWithin P)
    {x : EVec m} (hx : x ∈ P.X) {y : EVec n} (hy : y ∈ P.Y) :
    HasFDerivWithinAt (fun u ↦ P.f u y) (residualCLM (P.gradX x y)) P.X x := by
  have hinj := (hasFDerivAt_id (𝕜 := ℝ) x).prodMk
    (hasFDerivAt_const (𝕜 := ℝ) y x)
  have hcomp := (hrep x hx y hy).comp x hinj.hasFDerivWithinAt
    (show MapsTo (fun u : EVec m ↦ (u, y)) P.X (P.X ×ˢ P.Y) from
      fun _ hu ↦ ⟨hu, hy⟩)
  convert! hcomp using 1
  ext d
  simp [jointGradientCLM, residualCLM_apply, eDot]

theorem hasFDerivAt_euclideanSquared {m : Nat} (x : EVec m) :
    HasFDerivAt (fun u : EVec m ↦ vecSq u) (residualCLM ((2 : ℝ) • x)) x := by
  have hcoord (i : Fin m) :
      HasFDerivAt (fun u : EVec m ↦ u i ^ 2)
        ((2 * x i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m ↦ ℝ) i) x := by
    simpa using (hasFDerivAt_apply (𝕜 := ℝ) i x).pow 2
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hcoord i)
  convert! hsum using 1
  ext d
  simp [residualCLM_apply, eDot, mul_assoc]

theorem hasFDerivAt_quadraticCorrection {m : Nat} (ell : ℝ) (x : EVec m) :
    HasFDerivAt (quadraticCorrection ell) (residualCLM (ell • x)) x := by
  convert! (hasFDerivAt_euclideanSquared x).const_mul (ell / 2) using 1
  ext d
  simp only [smul_apply, residualCLM_apply, eDot, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hasFDerivWithinAt_shiftedSection {m n : Nat} {P : NCCInstance m n}
    (hrep : RepresentsJointGradientWithin P) (ell : ℝ)
    {x : EVec m} (hx : x ∈ P.X) {y : EVec n} (hy : y ∈ P.Y) :
    HasFDerivWithinAt (fun u ↦ P.f u y + quadraticCorrection ell u)
      (residualCLM (P.gradX x y + ell • x)) P.X x := by
  convert! (hasFDerivWithinAt_section hrep hx hy).add
    (hasFDerivAt_quadraticCorrection ell x).hasFDerivWithinAt using 1
  ext d
  simp [residualCLM_apply, eDot, add_mul, Finset.sum_add_distrib]

private theorem euclideanSquared_add_smul {m : Nat} (g d : EVec m) (ell : ℝ) :
    vecSq (g + ell • d) = vecSq g + 2 * ell * eDot g d + ell ^ 2 * vecSq d := by
  unfold vecSq NCPLVerification.vecSq eDot
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quadratic correction makes the prescribed gradient monotone.
This is a Euclidean algebraic consequence of the squared Lipschitz bound. -/
theorem shifted_gradient_monotone_of_squared_bound {m : Nat} {ell : ℝ}
    (hell : 0 < ell) (g h x z : EVec m)
    (hbound : vecSq (g - h) ≤ ell ^ 2 * vecSq (x - z)) :
    0 ≤ (residualCLM (g + ell • x) - residualCLM (h + ell • z)) (x - z) := by
  have hsq := vecSq_nonneg ((g - h) + ell • (x - z))
  rw [euclideanSquared_add_smul] at hsq
  have hdot : -ell * vecSq (x - z) ≤ eDot (g - h) (x - z) := by nlinarith
  have heq : (residualCLM (g + ell • x) - residualCLM (h + ell • z)) (x - z) =
      eDot (g - h) (x - z) + ell * vecSq (x - z) := by
    simp only [sub_apply, residualCLM_apply, eDot,
      vecSq, NCPLVerification.vecSq, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq]
  linarith

/-- The exact weak-convexity modulus of every primal section follows from
within-domain differentiability and the manuscript's joint smoothness. -/
theorem section_weaklyConvex_of_within {m n : Nat} {P : NCCInstance m n} {ell : ℝ}
    (hell : 0 < ell) (hX : Convex ℝ P.X)
    (hrep : RepresentsJointGradientWithin P) (hsmooth : JointlySmoothWithin ell P)
    {y : EVec n} (hy : y ∈ P.Y) :
    IsWeaklyConvexOn ell P.X (fun x ↦ P.f x y) := by
  apply convexOn_of_monotone_within_derivative
    (F := fun x ↦ residualCLM (P.gradX x y + ell • x)) hX
  · intro x hx
    exact hasFDerivWithinAt_shiftedSection hrep ell hx hy
  · intro x hx z hz
    exact shifted_gradient_monotone_of_squared_bound hell _ _ x z
      (section_gradient_squared_le_of_within hsmooth hx hz hy)

/-- The actual compact-domain maximized value has the exact weak-convexity
modulus needed by the Moreau backend, without a neighborhood extension. -/
theorem value_weaklyConvex_of_within {m n : Nat} {P : NCCInstance m n} {ell : ℝ}
    (hell : 0 < ell) (hX : Convex ℝ P.X)
    (hrep : RepresentsJointGradientWithin P) (hsmooth : JointlySmoothWithin ell P)
    (hY : IsCompact P.Y) (hYne : P.Y.Nonempty) :
    IsWeaklyConvexOn ell P.X (ValueOn P.Y P.f) :=
  value_weaklyConvexOn_of_sections hX
    (fun _ hx ↦ maximum_attained_of_within hrep hY hYne hx)
    (fun _ hy ↦ section_weaklyConvex_of_within hell hX hrep hsmooth hy)

/-- Existence and uniqueness of all original proximal minimizers under the
feasible-domain interpretation, using the actual pointwise initial gap. -/
theorem existsUnique_prox_of_within {m n : Nat} {P : NCCInstance m n} {ell Delta : ℝ}
    (hell : 0 < ell) (hX : Convex ℝ P.X) (hXclosed : IsClosed P.X)
    (hzero : (0 : EVec m) ∈ P.X)
    (hrep : RepresentsJointGradientWithin P) (hsmooth : JointlySmoothWithin ell P)
    (hY : IsCompact P.Y) (hYne : P.Y.Nonempty)
    (hgap : ∀ x ∈ P.X, ValueOn P.Y P.f 0 - ValueOn P.Y P.f x ≤ Delta)
    (z : EVec m) : ∃! u, IsProxPoint P.X (ValueOn P.Y P.f) ell z u := by
  obtain ⟨u, hu⟩ := prox_exists_of_within hrep hY hXclosed hzero hell hgap z
  refine ⟨u, hu, ?_⟩
  intro v hv
  exact proxPoint_unique_of_weaklyConvexOn hell
    (value_weaklyConvex_of_within hell hX hrep hsmooth hY hYne) hv hu

end

end NCC.Model
