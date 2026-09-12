import NCC.Extensions.NCSCMoreau
import NCCLowerBoundVerification.Upper.ClassOperator

/-!
# Exact intrinsic-curvature auxiliary objective for NC-SC

Adding the known dual quadratic gives a concave auxiliary objective.
The generic solver's regularization with `r=mu` removes exactly that
quadratic, recovering the original objective. A deliberately inflated
internal smoothness parameter leaves strict primal coercivity in every
pointwise conjugate, without any bounded dual diameter.
-/

namespace NCC.Extensions.NCSC

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open PointwiseConjugate

def internalSmoothness (ell mu : ℝ) : ℝ := 8 * (ell + mu)

def auxiliary {m n : ℕ} (P : NCCInstance m n) (mu : ℝ) : NCCInstance m n :=
  { P with
    f := fun x y => P.f x y + quadraticCorrection mu y
    gradY := fun x y => P.gradY x y + mu • y }

variable {m n : ℕ} {ell mu Delta : ℝ} {P : NCCInstance m n}

theorem internalSmoothness_pos (h : NCSCClass ell mu Delta P) :
    0 < internalSmoothness ell mu := by
  unfold internalSmoothness
  have := h.ell_pos
  have := h.mu_pos
  positivity

theorem intrinsic_parameter_le (h : NCSCClass ell mu Delta P) :
    mu ≤ internalSmoothness ell mu / 8 := by
  unfold internalSmoothness
  linarith [h.ell_pos]

theorem auxiliary_regularized_objective (P : NCCInstance m n) (mu : ℝ) :
    (fun x y => (auxiliary P mu).f x y - mu / 2 * vecSq y) = P.f := by
  funext x y
  simp [auxiliary, quadraticCorrection]

theorem auxiliary_regularized_value (P : NCCInstance m n) (mu : ℝ) :
    DualRegularizedValueOn P.Y (auxiliary P mu).f mu = ValueOn P.Y P.f := by
  unfold DualRegularizedValueOn
  rw [auxiliary_regularized_objective]

theorem auxiliary_representation (h : NCSCClass ell mu Delta P) :
    Model.RepresentsJointGradientWithin (auxiliary P mu) := by
  intro x hx y hy
  have hquad := (Model.hasFDerivAt_quadraticCorrection mu y).comp (x, y)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y)))
  convert! (h.gradient_representation x hx y hy).add hquad.hasFDerivWithinAt using 1
  apply ContinuousLinearMap.ext
  intro d
  rcases d with ⟨dx, dy⟩
  simp [auxiliary, Model.jointGradientCLM, residualCLM_apply, eDot,
    add_mul, Finset.sum_add_distrib, add_assoc]

theorem auxiliary_smooth (h : NCSCClass ell mu Delta P) :
    Model.JointlySmoothWithin (internalSmoothness ell mu) (auxiliary P mu) := by
  intro x hx y hy u hu v hv
  have hs := h.jointly_smooth x hx y hy u hu v hv
  let gx := P.gradX x y - P.gradX u v
  let gy := P.gradY x y - P.gradY u v
  let dx := x - u
  let dy := y - v
  have hyadd := ScaledOperator.vecSq_add_le_two gy (mu • dy)
  rw [vecSq_smul] at hyadd
  have hxe : 0 ≤ vecSq gx := vecSq_nonneg _
  have hde : 0 ≤ vecSq dx := vecSq_nonneg _
  have hdy : 0 ≤ vecSq dy := vecSq_nonneg _
  have hform : (P.gradY x y + mu • y) - (P.gradY u v + mu • v) = gy + mu • dy := by
    dsimp [gy, dy]
    module
  change vecSq gx + vecSq ((P.gradY x y + mu • y) - (P.gradY u v + mu • v)) ≤ _
  rw [hform]
  change vecSq gx + vecSq (gy + mu • dy) ≤
    internalSmoothness ell mu ^ 2 * (vecSq dx + vecSq dy)
  have hs' : vecSq gx + vecSq gy ≤ ell ^ 2 * (vecSq dx + vecSq dy) := hs
  have hcoef : 2 * ell ^ 2 + 2 * mu ^ 2 ≤ internalSmoothness ell mu ^ 2 := by
    unfold internalSmoothness
    nlinarith [h.ell_pos, h.mu_pos]
  have hm := mul_le_mul_of_nonneg_right hcoef (add_nonneg hde hdy)
  have hn := mul_nonneg (sq_nonneg mu) hde
  nlinarith

theorem auxiliary_dual_concave (h : NCSCClass ell mu Delta P)
    {x : EVec m} (hx : x ∈ P.X) : ConcaveOn ℝ P.Y ((auxiliary P mu).f x) :=
  h.dual_stronglyConcave x hx

theorem primal_support_at_origin (h : NCSCClass ell mu Delta P)
    {x : EVec m} (hx : x ∈ P.X) {y : EVec n} (hy : y ∈ P.Y) :
    P.f 0 y + dot (P.gradX 0 y) x ≤ P.f x y + ell / 2 * vecSq x := by
  have hc := Model.section_weaklyConvex_of_within h.ell_pos h.X_convex
    h.gradient_representation h.jointly_smooth hy
  have hs := Model.convex_support_of_within hc h.primal_origin hx
    (Model.hasFDerivWithinAt_shiftedSection h.gradient_representation ell h.primal_origin hy)
  simpa [quadraticCorrection, residualCLM_apply, eDot, dot, vecSq, NCPLVerification.vecSq] using hs

theorem dot_le_quadratic {d : ℕ} {a : ℝ} (ha : 0 < a) (g x : EVec d) :
    dot g x ≤ (1 / a) * vecSq g + a / 4 * vecSq x := by
  have hy := TrackingAnalytic.two_dot_le_sq_add_sq g ((a / 2) • x)
  rw [vecSq_smul, dot_comm g, dot_smul_left, dot_comm x] at hy
  apply (mul_le_mul_iff_right₀ ha).1
  calc
    a * dot g x ≤ vecSq g + a ^ 2 / 4 * vecSq x := by nlinarith
    _ = _ := by field_simp [ha.ne']

/-- Every pointwise conjugate used by the solver is genuinely finite.
The bound may depend on the fixed dual argument; no diameter is used. -/
theorem auxiliary_gamma_bounded (h : NCSCClass ell mu Delta P) (z : EVec m) :
    GammaBddAbove P.X P.Y
      (decurved (auxiliary P mu).f (internalSmoothness ell mu) mu z) := by
  intro q y
  let a : EVec m := q + (2 * internalSmoothness ell mu) • z - P.gradX 0 y.1
  refine ⟨(1 / ell) * vecSq a - P.f 0 y.1 - quadraticCorrection mu y.1 -
    internalSmoothness ell mu * vecSq z, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hs := primal_support_at_origin h hx y.2
  have hy := dot_le_quadratic h.ell_pos a x
  have hL : 2 * ell ≤ internalSmoothness ell mu := by
    unfold internalSmoothness
    linarith [h.ell_pos, h.mu_pos]
  have hLs := mul_le_mul_of_nonneg_right hL (vecSq_nonneg x)
  have hd : dot a x = dot q x + 2 * internalSmoothness ell mu * dot z x -
      dot (P.gradX 0 y.1) x := by
    simp only [a, dot_sub_left, dot_add_left, dot_smul_left]
  rw [hd] at hy
  change dot q x - decurved (auxiliary P mu).f (internalSmoothness ell mu) mu z x y.1 ≤ _
  rw [decurved_eq]
  change dot q x - ((P.f x y.1 + quadraticCorrection mu y.1) +
    internalSmoothness ell mu / 2 * vecSq x -
    2 * internalSmoothness ell mu * dot z x + internalSmoothness ell mu * vecSq z) ≤ _
  nlinarith [h.ell_pos, vecSq_nonneg x]

end

end NCC.Extensions.NCSC
