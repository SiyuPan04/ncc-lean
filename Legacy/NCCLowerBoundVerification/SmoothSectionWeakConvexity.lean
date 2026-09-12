import NCCLowerBoundVerification.Basic
import Mathlib.Analysis.Convex.Deriv

/-!
# Weak convexity inherited from joint smoothness

This module formalizes Lemma `lem:weak-convexity` of
`Upper+Lower_unified_lower.tex`.  First, every fixed-dual section becomes
convex after addition of `ell / 2 * ‖x‖₂²`.  Taking the attained pointwise
maximum then gives the identical weak-convexity modulus for the value
function.
-/

namespace NCCLowerBoundVerification

noncomputable section

private def eDot {m : Nat} (u v : EVec m) : ℝ :=
  ∑ i : Fin m, u i * v i

private def line (x d : EVec m) (t : ℝ) : EVec m :=
  t • d + x

private def shiftedSection {m n : Nat} (P : NCCInstance m n)
    (ell : ℝ) (y : EVec n) (x : EVec m) : ℝ :=
  P.f x y + ell / 2 * vecSq x

private def shiftedGrad {m n : Nat} (P : NCCInstance m n)
    (ell : ℝ) (y : EVec n) (x : EVec m) : EVec m :=
  P.gradX x y + ell • x

private theorem vecSq_nonneg {m : Nat} (u : EVec m) : 0 ≤ vecSq u := by
  unfold vecSq
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

private theorem eDot_add_left {m : Nat} (u v w : EVec m) :
    eDot (u + v) w = eDot u w + eDot v w := by
  simp [eDot, add_mul, Finset.sum_add_distrib]

private theorem eDot_sub_left {m : Nat} (u v w : EVec m) :
    eDot (u - v) w = eDot u w - eDot v w := by
  simp [eDot, sub_mul, Finset.sum_sub_distrib]

private theorem eDot_smul_right {m : Nat} (c : ℝ) (u v : EVec m) :
    eDot u (c • v) = c * eDot u v := by
  simp [eDot, Finset.mul_sum, mul_left_comm]

private theorem eDot_smul_left {m : Nat} (c : ℝ) (u v : EVec m) :
    eDot (c • u) v = c * eDot u v := by
  unfold eDot
  calc
    ∑ i : Fin m, (c • u) i * v i = ∑ i : Fin m, c * (u i * v i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = c * ∑ i : Fin m, u i * v i := by rw [Finset.mul_sum]

private theorem eDot_self {m : Nat} (u : EVec m) :
    eDot u u = vecSq u := by
  simp [eDot, vecSq, NCPLVerification.vecSq, pow_two]

private theorem vecSq_add_smul_expansion {m : Nat}
    (u v : EVec m) (c : ℝ) :
    vecSq (u + c • v) =
      vecSq u + 2 * c * eDot u v + c ^ 2 * vecSq v := by
  unfold vecSq NCPLVerification.vecSq eDot
  calc
    ∑ i : Fin m, (u + c • v) i ^ 2 =
        ∑ i : Fin m, (u i ^ 2 + 2 * c * (u i * v i) + c ^ 2 * v i ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
    _ = (∑ i : Fin m, u i ^ 2) +
          2 * c * (∑ i : Fin m, u i * v i) +
          c ^ 2 * (∑ i : Fin m, v i ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
            Finset.mul_sum, Finset.mul_sum]

private theorem line_sub_line {m : Nat} (x d : EVec m) (s t : ℝ) :
    line x d t - line x d s = (t - s) • d := by
  ext i
  simp [line]
  ring

private theorem line_mem_convex {m : Nat} {X : Set (EVec m)}
    (hX : Convex ℝ X) {x z : EVec m} (hx : x ∈ X) (hz : z ∈ X)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : line x (z - x) t ∈ X := by
  have hcombo : line x (z - x) t = (1 - t) • x + t • z := by
    ext i
    simp [line]
    ring
  rw [hcombo]
  exact hX hx hz (sub_nonneg.mpr ht.2) ht.1 (by ring)

/-- Fixed-dual primal gradients are `ell`-Lipschitz in squared Euclidean
norm, as a direct consequence of the joint smoothness inequality. -/
theorem IsNCCClass.sectionGradient_sq_le {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    {x z : EVec m} (hx : x ∈ P.X) (hz : z ∈ P.X)
    {y : EVec n} (hy : y ∈ P.Y) :
    vecSq (P.gradX x y - P.gradX z y) ≤ ell ^ 2 * vecSq (x - z) := by
  have h := hP.jointly_smooth x hx y hy z hz y hy
  have hdual : 0 ≤ vecSq (P.gradY x y - P.gradY z y) := vecSq_nonneg _
  simp only [jointSq, sub_self] at h
  have hzero : vecSq (0 : EVec n) = 0 := by
    simp [vecSq, NCPLVerification.vecSq]
  rw [hzero, add_zero] at h
  nlinarith

/-- The gradient of the quadratically shifted fixed-dual section is
monotone on the primal domain. -/
theorem IsNCCClass.shiftedSection_gradient_monotone {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P)
    {x z : EVec m} (hx : x ∈ P.X) (hz : z ∈ P.X)
    {y : EVec n} (hy : y ∈ P.Y) :
    0 ≤ eDot (shiftedGrad P ell y x - shiftedGrad P ell y z) (x - z) := by
  let gdiff := P.gradX x y - P.gradX z y
  let d := x - z
  have hg : vecSq gdiff ≤ ell ^ 2 * vecSq d :=
    hP.sectionGradient_sq_le hx hz hy
  have hsquare : 0 ≤ vecSq (gdiff + ell • d) := vecSq_nonneg _
  rw [vecSq_add_smul_expansion] at hsquare
  have hell : 0 < ell := hP.ell_pos
  have hdot : -ell * vecSq d ≤ eDot gdiff d := by
    nlinarith
  have hshift : shiftedGrad P ell y x - shiftedGrad P ell y z =
      gdiff + ell • d := by
    ext i
    simp [shiftedGrad, gdiff, d]
    ring
  rw [hshift, eDot_add_left]
  have hself : eDot (ell • d) d = ell * vecSq d := by
    unfold eDot vecSq NCPLVerification.vecSq
    calc
      ∑ i : Fin m, (ell • d) i * d i =
          ∑ i : Fin m, ell * (d i * d i) := by
            apply Finset.sum_congr rfl
            intro i _
            simp only [Pi.smul_apply, smul_eq_mul]
            ring
      _ = ell * ∑ i : Fin m, d i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  rw [hself]
  linarith

private theorem IsNCCClass.hasDerivAt_section_along_line {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (x d : EVec m) (y : EVec n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ P.f (line x d s) y)
      (eDot (P.gradX (line x d t) y) d) t := by
  let L : ℝ →L[ℝ] EVec m := (1 : ℝ →L[ℝ] ℝ).smulRight d
  have hxline : HasFDerivAt (line x d) L t := by
    simpa [line, L, ContinuousLinearMap.smulRight_apply] using
      L.hasFDerivAt.add_const x
  have hyconst : HasFDerivAt (fun _ : ℝ ↦ y) 0 t :=
    hasFDerivAt_const (𝕜 := ℝ) y t
  have hpath := hxline.prodMk hyconst
  have houter : HasFDerivAt (Function.uncurry P.f)
      (fderiv ℝ (Function.uncurry P.f) (line x d t, y)) (line x d t, y) :=
    hP.gradient_representation.1.differentiableAt.hasFDerivAt
  have hcomp := houter.comp t hpath
  have hderiv := hcomp.hasDerivAt
  apply hderiv.congr_deriv
  rw [ContinuousLinearMap.comp_apply]
  have hL : (L.prod (0 : ℝ →L[ℝ] EVec n)) 1 = (d, 0) := by
    ext i <;> simp [L, ContinuousLinearMap.smulRight_apply]
  rw [hL]
  rw [hP.gradient_representation.2]
  simp [eDot]

private theorem hasDerivAt_vecSq_line {m : Nat}
    (x d : EVec m) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ vecSq (line x d s))
      (2 * eDot (line x d t) d) t := by
  unfold vecSq NCPLVerification.vecSq
  have hsum : HasDerivAt
      (fun s : ℝ ↦ ∑ i : Fin m, (line x d s i) ^ 2)
      (∑ i : Fin m, 2 * line x d t i * d i) t := by
    apply HasDerivAt.fun_sum
    intro i _
    have hlin : HasDerivAt (fun s : ℝ ↦ s * d i + x i) (d i) t := by
      convert ((hasDerivAt_id t).mul_const (d i)).add_const (x i) using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      all_goals simp
    convert hlin.pow 2 using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    · funext s
      simp only [Pi.pow_apply]
      simp [line]
    · simp [line]
  apply hsum.congr_deriv
  unfold eDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem IsNCCClass.hasDerivAt_shiftedSection_along_line {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (x d : EVec m) (y : EVec n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ shiftedSection P ell y (line x d s))
      (eDot (shiftedGrad P ell y (line x d t)) d) t := by
  have hf := hP.hasDerivAt_section_along_line x d y t
  have hq0 := (hasDerivAt_vecSq_line x d t).const_mul (ell / 2)
  have hq : HasDerivAt (fun s : ℝ ↦ ell / 2 * vecSq (line x d s))
      (ell * eDot (line x d t) d) t := by
    exact hq0.congr_deriv (by ring)
  unfold shiftedSection shiftedGrad
  have h := hf.add hq
  apply h.congr_deriv
  rw [eDot_add_left, eDot_smul_left]

private theorem IsNCCClass.shiftedSection_line_derivative_monotone {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P)
    {x z : EVec m} (hx : x ∈ P.X) (hz : z ∈ P.X)
    {y : EVec n} (hy : y ∈ P.Y) :
    MonotoneOn
      (fun t : ℝ ↦ eDot (shiftedGrad P ell y (line x (z - x) t)) (z - x))
      (Set.Icc (0 : ℝ) 1) := by
  intro s hs t ht hst
  rcases hst.eq_or_lt with rfl | hst
  · exact le_rfl
  · have hxs : line x (z - x) s ∈ P.X :=
      line_mem_convex hP.X_convex hx hz hs
    have hxt : line x (z - x) t ∈ P.X :=
      line_mem_convex hP.X_convex hx hz ht
    have hmono := hP.shiftedSection_gradient_monotone hxt hxs hy
    rw [line_sub_line, eDot_smul_right, eDot_sub_left] at hmono
    nlinarith

private theorem IsNCCClass.shiftedSection_convexOn_segment {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P)
    {x z : EVec m} (hx : x ∈ P.X) (hz : z ∈ P.X)
    {y : EVec n} (hy : y ∈ P.Y) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t : ℝ ↦ shiftedSection P ell y (line x (z - x) t)) := by
  let q : ℝ → ℝ := fun t ↦ shiftedSection P ell y (line x (z - x) t)
  have hq (t : ℝ) : HasDerivAt q
      (eDot (shiftedGrad P ell y (line x (z - x) t)) (z - x)) t :=
    hP.hasDerivAt_shiftedSection_along_line x (z - x) y t
  have hdiff : Differentiable ℝ q := fun t ↦ (hq t).differentiableAt
  have hmono : MonotoneOn (deriv q) (Set.Icc (0 : ℝ) 1) := by
    intro s hs t ht hst
    rw [(hq s).deriv, (hq t).deriv]
    exact hP.shiftedSection_line_derivative_monotone hx hz hy hs ht hst
  exact (hmono.mono interior_subset).convexOn_of_deriv (convex_Icc 0 1)
    hdiff.continuous.continuousOn hdiff.differentiableOn

/-- For every fixed `y ∈ Y`, joint `ell`-smoothness makes
`x ↦ f x y + ell / 2 * ‖x‖₂²` convex on `X`. -/
theorem IsNCCClass.section_weakConvexity {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    {y : EVec n} (hy : y ∈ P.Y) :
    ConvexOn ℝ P.X (fun x ↦ P.f x y + ell / 2 * vecSq x) := by
  change ConvexOn ℝ P.X (shiftedSection P ell y)
  refine ⟨hP.X_convex, ?_⟩
  intro x hx z hz a b ha hb hab
  have hcurve := hP.shiftedSection_convexOn_segment hx hz hy
  have hc := hcurve.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp) ha hb hab
  simp only [smul_eq_mul, mul_zero, mul_one, zero_add] at hc
  have hline : line x (z - x) b = a • x + b • z := by
    have ha' : a = 1 - b := by linarith
    ext i
    simp [line]
    rw [ha']
    ring
  rw [hline] at hc
  simpa [line] using hc

private theorem IsNCCClass.section_le_value {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    {x : EVec m} (hx : x ∈ P.X) {y : EVec n} (hy : y ∈ P.Y) :
    P.f x y ≤ ValueOn P.Y P.f x := by
  obtain ⟨ymax, hymax⟩ := hP.maximum_attained x hx
  rw [value_eq_of_isMaximizerOn hymax]
  exact hymax.2 y hy

/-- Lemma `lem:weak-convexity`: the attained value function has exactly the
same weak-convexity modulus `ell` as every fixed-dual section.  Equivalently,
`ValueOn Y f + ell / 2 * ‖·‖₂²` is convex on `X`. -/
theorem IsNCCClass.value_weakConvexity {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P) :
    ConvexOn ℝ P.X
      (fun x ↦ ValueOn P.Y P.f x + ell / 2 * vecSq x) := by
  refine ⟨hP.X_convex, ?_⟩
  intro x hx z hz a b ha hb hab
  have hu : a • x + b • z ∈ P.X := hP.X_convex hx hz ha hb hab
  obtain ⟨y, hymax⟩ := hP.maximum_attained (a • x + b • z) hu
  have hjensen := (hP.section_weakConvexity hymax.1).2 hx hz ha hb hab
  have hxvalue : P.f x y + ell / 2 * vecSq x ≤
      ValueOn P.Y P.f x + ell / 2 * vecSq x :=
    by simpa [add_comm] using
      add_le_add_right (hP.section_le_value hx hymax.1) (ell / 2 * vecSq x)
  have hzvalue : P.f z y + ell / 2 * vecSq z ≤
      ValueOn P.Y P.f z + ell / 2 * vecSq z :=
    by simpa [add_comm] using
      add_le_add_right (hP.section_le_value hz hymax.1) (ell / 2 * vecSq z)
  change ValueOn P.Y P.f (a • x + b • z) + ell / 2 * vecSq (a • x + b • z) ≤
    a • (ValueOn P.Y P.f x + ell / 2 * vecSq x) +
      b • (ValueOn P.Y P.f z + ell / 2 * vecSq z)
  rw [value_eq_of_isMaximizerOn hymax]
  exact hjensen.trans (add_le_add
    (smul_le_smul_of_nonneg_left hxvalue ha)
    (smul_le_smul_of_nonneg_left hzvalue hb))

/-! ## First-order support inequalities used by the executable upper system -/

/-- The shifted primal section has its actual represented gradient as a
supporting hyperplane on the (possibly unbounded) primal domain. -/
theorem IsNCCClass.shiftedSection_support {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P)
    {x z : EVec m} (hx : x ∈ P.X) (hz : z ∈ P.X)
    {y : EVec n} (hy : y ∈ P.Y) :
    P.f x y + ell / 2 * vecSq x +
        (∑ i : Fin m, (P.gradX x y i + ell * x i) * (z i - x i)) ≤
      P.f z y + ell / 2 * vecSq z := by
  have hconv := hP.shiftedSection_convexOn_segment hx hz hy
  have hder := hP.hasDerivAt_shiftedSection_along_line x (z - x) y 0
  have hslope := hconv.le_slope_of_hasDerivAt
    (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp) zero_lt_one hder
  have hslope' :
      (∑ i : Fin m, (P.gradX x y i + ell * x i) * (z i - x i)) ≤
        (P.f z y + ell / 2 * vecSq z) -
          (P.f x y + ell / 2 * vecSq x) := by
    simpa [slope, shiftedSection, shiftedGrad, line, eDot] using hslope
  linarith

private theorem IsNCCClass.hasDerivAt_dual_along_line {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P)
    (x : EVec m) (y d : EVec n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ P.f x (line y d s))
      (∑ j : Fin n, P.gradY x (line y d t) j * d j) t := by
  let L : ℝ →L[ℝ] EVec n := (1 : ℝ →L[ℝ] ℝ).smulRight d
  have hxconst : HasFDerivAt (fun _ : ℝ ↦ x) 0 t :=
    hasFDerivAt_const (𝕜 := ℝ) x t
  have hyline : HasFDerivAt (line y d) L t := by
    simpa [line, L, ContinuousLinearMap.smulRight_apply] using
      L.hasFDerivAt.add_const y
  have hpath := hxconst.prodMk hyline
  have houter : HasFDerivAt (Function.uncurry P.f)
      (fderiv ℝ (Function.uncurry P.f) (x, line y d t))
      (x, line y d t) :=
    hP.gradient_representation.1.differentiableAt.hasFDerivAt
  have hcomp := houter.comp t hpath
  have hderiv := hcomp.hasDerivAt
  apply hderiv.congr_deriv
  rw [ContinuousLinearMap.comp_apply]
  have hL : ((0 : ℝ →L[ℝ] EVec m).prod L) 1 = (0, d) := by
    ext i <;> simp [L, ContinuousLinearMap.smulRight_apply]
  rw [hL, hP.gradient_representation.2]
  simp

private theorem IsNCCClass.dualSection_concaveOn_segment {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P)
    {x : EVec m} (hx : x ∈ P.X)
    {y v : EVec n} (hy : y ∈ P.Y) (hv : v ∈ P.Y) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t : ℝ ↦ P.f x (line y (v - y) t)) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro s hs t ht a b ha hb hab
  have hys : line y (v - y) s ∈ P.Y :=
    line_mem_convex hP.Y_convex hy hv hs
  have hyt : line y (v - y) t ∈ P.Y :=
    line_mem_convex hP.Y_convex hy hv ht
  have hc := (hP.dual_concave x hx).2 hys hyt ha hb hab
  have hline :
      a • line y (v - y) s + b • line y (v - y) t =
        line y (v - y) (a * s + b * t) := by
    ext i
    simp [line]
    linear_combination (y i) * hab
  rw [hline] at hc
  simpa only [smul_eq_mul] using hc

/-- The concave dual section has its represented dual gradient as a global
supporting hyperplane on the dual domain. -/
theorem IsNCCClass.dualSection_support {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P)
    {x : EVec m} (hx : x ∈ P.X)
    {y v : EVec n} (hy : y ∈ P.Y) (hv : v ∈ P.Y) :
    P.f x v ≤ P.f x y +
      ∑ j : Fin n, P.gradY x y j * (v j - y j) := by
  have hconc := hP.dualSection_concaveOn_segment hx hy hv
  have hder := hP.hasDerivAt_dual_along_line x y (v - y) 0
  have hslope := hconc.slope_le_of_hasDerivAt
    (show (0 : ℝ) ∈ Set.Icc 0 1 by simp)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by simp) zero_lt_one hder
  have hslope' :
      P.f x v ≤ (∑ j : Fin n, P.gradY x y j * (v j - y j)) + P.f x y := by
    simpa [slope, line] using hslope
  linarith

end

end NCCLowerBoundVerification
