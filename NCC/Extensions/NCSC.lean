import NCC.Model.WithinSupport
import NCCLowerBoundVerification.Upper.TrackingAnalytic

/-!
# An explicit NC-SC feasible-domain model

This module defines a nonconvex-strongly-concave class on closed convex
feasible sets, with prescribed derivatives within their product, joint
Euclidean smoothness, strong dual concavity, and a primal value gap.
No bounded dual diameter, compact dual set, maximum-attainment hypothesis,
or neighborhood extension is included.

Strong dual concavity is expressed by concavity after adding the Euclidean
quadratic `mu/2 * vecSq y`, not the square of the ambient Pi sup norm.
Actual attainment on the possibly unbounded dual set is proved below.
-/

namespace NCC.Extensions.NCSC

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper

structure NCSCClass {m n : ℕ} (ell mu Delta : ℝ) (P : NCCInstance m n) : Prop where
  ell_pos : 0 < ell
  mu_pos : 0 < mu
  Delta_pos : 0 < Delta
  primal_origin : (0 : EVec m) ∈ P.X
  dual_origin : (0 : EVec n) ∈ P.Y
  initialization : P.x0 = 0
  X_closed : IsClosed P.X
  X_convex : Convex ℝ P.X
  Y_closed : IsClosed P.Y
  Y_convex : Convex ℝ P.Y
  gradient_representation : Model.RepresentsJointGradientWithin P
  jointly_smooth : Model.JointlySmoothWithin ell P
  dual_stronglyConcave : ∀ x ∈ P.X,
    ConcaveOn ℝ P.Y (fun y => P.f x y + quadraticCorrection mu y)
  initial_gap_pointwise : ∀ x ∈ P.X, ValueOn P.Y P.f 0 - ValueOn P.Y P.f x ≤ Delta

variable {m n : ℕ} {ell mu Delta : ℝ} {P : NCCInstance m n}

theorem quadraticCorrection_convex {d : ℕ} {C : Set (EVec d)}
    {mu : ℝ} (hmu : 0 ≤ mu) (hC : Convex ℝ C) :
    ConvexOn ℝ C (quadraticCorrection mu) := by
  refine ⟨hC, ?_⟩
  intro x _ y _ a b ha hb hab
  have hs : ∑ i : Fin d, (a * x i + b * y i) ^ 2 ≤
      ∑ i : Fin d, (a * (x i) ^ 2 + b * (y i) ^ 2) := by
    apply Finset.sum_le_sum
    intro i _
    exact (Even.convexOn_pow (𝕜 := ℝ) (show Even (2 : ℕ) by decide)).2
      (Set.mem_univ (x i)) (Set.mem_univ (y i)) ha hb hab
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ mu / 2)
  simp only [quadraticCorrection, vecSq, NCPLVerification.vecSq,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, mul_add, mul_left_comm] using hm

theorem shifted_dual_derivative (h : NCSCClass ell mu Delta P)
    {x : EVec m} (hx : x ∈ P.X) {y : EVec n} (hy : y ∈ P.Y) :
    HasFDerivWithinAt (fun v => P.f x v + quadraticCorrection mu v)
      (residualCLM (P.gradY x y + mu • y)) P.Y y := by
  convert! (Model.hasFDerivWithinAt_dual_section h.gradient_representation hx hy).add
    (Model.hasFDerivAt_quadraticCorrection mu y).hasFDerivWithinAt using 1
  ext d
  simp [residualCLM_apply, eDot, add_mul, Finset.sum_add_distrib]

/-- Genuine first-order strong support, valid at dual boundary points. -/
theorem dual_strong_support (h : NCSCClass ell mu Delta P)
    {x : EVec m} (hx : x ∈ P.X) {y v : EVec n} (hy : y ∈ P.Y) (hv : v ∈ P.Y) :
    P.f x v ≤ P.f x y + eDot (P.gradY x y) (v - y) - mu / 2 * vecSq (v - y) := by
  have hs := Model.concave_support_of_within (h.dual_stronglyConcave x hx) hy hv
    (shifted_dual_derivative h hx hy)
  have heq : quadraticCorrection mu y +
        residualCLM (P.gradY x y + mu • y) (v - y) - quadraticCorrection mu v =
      eDot (P.gradY x y) (v - y) - mu / 2 * vecSq (v - y) := by
    simp only [quadraticCorrection, residualCLM_apply, eDot, vecSq, NCPLVerification.vecSq,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  linarith

theorem dual_concave (h : NCSCClass ell mu Delta P) {x : EVec m} (hx : x ∈ P.X) :
    ConcaveOn ℝ P.Y (P.f x) := by
  have hc := (h.dual_stronglyConcave x hx).add
    ((quadraticCorrection_convex h.mu_pos.le h.Y_convex).neg)
  apply hc.congr
  intro y _
  simp

theorem dual_continuousOn (h : NCSCClass ell mu Delta P)
    {x : EVec m} (hx : x ∈ P.X) : ContinuousOn (P.f x) P.Y := by
  intro y hy
  exact (Model.hasFDerivWithinAt_dual_section h.gradient_representation hx hy).continuousWithinAt

/-- Strong concavity gives quadratic coercivity; compactness of `Y` is
not used to prove that its actual supremum is attained. -/
theorem maximum_attained (h : NCSCClass ell mu Delta P)
    {x : EVec m} (hx : x ∈ P.X) : ∃ y, IsMaximizerOn P.Y P.f x y := by
  let g : EVec n → ℝ := fun y => -P.f x y - mu / 4 * vecSq y
  have hg : ContinuousOn g P.Y :=
    (dual_continuousOn h hx).neg.sub (continuous_const.mul continuous_vecSq).continuousOn
  have hlower : ∀ y ∈ P.Y,
      -P.f x 0 - (1 / mu) * vecSq (P.gradY x 0) ≤ g y := by
    intro y hy
    have hs := dual_strong_support h hx h.dual_origin hy
    simp only [sub_zero] at hs
    have hyoung := TrackingAnalytic.two_dot_le_sq_add_sq (P.gradY x 0) ((mu / 2) • y)
    rw [vecSq_smul] at hyoung
    have hd : PointwiseConjugate.dot (P.gradY x 0) ((mu / 2) • y) =
        mu / 2 * eDot (P.gradY x 0) y := by
      simp [PointwiseConjugate.dot, eDot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hd] at hyoung
    have hb : eDot (P.gradY x 0) y ≤
        (1 / mu) * vecSq (P.gradY x 0) + mu / 4 * vecSq y := by
      apply (mul_le_mul_iff_right₀ h.mu_pos).1
      calc
        mu * eDot (P.gradY x 0) y ≤
            vecSq (P.gradY x 0) + mu ^ 2 / 4 * vecSq y := by nlinarith
        _ = _ := by field_simp [h.mu_pos.ne']
    dsimp [g]
    linarith
  obtain ⟨u, hu⟩ := hasProxEverywhere_of_continuousOn_bddBelow
    ⟨0, h.dual_origin⟩ h.Y_closed (div_pos h.mu_pos (by norm_num) : 0 < mu / 4) hg hlower 0
  refine ⟨u, hu.1, ?_⟩
  intro v hv
  have hm := hu.2 v hv
  simp only [g, sub_zero] at hm
  linarith

theorem value_eq_maximum (h : NCSCClass ell mu Delta P)
    {x : EVec m} (hx : x ∈ P.X) :
    ∃ y ∈ P.Y, ValueOn P.Y P.f x = P.f x y := by
  obtain ⟨y, hy⟩ := maximum_attained h hx
  exact ⟨y, hy.1, value_eq_of_isMaximizerOn hy⟩

end

end NCC.Extensions.NCSC
