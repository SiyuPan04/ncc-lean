import NCCLowerBoundVerification.Upper.Proximal

/-!
# Algebraic perturbation-bias comparison

This module isolates the algebraic core of
`ub:lem:smoothing-comparison`.  It does not assume the analytic results that
the two proximal objectives are strongly convex or that their Moreau
envelopes are differentiable.  Instead, the precise strong-minimizer
inequalities used by the paper are explicit hypotheses.
-/

namespace NCCLowerBoundVerification
namespace Upper

noncomputable section

/-- Maximized value after subtracting the dual quadratic regularizer. -/
def DualRegularizedValueOn {m n : Nat} (Y : Set (EVec n))
    (f : EVec m → EVec n → ℝ) (r : ℝ) (x : EVec m) : ℝ :=
  ValueOn Y (fun u y ↦ f u y - r / 2 * vecSq y) x

private theorem vecSq_nonneg {n : Nat} (y : EVec n) : 0 ≤ vecSq y := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (y i)

/-- Pointwise value bias caused by the dual quadratic regularizer. -/
theorem dualRegularizedValue_bias {m n : Nat} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {r D : ℝ} (hr : 0 ≤ r)
    (hbound : ∀ y ∈ Y, vecSq y ≤ D ^ 2) {x : EVec m}
    (hmax : ∃ y, IsMaximizerOn Y f x y)
    (hmaxR : ∃ y, IsMaximizerOn Y
      (fun u v ↦ f u v - r / 2 * vecSq v) x y) :
    0 ≤ ValueOn Y f x - DualRegularizedValueOn Y f r x ∧
      ValueOn Y f x - DualRegularizedValueOn Y f r x ≤
        r / 2 * D ^ 2 := by
  obtain ⟨y, hy⟩ := hmax
  obtain ⟨yR, hyR⟩ := hmaxR
  rw [value_eq_of_isMaximizerOn hy]
  unfold DualRegularizedValueOn
  rw [value_eq_of_isMaximizerOn hyR]
  constructor
  · have horder := hy.2 yR hyR.1
    have hquad : 0 ≤ r / 2 * vecSq yR :=
      mul_nonneg (div_nonneg hr (by norm_num)) (vecSq_nonneg yR)
    linarith
  · have horder := hyR.2 y hy.1
    have hnorm := hbound y hy.1
    have hscale : r / 2 * vecSq y ≤ r / 2 * D ^ 2 :=
      mul_le_mul_of_nonneg_left hnorm (div_nonneg hr (by norm_num))
    linarith

/-- Uniform form of the pointwise dual-regularization bias. -/
theorem dualRegularizedValue_uniform_bias {m n : Nat}
    {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ} {r D : ℝ}
    (hr : 0 ≤ r)
    (hbound : ∀ y ∈ Y, vecSq y ≤ D ^ 2)
    (hmax : ∀ x, ∃ y, IsMaximizerOn Y f x y)
    (hmaxR : ∀ x, ∃ y, IsMaximizerOn Y
      (fun u v ↦ f u v - r / 2 * vecSq v) x y) :
    ∀ x, 0 ≤ ValueOn Y f x - DualRegularizedValueOn Y f r x ∧
      ValueOn Y f x - DualRegularizedValueOn Y f r x ≤
        r / 2 * D ^ 2 := by
  intro x
  exact dualRegularizedValue_bias hr hbound (hmax x) (hmaxR x)

/--
Adding the two strong-minimizer inequalities cancels the common proximal
penalty.  A pointwise bias in `[0, delta]` then controls the displacement of
the two minimizers.
-/
theorem strongMinimizers_vecSq_le {m : Nat} {phi phiR : EVec m → ℝ}
    {ell delta : ℝ} {z u v : EVec m}
    (hbias : ∀ w, 0 ≤ phi w - phiR w ∧ phi w - phiR w ≤ delta)
    (hphi :
      phi u + ell * vecSq (u - z) + ell / 2 * vecSq (v - u) ≤
        phi v + ell * vecSq (v - z))
    (hphiR :
      phiR v + ell * vecSq (v - z) + ell / 2 * vecSq (u - v) ≤
        phiR u + ell * vecSq (u - z)) :
    ell * vecSq (u - v) ≤ delta := by
  have hsym := vecSq_sub_comm u v
  have hu := (hbias u).1
  have hv := (hbias v).2
  rw [← hsym] at hphi
  linarith

/-- Squared difference between the two `2 * ell` proximal residuals. -/
theorem scaledResidualDifference_vecSq_le {m : Nat} {ell delta : ℝ}
    (hell : 0 ≤ ell) {z u v : EVec m}
    (hdist : ell * vecSq (u - v) ≤ delta) :
    vecSq ((2 * ell) • (z - u) - (2 * ell) • (z - v)) ≤
      4 * ell * delta := by
  have heq :
      vecSq ((2 * ell) • (z - u) - (2 * ell) • (z - v)) =
        (2 * ell) ^ 2 * vecSq (u - v) := by
    unfold vecSq NCPLVerification.vecSq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [heq]
  calc
    (2 * ell) ^ 2 * vecSq (u - v) =
        (4 * ell) * (ell * vecSq (u - v)) := by ring
    _ ≤ (4 * ell) * delta :=
      mul_le_mul_of_nonneg_left hdist (mul_nonneg (by norm_num) hell)
    _ = 4 * ell * delta := by ring

/-- Algebraic perturbation-to-residual comparison with a generic bias. -/
theorem strongMinimizers_residualDifference_vecSq_le {m : Nat}
    {phi phiR : EVec m → ℝ} {ell delta : ℝ} (hell : 0 ≤ ell)
    {z u v : EVec m}
    (hbias : ∀ w, 0 ≤ phi w - phiR w ∧ phi w - phiR w ≤ delta)
    (hphi :
      phi u + ell * vecSq (u - z) + ell / 2 * vecSq (v - u) ≤
        phi v + ell * vecSq (v - z))
    (hphiR :
      phiR v + ell * vecSq (v - z) + ell / 2 * vecSq (u - v) ≤
        phiR u + ell * vecSq (u - z)) :
    vecSq ((2 * ell) • (z - u) - (2 * ell) • (z - v)) ≤
      4 * ell * delta :=
  scaledResidualDifference_vecSq_le hell
    (strongMinimizers_vecSq_le hbias hphi hphiR)

/--
Specializing `delta = r / 2 * D²` yields the square of the paper's bound
`D * sqrt (2 * ell * r)`.
-/
theorem strongMinimizers_regularization_residual_vecSq_le {m : Nat}
    {phi phiR : EVec m → ℝ} {ell r D : ℝ} (hell : 0 ≤ ell)
    {z u v : EVec m}
    (hbias : ∀ w, 0 ≤ phi w - phiR w ∧
      phi w - phiR w ≤ r / 2 * D ^ 2)
    (hphi :
      phi u + ell * vecSq (u - z) + ell / 2 * vecSq (v - u) ≤
        phi v + ell * vecSq (v - z))
    (hphiR :
      phiR v + ell * vecSq (v - z) + ell / 2 * vecSq (u - v) ≤
        phiR u + ell * vecSq (u - z)) :
    vecSq ((2 * ell) • (z - u) - (2 * ell) • (z - v)) ≤
      2 * ell * r * D ^ 2 := by
  have h := strongMinimizers_residualDifference_vecSq_le hell hbias hphi hphiR
  calc
    _ ≤ 4 * ell * (r / 2 * D ^ 2) := h
    _ = 2 * ell * r * D ^ 2 := by ring

/-- The analytic hypotheses of `strongMinimizers_residualDifference_vecSq_le`
follow from actual proximal minimizers and weak convexity. -/
theorem weaklyConvex_prox_residualDifference_vecSq_le {m : Nat}
    {X : Set (EVec m)} {phi phiR : EVec m → ℝ}
    {ell delta : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hweakR : IsWeaklyConvexOn ell X phiR)
    {z u v : EVec m}
    (hu : IsProxPoint X phi ell z u)
    (hv : IsProxPoint X phiR ell z v)
    (hbias : ∀ w, 0 ≤ phi w - phiR w ∧ phi w - phiR w ≤ delta) :
    vecSq ((2 * ell) • (z - u) - (2 * ell) • (z - v)) ≤
      4 * ell * delta := by
  exact strongMinimizers_residualDifference_vecSq_le hell.le hbias
    (proxPoint_strongMinimizer_expanded hell hweak hu hv.1)
    (proxPoint_strongMinimizer_expanded hell hweakR hv hu.1)

/-- Fully discharged weak-convex version at the paper's dual-bias value
`delta = r D² / 2`. -/
theorem weaklyConvex_prox_regularization_residual_vecSq_le {m : Nat}
    {X : Set (EVec m)} {phi phiR : EVec m → ℝ}
    {ell r D : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hweakR : IsWeaklyConvexOn ell X phiR)
    {z u v : EVec m}
    (hu : IsProxPoint X phi ell z u)
    (hv : IsProxPoint X phiR ell z v)
    (hbias : ∀ w, 0 ≤ phi w - phiR w ∧
      phi w - phiR w ≤ r / 2 * D ^ 2) :
    vecSq ((2 * ell) • (z - u) - (2 * ell) • (z - v)) ≤
      2 * ell * r * D ^ 2 := by
  have h := weaklyConvex_prox_residualDifference_vecSq_le
    hell hweak hweakR hu hv hbias
  calc
    _ ≤ 4 * ell * (r / 2 * D ^ 2) := h
    _ = 2 * ell * r * D ^ 2 := by ring

/-- Unsquared Euclidean form of the perturbation-to-OS comparison exactly as
displayed in `ub:lem:smoothing-comparison`. -/
theorem weaklyConvex_prox_regularization_residual_norm_le {m : Nat}
    {X : Set (EVec m)} {phi phiR : EVec m → ℝ}
    {ell r D : ℝ} (hell : 0 < ell) (hr : 0 ≤ r) (hD : 0 ≤ D)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hweakR : IsWeaklyConvexOn ell X phiR)
    {z u v : EVec m}
    (hu : IsProxPoint X phi ell z u)
    (hv : IsProxPoint X phiR ell z v)
    (hbias : ∀ w, 0 ≤ phi w - phiR w ∧
      phi w - phiR w ≤ r / 2 * D ^ 2) :
    Real.sqrt (vecSq ((2 * ell) • (z - u) - (2 * ell) • (z - v))) ≤
      D * Real.sqrt (2 * ell * r) := by
  have hsq := weaklyConvex_prox_regularization_residual_vecSq_le
    hell hweak hweakR hu hv hbias
  have hleft : 0 ≤ vecSq ((2 * ell) • (z - u) - (2 * ell) • (z - v)) :=
    vecSq_nonneg _
  have hright : 0 ≤ 2 * ell * r := by positivity
  have hsqrtLeft := Real.sq_sqrt hleft
  have hsqrtRight := Real.sq_sqrt hright
  have hnonnegLeft := Real.sqrt_nonneg
    (vecSq ((2 * ell) • (z - u) - (2 * ell) • (z - v)))
  have hnonnegRight : 0 ≤ D * Real.sqrt (2 * ell * r) :=
    mul_nonneg hD (Real.sqrt_nonneg _)
  nlinarith [sq_nonneg
    (Real.sqrt (vecSq ((2 * ell) • (z - u) - (2 * ell) • (z - v))) -
      D * Real.sqrt (2 * ell * r))]

end

end Upper
end NCCLowerBoundVerification
