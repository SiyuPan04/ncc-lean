import NCC.Model.WithinSupport
import NCCLowerBoundVerification.Upper.ClassOperator

/-!
# The feasible-domain operator for the upper algorithm

The algebraic operator definitions are identical to the executable backend.
Their support, monotonicity, smoothness and projection-domain properties
are derived here from WithinClass, without an ambient extension.
-/

namespace NCC.Upper.WithinOperator

noncomputable section

open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open PointwiseConjugate ProjectionGeometry ScaledOperator ClassOperator

theorem convexSupportX {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (z : EVec m) {x : EVec m} (hx : x ∈ P.X)
    {y : EVec n} (hy : y ∈ P.Y) :
    ConvexSupportX P.X (decurved P.f ell r z)
      (gradXHat P ell z x y) x y := by
  intro u hu
  have h := hP.shiftedSection_support hx hu hy
  rw [decurved_eq, decurved_eq]
  unfold gradXHat dot
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have hsum :
      (∑ i : Fin m,
        (P.gradX x y i + ell * x i - 2 * ell * z i) * (u i - x i)) =
        (∑ i : Fin m, (P.gradX x y i + ell * x i) * (u i - x i)) -
          2 * ell * (∑ i : Fin m, z i * (u i - x i)) := by
    calc
      _ = ∑ i : Fin m,
          ((P.gradX x y i + ell * x i) * (u i - x i) -
            (2 * ell) * (z i * (u i - x i))) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsum]
  have hzsum :
      (∑ i : Fin m, z i * (u i - x i)) =
        (∑ i : Fin m, z i * u i) - ∑ i : Fin m, z i * x i := by
    calc
      _ = ∑ i : Fin m, (z i * u i - z i * x i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [hzsum]
  linarith

theorem concaveSupportY {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (z : EVec m) {x : EVec m} (hx : x ∈ P.X)
    {y : EVec n} (hy : y ∈ P.Y) :
    ConcaveSupportY P.Y (decurved P.f ell r z)
      (gradYHat P ell z x y) x y := by
  intro v hv
  have h := hP.dualSection_support hx hy hv
  rw [decurved_eq, decurved_eq]
  unfold gradYHat dot
  simp only [Pi.sub_apply] at h ⊢
  linarith

/-- The saddle vector field of the decurved objective is monotone on the
actual feasible product domain. -/
theorem saddleGradientMonotoneOn {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (z : EVec m) :
    SaddleGradientMonotoneOn P.X P.Y
      (gradXHat P ell z) (gradYHat P ell z) := by
  intro x hx y hy x' hx' y' hy'
  have hxx' := convexSupportX (r := r) hP z hx hy x' hx'
  have hx'x := convexSupportX (r := r) hP z hx' hy' x hx
  have hyy' := concaveSupportY (r := r) hP z hx hy y' hy'
  have hy'y := concaveSupportY (r := r) hP z hx' hy' y hy
  unfold vecDot
  unfold dot at hxx' hx'x hyy' hy'y
  simp only [Pi.sub_apply] at hxx' hx'x hyy' hy'y ⊢
  have hnegX :
      (∑ i : Fin m, gradXHat P ell z x y i * (x' i - x i)) =
        -(∑ i : Fin m, gradXHat P ell z x y i * (x i - x' i)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hnegY :
      (∑ j : Fin n, gradYHat P ell z x y j * (y' j - y j)) =
        -(∑ j : Fin n, gradYHat P ell z x y j * (y j - y' j)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hnegX] at hxx'
  rw [hnegY] at hyy'
  have hdx :
      (∑ i : Fin m,
        (gradXHat P ell z x y i - gradXHat P ell z x' y' i) *
          (x i - x' i)) =
        (∑ i : Fin m, gradXHat P ell z x y i * (x i - x' i)) -
          ∑ i : Fin m, gradXHat P ell z x' y' i * (x i - x' i) := by
    calc
      _ = ∑ i : Fin m,
          (gradXHat P ell z x y i * (x i - x' i) -
            gradXHat P ell z x' y' i * (x i - x' i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hdy :
      (∑ j : Fin n,
        (gradYHat P ell z x y j - gradYHat P ell z x' y' j) *
          (y j - y' j)) =
        (∑ j : Fin n, gradYHat P ell z x y j * (y j - y' j)) -
          ∑ j : Fin n, gradYHat P ell z x' y' j * (y j - y' j) := by
    calc
      _ = ∑ j : Fin n,
          (gradYHat P ell z x y j * (y j - y' j) -
            gradYHat P ell z x' y' j * (y j - y' j)) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [Finset.sum_sub_distrib]
  rw [hdx, hdy]
  linarith

/-- Adding the known affine primal term to an `ell`-smooth class gradient
gives the paper's `2*ell` joint Lipschitz bound. -/
theorem jointGradientLipschitzOn {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (z : EVec m) :
    JointGradientLipschitzOn P.X P.Y
      (gradXHat P ell z) (gradYHat P ell z) (2 * ell) := by
  intro x hx y hy x' hx' y' hy'
  have hs :
      vecSq (P.gradX x y - P.gradX x' y') +
          vecSq (P.gradY x y - P.gradY x' y') ≤
        ell ^ 2 * (vecSq (x - x') + vecSq (y - y')) := by
    simpa [jointSq] using hP.jointly_smooth x hx y hy x' hx' y' hy'
  let gx := P.gradX x y - P.gradX x' y'
  let gy := P.gradY x y - P.gradY x' y'
  let dx := x - x'
  let dy := y - y'
  have hxadd := ScaledOperator.vecSq_add_le_two gx (ell • dx)
  rw [vecSq_smul] at hxadd
  have hgy : 0 ≤ vecSq gy := ProjectionGeometry.vecSq_nonneg gy
  have hdx : 0 ≤ vecSq dx := ProjectionGeometry.vecSq_nonneg dx
  have hdy : 0 ≤ vecSq dy := ProjectionGeometry.vecSq_nonneg dy
  have hformX :
      gradXHat P ell z x y - gradXHat P ell z x' y' = gx + ell • dx := by
    ext i
    simp [gradXHat, gx, dx]
    ring
  have hformY :
      gradYHat P ell z x y - gradYHat P ell z x' y' = gy := by
    rfl
  rw [hformX, hformY]
  have hs' : vecSq gx + vecSq gy ≤
      ell ^ 2 * (vecSq dx + vecSq dy) := by
    simpa [gx, gy, dx, dy] using hs
  change vecSq (gx + ell • dx) + vecSq gy ≤
    (2 * ell) ^ 2 * (vecSq dx + vecSq dy)
  have hscale := mul_le_mul_of_nonneg_left hs' (by norm_num : (0 : ℝ) ≤ 2)
  have helldy : 0 ≤ ell ^ 2 * vecSq dy :=
    mul_nonneg (sq_nonneg ell) hdy
  nlinarith

theorem scaledSet_nonempty {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P) :
    (scaledSet ell P.X P.Y).Nonempty := by
  obtain ⟨x, hx⟩ := hP.X_nonempty
  obtain ⟨y, hy⟩ := hP.Y_nonempty
  exact ⟨scalePair ell x y,
    (scalePair_mem_scaledSet_iff hP.ell_pos x y).2 ⟨hx, hy⟩⟩

theorem scaledSet_closed {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P) :
    IsClosed (scaledSet ell P.X P.Y) := by
  let LX : Pair m n →ₗ[ℝ] EVec m :=
    { toFun := unscaleX ell
      map_add' := by
        intro u v
        ext i
        simp [unscaleX, unpackX]
        ring
      map_smul' := by
        intro c u
        ext i
        simp [unscaleX, unpackX]
        ring }
  let LY : Pair m n →ₗ[ℝ] EVec n :=
    { toFun := unscaleY ell
      map_add' := by
        intro u v
        ext i
        simp [unscaleY, unpackY]
        ring
      map_smul' := by
        intro c u
        ext i
        simp [unscaleY, unpackY]
        ring }
  have hxcont : Continuous (unscaleX ell : Pair m n → EVec m) :=
    LX.continuous_of_finiteDimensional
  have hycont : Continuous (unscaleY ell : Pair m n → EVec n) :=
    LY.continuous_of_finiteDimensional
  have hc := (hP.X_closed.preimage hxcont).inter
    (hP.Y_closed.preimage hycont)
  change IsClosed
    ((unscaleX ell : Pair m n → EVec m) ⁻¹' P.X ∩
      (unscaleY ell : Pair m n → EVec n) ⁻¹' P.Y)
  exact hc

theorem scaledSet_convex {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P) :
    Convex ℝ (scaledSet ell P.X P.Y) := by
  intro u hu v hv a b ha hb hab
  constructor
  · have h := hP.X_convex hu.1 hv.1 ha hb hab
    have heq : unscaleX ell (a • u + b • v) =
        a • unscaleX ell u + b • unscaleX ell v := by
      ext i
      simp [unscaleX, unpackX]
      ring
    rwa [heq]
  · have h := hP.Y_convex hu.2 hv.2 ha hb hab
    have heq : unscaleY ell (a • u + b • v) =
        a • unscaleY ell u + b • unscaleY ell v := by
      ext i
      simp [unscaleY, unpackY]
      ring
    rwa [heq]

end

end NCC.Upper.WithinOperator

