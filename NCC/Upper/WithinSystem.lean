import NCC.Upper.WithinAnalytic
import NCC.Upper.WithinOperator
import NCCLowerBoundVerification.Upper.SystemInstantiation

/-!
# Concrete FOAM systems under derivatives within the feasible domain

The saddle existence and solver algebra follow the checked generic backend.
All class-dependent support, continuity and proximal facts here come from
WithinClass; no global representative or ambient interior is assumed.
-/

namespace NCC.Upper.WithinSystem

noncomputable section

open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper


open PointwiseConjugate
open RelativeFOAM
open RelativeFOAMContraction
open ScaledOperator
open OuterTrajectoryConcrete

set_option maxHeartbeats 3000000

/-! ## Finiteness of the pointwise conjugate -/

/-- A section at an arbitrary dual point can lose from the maximized value at
most linearly in the primal variable.  The proof uses only the bounded dual
diameter and the joint gradient Lipschitz estimate. -/
private theorem section_lower_bound {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (lower : ℝ) (hlower : ∀ x ∈ P.X, lower ≤ ValueOn P.Y P.f x)
    (y0 : EVec n) (hy0 : y0 ∈ P.Y) (x : EVec m) (hx : x ∈ P.X)
    (y : EVec n) (hy : y ∈ P.Y) :
    lower -
        (ell / 4 * vecSq x + ell / 4 * vecSq P.x0 +
          (17 * ell / 8 + 1 / 2) * D ^ 2 +
          1 / 2 * vecSq (P.gradY P.x0 y0)) ≤
      P.f x y := by
  obtain ⟨ym, hym⟩ := hP.maximum_attained hx
  have hvalue : ValueOn P.Y P.f x = P.f x ym :=
    value_eq_of_isMaximizerOn hym
  have hsupport := hP.dualSection_support hx hy hym.1
  have hlow : lower ≤ P.f x y +
      dot (P.gradY x y) (ym - y) := by
    have hl := hlower x hx
    rw [hvalue] at hl
    exact hl.trans hsupport
  let gd := P.gradY x y - P.gradY P.x0 y0
  let d := ym - y
  have hsmooth := hP.jointly_smooth x hx y hy P.x0 hP.x0_mem y0 hy0
  have hgx0 : 0 ≤ vecSq (P.gradX x y - P.gradX P.x0 y0) :=
    ProjectionGeometry.vecSq_nonneg _
  have hgd : vecSq gd ≤
      ell ^ 2 * (vecSq (x - P.x0) + vecSq (y - y0)) := by
    dsimp [jointSq, gd] at hsmooth ⊢
    linarith
  have hyref : vecSq (y - y0) ≤ D ^ 2 :=
    hP.dual_diameter y hy y0 hy0
  have hd : vecSq d ≤ D ^ 2 :=
    hP.dual_diameter ym hym.1 y hy
  have hxsub := vecSq_sub_le_two x P.x0
  have hell0 : 0 ≤ ell := hP.ell_pos.le
  have hgd' : vecSq gd ≤
      2 * ell ^ 2 * vecSq x + 2 * ell ^ 2 * vecSq P.x0 +
        ell ^ 2 * D ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left
      (add_le_add hxsub hyref) (sq_nonneg ell)
    nlinarith
  have hyoungD :=
    TrackingAnalytic.two_dot_le_sq_add_sq gd ((4 * ell) • d)
  rw [vecSq_smul] at hyoungD
  have hdotScale : dot gd ((4 * ell) • d) =
      (4 * ell) * dot gd d := by
    rw [dot_comm, dot_smul_left, dot_comm]
  rw [hdotScale] at hyoungD
  have hyoung0 := TrackingAnalytic.two_dot_le_sq_add_sq
    (P.gradY P.x0 y0) d
  have hsplit : dot (P.gradY x y) d =
      dot gd d + dot (P.gradY P.x0 y0) d := by
    unfold gd dot
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  have hdot : dot (P.gradY x y) d ≤
      ell / 4 * vecSq x + ell / 4 * vecSq P.x0 +
        (17 * ell / 8 + 1 / 2) * D ^ 2 +
        1 / 2 * vecSq (P.gradY P.x0 y0) := by
    rw [hsplit]
    have hD0 : 0 ≤ D ^ 2 := sq_nonneg D
    have hgd0 : 0 ≤ vecSq gd := ProjectionGeometry.vecSq_nonneg _
    have hd0 : 0 ≤ vecSq d := ProjectionGeometry.vecSq_nonneg _
    have hg00 : 0 ≤ vecSq (P.gradY P.x0 y0) :=
      ProjectionGeometry.vecSq_nonneg _
    have hgdpart : dot gd d ≤
        ell / 4 * vecSq x + ell / 4 * vecSq P.x0 +
          17 * ell / 8 * D ^ 2 := by
      refine le_of_mul_le_mul_left ?_
        (mul_pos (by norm_num : (0 : ℝ) < 8) hP.ell_pos)
      calc
        (8 * ell) * dot gd d = 2 * (4 * ell * dot gd d) := by ring
        _ ≤ vecSq gd + (4 * ell) ^ 2 * vecSq d := hyoungD
        _ ≤ (2 * ell ^ 2 * vecSq x + 2 * ell ^ 2 * vecSq P.x0 +
              ell ^ 2 * D ^ 2) + (4 * ell) ^ 2 * D ^ 2 := by
          exact add_le_add hgd'
            (mul_le_mul_of_nonneg_left hd (sq_nonneg (4 * ell)))
        _ = (8 * ell) *
            (ell / 4 * vecSq x + ell / 4 * vecSq P.x0 +
              17 * ell / 8 * D ^ 2) := by ring
    have hg0part : dot (P.gradY P.x0 y0) d ≤
        1 / 2 * vecSq (P.gradY P.x0 y0) + 1 / 2 * D ^ 2 := by
      nlinarith
    nlinarith
  nlinarith

/-- The class lower bound and bounded dual diameter make every conjugate
section finite, including when the primal feasible set is unbounded. -/
theorem gammaBddAbove_of_class {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P) :
    ∀ z, GammaBddAbove P.X P.Y (decurved P.f ell r z) := by
  obtain ⟨lower, hlower⟩ := WithinClass.exists_value_lower_bound hP
  obtain ⟨y0, hy0⟩ := hP.Y_nonempty
  intro z q y
  let a : EVec m := q + (2 * ell) • z
  let C : ℝ := ell / 4 * vecSq P.x0 +
    (17 * ell / 8 + 1 / 2) * D ^ 2 +
    1 / 2 * vecSq (P.gradY P.x0 y0)
  refine ⟨2 / ell * vecSq a - lower + C - ell * vecSq z, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hsection := section_lower_bound hP lower hlower y0 hy0 x hx y.1 y.2
  have hyoung := TrackingAnalytic.two_dot_le_sq_add_sq
    a ((ell / 4) • x)
  rw [vecSq_smul] at hyoung
  have hdotScale : dot a ((ell / 4) • x) =
      (ell / 4) * dot a x := by
    rw [dot_comm, dot_smul_left, dot_comm]
  rw [hdotScale] at hyoung
  have haDot : dot a x = dot q x + 2 * ell * dot z x := by
    dsimp [a]
    rw [dot_add_left, dot_smul_left]
  have hellinv : ell * (2 / ell) = 2 := by
    field_simp [ne_of_gt hP.ell_pos]
  have hx0 : 0 ≤ vecSq x := ProjectionGeometry.vecSq_nonneg _
  have hax : dot a x ≤ 2 / ell * vecSq a + ell / 8 * vecSq x := by
    refine le_of_mul_le_mul_left ?_ (half_pos hP.ell_pos)
    calc
      ell / 2 * dot a x = 2 * (ell / 4 * dot a x) := by ring
      _ ≤ vecSq a + (ell / 4) ^ 2 * vecSq x := hyoung
      _ = ell / 2 *
          (2 / ell * vecSq a + ell / 8 * vecSq x) := by
        field_simp [ne_of_gt hP.ell_pos]
        ring
  change dot q x - decurved P.f ell r z x y.1 ≤ _
  rw [decurved_eq]
  calc
    dot q x -
          (P.f x y.1 + ell / 2 * vecSq x - 2 * ell * dot z x +
            ell * vecSq z) =
        dot a x - P.f x y.1 - ell / 2 * vecSq x - ell * vecSq z := by
      rw [haDot]
      ring
    _ ≤ dot a x -
          (lower - (ell / 4 * vecSq x + C)) -
            ell / 2 * vecSq x - ell * vecSq z := by
      have hsection' : lower - (ell / 4 * vecSq x + C) ≤ P.f x y.1 := by
        dsimp only [C]
        convert hsection using 1; ring
      linarith
    _ ≤ 2 / ell * vecSq a - lower + C - ell * vecSq z := by
      have hellx : 0 ≤ ell * vecSq x :=
        mul_nonneg hP.ell_pos.le hx0
      nlinarith

/-! ## Exact saddle stationarity at the selected proximal point -/

/-! We obtain the strongly convex--concave saddle point as a variational
inequality solution.  This avoids assuming a minimax theorem as an extra
interface. -/

def saddleX {m n : Nat} (P : NCCInstance m n) (ell : ℝ)
    (z x : EVec m) (y : EVec n) : EVec m :=
  ClassOperator.gradXHat P ell z x y + ell • x

def saddleY {m n : Nat} (P : NCCInstance m n) (r : ℝ)
    (x : EVec m) (y : EVec n) : EVec n :=
  -ClassOperator.gradYHat P r x x y + r • y

def saddleRaw {m n : Nat} (P : NCCInstance m n) (ell r : ℝ)
    (z : EVec m) (u : Pair m n) : Pair m n :=
  pack
    (scaleRoot ell • saddleX P ell z (unscaleX ell u) (unscaleY ell u))
    (scaleRoot ell • saddleY P r (unscaleX ell u) (unscaleY ell u))

def saddleSigma (ell r : ℝ) : ℝ := 8 * r / ell

def saddleOperator {m n : Nat} (P : NCCInstance m n) (ell r : ℝ)
    (z : EVec m) (u : Pair m n) : Pair m n :=
  (saddleSigma ell r)⁻¹ • saddleRaw P ell r z u

def saddleM (ell r : ℝ) : ℝ := 32 / saddleSigma ell r

theorem saddleSigma_pos {ell r : ℝ} (hell : 0 < ell) (hr : 0 < r) :
    0 < saddleSigma ell r := by
  unfold saddleSigma
  positivity

private theorem unscaleX_saddleRaw {m n : Nat} {ell r : ℝ}
    (hell : 0 < ell) (P : NCCInstance m n) (z : EVec m) (u : Pair m n) :
    unscaleX ell (saddleRaw P ell r z u) =
      gamma ell • saddleX P ell z (unscaleX ell u) (unscaleY ell u) := by
  unfold saddleRaw unscaleX
  rw [unpackX_pack, smul_smul,
    show scaleRoot ell * scaleRoot ell = scaleRoot ell ^ 2 by ring,
    scaleRoot_sq hell]

private theorem unscaleY_saddleRaw {m n : Nat} {ell r : ℝ}
    (hell : 0 < ell) (P : NCCInstance m n) (z : EVec m) (u : Pair m n) :
    unscaleY ell (saddleRaw P ell r z u) =
      gamma ell • saddleY P r (unscaleX ell u) (unscaleY ell u) := by
  unfold saddleRaw unscaleY
  rw [unpackY_pack, smul_smul,
    show scaleRoot ell * scaleRoot ell = scaleRoot ell ^ 2 by ring,
    scaleRoot_sq hell]

private theorem saddleRaw_pairing {m n : Nat} {ell r : ℝ}
    (hell : 0 < ell) (P : NCCInstance m n) (z : EVec m)
    (u v : Pair m n) :
    ProjectionGeometry.vecDot
        (saddleRaw P ell r z u - saddleRaw P ell r z v) (u - v) =
      ProjectionGeometry.vecDot
          (saddleX P ell z (unscaleX ell u) (unscaleY ell u) -
            saddleX P ell z (unscaleX ell v) (unscaleY ell v))
          (unscaleX ell u - unscaleX ell v) +
        ProjectionGeometry.vecDot
          (saddleY P r (unscaleX ell u) (unscaleY ell u) -
            saddleY P r (unscaleX ell v) (unscaleY ell v))
          (unscaleY ell u - unscaleY ell v) := by
  rw [pair_difference hell, pair_difference hell, vecDot_scalePair hell,
    unscaleX_saddleRaw hell, unscaleX_saddleRaw hell,
    unscaleY_saddleRaw hell, unscaleY_saddleRaw hell]
  rw [← smul_sub, ← smul_sub]
  unfold ProjectionGeometry.vecDot
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [mul_assoc]
  rw [← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
  have hgamma : (gamma ell)⁻¹ * gamma ell = 1 := by
    exact inv_mul_cancel₀ (ne_of_gt (gamma_pos hell))
  rw [← mul_assoc, hgamma, one_mul]

private theorem saddleRaw_difference_sq {m n : Nat} {ell r : ℝ}
    (hell : 0 < ell) (P : NCCInstance m n) (z : EVec m)
    (u v : Pair m n) :
    vecSq (saddleRaw P ell r z u - saddleRaw P ell r z v) =
      gamma ell *
        (vecSq
            (saddleX P ell z (unscaleX ell u) (unscaleY ell u) -
              saddleX P ell z (unscaleX ell v) (unscaleY ell v)) +
          vecSq
            (saddleY P r (unscaleX ell u) (unscaleY ell u) -
              saddleY P r (unscaleX ell v) (unscaleY ell v))) := by
  rw [pair_difference hell, vecSq_scalePair hell,
    unscaleX_saddleRaw hell, unscaleX_saddleRaw hell,
    unscaleY_saddleRaw hell, unscaleY_saddleRaw hell]
  rw [← smul_sub, ← smul_sub, vecSq_smul, vecSq_smul]
  have hgamma : (gamma ell)⁻¹ * gamma ell ^ 2 = gamma ell := by
    field_simp [ne_of_gt (gamma_pos hell)]
  rw [← mul_add, ← mul_assoc, hgamma]

private theorem jointSq_unscale_eq {m n : Nat} {ell : ℝ}
    (hell : 0 < ell) (u v : Pair m n) :
    vecSq (unscaleX ell u - unscaleX ell v) +
        vecSq (unscaleY ell u - unscaleY ell v) =
      gamma ell * vecSq (u - v) := by
  rw [pair_difference hell, vecSq_scalePair hell]
  field_simp [ne_of_gt (gamma_pos hell)]

theorem saddleOperator_stronglyMonotoneOn {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 < r)
    (hrle : r ≤ ell / 8) (z : EVec m) :
    ProjectionGeometry.IsStronglyMonotoneOn (scaledSet ell P.X P.Y)
      (saddleOperator P ell r z) 1 := by
  intro u hu v hv
  let dx := unscaleX ell u - unscaleX ell v
  let dy := unscaleY ell u - unscaleY ell v
  let gx := ClassOperator.gradXHat P ell z (unscaleX ell u) (unscaleY ell u) -
    ClassOperator.gradXHat P ell z (unscaleX ell v) (unscaleY ell v)
  let gy := ClassOperator.gradYHat P ell z (unscaleX ell u) (unscaleY ell u) -
    ClassOperator.gradYHat P ell z (unscaleX ell v) (unscaleY ell v)
  have hmon := WithinOperator.saddleGradientMonotoneOn (r := r) hP z
    (unscaleX ell u) hu.1 (unscaleY ell u) hu.2
    (unscaleX ell v) hv.1 (unscaleY ell v) hv.2
  have hdx0 := ProjectionGeometry.vecSq_nonneg dx
  have hdy0 := ProjectionGeometry.vecSq_nonneg dy
  have hellr : r ≤ ell := by linarith [hP.ell_pos]
  have hpair := saddleRaw_pairing (r := r) hP.ell_pos P z u v
  have hsigma := saddleSigma_pos hP.ell_pos hr
  have hraw : saddleSigma ell r * vecSq (u - v) ≤
      ProjectionGeometry.vecDot
        (saddleRaw P ell r z u - saddleRaw P ell r z v) (u - v) := by
    rw [hpair]
    have hjoint := jointSq_unscale_eq hP.ell_pos u v
    change 0 ≤ ProjectionGeometry.vecDot gx dx -
      ProjectionGeometry.vecDot gy dy at hmon
    have hsx :
        saddleX P ell z (unscaleX ell u) (unscaleY ell u) -
            saddleX P ell z (unscaleX ell v) (unscaleY ell v) =
          gx + ell • dx := by
      ext i
      simp [saddleX, gx, dx]
      ring
    have hsy :
        saddleY P r (unscaleX ell u) (unscaleY ell u) -
            saddleY P r (unscaleX ell v) (unscaleY ell v) =
          -gy + r • dy := by
      ext i
      simp [saddleY, ClassOperator.gradYHat, gy, dy]
      ring
    rw [hsx, hsy]
    rw [show saddleSigma ell r = r * ScaledOperator.gamma ell by
      unfold saddleSigma ScaledOperator.gamma
      field_simp [ne_of_gt hP.ell_pos]]
    rw [mul_assoc, ← hjoint]
    unfold ProjectionGeometry.vecDot at hmon ⊢
    change r * (vecSq dx + vecSq dy) ≤
      (∑ i : Fin m, (gx i + ell * dx i) * dx i) +
        ∑ i : Fin n, (-gy i + r * dy i) * dy i
    have hxform :
        (∑ i : Fin m, (gx i + ell * dx i) * dx i) =
          (∑ i : Fin m, gx i * dx i) + ell * vecSq dx := by
      unfold vecSq NCPLVerification.vecSq
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hyform :
        (∑ i : Fin n, (-gy i + r * dy i) * dy i) =
          -(∑ i : Fin n, gy i * dy i) + r * vecSq dy := by
      unfold vecSq NCPLVerification.vecSq
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hxform, hyform]
    nlinarith
  have hinv : (saddleSigma ell r)⁻¹ * saddleSigma ell r = 1 :=
    inv_mul_cancel₀ (ne_of_gt hsigma)
  have hscaled := mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hsigma.le)
  calc
    1 * vecSq (u - v) =
        (saddleSigma ell r)⁻¹ *
          (saddleSigma ell r * vecSq (u - v)) := by
      rw [← mul_assoc, hinv]
    _ ≤ (saddleSigma ell r)⁻¹ *
        ProjectionGeometry.vecDot
          (saddleRaw P ell r z u - saddleRaw P ell r z v) (u - v) := hscaled
    _ = ProjectionGeometry.vecDot
        (saddleOperator P ell r z u - saddleOperator P ell r z v)
        (u - v) := by
      unfold saddleOperator
      rw [← smul_sub]
      unfold ProjectionGeometry.vecDot
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
      rw [← Finset.mul_sum]

theorem saddleM_ge_one {ell r : ℝ} (hell : 0 < ell) (hr : 0 < r)
    (hrle : r ≤ ell / 8) : 1 ≤ saddleM ell r := by
  have hspos := saddleSigma_pos hell hr
  have hsle : saddleSigma ell r ≤ 1 := by
    unfold saddleSigma
    apply (div_le_iff₀ hell).2
    linarith
  unfold saddleM
  have hdiv : 1 ≤ 1 / saddleSigma ell r := by
    exact (le_div_iff₀ hspos).2 (by simpa using hsle)
  calc
    1 ≤ 32 * (1 / saddleSigma ell r) := by nlinarith
    _ = 32 / saddleSigma ell r := by ring

theorem saddleOperator_lipschitzOn {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 < r)
    (hrle : r ≤ ell / 8) (z : EVec m) :
    ProjectionGeometry.IsEuclideanLipschitzOn (scaledSet ell P.X P.Y)
      (saddleOperator P ell r z) (saddleM ell r) := by
  intro u hu v hv
  let dx := unscaleX ell u - unscaleX ell v
  let dy := unscaleY ell u - unscaleY ell v
  let gx := ClassOperator.gradXHat P ell z (unscaleX ell u) (unscaleY ell u) -
    ClassOperator.gradXHat P ell z (unscaleX ell v) (unscaleY ell v)
  let gy := ClassOperator.gradYHat P ell z (unscaleX ell u) (unscaleY ell u) -
    ClassOperator.gradYHat P ell z (unscaleX ell v) (unscaleY ell v)
  let sx := gx + ell • dx
  let sy := -gy + r • dy
  have hsource := WithinOperator.jointGradientLipschitzOn hP z
    (unscaleX ell u) hu.1 (unscaleY ell u) hu.2
    (unscaleX ell v) hv.1 (unscaleY ell v) hv.2
  change vecSq gx + vecSq gy ≤
    (2 * ell) ^ 2 * (vecSq dx + vecSq dy) at hsource
  have hx := ScaledOperator.vecSq_add_le_two gx (ell • dx)
  have hy := ScaledOperator.vecSq_neg_add_le_two gy (r • dy)
  rw [vecSq_smul] at hx hy
  have hdx0 := ProjectionGeometry.vecSq_nonneg dx
  have hdy0 := ProjectionGeometry.vecSq_nonneg dy
  have hgx0 := ProjectionGeometry.vecSq_nonneg gx
  have hgy0 := ProjectionGeometry.vecSq_nonneg gy
  have hrleell : r ≤ ell := by linarith [hP.ell_pos]
  have hrsq : r ^ 2 ≤ ell ^ 2 := by nlinarith
  have hsy : vecSq sy ≤ 2 * vecSq gy + 2 * r ^ 2 * vecSq dy := by
    simpa only [sy, mul_assoc] using hy
  have hsx : vecSq sx ≤ 2 * vecSq gx + 2 * ell ^ 2 * vecSq dx := by
    simpa only [sx, mul_assoc] using hx
  have hins : vecSq sx + vecSq sy ≤
      10 * ell ^ 2 * (vecSq dx + vecSq dy) := by
    have hry := mul_le_mul_of_nonneg_right hrsq hdy0
    nlinarith [sq_nonneg ell]
  have hrawEq := saddleRaw_difference_sq (r := r) hP.ell_pos P z u v
  have hsxEq :
      saddleX P ell z (unscaleX ell u) (unscaleY ell u) -
          saddleX P ell z (unscaleX ell v) (unscaleY ell v) = sx := by
    ext i
    simp [saddleX, sx, gx, dx]
    ring
  have hsyEq :
      saddleY P r (unscaleX ell u) (unscaleY ell u) -
          saddleY P r (unscaleX ell v) (unscaleY ell v) = sy := by
    ext i
    simp [saddleY, ClassOperator.gradYHat, sy, gy, dy]
    ring
  rw [hsxEq, hsyEq] at hrawEq
  have hjoint := jointSq_unscale_eq hP.ell_pos u v
  have hgamma0 := (gamma_pos hP.ell_pos).le
  have hraw : vecSq (saddleRaw P ell r z u - saddleRaw P ell r z v) ≤
      640 * vecSq (u - v) := by
    rw [hrawEq]
    have hmul := mul_le_mul_of_nonneg_left hins hgamma0
    have hconst :
        ScaledOperator.gamma ell *
            (10 * ell ^ 2 * (vecSq dx + vecSq dy)) =
          640 * vecSq (u - v) := by
      rw [hjoint]
      unfold ScaledOperator.gamma
      field_simp [ne_of_gt hP.ell_pos]
      ring
    exact hmul.trans_eq hconst
  have hspos := saddleSigma_pos hP.ell_pos hr
  have hsInv0 : 0 ≤ (saddleSigma ell r)⁻¹ ^ 2 := sq_nonneg _
  unfold saddleOperator saddleM
  rw [← smul_sub, vecSq_smul]
  have hscaled := mul_le_mul_of_nonneg_left hraw hsInv0
  have hcoef :
      (saddleSigma ell r)⁻¹ ^ 2 * 640 ≤
        (32 / saddleSigma ell r) ^ 2 := by
    field_simp [ne_of_gt hspos]
    norm_num
  have huv0 := ProjectionGeometry.vecSq_nonneg (u - v)
  nlinarith

structure SaddleWitness {m n : Nat} (P : NCCInstance m n)
    (ell r : ℝ) (z : EVec m) where
  x : EVec m
  y : EVec n
  x_mem : x ∈ P.X
  y_mem : y ∈ P.Y
  normalX : IsEuclideanNormal P.X x (-saddleX P ell z x y)
  normalY : IsEuclideanNormal P.Y y (-saddleY P r x y)

private theorem scaledNormalX_eq {m n : Nat} {ell r : ℝ}
    (hell : 0 < ell) (hr : 0 < r) (P : NCCInstance m n)
    (z : EVec m) (u : Pair m n) :
    saddleSigma ell r •
        unscaledNormalX ell (-saddleOperator P ell r z u) =
      -saddleX P ell z (unscaleX ell u) (unscaleY ell u) := by
  ext i
  simp only [unscaledNormalX, saddleOperator, saddleRaw, unpackX,
    pack, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Fin.append_left]
  have hs := saddleSigma_pos hell hr
  have hroot := scaleRoot_pos hell
  field_simp [ne_of_gt hs, ne_of_gt hroot]

private theorem scaledNormalY_eq {m n : Nat} {ell r : ℝ}
    (hell : 0 < ell) (hr : 0 < r) (P : NCCInstance m n)
    (z : EVec m) (u : Pair m n) :
    saddleSigma ell r •
        unscaledNormalY ell (-saddleOperator P ell r z u) =
      -saddleY P r (unscaleX ell u) (unscaleY ell u) := by
  ext i
  simp only [unscaledNormalY, saddleOperator, saddleRaw, unpackY,
    pack, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, Fin.append_right]
  have hs := saddleSigma_pos hell hr
  have hroot := scaleRoot_pos hell
  field_simp [ne_of_gt hs, ne_of_gt hroot]

theorem exists_saddleWitness {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (hr : 0 < r) (hrle : r ≤ ell / 8)
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hprojX : ProjectionGeometry.IsEuclideanProjection P.X projectX)
    (hprojY : ProjectionGeometry.IsEuclideanProjection P.Y projectY)
    (z : EVec m) :
    Nonempty (SaddleWitness P ell r z) := by
  have hproj : ProjectionGeometry.IsEuclideanProjection
      (scaledSet ell P.X P.Y) (scaledProject ell projectX projectY) :=
    scaledProject_isProjection hP.ell_pos hprojX hprojY
  obtain ⟨u, hu, hnormal⟩ :=
    ProjectedVIExistence.exists_projectedVI_solution
      (WithinOperator.scaledSet_nonempty hP)
      (WithinOperator.scaledSet_closed hP)
      (WithinOperator.scaledSet_convex hP)
      hproj (saddleM_ge_one hP.ell_pos hr hrle)
      (saddleOperator_stronglyMonotoneOn hP hr hrle z)
      (saddleOperator_lipschitzOn hP hr hrle z)
  obtain ⟨hnx, hny⟩ := unscale_normal hP.ell_pos hu hnormal
  have hnx' := hnx.nonneg_smul (saddleSigma_pos hP.ell_pos hr).le
  have hny' := hny.nonneg_smul (saddleSigma_pos hP.ell_pos hr).le
  rw [scaledNormalX_eq hP.ell_pos hr P z u] at hnx'
  rw [scaledNormalY_eq hP.ell_pos hr P z u] at hny'
  exact ⟨{
    x := unscaleX ell u
    y := unscaleY ell u
    x_mem := hu.1
    y_mem := hu.2
    normalX := hnx'
    normalY := hny' }⟩

theorem SaddleWitness.primal_minimizes {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (_hr : 0 < r)
    {z : EVec m} (W : SaddleWitness P ell r z) :
    ∀ u ∈ P.X,
      P.f W.x W.y + ell * vecSq (W.x - z) ≤
        P.f u W.y + ell * vecSq (u - z) := by
  intro u hu
  let d := u - W.x
  have hsupp := WithinOperator.convexSupportX (r := r) hP z
    W.x_mem W.y_mem u hu
  have hn := W.normalX u hu
  change dot (-saddleX P ell z W.x W.y) d ≤ 0 at hn
  have hneg : dot (-saddleX P ell z W.x W.y) d =
      -dot (saddleX P ell z W.x W.y) d := by
    unfold dot
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.neg_apply]
    ring
  rw [hneg] at hn
  have hsaddle : dot (saddleX P ell z W.x W.y) d =
      dot (ClassOperator.gradXHat P ell z W.x W.y) d +
        ell * dot W.x d := by
    unfold saddleX dot
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsq := vecSq_translate u W.x
  have hsq' : vecSq u = vecSq W.x + 2 * dot W.x d + vecSq d := by
    simpa only [d] using hsq
  have hd0 := ProjectionGeometry.vecSq_nonneg d
  have hH :
      decurved P.f ell r z W.x W.y + ell / 2 * vecSq W.x ≤
        decurved P.f ell r z u W.y + ell / 2 * vecSq u := by
    rw [hsaddle] at hn
    change decurved P.f ell r z W.x W.y +
      dot (ClassOperator.gradXHat P ell z W.x W.y) d ≤
        decurved P.f ell r z u W.y at hsupp
    have held0 : 0 ≤ ell * vecSq d :=
      mul_nonneg hP.ell_pos.le hd0
    calc
      decurved P.f ell r z W.x W.y + ell / 2 * vecSq W.x ≤
          decurved P.f ell r z u W.y -
            dot (ClassOperator.gradXHat P ell z W.x W.y) d +
              ell / 2 * vecSq W.x := by linarith
      _ ≤ decurved P.f ell r z u W.y + ell * dot W.x d +
            ell / 2 * vecSq W.x := by linarith
      _ ≤ decurved P.f ell r z u W.y + ell / 2 * vecSq u := by
        rw [hsq']
        nlinarith
  rw [vecSq_sub_expand, vecSq_sub_expand]
  rw [decurved_eq, decurved_eq] at hH
  nlinarith

theorem SaddleWitness.dual_maximizes {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 < r)
    {z : EVec m} (W : SaddleWitness P ell r z) :
    IsMaximizerOn P.Y (fun x y => P.f x y - r / 2 * vecSq y)
      W.x W.y := by
  refine ⟨W.y_mem, ?_⟩
  intro v hv
  let d := v - W.y
  have hsupp := WithinOperator.concaveSupportY (r := r) hP z
    W.x_mem W.y_mem v hv
  have hn := W.normalY v hv
  have hsaddle : -saddleY P r W.x W.y =
      P.gradY W.x W.y - r • W.y := by
    ext i
    simp [saddleY, ClassOperator.gradYHat]
    ring
  rw [hsaddle] at hn
  change dot (P.gradY W.x W.y - r • W.y) d ≤ 0 at hn
  have hdot : dot (P.gradY W.x W.y - r • W.y) d =
      dot (P.gradY W.x W.y) d - r * dot W.y d := by
    unfold dot
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdot] at hn
  have hsq := vecSq_translate v W.y
  have hd0 := ProjectionGeometry.vecSq_nonneg d
  have hsupp' : P.f W.x v ≤ P.f W.x W.y +
      dot (P.gradY W.x W.y) d := by
    unfold ClassOperator.gradYHat at hsupp
    rw [decurved_eq, decurved_eq] at hsupp
    change P.f W.x v + ell / 2 * vecSq W.x -
        2 * ell * dot z W.x + ell * vecSq z ≤
      P.f W.x W.y + ell / 2 * vecSq W.x -
        2 * ell * dot z W.x + ell * vecSq z +
          dot (P.gradY W.x W.y) (v - W.y) at hsupp
    simpa only [d] using (show P.f W.x v ≤ P.f W.x W.y +
      dot (P.gradY W.x W.y) (v - W.y) by linarith)
  nlinarith [mul_nonneg hr.le hd0]

theorem SaddleWitness.isProxPoint {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 < r)
    {z : EVec m} (W : SaddleWitness P ell r z) :
    IsProxPoint P.X (DualRegularizedValueOn P.Y P.f r) ell z W.x := by
  refine ⟨W.x_mem, ?_⟩
  intro u hu
  have hmaxW := W.dual_maximizes hP hr
  obtain ⟨yu, hyu⟩ := WithinClass.regularized_maximum_attained hP u hu
  have hvalueW : DualRegularizedValueOn P.Y P.f r W.x =
      P.f W.x W.y - r / 2 * vecSq W.y := by
    unfold DualRegularizedValueOn
    exact value_eq_of_isMaximizerOn hmaxW
  have hvalueU : DualRegularizedValueOn P.Y P.f r u =
      P.f u yu - r / 2 * vecSq yu := by
    unfold DualRegularizedValueOn
    exact value_eq_of_isMaximizerOn hyu
  have hfixed := W.primal_minimizes hP hr u hu
  have hinner := hyu.2 W.y W.y_mem
  rw [hvalueW, hvalueU]
  nlinarith

def stationaryAt_of_class {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (hr : 0 < r) (hrle : r ≤ ell / 8)
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hprojX : ProjectionGeometry.IsEuclideanProjection P.X projectX)
    (hprojY : ProjectionGeometry.IsEuclideanProjection P.Y projectY)
    (hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) :
    StationaryAt P.X P.Y P.f ell r hexistsR z := by
  let W : SaddleWitness P ell r z :=
    Classical.choice (exists_saddleWitness hP hr hrle hprojX hprojY z)
  have hprox := W.isProxPoint hP hr
  have hxEq : selectedProx hexistsR z = W.x :=
    selectedProx_unique hP.ell_pos
      (WithinClass.regularizedValue_weaklyConvex hP) hexistsR hprox
  let yStar : P.Y := ⟨W.y, W.y_mem⟩
  let qStar : EVec m := (-ell) • selectedProx hexistsR z
  let wStar : EVec n := (-r) • W.y
  have hnormalX : IsEuclideanNormal P.X (selectedProx hexistsR z)
      (qStar - ClassOperator.gradXHat P ell z
        (selectedProx hexistsR z) W.y) := by
    rw [hxEq]
    have heq : qStar - ClassOperator.gradXHat P ell z W.x W.y =
        -saddleX P ell z W.x W.y := by
      ext i
      simp [qStar, saddleX, hxEq]
      ring
    rw [heq]
    exact W.normalX
  have hnormalY : IsEuclideanNormal P.Y W.y
      (wStar + ClassOperator.gradYHat P ell z
        (selectedProx hexistsR z) W.y) := by
    rw [hxEq]
    have heq : wStar + ClassOperator.gradYHat P ell z W.x W.y =
        -saddleY P r W.x W.y := by
      ext i
      simp [wStar, saddleY, ClassOperator.gradYHat]
    rw [heq]
    exact W.normalY
  have hsub : IsGammaSubgradient P.X P.Y (decurved P.f ell r z)
      qStar yStar (selectedProx hexistsR z) wStar := by
    apply gamma_subgradient (gammaBddAbove_of_class hP z)
      (selectedProx_spec hexistsR z).1
      (WithinOperator.convexSupportX (r := r) hP z
        (selectedProx_spec hexistsR z).1 W.y_mem)
      (WithinOperator.concaveSupportY (r := r) hP z
        (selectedProx_spec hexistsR z).1 W.y_mem)
      hnormalX hnormalY
  refine {
    qStar := qStar
    yStar := yStar
    wStar := wStar
    subgradient := hsub
    stationQ := ?_
    stationY := ?_ }
  · ext i
    simp only [qStar, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul]
    field_simp [ne_of_gt hP.ell_pos]
    ring
  · ext i
    simp [wStar, yStar]

/-! ## Proximal existence and the actual finite micro oracle -/

theorem regularized_dual_sq_bound {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y ∈ P.Y, vecSq y ≤ K := by
  obtain ⟨y0, hy0⟩ := hP.Y_nonempty
  let K := 2 * D ^ 2 + 2 * vecSq y0
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    exact add_nonneg (mul_nonneg (by norm_num) (sq_nonneg D))
      (mul_nonneg (by norm_num) (ProjectionGeometry.vecSq_nonneg y0))
  · intro y hy
    have hdiam := hP.dual_diameter y hy y0 hy0
    have hadd := ScaledOperator.vecSq_add_le_two (y - y0) y0
    have heq : (y - y0) + y0 = y := by module
    rw [heq] at hadd
    dsimp [K]
    nlinarith [ProjectionGeometry.vecSq_nonneg y0]

theorem regularizedValue_hasProxEverywhere_of_class {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) :
    HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell :=
  hP.regularizedValue_hasProxEverywhere hr

def chosenProjectX {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P) :
    EVec m → EVec m :=
  Classical.choose (ProjectionExistence.exists_euclideanProjection
    hP.X_nonempty hP.X_closed hP.X_convex)

def chosenProjectY {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P) :
    EVec n → EVec n :=
  Classical.choose (ProjectionExistence.exists_euclideanProjection
    hP.Y_nonempty hP.Y_closed hP.Y_convex)

theorem chosenProjectX_spec {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P) :
    ProjectionGeometry.IsEuclideanProjection P.X (chosenProjectX hP) :=
  Classical.choose_spec (ProjectionExistence.exists_euclideanProjection
    hP.X_nonempty hP.X_closed hP.X_convex)

theorem chosenProjectY_spec {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P) :
    ProjectionGeometry.IsEuclideanProjection P.Y (chosenProjectY hP) :=
  Classical.choose_spec (ProjectionExistence.exists_euclideanProjection
    hP.Y_nonempty hP.Y_closed hP.Y_convex)

def classMicroU {m n : Nat} (P : NCCInstance m n) (ell r : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (z : EVec m) (S : State m n) : Pair m n :=
  RelativeFOAM.projectedIterate
    (scaledProject ell projectX projectY)
    (scaledOperator ell r (qCenter ell r S) (yCenter ell r S)
      (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z))
    (M0 ^ 2)⁻¹
    (scaledCenter ell (qCenter ell r S) (yCenter ell r S))
    ProjectedMicro.feasibleMicroIterations

def classMicroB {m n : Nat} (P : NCCInstance m n) (ell r : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (z : EVec m) (S : State m n) : Pair m n :=
  RelativeFOAM.projectedB
    (scaledProject ell projectX projectY)
    (scaledOperator ell r (qCenter ell r S) (yCenter ell r S)
      (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z))
    (M0 ^ 2)⁻¹
    (scaledCenter ell (qCenter ell r S) (yCenter ell r S))
    (ProjectedMicro.feasibleMicroIterations - 1)

def classOracle {m n : Nat} (P : NCCInstance m n) (ell r : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (z : EVec m) (S : State m n) : MicroOutput m n :=
  decodeOutput ell (ClassOperator.gradXHat P ell z)
    (ClassOperator.gradYHat P ell z)
    (classMicroU P ell r projectX projectY z S)
    (classMicroB P ell r projectX projectY z S)

theorem classOracle_certificate {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hprojX : ProjectionGeometry.IsEuclideanProjection P.X projectX)
    (hprojY : ProjectionGeometry.IsEuclideanProjection P.Y projectY)
    (z : EVec m) (S : State m n) :
    (classOracle P ell r projectX projectY z S).xFast ∈ P.X ∧
      (classOracle P ell r projectX projectY z S).yFastNext ∈ P.Y ∧
      MicroNormalRelations P.X P.Y
        (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z)
        (classOracle P ell r projectX projectY z S) ∧
      RelativeResidual ell r S
        (classOracle P ell r projectX projectY z S) := by
  have cert := feasibleMicro_scaledOperator_of_closedConvex
    hP.ell_pos hr hrle
    (WithinOperator.scaledSet_nonempty hP)
    (WithinOperator.scaledSet_closed hP)
    (WithinOperator.scaledSet_convex hP)
    hprojX hprojY S
    (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z)
    (WithinOperator.saddleGradientMonotoneOn (r := r) hP z)
    (WithinOperator.jointGradientLipschitzOn hP z)
  dsimp only at cert
  have hx : (classOracle P ell r projectX projectY z S).xFast ∈ P.X := by
    simpa only [classOracle, classMicroU, classMicroB, decodeOutput] using
      cert.2.1.1
  have hy : (classOracle P ell r projectX projectY z S).yFastNext ∈ P.Y := by
    simpa only [classOracle, classMicroU, classMicroB, decodeOutput] using
      cert.2.1.2
  refine ⟨hx, hy, ?_, ?_⟩
  · simpa only [classOracle, classMicroU, classMicroB] using cert.2.2.1
  · simpa only [classOracle, classMicroU, classMicroB] using cert.2.2.2

theorem classOracle_feasible {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hprojX : ProjectionGeometry.IsEuclideanProjection P.X projectX)
    (hprojY : ProjectionGeometry.IsEuclideanProjection P.Y projectY)
    (z : EVec m) (S : State m n) :
    (classOracle P ell r projectX projectY z S).yFastNext ∈ P.Y :=
  (classOracle_certificate hP hr hrle hprojX hprojY z S).2.1

theorem classOracle_subgradient {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hprojX : ProjectionGeometry.IsEuclideanProjection P.X projectX)
    (hprojY : ProjectionGeometry.IsEuclideanProjection P.Y projectY)
    (z : EVec m) (S : State m n)
    (hy : (classOracle P ell r projectX projectY z S).yFastNext ∈ P.Y) :
    IsGammaSubgradient P.X P.Y (decurved P.f ell r z)
      (classOracle P ell r projectX projectY z S).qFastNext
      ⟨(classOracle P ell r projectX projectY z S).yFastNext, hy⟩
      (classOracle P ell r projectX projectY z S).xFast
      (classOracle P ell r projectX projectY z S).wFastNext := by
  have cert := classOracle_certificate hP hr hrle hprojX hprojY z S
  exact gamma_subgradient (gammaBddAbove_of_class hP z)
    cert.1
    (WithinOperator.convexSupportX (r := r) hP z cert.1 cert.2.1)
    (WithinOperator.concaveSupportY (r := r) hP z cert.1 cert.2.1)
    cert.2.2.1.1 cert.2.2.1.2

theorem classOracle_residual {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hprojX : ProjectionGeometry.IsEuclideanProjection P.X projectX)
    (hprojY : ProjectionGeometry.IsEuclideanProjection P.Y projectY)
    (z : EVec m) (S : State m n) :
    RelativeResidual ell r S
      (classOracle P ell r projectX projectY z S) :=
  (classOracle_certificate hP hr hrle hprojX hprojY z S).2.2.2

/-! ## Packaging all class data as the concrete outer system -/

/-- Assemble an `OuterSystem` when a particular proximal-existence witness is
already in scope.  The witness affects only the selected representative used
by the stationary field; every remaining component is constructed here. -/
def outerSystemOfClassWithProx {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell) :
    OuterSystem P.X P.Y P.f ell r hexistsR := by
  let projectX := chosenProjectX hP
  let projectY := chosenProjectY hP
  have hprojX : ProjectionGeometry.IsEuclideanProjection P.X projectX := by
    simpa only [projectX] using chosenProjectX_spec hP
  have hprojY : ProjectionGeometry.IsEuclideanProjection P.Y projectY := by
    simpa only [projectY] using chosenProjectY_spec hP
  let oracle : EVec m → ValidState (m := m) P.Y → MicroOutput m n :=
    fun z S => classOracle P ell r projectX projectY z S.1
  have horacleFeasible : ∀ z S, (oracle z S).yFastNext ∈ P.Y := by
    intro z S
    exact classOracle_feasible hP hr.le hrle hprojX hprojY z S.1
  refine {
    projectX := projectX
    project_spec := hprojX
    gamma_bounded := gammaBddAbove_of_class hP
    stationary := stationaryAt_of_class hP hr hrle hprojX hprojY hexistsR
    oracle := oracle
    oracle_feasible := horacleFeasible
    oracle_subgradient := ?_
    oracle_residual := ?_ }
  · intro z S
    exact classOracle_subgradient hP hr.le hrle hprojX hprojY z S.1
      (horacleFeasible z S)
  · intro z S
    exact classOracle_residual hP hr.le hrle hprojX hprojY z S.1

/-- The concrete outer system follows from the NC--C class itself.  In
particular, proximal existence, both projections, conjugate finiteness, the
stationary saddle witness, and the finite micro solver are all derived rather
than assumed. -/
def outerSystemOfClass {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : WithinClass ell D Delta P)
    (hr : 0 < r) (hrle : r ≤ ell / 8) :
    OuterSystem P.X P.Y P.f ell r
      (regularizedValue_hasProxEverywhere_of_class hP hr.le) :=
  outerSystemOfClassWithProx hP hr hrle
    (regularizedValue_hasProxEverywhere_of_class hP hr.le)

end

end NCC.Upper.WithinSystem
