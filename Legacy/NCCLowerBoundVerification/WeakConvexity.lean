import NCCLowerBoundVerification.Basic

/-!
# Weak convexity of a maximized value

This module isolates the pointwise-supremum step in Lemma 2.6 of the paper.
The remaining analytic step—deriving weak convexity of every fixed-dual
section from the jointly Lipschitz gradient—is kept as a separate proof
obligation rather than hidden in the definition of the function class.
-/

namespace NCCLowerBoundVerification

noncomputable section

def quadraticCorrection {m : Nat} (ell : ℝ) (x : EVec m) : ℝ :=
  ell / 2 * vecSq x

def IsWeaklyConvexOn {m : Nat} (ell : ℝ) (X : Set (EVec m))
    (phi : EVec m → ℝ) : Prop :=
  ConvexOn ℝ X (fun x ↦ phi x + quadraticCorrection ell x)

theorem vecSq_nonneg {m : Nat} (x : EVec m) : 0 ≤ vecSq x := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i)

theorem vecSq_pos_of_ne_zero {m : Nat} {x : EVec m} (hx : x ≠ 0) :
    0 < vecSq x := by
  rw [Function.ne_iff] at hx
  obtain ⟨i, hi⟩ := hx
  unfold vecSq NCPLVerification.vecSq
  apply Finset.sum_pos'
  · exact fun j _ ↦ sq_nonneg (x j)
  · exact ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero (by simpa using hi)⟩

/-- Euclidean midpoint identity, stated using the paper's explicit sum-of-
squares norm so it is independent of Lean's ambient norm on function types. -/
theorem vecSq_midpoint_sub {m : Nat} (u v x : EVec m) :
    vecSq (((1 : ℝ) / 2) • u + ((1 : ℝ) / 2) • v - x) =
      (1 : ℝ) / 2 * vecSq (u - x) +
      (1 : ℝ) / 2 * vecSq (v - x) -
      (1 : ℝ) / 4 * vecSq (u - v) := by
  unfold vecSq NCPLVerification.vecSq
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem le_valueOn_of_mem {m n : Nat} {X : Set (EVec m)}
    {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ}
    (hmax : ∀ x ∈ X, ∃ y, IsMaximizerOn Y f x y)
    {x : EVec m} (hx : x ∈ X) {y : EVec n} (hy : y ∈ Y) :
    f x y ≤ ValueOn Y f x := by
  obtain ⟨z, hz⟩ := hmax x hx
  rw [value_eq_of_isMaximizerOn hz]
  exact hz.2 y hy

/-- A pointwise maximum of functions sharing the same quadratic convexifying
correction is weakly convex with that correction. -/
theorem value_weaklyConvexOn_of_sections {m n : Nat}
    {ell : ℝ} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ}
    (hX : Convex ℝ X)
    (hmax : ∀ x ∈ X, ∃ y, IsMaximizerOn Y f x y)
    (hsections : ∀ y ∈ Y,
      IsWeaklyConvexOn ell X (fun x ↦ f x y)) :
    IsWeaklyConvexOn ell X (ValueOn Y f) := by
  refine ⟨hX, ?_⟩
  intro x hx z hz a b ha hb hab
  have hcombo : a • x + b • z ∈ X := hX hx hz ha hb hab
  obtain ⟨y, hy⟩ := hmax (a • x + b • z) hcombo
  change ValueOn Y f (a • x + b • z) +
      quadraticCorrection ell (a • x + b • z) ≤
    a • (ValueOn Y f x + quadraticCorrection ell x) +
      b • (ValueOn Y f z + quadraticCorrection ell z)
  rw [value_eq_of_isMaximizerOn hy]
  have hsection := (hsections y hy.1).2 hx hz ha hb hab
  have hxy : f x y ≤ ValueOn Y f x :=
    le_valueOn_of_mem hmax hx hy.1
  have hzy : f z y ≤ ValueOn Y f z :=
    le_valueOn_of_mem hmax hz hy.1
  simp only [smul_eq_mul] at hsection ⊢
  exact hsection.trans (by gcongr)

theorem IsNCCClass.value_weaklyConvexOn_of_sections {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P)
    (hsections : ∀ y ∈ P.Y,
      IsWeaklyConvexOn ell P.X (fun x ↦ P.f x y)) :
    IsWeaklyConvexOn ell P.X (ValueOn P.Y P.f) :=
  NCCLowerBoundVerification.value_weaklyConvexOn_of_sections
    hP.X_convex hP.maximum_attained hsections

/-- The proximal subproblem used in Definition 2.5 has at most one minimizer.
This is the uniqueness half of Lemma 2.6; existence is proved separately from
closedness, lower semicontinuity, and coercivity. -/
theorem proxPoint_unique_of_weaklyConvexOn {m : Nat}
    {ell : ℝ} {X : Set (EVec m)} {phi : EVec m → ℝ} {x u v : EVec m}
    (hell : 0 < ell) (hweak : IsWeaklyConvexOn ell X phi)
    (hu : IsProxPoint X phi ell x u)
    (hv : IsProxPoint X phi ell x v) : u = v := by
  by_contra huv
  let w : EVec m := ((1 : ℝ) / 2) • u + ((1 : ℝ) / 2) • v
  have hw : w ∈ X := hweak.1 hu.1 hv.1 (by norm_num) (by norm_num) (by norm_num)
  have hconv :
      phi w + quadraticCorrection ell w ≤
        (1 : ℝ) / 2 * (phi u + quadraticCorrection ell u) +
          (1 : ℝ) / 2 * (phi v + quadraticCorrection ell v) := by
    have hwc : ConvexOn ℝ X (fun q ↦ phi q + quadraticCorrection ell q) := hweak
    dsimp [w]
    simpa only [smul_eq_mul] using
      hwc.2 hu.1 hv.1 (by norm_num) (by norm_num) (by norm_num)
  have hmid0 := vecSq_midpoint_sub u v (0 : EVec m)
  have hmidx := vecSq_midpoint_sub u v x
  have hminu := hu.2 w hw
  have hminv := hv.2 w hw
  have hdiff : 0 < vecSq (u - v) := by
    apply vecSq_pos_of_ne_zero
    exact sub_ne_zero.mpr huv
  change vecSq (w - 0) = _ at hmid0
  change vecSq (w - x) = _ at hmidx
  unfold quadraticCorrection at hconv
  dsimp [w] at hmid0 hmidx
  have hstrong :
      phi w + ell * vecSq (w - x) ≤
        (1 : ℝ) / 2 * (phi u + ell * vecSq (u - x)) +
        (1 : ℝ) / 2 * (phi v + ell * vecSq (v - x)) -
        ell / 8 * vecSq (u - v) := by
    dsimp [w] at hconv ⊢
    simp only [sub_zero] at hmid0
    nlinarith
  have havg_le :
      (1 : ℝ) / 2 * (phi u + ell * vecSq (u - x)) +
        (1 : ℝ) / 2 * (phi v + ell * vecSq (v - x)) ≤
      phi w + ell * vecSq (w - x) := by
    nlinarith
  have : ell / 8 * vecSq (u - v) ≤ 0 := by
    linarith
  nlinarith

end

end NCCLowerBoundVerification
