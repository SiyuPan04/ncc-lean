import NCCLowerBoundVerification.WeakConvexity

/-!
# Strong proximal inequalities from weak convexity

This module supplies the analytic step used (but only cited informally) in
the proof of `ub:lem:smoothing-comparison`.  All squared distances are the
paper's Euclidean coordinate sum `vecSq`, so no conclusion depends on the
ambient sup norm carried by Lean's function type `Fin n → ℝ`.
-/

namespace NCCLowerBoundVerification
namespace Upper

noncomputable section

/-- The proximal objective with the paper's normalization. -/
def proxObjective {m : Nat} (phi : EVec m → ℝ) (ell : ℝ)
    (z u : EVec m) : ℝ :=
  phi u + ell * vecSq (u - z)

/-- Polarization identity for an affine combination, in the exact
sum-of-coordinate-squares geometry used throughout the development. -/
theorem vecSq_affine_sub {m : Nat} (u v z : EVec m) {a b : ℝ}
    (hab : a + b = 1) :
    vecSq (a • u + b • v - z) =
      a * vecSq (u - z) + b * vecSq (v - z) -
        a * b * vecSq (u - v) := by
  have hb : b = 1 - a := by linarith
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hb]
  ring

theorem vecSq_affine {m : Nat} (u v : EVec m) {a b : ℝ}
    (hab : a + b = 1) :
    vecSq (a • u + b • v) =
      a * vecSq u + b * vecSq v - a * b * vecSq (u - v) := by
  simpa using vecSq_affine_sub u v (0 : EVec m) hab

theorem vecSq_sub_comm {m : Nat} (u v : EVec m) :
    vecSq (u - v) = vecSq (v - u) := by
  unfold vecSq NCPLVerification.vecSq
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

/-- Weak convexity of `phi` makes its proximal objective strongly convex in
the explicit Jensen form needed below. -/
theorem proxObjective_strongJensen {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ}
    (hweak : IsWeaklyConvexOn ell X phi)
    {u v z : EVec m} (hu : u ∈ X) (hv : v ∈ X)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    proxObjective phi ell z (a • u + b • v) ≤
      a * proxObjective phi ell z u + b * proxObjective phi ell z v -
        ell / 2 * a * b * vecSq (u - v) := by
  have hconv := hweak.2 hu hv ha hb hab
  have hzero := vecSq_affine u v hab
  have hz := vecSq_affine_sub u v z hab
  unfold proxObjective quadraticCorrection at *
  simp only [smul_eq_mul] at hconv
  rw [hzero] at hconv
  rw [hz]
  nlinarith

/-- A minimizer of the proximal objective satisfies the sharp strong
minimizer inequality.  The proof takes an arbitrary interior point on the
segment and lets its weight tend to zero via the Archimedean epsilon lemma;
no differentiability or subgradient theorem is assumed. -/
theorem proxPoint_strongMinimizer {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    {z u : EVec m} (hu : IsProxPoint X phi ell z u) :
    ∀ v ∈ X,
      proxObjective phi ell z u + ell / 2 * vecSq (v - u) ≤
        proxObjective phi ell z v := by
  intro v hv
  have hdnonneg : 0 ≤ vecSq (v - u) := vecSq_nonneg _
  by_cases hd : vecSq (v - u) = 0
  · have hmin := hu.2 v hv
    unfold proxObjective
    rw [hd]
    linarith
  · have hdpos : 0 < vecSq (v - u) := lt_of_le_of_ne hdnonneg (Ne.symm hd)
    let c : ℝ := ell / 2 * vecSq (v - u)
    have hc : 0 < c := by
      dsimp [c]
      positivity
    apply le_of_forall_pos_le_add
    intro eps heps
    let b : ℝ := eps / (c + eps)
    let a : ℝ := 1 - b
    have hden : 0 < c + eps := add_pos hc heps
    have hbpos : 0 < b := div_pos heps hden
    have hblt : b < 1 := (div_lt_one hden).2 (by linarith)
    have ha : 0 ≤ a := by dsimp [a]; linarith
    have hb : 0 ≤ b := hbpos.le
    have hab : a + b = 1 := by dsimp [a]; ring
    let w : EVec m := a • u + b • v
    have hw : w ∈ X := hweak.1 hu.1 hv ha hb hab
    have hmin : proxObjective phi ell z u ≤ proxObjective phi ell z w := by
      exact hu.2 w hw
    have hjensen : proxObjective phi ell z w ≤
        a * proxObjective phi ell z u + b * proxObjective phi ell z v -
          a * b * c := by
      have h := proxObjective_strongJensen hweak hu.1 hv ha hb hab (z := z)
      rw [vecSq_sub_comm u v] at h
      dsimp [w]
      dsimp [c]
      convert h using 1 <;> ring
    have hsegment :
        proxObjective phi ell z u + a * c ≤ proxObjective phi ell z v := by
      nlinarith
    have hbc : b * c ≤ eps := by
      dsimp [b]
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [mul_pos heps heps]
    dsimp [c] at hsegment ⊢
    have hac : a * (ell / 2 * vecSq (v - u)) +
        b * (ell / 2 * vecSq (v - u)) = ell / 2 * vecSq (v - u) := by
      rw [← add_mul, hab, one_mul]
    dsimp [c] at hbc
    nlinarith

/-- The same conclusion in the expanded form used by the perturbation
comparison module. -/
theorem proxPoint_strongMinimizer_expanded {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    {z u v : EVec m} (hu : IsProxPoint X phi ell z u) (hv : v ∈ X) :
    phi u + ell * vecSq (u - z) + ell / 2 * vecSq (v - u) ≤
      phi v + ell * vecSq (v - z) := by
  exact proxPoint_strongMinimizer hell hweak hu v hv

end

end Upper
end NCCLowerBoundVerification
