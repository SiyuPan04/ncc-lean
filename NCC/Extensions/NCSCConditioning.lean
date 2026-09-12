import NCC.Extensions.NCSC
import NCCLowerBoundVerification.Upper.ProjectionGeometry

/-! The usual condition-number inequality is automatic on a nontrivial
dual feasible set. Degenerate singleton domains require a convention. -/
namespace NCC.Extensions.NCSC
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper

theorem strongConcavity_le_smoothness {m n : ℕ} {ell mu Delta : ℝ}
    {P : NCCInstance m n} (h : NCSCClass ell mu Delta P)
    {y v : EVec n} (hy : y ∈ P.Y) (hv : v ∈ P.Y) (hne : y ≠ v) : mu ≤ ell := by
  let d := v - y
  let g := P.gradY 0 y - P.gradY 0 v
  have hd0 : 0 < vecSq d := by
    have hnn := ProjectionGeometry.vecSq_nonneg d
    have hn : vecSq d ≠ 0 := by
      intro heq
      have hd := (ProjectionGeometry.vecSq_eq_zero_iff d).mp heq
      exact hne (sub_eq_zero.mp hd).symm
    exact lt_of_le_of_ne hnn (Ne.symm hn)
  have h1 := dual_strong_support h h.primal_origin hy hv
  have h2 := dual_strong_support h h.primal_origin hv hy
  have hdrev : vecSq (y - v) = vecSq d := vecSq_sub_comm y v
  have hdot : eDot (P.gradY 0 y) (v - y) + eDot (P.gradY 0 v) (y - v) =
      eDot g d := by
    simp only [g, d, eDot, Pi.sub_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hstrong : mu * vecSq d ≤ eDot g d := by
    rw [hdrev] at h2
    change P.f 0 v ≤ P.f 0 y + eDot (P.gradY 0 y) (v - y) - mu / 2 * vecSq d at h1
    linarith
  have hs := h.jointly_smooth 0 h.primal_origin y hy 0 h.primal_origin v hv
  have hg : vecSq g ≤ ell ^ 2 * vecSq d := by
    have hz : vecSq (0 : EVec m) = 0 := by simp [vecSq, NCPLVerification.vecSq]
    simp only [jointSq, sub_self, hz, zero_add] at hs
    rw [hdrev] at hs
    linarith [ProjectionGeometry.vecSq_nonneg (P.gradX 0 y - P.gradX 0 v)]
  have ht := TrackingAnalytic.two_dot_le_sq_add_sq g (ell • d)
  rw [vecSq_smul] at ht
  have hscale : PointwiseConjugate.dot g (ell • d) = ell * eDot g d := by
    simp only [PointwiseConjugate.dot, eDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hscale] at ht
  have hm := mul_le_mul_of_nonneg_left hstrong h.ell_pos.le
  have hpos : 0 < ell * vecSq d := mul_pos h.ell_pos hd0
  nlinarith

theorem dual_set_eq_origin_of_smoothness_lt {m n : ℕ} {ell mu Delta : ℝ}
    {P : NCCInstance m n} (h : NCSCClass ell mu Delta P) (hlt : ell < mu) :
    P.Y = {0} := by
  ext y
  constructor
  · intro hy
    by_contra hn
    have hne : y ≠ 0 := by simpa only [Set.mem_singleton_iff] using hn
    exact (not_le.mpr hlt) (strongConcavity_le_smoothness h hy h.dual_origin hne)
  · intro hy
    have heq : y = 0 := Set.mem_singleton_iff.mp hy
    simpa only [heq] using h.dual_origin

end
end NCC.Extensions.NCSC
