import NCC.Extensions.NCSCMoreau

/-! A larger internal proximal coefficient does not change the claimed
OS convention: its actual residual controls the source-envelope gradient.
The comparison is proved for the genuine proximal minimizers. -/
namespace NCC.Extensions.NCSC
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper

theorem proxObjective_general_strongJensen {d : ℕ} {X : Set (EVec d)}
    {phi : EVec d → ℝ} {ell L : ℝ} (hweak : IsWeaklyConvexOn ell X phi)
    {u v z : EVec d} (hu : u ∈ X) (hv : v ∈ X)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    proxObjective phi L z (a • u + b • v) ≤
      a * proxObjective phi L z u + b * proxObjective phi L z v -
        (L - ell / 2) * a * b * vecSq (u - v) := by
  have hc := hweak.2 hu hv ha hb hab
  have hzero := vecSq_affine u v hab
  have hz := vecSq_affine_sub u v z hab
  unfold proxObjective quadraticCorrection at *
  simp only [smul_eq_mul] at hc
  rw [hzero] at hc
  rw [hz]
  nlinarith

theorem proxPoint_general_strongMinimizer {d : ℕ} {X : Set (EVec d)}
    {phi : EVec d → ℝ} {ell L : ℝ} (hL : ell / 2 < L)
    (hweak : IsWeaklyConvexOn ell X phi)
    {z u : EVec d} (hu : IsProxPoint X phi L z u) :
    ∀ v ∈ X,
      proxObjective phi L z u + (L - ell / 2) * vecSq (v - u) ≤
        proxObjective phi L z v := by
  intro v hv
  have hdnonneg : 0 ≤ vecSq (v - u) := vecSq_nonneg _
  by_cases hd : vecSq (v - u) = 0
  · have hmin := hu.2 v hv
    unfold proxObjective
    rw [hd]
    linarith
  · have hdpos : 0 < vecSq (v - u) := lt_of_le_of_ne hdnonneg (Ne.symm hd)
    let c : ℝ := (L - ell / 2) * vecSq (v - u)
    have hc : 0 < c := mul_pos (sub_pos.mpr hL) hdpos
    apply le_of_forall_pos_le_add
    intro eps heps
    let b : ℝ := eps / (c + eps)
    let a : ℝ := 1 - b
    have hden : 0 < c + eps := add_pos hc heps
    have hbpos : 0 < b := div_pos heps hden
    have hblt : b < 1 := (div_lt_one hden).2 (by linarith)
    have ha : 0 ≤ a := by dsimp [a]; linarith
    have hab : a + b = 1 := by dsimp [a]; ring
    let w : EVec d := a • u + b • v
    have hw : w ∈ X := hweak.1 hu.1 hv ha hbpos.le hab
    have hmin : proxObjective phi L z u ≤ proxObjective phi L z w := hu.2 w hw
    have hjensen : proxObjective phi L z w ≤
        a * proxObjective phi L z u + b * proxObjective phi L z v - a * b * c := by
      have hj := proxObjective_general_strongJensen (L := L) hweak hu.1 hv ha hbpos.le hab (z := z)
      rw [vecSq_sub_comm u v] at hj
      dsimp [w, c]
      convert hj using 1
      ring
    have hsegment : proxObjective phi L z u + a * c ≤ proxObjective phi L z v := by
      nlinarith
    have hbc : b * c ≤ eps := by
      dsimp [b]
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [mul_pos heps heps]
    have hac : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    change proxObjective phi L z u + c ≤ proxObjective phi L z v + eps
    linarith

/-- The squared residual at the source coefficient is at most four
times the squared residual at a larger internal coefficient. -/
theorem proximal_residual_parameter_comparison {d : ℕ} {X : Set (EVec d)}
    {phi : EVec d → ℝ} {ell L : ℝ} (hell : 0 < ell) (hL : ell ≤ L)
    (hweak : IsWeaklyConvexOn ell X phi) {z u v : EVec d}
    (hu : IsProxPoint X phi ell z u) (hv : IsProxPoint X phi L z v) :
    vecSq ((2 * ell) • (z - u)) ≤ 4 * vecSq ((2 * L) • (z - v)) := by
  let a := z - u
  let b := z - v
  have h1 := proxPoint_strongMinimizer hell hweak hu v hv.1
  have h2 := proxPoint_general_strongMinimizer (by linarith : ell / 2 < L) hweak hv u hu.1
  have ha : vecSq (u - z) = vecSq a := vecSq_sub_comm u z
  have hb : vecSq (v - z) = vecSq b := vecSq_sub_comm v z
  have huv : vecSq (v - u) = vecSq a + vecSq b - 2 * eDot a b := by
    simp only [a, b, vecSq, NCPLVerification.vecSq, eDot, Pi.sub_apply,
      Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hvu : vecSq (u - v) = vecSq (v - u) := vecSq_sub_comm u v
  unfold proxObjective at h1 h2
  rw [ha, hb, huv] at h1
  rw [ha, hb, hvu, huv] at h2
  have hcomparison : ell * vecSq a + (2 * L - ell) * vecSq b ≤ 2 * L * eDot a b := by
    linarith
  have hyoung := TrackingAnalytic.two_dot_le_sq_add_sq ((ell / 2) • a) (L • b)
  rw [vecSq_smul, vecSq_smul] at hyoung
  have hdot : PointwiseConjugate.dot ((ell / 2) • a) (L • b) =
      ell / 2 * L * eDot a b := by
    simp only [PointwiseConjugate.dot, eDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdot] at hyoung
  have hm := mul_le_mul_of_nonneg_left hcomparison hell.le
  have hn := mul_nonneg (by nlinarith : 0 ≤ ell * (2 * L - ell)) (vecSq_nonneg b)
  have hs : ell ^ 2 * vecSq a ≤ 4 * L ^ 2 * vecSq b := by nlinarith
  rw [vecSq_smul, vecSq_smul]
  change (2 * ell) ^ 2 * vecSq a ≤ 4 * ((2 * L) ^ 2 * vecSq b)
  nlinarith

theorem gradient_le_internal_residual {m n : ℕ} {ell mu Delta L : ℝ}
    {P : NCCInstance m n} (h : NCSCClass ell mu Delta P) (hL : ell ≤ L)
    {z v : EVec m} (hv : IsProxPoint P.X (ValueOn P.Y P.f) L z v) :
    vecSq (gradient h z) ≤ 4 * vecSq ((2 * L) • (z - v)) := by
  rw [gradient_formula]
  exact proximal_residual_parameter_comparison h.ell_pos hL (value_weaklyConvex h)
    (prox_spec h z) hv

theorem isOS_of_internal_residual {m n : ℕ} {ell mu Delta L eps : ℝ}
    {P : NCCInstance m n} (h : NCSCClass ell mu Delta P) (hL : ell ≤ L)
    (heps : 0 < eps) {z v : EVec m} (hz : z ∈ P.X)
    (hv : IsProxPoint P.X (ValueOn P.Y P.f) L z v)
    (hres : 4 * vecSq ((2 * L) • (z - v)) ≤ eps ^ 2) : IsOS h eps z :=
  ⟨heps, hz, (gradient_le_internal_residual h hL hv).trans hres⟩

end
end NCC.Extensions.NCSC
