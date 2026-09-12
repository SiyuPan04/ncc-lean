import NCC.Extensions.ProjectedReadout

/-!
# GS output conversion without a bounded dual domain

Only the primal proximal quadratic is present in the actual objective.
Consequently this conversion has no dual regularization bias and no
diameter assumption. The saddle point is a proof witness, not an input
to the projected output rule.
-/
namespace NCC.Extensions.NCSCGSReadout
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open RelativeFOAM ProjectionGeometry ScaledOperator
open NCC.Model NCC.Upper.WithinSystem ProjectedReadout

theorem operator_lipschitz {m n : ℕ} {P : NCCInstance m n} {L : ℝ}
    (hsmooth : JointlySmoothWithin L P) (z : EVec m) :
    ∀ u ∈ pairSet P.X P.Y, ∀ v ∈ pairSet P.X P.Y,
      vecSq (saddlePair P L 0 z u - saddlePair P L 0 z v) ≤
        10 * L ^ 2 * vecSq (u - v) := by
  intro u hu v hv
  let dx := unpackX u - unpackX v
  let dy := unpackY u - unpackY v
  let gx := P.gradX (unpackX u) (unpackY u) - P.gradX (unpackX v) (unpackY v)
  let gy := P.gradY (unpackX u) (unpackY u) - P.gradY (unpackX v) (unpackY v)
  have hs : vecSq gx + vecSq gy ≤ L ^ 2 * (vecSq dx + vecSq dy) := by
    exact hsmooth (unpackX u) hu.1 (unpackY u) hu.2
      (unpackX v) hv.1 (unpackY v) hv.2
  have hform : saddlePair P L 0 z u - saddlePair P L 0 z v =
      pack (gx + (2 * L) • dx) (-gy) := by
    unfold saddlePair
    rw [← pack_sub]
    congr 1 <;> ext i <;>
      simp only [saddleX, saddleY, ClassOperator.gradXHat, ClassOperator.gradYHat,
        gx, gy, dx, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
        smul_eq_mul] <;> ring
  have huform : vecSq (u - v) = vecSq dx + vecSq dy := by
    rw [← pack_unpack u, ← pack_unpack v, ← pack_sub, vecSq_pack]
  rw [hform, vecSq_pack, huform, Tracking.vecSq_neg]
  have ht := vecSq_add_le_two gx ((2 * L) • dx)
  rw [vecSq_smul] at ht
  have hx := mul_nonneg (sq_nonneg L) (ProjectionGeometry.vecSq_nonneg dx)
  have hy := mul_nonneg (sq_nonneg L) (ProjectionGeometry.vecSq_nonneg dy)
  nlinarith [ProjectionGeometry.vecSq_nonneg gx, ProjectionGeometry.vecSq_nonneg gy]

/-- One original saddle-oracle reply and two projections give actual
normal-cone GS witnesses. The hypotheses are numerical proximity and
primal displacement bounds, with no bound on the dual solution's norm. -/
theorem readout_hasGSWitness {m n : ℕ} {P : NCCInstance m n}
    {L eps : ℝ} (hL : 0 < L) (heps : 0 < eps)
    (hsmooth : JointlySmoothWithin L P)
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hpX : IsEuclideanProjection P.X projectX)
    (hpY : IsEuclideanProjection P.Y projectY)
    {z : EVec m} (W : NCC.Upper.WithinSystem.SaddleWitness P L 0 z)
    {u : Pair m n} (hu : u ∈ pairSet P.X P.Y)
    (hprecision : 50000 * L ^ 2 * vecSq (u - pack W.x W.y) ≤ eps ^ 2)
    (hanchor : 64 * L ^ 2 * vecSq (z - W.x) ≤ eps ^ 2) :
    HasGSWitness P eps
      (unpackX (readoutPair P L 0 projectX projectY z u))
      (unpackY (readoutPair P L 0 projectX projectY z u)) := by
  let A := saddlePair P L 0 z
  let w := readoutPair P L 0 projectX projectY z u
  let b := L • (u - L⁻¹ • A u - w)
  have hstar : pack W.x W.y ∈ pairSet P.X P.Y := by
    simpa only [pairSet, Set.mem_setOf_eq, unpackX_pack, unpackY_pack] using
      And.intro W.x_mem W.y_mem
  have hnstar : IsEuclideanNormal (pairSet P.X P.Y) (pack W.x W.y)
      (-A (pack W.x W.y)) := by
    have hn := normal_pair W.normalX W.normalY
    have heq : pack (-saddleX P L z W.x W.y) (-saddleY P 0 W.x W.y) =
        -A (pack W.x W.y) := by
      dsimp only [A, saddlePair]
      simp only [unpackX_pack, unpackY_pack]
      simpa only [neg_one_smul] using
        (pack_smul (-1 : ℝ) (saddleX P L z W.x W.y) (saddleY P 0 W.x W.y))
    rwa [heq] at hn
  obtain ⟨hw, hb, hclose, hres⟩ := residual_of_proximity
    (pairProject_spec hpX hpY) hL (operator_lipschitz hsmooth z) hstar hu hnstar
  change w ∈ pairSet P.X P.Y at hw
  change IsEuclideanNormal (pairSet P.X P.Y) w b at hb
  change vecSq (w - pack W.x W.y) ≤ 22 * vecSq (u - pack W.x W.y) at hclose
  change vecSq (A w + b) ≤ 1012 * L ^ 2 * vecSq (u - pack W.x W.y) at hres
  obtain ⟨hnx, hny⟩ := normal_unpair hw hb
  have hsquares (v : Pair m n) :
      vecSq (unpackX v) + vecSq (unpackY v) = vecSq v := by
    rw [← vecSq_pack, pack_unpack]
  have hresX : vecSq (unpackX (A w + b)) ≤ vecSq (A w + b) := by
    rw [← hsquares]
    linarith [ProjectionGeometry.vecSq_nonneg (unpackY (A w + b))]
  have hresY : vecSq (unpackY (A w + b)) ≤ vecSq (A w + b) := by
    rw [← hsquares]
    linarith [ProjectionGeometry.vecSq_nonneg (unpackX (A w + b))]
  have hcloseX : vecSq (unpackX w - W.x) ≤ 22 * vecSq (u - pack W.x W.y) := by
    have heq : vecSq (w - pack W.x W.y) =
        vecSq (unpackX w - W.x) + vecSq (unpackY w - W.y) := by
      rw [← pack_unpack w, ← pack_sub, vecSq_pack]
      simp only [unpackX_pack, unpackY_pack]
    rw [heq] at hclose
    linarith [ProjectionGeometry.vecSq_nonneg (unpackY w - W.y)]
  have hza : vecSq (z - unpackX w) ≤
      2 * vecSq (z - W.x) + 44 * vecSq (u - pack W.x W.y) := by
    have hh := square_sub_le (z - W.x) (unpackX w - W.x)
    have heq : (z - W.x) - (unpackX w - W.x) = z - unpackX w := by module
    rw [heq] at hh
    linarith
  have hformX : P.gradX (unpackX w) (unpackY w) + unpackX b =
      unpackX (A w + b) + (2 * L) • (z - unpackX w) := by
    ext i
    simp only [A, saddlePair, saddleX, ClassOperator.gradXHat, unpackX,
      pack, Fin.append_left, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hformY : -P.gradY (unpackX w) (unpackY w) + unpackY b =
      unpackY (A w + b) := by
    ext i
    simp only [A, saddlePair, saddleY, ClassOperator.gradYHat, unpackY,
      pack, Fin.append_right, Pi.add_apply, Pi.neg_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨heps, hw.1, hw.2, unpackX b, unpackY b, hnx, hny, ?_, ?_⟩
  · change vecSq (P.gradX (unpackX w) (unpackY w) + unpackX b) ≤ _
    rw [hformX]
    have ht := vecSq_add_le_two (unpackX (A w + b)) ((2 * L) • (z - unpackX w))
    rw [vecSq_smul] at ht
    have hzbound := mul_le_mul_of_nonneg_left hza (sq_nonneg L)
    nlinarith [sq_nonneg eps]
  · change vecSq (-P.gradY (unpackX w) (unpackY w) + unpackY b) ≤ _
    rw [hformY]
    nlinarith [mul_nonneg (sq_nonneg L) (ProjectionGeometry.vecSq_nonneg (u - pack W.x W.y))]

end
end NCC.Extensions.NCSCGSReadout
