import NCPLVerification.InnerSmoothness
import NCPLVerification.Perspective
import NCPLVerification.Definitions

/-!
# Uniform dual smoothness of the perspective block

This module proves the fixed-parameter part of the perspective smoothness
lemma.  The estimate is first established in the weighted coordinates and is
then transported exactly to the Euclidean diagonal coordinates.  Its
constant is independent of the inner-chain length.
-/

namespace NCPLVerification

noncomputable section

theorem innerDualSq_smul {N : Nat} (c : ℝ) (v : EVec N) :
    innerDualSq N (c • v) = c ^ 2 * innerDualSq N v := by
  unfold innerDualSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem innerPrimalSq_smul {N : Nat} (c : ℝ) (v : EVec N) :
    innerPrimalSq N (c • v) = c ^ 2 * innerPrimalSq N v := by
  unfold innerPrimalSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem innerDualSq_add_le_two {N : Nat} (hN : 0 < N)
    (v w : EVec N) :
    innerDualSq N (v + w) ≤ 2 * (innerDualSq N v + innerDualSq N w) := by
  unfold innerDualSq
  rw [mul_add, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hd := innerD_pos hN i
  simp only [Pi.add_apply]
  field_simp [hd.ne']
  nlinarith [sq_nonneg (v i - w i)]

/-- The terminal reward field is uniformly Lipschitz in the weighted metric.
The terminal metric weight is exactly one. -/
theorem innerGammaField_weighted_lipschitz {N : Nat} (hN : 0 < N)
    (z w : EVec N) :
    innerDualSq N (innerGammaField N z - innerGammaField N w) ≤
      36 * innerPrimalSq N (z - w) := by
  unfold innerDualSq innerPrimalSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let last : Fin N := ⟨N - 1, Nat.sub_lt hN (by omega)⟩
  by_cases hi : i = last
  · subst i
    rw [innerD_terminal hN]
    simp only [innerGammaField, hN, ↓reduceDIte, last,
      Pi.sub_apply, div_one, one_mul]
    have hs := sigmaDeriv_abs_sub_le (z last) (w last)
    have hsq : (sigmaDeriv (z last) - sigmaDeriv (w last)) ^ 2 ≤
        36 * (z last - w last) ^ 2 := by
      calc
        (sigmaDeriv (z last) - sigmaDeriv (w last)) ^ 2 =
            |sigmaDeriv (z last) - sigmaDeriv (w last)| ^ 2 := by
          rw [sq_abs]
        _ ≤ (6 * |z last - w last|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hs 2
        _ = 36 * (z last - w last) ^ 2 := by
          rw [mul_pow, sq_abs]
          norm_num
    exact hsq
  · dsimp [last] at hi
    have hz : innerGammaField N z i = 0 := by
      simp [innerGammaField, hN, hi]
    have hw : innerGammaField N w i = 0 := by
      simp [innerGammaField, hN, hi]
    simp only [Pi.sub_apply]
    rw [hz, hw]
    simp only [sub_self, pow_two, zero_mul, zero_div]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (innerD_pos hN i).le
        (mul_self_nonneg (z i - w i)))

def perspectiveDualSmoothCoeff (lambdaWall eta Amax : ℝ) : ℝ :=
  72 * Amax ^ 2 +
    2 * eta ^ 2 * (225 + 4 * |lambdaWall|) ^ 2

theorem perspectiveDualSmoothCoeff_nonneg
    (lambdaWall eta Amax : ℝ) :
    0 ≤ perspectiveDualSmoothCoeff lambdaWall eta Amax := by
  unfold perspectiveDualSmoothCoeff
  positivity

theorem delayGradient_weighted_lipschitz {N : Nat} (hN : 0 < N)
    {lambdaWall eta a Amax : ℝ} (ha0 : 0 ≤ a) (ha : a ≤ Amax)
    (z w : EVec N) :
    innerDualSq N
        (delayGradient N lambdaWall eta a z -
          delayGradient N lambdaWall eta a w) ≤
      perspectiveDualSmoothCoeff lambdaWall eta Amax *
        innerPrimalSq N (z - w) := by
  let dg : EVec N := innerGammaField N z - innerGammaField N w
  let dh : EVec N := innerGradient N lambdaWall z -
    innerGradient N lambdaWall w
  have hfield :
      delayGradient N lambdaWall eta a z -
          delayGradient N lambdaWall eta a w =
        a • dg + (-eta) • dh := by
    funext i
    simp [delayGradient, dg, dh]
    ring
  rw [hfield]
  have hadd := innerDualSq_add_le_two hN (a • dg) ((-eta) • dh)
  rw [innerDualSq_smul, innerDualSq_smul] at hadd
  have hg := innerGammaField_weighted_lipschitz hN z w
  have hh := innerGradient_weighted_lipschitz hN lambdaWall z w
  have hA0 : 0 ≤ Amax := ha0.trans ha
  have haSq : a ^ 2 ≤ Amax ^ 2 := by nlinarith
  have hP0 := innerPrimalSq_nonneg hN (z - w)
  have hgamma : a ^ 2 * innerDualSq N dg ≤
      36 * Amax ^ 2 * innerPrimalSq N (z - w) := by
    calc
      a ^ 2 * innerDualSq N dg ≤
          a ^ 2 * (36 * innerPrimalSq N (z - w)) :=
        mul_le_mul_of_nonneg_left hg (sq_nonneg a)
      _ ≤ 36 * Amax ^ 2 * innerPrimalSq N (z - w) := by
        nlinarith
  have hinner : (-eta) ^ 2 * innerDualSq N dh ≤
      eta ^ 2 * (225 + 4 * |lambdaWall|) ^ 2 *
        innerPrimalSq N (z - w) := by
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg eta)
    simpa only [dh, neg_sq, mul_assoc] using hm
  unfold perspectiveDualSmoothCoeff
  nlinarith

/-- Fixed-parameter weighted smoothness of the full perspective field. -/
theorem perspectiveGradient_weighted_lipschitz {N : Nat} (hN : 0 < N)
    {lambdaWall eta rho A Amax : ℝ} (hrho : 0 ≤ rho)
    (hA : 0 ≤ A) (hAmax0 : 0 ≤ Amax) (hAmax : A ≤ Amax * rho ^ 2)
    (u v : EVec N) :
    innerDualSq N
        (perspectiveGradient N lambdaWall eta rho A u -
          perspectiveGradient N lambdaWall eta rho A v) ≤
      perspectiveDualSmoothCoeff lambdaWall eta Amax *
        innerPrimalSq N (u - v) := by
  rcases hrho.eq_or_lt with rfl | hrhopos
  · rw [perspectiveGradient_zero, perspectiveGradient_zero]
    let d : EVec N := fun i ↦ negPart (u i) - negPart (v i)
    have hfield :
        (fun i ↦ 2 * eta * lambdaWall * innerD N i * negPart (u i)) -
            (fun i ↦ 2 * eta * lambdaWall * innerD N i * negPart (v i)) =
          fun i ↦ 2 * eta * lambdaWall * innerD N i * d i := by
      funext i
      simp [d]
      ring
    rw [hfield]
    unfold innerDualSq innerPrimalSq
    have hpoint :
        (∑ i : Fin N,
            (2 * eta * lambdaWall * innerD N i * d i) ^ 2 /
              innerD N i) ≤
          (4 * eta ^ 2 * lambdaWall ^ 2) *
            ∑ i : Fin N, innerD N i * (u - v) i ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hd := innerD_pos hN i
      have hneg := negPart_abs_sub_le (u i) (v i)
      have hdsq : d i ^ 2 ≤ (u i - v i) ^ 2 := by
        dsimp [d]
        calc
          (negPart (u i) - negPart (v i)) ^ 2 =
              |negPart (u i) - negPart (v i)| ^ 2 := by rw [sq_abs]
          _ ≤ |u i - v i| ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) hneg 2
          _ = (u i - v i) ^ 2 := sq_abs _
      change
        (2 * eta * lambdaWall * innerD N i * d i) ^ 2 /
            innerD N i ≤
          4 * eta ^ 2 * lambdaWall ^ 2 *
            (innerD N i * (u i - v i) ^ 2)
      calc
        (2 * eta * lambdaWall * innerD N i * d i) ^ 2 /
            innerD N i =
          (4 * eta ^ 2 * lambdaWall ^ 2 * innerD N i) * d i ^ 2 := by
            field_simp [hd.ne']
            ring
        _ ≤ (4 * eta ^ 2 * lambdaWall ^ 2 * innerD N i) *
            (u i - v i) ^ 2 :=
          mul_le_mul_of_nonneg_left hdsq
            (mul_nonneg
              (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg eta))
                (sq_nonneg lambdaWall)) hd.le)
        _ = 4 * eta ^ 2 * lambdaWall ^ 2 *
            (innerD N i * (u i - v i) ^ 2) := by ring
    have hcoef : 4 * eta ^ 2 * lambdaWall ^ 2 ≤
        perspectiveDualSmoothCoeff lambdaWall eta Amax := by
      unfold perspectiveDualSmoothCoeff
      nlinarith [sq_abs lambdaWall, abs_nonneg lambdaWall,
        sq_nonneg eta, sq_nonneg Amax]
    have hsum0 : 0 ≤ ∑ i : Fin N, innerD N i * (u - v) i ^ 2 :=
      Finset.sum_nonneg fun i _ ↦
        mul_nonneg (innerD_pos hN i).le (sq_nonneg ((u - v) i))
    exact hpoint.trans (mul_le_mul_of_nonneg_right hcoef hsum0)
  · let z := rescaleEVec rho u
    let w := rescaleEVec rho v
    let a := A / rho ^ 2
    have ha0 : 0 ≤ a := div_nonneg hA (sq_nonneg rho)
    have ha : a ≤ Amax := by
      apply (div_le_iff₀ (sq_pos_of_pos hrhopos)).2
      simpa [a, mul_comm] using hAmax
    have hbase := delayGradient_weighted_lipschitz hN
      (lambdaWall := lambdaWall) (eta := eta) ha0 ha z w
    rw [perspectiveGradient_pos hrhopos,
      perspectiveGradient_pos hrhopos]
    have hdiff :
        (fun i ↦ rho * delayGradient N lambdaWall eta a z i) -
            (fun i ↦ rho * delayGradient N lambdaWall eta a w i) =
          rho • (delayGradient N lambdaWall eta a z -
            delayGradient N lambdaWall eta a w) := by
      funext i
      simp
      ring
    rw [hdiff, innerDualSq_smul]
    have hprimal : rho ^ 2 * innerPrimalSq N (z - w) =
        innerPrimalSq N (u - v) := by
      unfold innerPrimalSq z w rescaleEVec
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change rho ^ 2 *
          (innerD N i * (u i / rho - v i / rho) ^ 2) =
        innerD N i * (u i - v i) ^ 2
      field_simp [hrhopos.ne']
    calc
      rho ^ 2 * innerDualSq N
          (delayGradient N lambdaWall eta a z -
            delayGradient N lambdaWall eta a w) ≤
          rho ^ 2 *
            (perspectiveDualSmoothCoeff lambdaWall eta Amax *
              innerPrimalSq N (z - w)) :=
        mul_le_mul_of_nonneg_left hbase (sq_nonneg rho)
      _ = perspectiveDualSmoothCoeff lambdaWall eta Amax *
          innerPrimalSq N (u - v) := by rw [← hprimal]; ring

theorem innerPrimalSq_toWeighted_sub {N : Nat} (hN : 0 < N)
    (y y' : EVec N) :
    innerPrimalSq N
        (toWeightedCoordinates y - toWeightedCoordinates y') =
      vecSq (y - y') := by
  unfold innerPrimalSq vecSq toWeightedCoordinates
  apply Finset.sum_congr rfl
  intro i _
  have hd := innerD_pos hN i
  have hs := Real.sqrt_pos.2 hd
  rw [← Real.sq_sqrt hd.le]
  change Real.sqrt (innerD N i) ^ 2 *
      (y i / Real.sqrt (innerD N i) -
        y' i / Real.sqrt (innerD N i)) ^ 2 =
    (y i - y' i) ^ 2
  field_simp [hs.ne']

theorem vecSq_toEuclideanGradient_sub {N : Nat} (hN : 0 < N)
    (g g' : EVec N) :
    vecSq (toEuclideanGradient g - toEuclideanGradient g') =
      innerDualSq N (g - g') := by
  unfold vecSq toEuclideanGradient innerDualSq
  apply Finset.sum_congr rfl
  intro i _
  have hd := innerD_pos hN i
  rw [← Real.sq_sqrt hd.le]
  change
    (g i / Real.sqrt (innerD N i) -
      g' i / Real.sqrt (innerD N i)) ^ 2 =
      (g i - g' i) ^ 2 / Real.sqrt (innerD N i) ^ 2
  field_simp [Real.sqrt_ne_zero'.2 hd]

/-- Fixed-parameter smoothness in the article's ordinary Euclidean dual
coordinates. -/
theorem perspectiveEuclideanGradient_lipschitz {N : Nat} (hN : 0 < N)
    {lambdaWall eta rho A Amax : ℝ} (hrho : 0 ≤ rho)
    (hA : 0 ≤ A) (hAmax0 : 0 ≤ Amax) (hAmax : A ≤ Amax * rho ^ 2)
    (y y' : EVec N) :
    vecSq
        (toEuclideanGradient
            (perspectiveGradient N lambdaWall eta rho A
              (toWeightedCoordinates y)) -
          toEuclideanGradient
            (perspectiveGradient N lambdaWall eta rho A
              (toWeightedCoordinates y'))) ≤
      perspectiveDualSmoothCoeff lambdaWall eta Amax * vecSq (y - y') := by
  rw [vecSq_toEuclideanGradient_sub hN]
  have h := perspectiveGradient_weighted_lipschitz hN
    (lambdaWall := lambdaWall) (eta := eta) hrho hA hAmax0 hAmax
    (toWeightedCoordinates y) (toWeightedCoordinates y')
  rwa [innerPrimalSq_toWeighted_sub hN] at h

end

end NCPLVerification
