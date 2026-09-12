import NCPLVerification.DelayBlock

/-!
# Perspective delay block and Euclidean dual scaling

The positive-scale and zero-scale branches are defined explicitly.  This
file proves the maximum and max-PL assertions of Lemma 5.2, as well as the
exact diagonal norm identity used later in the hard instance.
-/

namespace NCPLVerification

noncomputable section

def rescaleEVec {N : ℕ} (rho : ℝ) (u : EVec N) : EVec N :=
  fun i ↦ u i / rho

def perspectiveDelay (N : ℕ) (lambdaWall eta rho A : ℝ)
    (u : EVec N) : ℝ :=
  if 0 < rho then
    A * innerGamma (rescaleEVec rho u) -
      eta * rho ^ 2 * innerH N lambdaWall (rescaleEVec rho u)
  else
    -eta * lambdaWall * innerWallEnergy N u

def perspectiveGradient (N : ℕ) (lambdaWall eta rho A : ℝ)
    (u : EVec N) : EVec N :=
  if 0 < rho then
    fun i ↦ rho * delayGradient N lambdaWall eta (A / rho ^ 2)
      (rescaleEVec rho u) i
  else
    fun i ↦ 2 * eta * lambdaWall * innerD N i * negPart (u i)

/-- For every nonnegative scale, the perspective dual field retains the
one-coordinate discovery rule of the inner chain. -/
theorem perspectiveGradient_is_zeroChain (N : ℕ) (lambdaWall eta A : ℝ)
    {rho : ℝ} (hrho : 0 ≤ rho) :
    IsFirstOrderZeroChain (perspectiveGradient N lambdaWall eta rho A) := by
  rcases hrho.eq_or_lt with rfl | hrhopos
  · intro r u hu i hir
    have hui : u i = 0 := hu i (by omega)
    simp [perspectiveGradient, hui, negPart]
  · intro r u hu
    have hscaled : SupportedBelow r (rescaleEVec rho u) := by
      intro i hir
      simp [rescaleEVec, hu i hir]
    have hdelay := delayGradient_is_zeroChain N lambdaWall eta (A / rho ^ 2)
      r (rescaleEVec rho u) hscaled
    intro i hir
    rw [perspectiveGradient, if_pos hrhopos]
    rw [hdelay i hir]
    ring

theorem perspectiveDelay_pos {N : ℕ} {rho : ℝ} (hrho : 0 < rho)
    (lambdaWall eta A : ℝ) (u : EVec N) :
    perspectiveDelay N lambdaWall eta rho A u =
      rho ^ 2 * delayG N lambdaWall eta (A / rho ^ 2)
        (rescaleEVec rho u) := by
  rw [perspectiveDelay, if_pos hrho]
  unfold delayG
  field_simp

theorem perspectiveGradient_pos {N : ℕ} {rho : ℝ} (hrho : 0 < rho)
    (lambdaWall eta A : ℝ) (u : EVec N) :
    perspectiveGradient N lambdaWall eta rho A u =
      fun i ↦ rho * delayGradient N lambdaWall eta (A / rho ^ 2)
        (rescaleEVec rho u) i := by
  simp [perspectiveGradient, hrho]

theorem perspectiveDelay_zero (N : ℕ) (lambdaWall eta A : ℝ)
    (u : EVec N) :
    perspectiveDelay N lambdaWall eta 0 A u =
      -eta * lambdaWall * innerWallEnergy N u := by
  simp [perspectiveDelay]

theorem perspectiveGradient_zero (N : ℕ) (lambdaWall eta A : ℝ)
    (u : EVec N) :
    perspectiveGradient N lambdaWall eta 0 A u =
      fun i ↦ 2 * eta * lambdaWall * innerD N i * negPart (u i) := by
  simp [perspectiveGradient]

theorem innerWallEnergy_zero (N : ℕ) :
    innerWallEnergy N (fun _ ↦ 0) = 0 := by
  simp [innerWallEnergy, negPart]

theorem perspective_attains_max {N : ℕ} (hN : 0 < N)
    {lambdaWall eta rho A Amax : ℝ} (hrho : 0 ≤ rho)
    (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (hA : 0 ≤ A) (hAmax : A ≤ Amax * rho ^ 2) :
    ∃ u : EVec N, perspectiveDelay N lambdaWall eta rho A u = A := by
  rcases hrho.eq_or_lt with rfl | hrhopos
  · have hAzero : A = 0 := by
      have : A ≤ 0 := by simpa using hAmax
      linarith
    refine ⟨fun _ ↦ 0, ?_⟩
    rw [hAzero, perspectiveDelay_zero, innerWallEnergy_zero]
    ring
  · let u : EVec N := fun _ ↦ rho
    refine ⟨u, ?_⟩
    rw [perspectiveDelay_pos hrhopos]
    have hscaled : rescaleEVec rho u = innerAllOnes N := by
      funext i
      simp [rescaleEVec, u, innerAllOnes, ne_of_gt hrhopos]
    rw [hscaled, delayG_allOnes hN]
    field_simp

theorem perspective_le_A {N : ℕ} (hN : 0 < N)
    {lambdaWall eta rho A Amax : ℝ} (hrho : 0 ≤ rho)
    (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (hA : 0 ≤ A) (hAmax : A ≤ Amax * rho ^ 2)
    (u : EVec N) : perspectiveDelay N lambdaWall eta rho A u ≤ A := by
  rcases hrho.eq_or_lt with rfl | hrhopos
  · have hAzero : A = 0 := by
      have : A ≤ 0 := by simpa using hAmax
      linarith
    rw [hAzero, perspectiveDelay_zero]
    have hwall : 0 ≤ innerWallEnergy N u := by
      unfold innerWallEnergy
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (innerD_pos hN i).le (sq_nonneg _)
    have hprod : 0 ≤ eta * lambdaWall * innerWallEnergy N u :=
      mul_nonneg (mul_nonneg heta hlambda) hwall
    convert neg_nonpos.mpr hprod using 1 <;> ring
  · rw [perspectiveDelay_pos hrhopos]
    have ha0 : 0 ≤ A / rho ^ 2 := div_nonneg hA (sq_nonneg rho)
    have haMax' : A / rho ^ 2 ≤ Amax := by
      rw [div_le_iff₀ (sq_pos_of_pos hrhopos)]
      simpa [mul_comm] using hAmax
    have hdelay := delayG_le_a hN hlambda heta ha0
      (rescaleEVec rho u)
    have hrhosq := sq_nonneg rho
    calc
      rho ^ 2 * delayG N lambdaWall eta (A / rho ^ 2)
          (rescaleEVec rho u) ≤ rho ^ 2 * (A / rho ^ 2) :=
        mul_le_mul_of_nonneg_left hdelay hrhosq
      _ = A := by field_simp

theorem innerDualSq_perspectiveGradient_pos {N : ℕ} (hN : 0 < N)
    {rho : ℝ} (hrho : 0 < rho) (lambdaWall eta A : ℝ) (u : EVec N) :
    innerDualSq N (perspectiveGradient N lambdaWall eta rho A u) =
      rho ^ 2 * innerDualSq N
        (delayGradient N lambdaWall eta (A / rho ^ 2) (rescaleEVec rho u)) := by
  rw [perspectiveGradient_pos hrho]
  unfold innerDualSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem innerDualSq_perspectiveGradient_zero {N : ℕ} (hN : 0 < N)
    (lambdaWall eta A : ℝ) (u : EVec N) :
    innerDualSq N (perspectiveGradient N lambdaWall eta 0 A u) =
      4 * eta ^ 2 * lambdaWall ^ 2 * innerWallEnergy N u := by
  rw [perspectiveGradient_zero]
  unfold innerDualSq innerWallEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [ne_of_gt (innerD_pos hN i)]
  ring

/-- The common PL constant for both perspective branches. -/
def perspectivePLConstant (lambdaWall eta Amax : ℝ) : ℝ :=
  min (eta ^ 2 / (2 * (192 * Amax + 193 * eta)))
    (2 * eta * lambdaWall)

theorem perspectivePLConstant_nonneg {lambdaWall eta Amax : ℝ}
    (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta) (hAmax : 0 ≤ Amax) :
    0 ≤ perspectivePLConstant lambdaWall eta Amax := by
  unfold perspectivePLConstant
  exact le_min (by positivity) (by positivity)

/-- Lemma 5.2 max-PL assertion, including the exact `rho = 0` extension. -/
theorem perspective_delay_PL_field {N : ℕ} (hN2 : 2 ≤ N)
    {lambdaWall eta rho A Amax : ℝ} (hrho : 0 ≤ rho)
    (hlambda : 12 ≤ lambdaWall) (heta : 0 < eta)
    (hA : 0 ≤ A) (hAmax0 : 0 ≤ Amax) (hAmax : A ≤ Amax * rho ^ 2)
    (u : EVec N) :
    (1 : ℝ) / 2 * innerDualSq N
        (perspectiveGradient N lambdaWall eta rho A u) ≥
      perspectivePLConstant lambdaWall eta Amax / (N : ℝ) *
        (A - perspectiveDelay N lambdaWall eta rho A u) := by
  have hN : 0 < N := by omega
  have hNreal : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  rcases hrho.eq_or_lt with rfl | hrhopos
  · have hAzero : A = 0 := by
      have : A ≤ 0 := by simpa using hAmax
      linarith
    rw [hAzero, perspectiveDelay_zero,
      innerDualSq_perspectiveGradient_zero hN]
    have hwall : 0 ≤ innerWallEnergy N u := by
      unfold innerWallEnergy
      apply Finset.sum_nonneg
      intro i _
      exact mul_nonneg (innerD_pos hN i).le (sq_nonneg _)
    have hc : perspectivePLConstant lambdaWall eta Amax ≤
        2 * eta * lambdaWall := min_le_right _ _
    have hc0 := perspectivePLConstant_nonneg
      (by linarith : 0 ≤ lambdaWall) heta.le hAmax0
    have hlpos : 0 ≤ eta * lambdaWall :=
      mul_nonneg heta.le (by linarith)
    have hcoef : perspectivePLConstant lambdaWall eta Amax / (N : ℝ) *
        (eta * lambdaWall) ≤ 2 * eta ^ 2 * lambdaWall ^ 2 := by
      have hdiv : perspectivePLConstant lambdaWall eta Amax / (N : ℝ) ≤
          perspectivePLConstant lambdaWall eta Amax := by
        exact (div_le_self hc0 (by exact_mod_cast (show 1 ≤ N by omega)))
      have := mul_le_mul_of_nonneg_right (hdiv.trans hc) hlpos
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef hwall]
  · have ha0 : 0 ≤ A / rho ^ 2 := div_nonneg hA (sq_nonneg rho)
    have haMax' : A / rho ^ 2 ≤ Amax := by
      rw [div_le_iff₀ (sq_pos_of_pos hrhopos)]
      simpa [mul_comm] using hAmax
    have hbase := delay_block_PL_field hN2 hlambda heta ha0 haMax'
      (rescaleEVec rho u)
    have hgap0 : 0 ≤ A - perspectiveDelay N lambdaWall eta rho A u := by
      linarith [perspective_le_A hN hrho (by linarith : 0 ≤ lambdaWall)
        heta.le hA hAmax u]
    have hc : perspectivePLConstant lambdaWall eta Amax ≤
        eta ^ 2 / (2 * (192 * Amax + 193 * eta)) := min_le_left _ _
    rw [perspectiveDelay_pos hrhopos,
      innerDualSq_perspectiveGradient_pos hN hrhopos]
    have hrhosq : 0 < rho ^ 2 := sq_pos_of_pos hrhopos
    have hscaledGap :
        A - rho ^ 2 * delayG N lambdaWall eta (A / rho ^ 2)
            (rescaleEVec rho u) =
          rho ^ 2 *
            (A / rho ^ 2 - delayG N lambdaWall eta (A / rho ^ 2)
              (rescaleEVec rho u)) := by
      field_simp
    rw [hscaledGap]
    have hsmall : perspectivePLConstant lambdaWall eta Amax / (N : ℝ) *
        (A / rho ^ 2 - delayG N lambdaWall eta (A / rho ^ 2)
          (rescaleEVec rho u)) ≤
        (eta ^ 2 / (2 * (192 * Amax + 193 * eta))) / (N : ℝ) *
          (A / rho ^ 2 - delayG N lambdaWall eta (A / rho ^ 2)
            (rescaleEVec rho u)) := by
      have hgapBase : 0 ≤ A / rho ^ 2 -
          delayG N lambdaWall eta (A / rho ^ 2) (rescaleEVec rho u) := by
        linarith [delayG_le_a hN (by linarith : 0 ≤ lambdaWall) heta.le ha0
          (rescaleEVec rho u)]
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hc (by positivity)) hgapBase
    nlinarith [mul_le_mul_of_nonneg_left hsmall hrhosq.le,
      mul_le_mul_of_nonneg_left hbase hrhosq.le]

/-! ## Euclidean diagonal coordinates -/

def toWeightedCoordinates {N : ℕ} (y : EVec N) : EVec N :=
  fun i ↦ y i / Real.sqrt (innerD N i)

def fromWeightedCoordinates {N : ℕ} (u : EVec N) : EVec N :=
  fun i ↦ Real.sqrt (innerD N i) * u i

def toEuclideanGradient {N : ℕ} (g : EVec N) : EVec N :=
  fun i ↦ g i / Real.sqrt (innerD N i)

def euclideanSq {N : ℕ} (v : EVec N) : ℝ := ∑ i : Fin N, v i ^ 2

theorem euclideanSq_toEuclideanGradient {N : ℕ} (hN : 0 < N)
    (g : EVec N) :
    euclideanSq (toEuclideanGradient g) = innerDualSq N g := by
  unfold euclideanSq toEuclideanGradient innerDualSq
  apply Finset.sum_congr rfl
  intro i _
  have hd := innerD_pos hN i
  rw [div_pow, Real.sq_sqrt hd.le]

theorem toWeightedCoordinates_eq_zero_iff {N : ℕ} (hN : 0 < N)
    (y : EVec N) (i : Fin N) :
    toWeightedCoordinates y i = 0 ↔ y i = 0 := by
  unfold toWeightedCoordinates
  simp [ne_of_gt (Real.sqrt_pos.2 (innerD_pos hN i))]

theorem toWeightedCoordinates_fromWeighted {N : ℕ} (hN : 0 < N)
    (u : EVec N) :
    toWeightedCoordinates (fromWeightedCoordinates u) = u := by
  funext i
  unfold toWeightedCoordinates fromWeightedCoordinates
  field_simp [ne_of_gt (Real.sqrt_pos.2 (innerD_pos hN i))]

theorem fromWeightedCoordinates_toWeighted {N : ℕ} (hN : 0 < N)
    (y : EVec N) :
    fromWeightedCoordinates (toWeightedCoordinates y) = y := by
  funext i
  unfold toWeightedCoordinates fromWeightedCoordinates
  field_simp [ne_of_gt (Real.sqrt_pos.2 (innerD_pos hN i))]

end

end NCPLVerification
