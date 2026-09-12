import NCPLVerification.Scaling
import NCPLVerification.HardJointDifferentiability
import NCPLVerification.HardPrimalSmoothness

/-!
# The scaled hard instance belongs to the NC--PL class

This file carries the actual joint Fréchet derivative and the dimension-free
smoothness estimate through the scaling used in Section 8 of the article.
-/

namespace NCPLVerification

noncomputable section

def scaledHardGradX (T N : Nat) (lambdaWall eta scale amp : ℝ)
    (x : EVec T) (y : EVec (T * N)) : EVec T :=
  scaleEVec (amp / scale)
    (hardGradX T N lambdaWall eta
      (rescaleEVec scale x) (rescaleEVec scale y))

theorem hasFDerivAt_rescaleProd {dx dy : Nat} (scale : ℝ)
    (x : EVec dx) (y : EVec dy) :
    HasFDerivAt
      (fun p : EVec dx × EVec dy ↦
        (rescaleEVec scale p.1, rescaleEVec scale p.2))
      (((1 / scale) • ContinuousLinearMap.fst ℝ (EVec dx) (EVec dy)).prod
        ((1 / scale) • ContinuousLinearMap.snd ℝ (EVec dx) (EVec dy))) (x, y) := by
  have hx := (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, y))).const_smul
    (1 / scale)
  have hy := (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y))).const_smul
    (1 / scale)
  have hxy := hx.prodMk hy
  convert hxy using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  all_goals try { rfl }
  · funext p
    apply Prod.ext <;> funext i
    · simp [rescaleEVec, div_eq_mul_inv, mul_comm]
    · simp [rescaleEVec, div_eq_mul_inv, mul_comm]

theorem differentiable_scaledHardF_joint {T N : Nat} (hN : 0 < N)
    (lambdaWall eta scale amp : ℝ) :
    Differentiable ℝ
      (Function.uncurry (scaledHardF T N lambdaWall eta scale amp)) := by
  intro p
  rcases p with ⟨x, y⟩
  have hR := hasFDerivAt_rescaleProd (dx := T) (dy := T * N) scale x y
  have hbase := differentiableAt_hardF_joint hN lambdaWall eta
    (rescaleEVec scale x) (rescaleEVec scale y)
  have hc := hbase.hasFDerivAt.comp (x, y) hR
  have hs := hc.const_mul amp
  convert hs.differentiableAt using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  all_goals try { rfl }

theorem scaledHardF_representsJointGradient {T N : Nat} (hN : 0 < N)
    (lambdaWall eta scale amp : ℝ) :
    RepresentsJointGradient (scaledHardF T N lambdaWall eta scale amp)
      (scaledHardGradX T N lambdaWall eta scale amp)
      (scaledHardGradY T N lambdaWall eta scale amp) := by
  constructor
  · exact differentiable_scaledHardF_joint hN lambdaWall eta scale amp
  · intro x y hx hy
    let B := Function.uncurry (hardF T N lambdaWall eta)
    let R : EVec T × EVec (T * N) → EVec T × EVec (T * N) := fun p ↦
      (rescaleEVec scale p.1, rescaleEVec scale p.2)
    let R' : (EVec T × EVec (T * N)) →L[ℝ]
        (EVec T × EVec (T * N)) :=
      ((1 / scale) • ContinuousLinearMap.fst ℝ (EVec T) (EVec (T * N))).prod
        ((1 / scale) • ContinuousLinearMap.snd ℝ (EVec T) (EVec (T * N)))
    have hR : HasFDerivAt R R' (x, y) := by
      exact hasFDerivAt_rescaleProd scale x y
    have hbase : HasFDerivAt B (fderiv ℝ B (R (x, y))) (R (x, y)) := by
      apply DifferentiableAt.hasFDerivAt
      exact differentiableAt_hardF_joint hN lambdaWall eta
        (rescaleEVec scale x) (rescaleEVec scale y)
    have hc := hbase.comp (x, y) hR
    have hs := hc.const_mul amp
    have hscaled : HasFDerivAt
        (Function.uncurry (scaledHardF T N lambdaWall eta scale amp))
        (amp • (fderiv ℝ B (R (x, y))).comp R') (x, y) := by
      convert hs using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      all_goals try { rfl }
    rw [hscaled.fderiv]
    simp only [smul_apply, ContinuousLinearMap.comp_apply]
    have hrep := (hardF_representsJointGradient hN lambdaWall eta).2
      (rescaleEVec scale x) (rescaleEVec scale y)
      ((1 / scale) • hx) ((1 / scale) • hy)
    change amp * (fderiv ℝ B (R (x, y)))
        ((1 / scale) • hx, (1 / scale) • hy) = _
    change amp * (fderiv ℝ B
        (rescaleEVec scale x, rescaleEVec scale y))
        ((1 / scale) • hx, (1 / scale) • hy) = _
    rw [hrep]
    unfold scaledHardGradX scaledHardGradY scaleEVec
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      ring

theorem rescaleEVec_eq_scaleEVec {m : Nat} (scale : ℝ) (z : EVec m) :
    rescaleEVec scale z = scaleEVec (1 / scale) z := by
  funext i
  simp [rescaleEVec, scaleEVec, div_eq_mul_inv]
  ring

theorem rescaleEVec_sub {m : Nat} (scale : ℝ) (z z' : EVec m) :
    rescaleEVec scale z - rescaleEVec scale z' =
      rescaleEVec scale (z - z') := by
  funext i
  simp [rescaleEVec]
  ring

theorem vecSq_rescaleEVec {m : Nat} (scale : ℝ) (z : EVec m) :
    vecSq (rescaleEVec scale z) = (1 / scale) ^ 2 * vecSq z := by
  rw [rescaleEVec_eq_scaleEVec, vecSq_scaleEVec]

theorem jointSq_scaleEVec {dx dy : Nat} (c : ℝ)
    (x : EVec dx) (y : EVec dy) :
    jointSq (scaleEVec c x) (scaleEVec c y) = c ^ 2 * jointSq x y := by
  unfold jointSq
  rw [vecSq_scaleEVec, vecSq_scaleEVec]
  ring

theorem jointSq_rescaleEVec {dx dy : Nat} (scale : ℝ)
    (x : EVec dx) (y : EVec dy) :
    jointSq (rescaleEVec scale x) (rescaleEVec scale y) =
      (1 / scale) ^ 2 * jointSq x y := by
  unfold jointSq
  rw [vecSq_rescaleEVec, vecSq_rescaleEVec]
  ring

def scaledHardSmoothL (lambdaWall eta scale amp : ℝ) : ℝ :=
  amp / scale ^ 2 * hardJointSmoothL lambdaWall eta

theorem scaledHardSmoothL_nonneg (lambdaWall eta : ℝ)
    {scale amp : ℝ} (hscale : scale ≠ 0) (hamp : 0 ≤ amp) :
    0 ≤ scaledHardSmoothL lambdaWall eta scale amp := by
  unfold scaledHardSmoothL
  exact mul_nonneg (div_nonneg hamp (sq_nonneg scale))
    (hardJointSmoothL_nonneg lambdaWall eta)

theorem scaledHardF_isJointlySmooth {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (heta : |eta| ≤ 1)
    {scale amp : ℝ} (hscale : scale ≠ 0) (hamp : 0 ≤ amp) :
    IsJointlySmooth (scaledHardSmoothL lambdaWall eta scale amp)
      (scaledHardGradX T N lambdaWall eta scale amp)
      (scaledHardGradY T N lambdaWall eta scale amp) := by
  intro x y x' y'
  let xr := rescaleEVec scale x
  let xr' := rescaleEVec scale x'
  let yr := rescaleEVec scale y
  let yr' := rescaleEVec scale y'
  let gx := hardGradX T N lambdaWall eta xr yr -
    hardGradX T N lambdaWall eta xr' yr'
  let gy := hardGradY T N lambdaWall eta xr yr -
    hardGradY T N lambdaWall eta xr' yr'
  have hgx : scaledHardGradX T N lambdaWall eta scale amp x y -
      scaledHardGradX T N lambdaWall eta scale amp x' y' =
      scaleEVec (amp / scale) gx := by
    funext i
    simp [scaledHardGradX, scaleEVec, gx, xr, xr', yr, yr']
    ring
  have hgy : scaledHardGradY T N lambdaWall eta scale amp x y -
      scaledHardGradY T N lambdaWall eta scale amp x' y' =
      scaleEVec (amp / scale) gy := by
    funext i
    simp [scaledHardGradY, scaleEVec, gy, xr, xr', yr, yr']
    ring
  have hbase := hardF_isJointlySmooth hN lambdaWall eta heta xr yr xr' yr'
  have hinput : jointSq (xr - xr') (yr - yr') =
      (1 / scale) ^ 2 * jointSq (x - x') (y - y') := by
    rw [rescaleEVec_sub, rescaleEVec_sub]
    exact jointSq_rescaleEVec scale (x - x') (y - y')
  rw [hinput] at hbase
  rw [hgx, hgy, jointSq_scaleEVec]
  have hmul := mul_le_mul_of_nonneg_left hbase (sq_nonneg (amp / scale))
  calc
    (amp / scale) ^ 2 * jointSq gx gy ≤
        (amp / scale) ^ 2 *
          (hardJointSmoothL lambdaWall eta ^ 2 *
            ((1 / scale) ^ 2 * jointSq (x - x') (y - y'))) := hmul
    _ = scaledHardSmoothL lambdaWall eta scale amp ^ 2 *
          jointSq (x - x') (y - y') := by
      unfold scaledHardSmoothL
      field_simp [hscale]

theorem scaledHardF_NCPLClass {T N : Nat} (hN2 : 2 ≤ N)
    {lambdaWall eta scale amp : ℝ}
    (hlambda : 12 ≤ lambdaWall) (heta : 0 < eta) (heta1 : |eta| ≤ 1)
    (hscale : 0 < scale) (hamp : 0 ≤ amp) :
    NCPLClass
      (scaledHardSmoothL lambdaWall eta scale amp)
      ((amp / scale ^ 2) *
        (perspectivePLConstant lambdaWall eta carmonAmax / (N : ℝ)))
      (amp * (T : ℝ) * carmonTermCap)
      (scaledHardF T N lambdaWall eta scale amp)
      (scaledHardGradX T N lambdaWall eta scale amp)
      (scaledHardGradY T N lambdaWall eta scale amp) := by
  have hN : 0 < N := by omega
  have hlambda0 : 0 ≤ lambdaWall := by linarith
  have hpl0 : 0 ≤ perspectivePLConstant lambdaWall eta carmonAmax :=
    perspectivePLConstant_nonneg hlambda0 heta.le carmonAmax_nonneg
  refine
    { L_nonneg := scaledHardSmoothL_nonneg lambdaWall eta hscale.ne' hamp
      mu_nonneg := ?_
      Delta_nonneg := ?_
      gradient_representation := scaledHardF_representsJointGradient hN
        lambdaWall eta scale amp
      jointly_smooth := scaledHardF_isJointlySmooth hN lambdaWall eta heta1
        hscale.ne' hamp
      maximum_attained := ?_
      maximization_PL := ?_
      envelope_bddBelow := scaledHardF_envelope_bddBelow hN hlambda0 heta.le
        hscale.ne' hamp
      initial_gap := scaledHardF_initial_gap hN hlambda0 heta.le
        hscale.ne' hamp }
  · positivity
  · exact mul_nonneg (mul_nonneg hamp (Nat.cast_nonneg T)) carmonTermCap_nonneg
  · intro x
    exact scaledHardF_isMaximizer hN hlambda0 heta.le hscale.ne' hamp x
  · intro x y
    exact scaledHardF_dual_PL hN2 hlambda heta hscale hamp x y

end

end NCPLVerification
