import NCPLVerification.HardInstance
import NCPLVerification.CarmonSmoothness

/-!
# Scaling the unscaled hard instance

This file formalizes Section 8's change of variables.  The amplitude and
length scale are kept as parameters so the algebra can be reused verbatim for
the article's choices.
-/

namespace NCPLVerification

noncomputable section

def scaleEVec {m : Nat} (c : ℝ) (z : EVec m) : EVec m :=
  fun i ↦ c * z i

@[simp] theorem rescaleEVec_scaleEVec {m : Nat} {c : ℝ} (hc : c ≠ 0)
    (z : EVec m) :
    rescaleEVec c (scaleEVec c z) = z := by
  funext i
  unfold rescaleEVec scaleEVec
  field_simp [hc]

@[simp] theorem scaleEVec_rescaleEVec {m : Nat} {c : ℝ} (hc : c ≠ 0)
    (z : EVec m) :
    scaleEVec c (rescaleEVec c z) = z := by
  funext i
  unfold rescaleEVec scaleEVec
  field_simp [hc]

theorem vecSq_scaleEVec {m : Nat} (c : ℝ) (z : EVec m) :
    vecSq (scaleEVec c z) = c ^ 2 * vecSq z := by
  unfold vecSq scaleEVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def scaledHardF (T N : Nat) (lambdaWall eta scale amp : ℝ)
    (x : EVec T) (y : EVec (T * N)) : ℝ :=
  amp * hardF T N lambdaWall eta
    (rescaleEVec scale x) (rescaleEVec scale y)

def scaledHardGradY (T N : Nat) (lambdaWall eta scale amp : ℝ)
    (x : EVec T) (y : EVec (T * N)) : EVec (T * N) :=
  scaleEVec (amp / scale)
    (hardGradY T N lambdaWall eta
      (rescaleEVec scale x) (rescaleEVec scale y))

def scaledEnvelopeGradient (T : Nat) (scale amp : ℝ)
    (x : EVec T) : EVec T :=
  scaleEVec (amp / scale) (carmonGradient T (rescaleEVec scale x))

theorem scaledHardF_isMaximizer {T N : Nat} (hN : 0 < N)
    {lambdaWall eta scale amp : ℝ}
    (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (hscale : scale ≠ 0) (hamp : 0 ≤ amp) (x : EVec T) :
    ∃ y : EVec (T * N),
      IsMaximizer (scaledHardF T N lambdaWall eta scale amp) x y := by
  obtain ⟨u, hu⟩ := hardF_isMaximizer hN hlambda heta (rescaleEVec scale x)
  let y := scaleEVec scale u
  refine ⟨y, ?_⟩
  intro v
  unfold scaledHardF
  rw [rescaleEVec_scaleEVec hscale]
  exact mul_le_mul_of_nonneg_left (hu (rescaleEVec scale v)) hamp

theorem scaledHardF_envelope_eq {T N : Nat} (hN : 0 < N)
    {lambdaWall eta scale amp : ℝ}
    (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (hscale : scale ≠ 0) (hamp : 0 ≤ amp) (x : EVec T) :
    Envelope (scaledHardF T N lambdaWall eta scale amp) x =
      amp * carmonF T (rescaleEVec scale x) := by
  obtain ⟨y, hy⟩ := scaledHardF_isMaximizer hN hlambda heta hscale hamp x
  rw [envelope_eq_of_isMaximizer hy]
  unfold scaledHardF
  have hbase := hardF_envelope_eq_carmonF hN hlambda heta
    (rescaleEVec scale x)
  obtain ⟨u, hu⟩ := hardF_isMaximizer hN hlambda heta (rescaleEVec scale x)
  have hvalue : hardF T N lambdaWall eta (rescaleEVec scale x) u =
      carmonF T (rescaleEVec scale x) := by
    rw [← hbase, envelope_eq_of_isMaximizer hu]
  have hyu := hy (scaleEVec scale u)
  unfold scaledHardF at hyu
  rw [rescaleEVec_scaleEVec hscale, hvalue] at hyu
  have huy := hu (rescaleEVec scale y)
  have hle : hardF T N lambdaWall eta (rescaleEVec scale x)
      (rescaleEVec scale y) ≤ carmonF T (rescaleEVec scale x) := by
    exact huy.trans_eq hvalue
  exact le_antisymm (mul_le_mul_of_nonneg_left hle hamp) hyu

theorem vecSq_scaledHardGradY (T N : Nat)
    (lambdaWall eta scale amp : ℝ) (x : EVec T) (y : EVec (T * N)) :
    vecSq (scaledHardGradY T N lambdaWall eta scale amp x y) =
      (amp / scale) ^ 2 *
        vecSq (hardGradY T N lambdaWall eta
          (rescaleEVec scale x) (rescaleEVec scale y)) := by
  unfold scaledHardGradY
  exact vecSq_scaleEVec _ _

theorem scaledHardF_dual_PL {T N : Nat} (hN2 : 2 ≤ N)
    {lambdaWall eta scale amp : ℝ}
    (hlambda : 12 ≤ lambdaWall) (heta : 0 < eta)
    (hscale : 0 < scale) (hamp : 0 ≤ amp)
    (x : EVec T) (y : EVec (T * N)) :
    (1 : ℝ) / 2 * vecSq
        (scaledHardGradY T N lambdaWall eta scale amp x y) ≥
      (amp / scale ^ 2) *
        (perspectivePLConstant lambdaWall eta carmonAmax / (N : ℝ)) *
        (Envelope (scaledHardF T N lambdaWall eta scale amp) x -
          scaledHardF T N lambdaWall eta scale amp x y) := by
  have hN : 0 < N := by omega
  have hwall0 : 0 ≤ lambdaWall := le_trans (by norm_num) hlambda
  let xr := rescaleEVec scale x
  let yr := rescaleEVec scale y
  have hbase := hardF_dual_PL (T := T) hN2 hlambda heta xr yr
  have henv := scaledHardF_envelope_eq hN hwall0 heta.le hscale.ne' hamp x
  have hbaseEnv := hardF_envelope_eq_carmonF hN hwall0 heta.le xr
  have hgap0 : 0 ≤ Envelope (hardF T N lambdaWall eta) xr -
      hardF T N lambdaWall eta xr yr := by
    obtain ⟨v, hv⟩ := hardF_isMaximizer hN hwall0 heta.le xr
    rw [envelope_eq_of_isMaximizer hv]
    linarith [hv yr]
  have hfactor0 : 0 ≤ (amp / scale) ^ 2 := sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hbase hfactor0
  rw [vecSq_scaledHardGradY, henv]
  unfold scaledHardF
  dsimp [xr, yr] at hbaseEnv hmul ⊢
  rw [hbaseEnv] at hmul
  field_simp [hscale.ne'] at hmul ⊢
  nlinarith

theorem scaledHardF_envelope_bddBelow {T N : Nat} (hN : 0 < N)
    {lambdaWall eta scale amp : ℝ}
    (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (hscale : scale ≠ 0) (hamp : 0 ≤ amp) :
    BddBelow (Set.range
      (Envelope (scaledHardF T N lambdaWall eta scale amp))) := by
  refine ⟨-amp * (T : ℝ) * carmonTermCap, ?_⟩
  rintro _ ⟨x, rfl⟩
  rw [scaledHardF_envelope_eq hN hlambda heta hscale hamp]
  have h := carmonF_lower T (rescaleEVec scale x)
  have hm := mul_le_mul_of_nonneg_left h hamp
  nlinarith

theorem scaledHardF_initial_gap {T N : Nat} (hN : 0 < N)
    {lambdaWall eta scale amp : ℝ}
    (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (hscale : scale ≠ 0) (hamp : 0 ≤ amp) :
    Envelope (scaledHardF T N lambdaWall eta scale amp) 0 -
        sInf (Set.range
          (Envelope (scaledHardF T N lambdaWall eta scale amp))) ≤
      amp * (T : ℝ) * carmonTermCap := by
  have hbdd := scaledHardF_envelope_bddBelow (T := T) hN hlambda heta hscale hamp
  have hinf : -amp * (T : ℝ) * carmonTermCap ≤
      sInf (Set.range
        (Envelope (scaledHardF T N lambdaWall eta scale amp))) := by
    rw [le_csInf_iff hbdd (Set.range_nonempty _)]
    rintro _ ⟨x, rfl⟩
    rw [scaledHardF_envelope_eq hN hlambda heta hscale hamp]
    have h := carmonF_lower T (rescaleEVec scale x)
    have hm := mul_le_mul_of_nonneg_left h hamp
    nlinarith
  have hzero := carmonF_zero_nonpos T
  have henv0 := scaledHardF_envelope_eq hN hlambda heta hscale hamp (0 : EVec T)
  have hrescale0 : rescaleEVec scale (0 : EVec T) = 0 := by
    funext i
    simp [rescaleEVec]
  rw [hrescale0] at henv0
  have htop : Envelope (scaledHardF T N lambdaWall eta scale amp) 0 ≤ 0 := by
    rw [henv0]
    exact mul_nonpos_of_nonneg_of_nonpos hamp hzero
  linarith

theorem vecSq_scaledEnvelopeGradient (T : Nat) (scale amp : ℝ)
    (x : EVec T) :
    vecSq (scaledEnvelopeGradient T scale amp x) =
      (amp / scale) ^ 2 * vecSq (carmonGradient T (rescaleEVec scale x)) := by
  unfold scaledEnvelopeGradient
  exact vecSq_scaleEVec _ _

theorem scaledEnvelope_terminal_gradient {T : Nat} (hT : 0 < T)
    {scale amp : ℝ} (hscale : 0 < scale) (hamp : 0 ≤ amp)
    (x : EVec T) (hlast : x (carmonLastIndex T hT) = 0) :
    (amp / scale) ^ 2 ≤ vecSq (scaledEnvelopeGradient T scale amp x) := by
  have hlast' : (rescaleEVec scale x) (carmonLastIndex T hT) = 0 := by
    simp [rescaleEVec, hlast]
  have hbase := one_le_vecSq_carmonGradient_of_terminal_zero hT
    (rescaleEVec scale x) hlast'
  rw [vecSq_scaledEnvelopeGradient]
  simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hbase (sq_nonneg (amp / scale))

theorem scaledEnvelopeGradient_is_zeroChain (T : Nat)
    {scale amp : ℝ} (hscale : scale ≠ 0) :
    IsFirstOrderZeroChain (scaledEnvelopeGradient T scale amp) := by
  intro r x hx
  have hscaled : SupportedBelow r (rescaleEVec scale x) := by
    intro i hir
    simp [rescaleEVec, hx i hir]
  have hbase := carmonGradient_is_zeroChain T r (rescaleEVec scale x) hscaled
  intro i hir
  unfold scaledEnvelopeGradient scaleEVec
  rw [hbase i hir]
  ring

end

end NCPLVerification
