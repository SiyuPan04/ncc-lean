import NCPLVerification.ResistingOracle

/-!
# Deterministic black-box lower bound

This file instantiates the finite-horizon hidden-basis theorem with the
scaled NC--PL hard family and combines it with rotation invariance and the
terminal-coordinate stationarity certificate.
-/

namespace NCPLVerification

noncomputable section

theorem orderedSaddleFieldOf_scaledHard_eq (T N : Nat)
    (lambdaWall eta scale amp : ℝ) :
    orderedSaddleFieldOf
      (scaledHardGradX T N lambdaWall eta scale amp)
      (scaledHardGradY T N lambdaWall eta scale amp) =
    scaledHardOrderedSaddleField T N lambdaWall eta scale amp := by
  funext z k
  rcases hp : finProdFinEquiv.symm k with ⟨i, s⟩
  unfold orderedSaddleFieldOf orderedJoint scaledHardOrderedSaddleField
  simp only [hp]
  by_cases hs : s.1 < N
  · rw [dif_pos hs, dif_pos hs]
    rfl
  · rw [dif_neg hs, dif_neg hs]

theorem scaledHard_orderedSaddleField_is_zeroChain {T N : Nat}
    (hN : 0 < N) (lambdaWall eta scale amp : ℝ) :
    IsFirstOrderZeroChain
      (orderedSaddleFieldOf
        (scaledHardGradX T N lambdaWall eta scale amp)
        (scaledHardGradY T N lambdaWall eta scale amp)) := by
  rw [orderedSaddleFieldOf_scaledHard_eq]
  exact scaledHardOrderedSaddleField_is_zeroChain hN
    lambdaWall eta scale amp

def rotatedScaledEnvelopeGradient {T DX : Nat}
    (U : Fin T → EVec DX) (scale amp : ℝ) (X : EVec DX) : EVec DX :=
  frameEmbed U (scaledEnvelopeGradient T scale amp (frameProject U X))

theorem article_deterministic_black_box_lower_bound
    {L Delta kappa eps : ℝ}
    (hL : 0 < L) (hDelta : 0 < Delta) (hkappa : 0 < kappa)
    (heps : 0 < eps)
    (hkappaLarge : 4 * articleEll0 / articleC0 ≤ kappa)
    (hregime : 16 * carmonTermCap * articleEll0 * eps ^ 2 ≤ L * Delta)
    {DX DY K : Nat}
    (hK : K < articleT L Delta eps * (articleN kappa + 1))
    (hcapX : articleT L Delta eps + (K + 1) < DX)
    (hcapY : articleT L Delta eps * articleN kappa + (K + 1) < DY)
    (A : DeterministicFOBlackBox DX DY) :
    ∃ U : Fin (articleT L Delta eps) → EVec DX,
      ∃ V : Fin (articleT L Delta eps * articleN kappa) → EVec DY,
      IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      NCPLClass L (L / kappa) Delta
        (rotatedF U V
          (scaledHardF (articleT L Delta eps) (articleN kappa)
            articleLambdaWall articleEta (articleScale L eps)
            (articleAmp L eps)))
        (rotatedGradX U V
          (scaledHardGradX (articleT L Delta eps) (articleN kappa)
            articleLambdaWall articleEta (articleScale L eps)
            (articleAmp L eps)))
        (rotatedGradY U V
          (scaledHardGradY (articleT L Delta eps) (articleN kappa)
            articleLambdaWall articleEta (articleScale L eps)
            (articleAmp L eps))) ∧
      let hist := runHistory A
        (rotatedF U V
          (scaledHardF (articleT L Delta eps) (articleN kappa)
            articleLambdaWall articleEta (articleScale L eps)
            (articleAmp L eps)))
        (rotatedGradX U V
          (scaledHardGradX (articleT L Delta eps) (articleN kappa)
            articleLambdaWall articleEta (articleScale L eps)
            (articleAmp L eps)))
        (rotatedGradY U V
          (scaledHardGradY (articleT L Delta eps) (articleN kappa)
            articleLambdaWall articleEta (articleScale L eps)
            (articleAmp L eps))) K
      ¬vecSq (rotatedScaledEnvelopeGradient U
        (articleScale L eps) (articleAmp L eps) (A.output hist)) ≤ eps ^ 2 := by
  let T := articleT L Delta eps
  let N := articleN kappa
  let scale := articleScale L eps
  let amp := articleAmp L eps
  have hN : 0 < N := by
    have := articleN_two_le hkappaLarge
    omega
  have hchain := scaledHard_orderedSaddleField_is_zeroChain (T := T) hN
    articleLambdaWall articleEta scale amp
  obtain ⟨U, V, hU, hV, i, hi, hout⟩ :=
    finite_horizon_hidden_basis A
      (scaledHardF T N articleLambdaWall articleEta scale amp)
      (scaledHardGradX T N articleLambdaWall articleEta scale amp)
      (scaledHardGradY T N articleLambdaWall articleEta scale amp)
      hchain hK hcapX hcapY
  have hclassBase := articleScaledHardF_NCPLClass hL hDelta hkappa heps
    hkappaLarge hregime
  have hclass := hclassBase.rotate hU hV
  have hT : 0 < T := by
    exact lt_of_lt_of_le Nat.zero_lt_one
      (articleT_one_le hL hDelta heps hregime)
  have hiLast : i = carmonLastIndex T hT := by
    apply Fin.ext
    exact hi
  rw [hiLast] at hout
  let hist := runHistory A
    (rotatedF U V
      (scaledHardF T N articleLambdaWall articleEta scale amp))
    (rotatedGradX U V
      (scaledHardGradX T N articleLambdaWall articleEta scale amp))
    (rotatedGradY U V
      (scaledHardGradY T N articleLambdaWall articleEta scale amp)) K
  let Xout := A.output hist
  have hterminal := scaledEnvelope_terminal_gradient hT
    (articleScale_pos hL heps)
    (articleAmp_nonneg (L := L) (eps := eps) hL.le)
    (frameProject U Xout) hout
  have hthreshold : eps ^ 2 < (amp / scale) ^ 2 := by
    unfold amp scale
    rw [articleAmp_div_scale hL.ne' heps.ne']
    nlinarith [sq_pos_of_pos heps]
  have hnorm : vecSq (rotatedScaledEnvelopeGradient U scale amp Xout) =
      vecSq (scaledEnvelopeGradient T scale amp (frameProject U Xout)) := by
    unfold rotatedScaledEnvelopeGradient
    exact vecSq_frameEmbed hU _
  refine ⟨U, V, hU, hV, ?_, ?_⟩
  · simpa [T, N, scale, amp] using hclass
  · dsimp only
    intro hstationary
    change vecSq (rotatedScaledEnvelopeGradient U scale amp Xout) ≤ eps ^ 2 at hstationary
    change (amp / scale) ^ 2 ≤
      vecSq (scaledEnvelopeGradient T scale amp (frameProject U Xout)) at hterminal
    rw [hnorm] at hstationary
    linarith

end

end NCPLVerification
