import NCPLVerification.DeterministicLowerBound
import NCPLVerification.CarmonDifferentiability

/-!
# Actual Fréchet gradient of the scaled and rotated envelope

The lower-bound certificate uses an explicit vector called
`rotatedScaledEnvelopeGradient`.  This file closes the semantic gap by proving
that its Euclidean dot-product functional is the actual Fréchet derivative of
the max-envelope, first before and then after the hidden orthogonal rotation.
-/

namespace NCPLVerification

noncomputable section

theorem scaledEnvelopeGradient_deriv_map (T : Nat) (scale amp : ℝ)
    (x : EVec T) :
    amp • ((evecDot (carmonGradient T (rescaleEVec scale x))).comp
      (rescaleCLM scale)) =
      evecDot (scaledEnvelopeGradient T scale amp x) := by
  ext h
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    evecDot_apply, rescaleCLM_apply]
  unfold scaledEnvelopeGradient scaleEVec rescaleEVec
  simp only [smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hasCarmonFDerivAt_scaledCarmon (T : Nat) (scale amp : ℝ)
    (x : EVec T) :
    HasCarmonFDerivAt
      (fun z : EVec T => amp * carmonF T (rescaleEVec scale z))
      (evecDot (scaledEnvelopeGradient T scale amp x)) x := by
  letI : AddCommGroup (EVec T) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec T) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec T) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasCarmonFDerivAt
  have hscale : HasFDerivAt (rescaleEVec scale) (rescaleCLM scale) x := by
    refine (rescaleCLM (N := T) scale).hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun h => ?_)
    exact (rescaleCLM_apply scale h).symm
  have hbase : HasFDerivAt (carmonF T)
      (evecDot (carmonGradient T (rescaleEVec scale x)))
      (rescaleEVec scale x) := by
    simpa only [HasCarmonFDerivAt] using
      hasEVecFDerivAt_carmonF_gradient T (rescaleEVec scale x)
  have hcomp := hbase.comp x hscale
  have hmul := hcomp.const_mul amp
  rw [scaledEnvelopeGradient_deriv_map] at hmul
  exact hmul

theorem scaledHardF_hasEnvelopeFDerivAt {T N : Nat} (hN : 0 < N)
    {lambdaWall eta scale amp : ℝ}
    (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (hscale : scale ≠ 0) (hamp : 0 ≤ amp) (x : EVec T) :
    HasCarmonFDerivAt
      (Envelope (scaledHardF T N lambdaWall eta scale amp))
      (evecDot (scaledEnvelopeGradient T scale amp x)) x := by
  have heq : Envelope (scaledHardF T N lambdaWall eta scale amp) =
      fun z : EVec T => amp * carmonF T (rescaleEVec scale z) := by
    funext z
    exact scaledHardF_envelope_eq hN hlambda heta hscale hamp z
  rw [heq]
  exact hasCarmonFDerivAt_scaledCarmon T scale amp x

theorem frameGradient_deriv_map {m D : Nat}
    (U : Fin m → EVec D) (g : EVec m) :
    (evecDot g).comp (frameProjectCLM U) = evecDot (frameEmbed U g) := by
  ext H
  change evecDotValue g (frameProject U H) =
    evecDotValue (frameEmbed U g) H
  rw [evecDotValue_frameEmbed_left]
  rfl

theorem rotatedScaledHardF_hasEnvelopeFDerivAt
    {T N DX DY : Nat} (hN : 0 < N)
    {lambdaWall eta scale amp : ℝ}
    (hlambda : 0 ≤ lambdaWall) (heta : 0 ≤ eta)
    (hscale : scale ≠ 0) (hamp : 0 ≤ amp)
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    (hV : IsOrthonormalFrame V) (X : EVec DX) :
    HasCarmonFDerivAt
      (Envelope (rotatedF U V
        (scaledHardF T N lambdaWall eta scale amp)))
      (evecDot (rotatedScaledEnvelopeGradient U scale amp X)) X := by
  letI : AddCommGroup (EVec DX) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec DX) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec DX) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup (EVec T) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec T) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec T) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasCarmonFDerivAt
  have hproject : HasFDerivAt (frameProject U) (frameProjectCLM U) X := by
    refine (frameProjectCLM U).hasFDerivAt.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun H => ?_)
    exact (frameProjectCLM_apply U H).symm
  have hbase : HasFDerivAt
      (Envelope (scaledHardF T N lambdaWall eta scale amp))
      (evecDot (scaledEnvelopeGradient T scale amp (frameProject U X)))
      (frameProject U X) := by
    simpa only [HasCarmonFDerivAt] using
      scaledHardF_hasEnvelopeFDerivAt hN hlambda heta hscale hamp
        (frameProject U X)
  have hcomp := hbase.comp X hproject
  have heq : Envelope (rotatedF U V
      (scaledHardF T N lambdaWall eta scale amp)) =
      fun Z : EVec DX => Envelope
        (scaledHardF T N lambdaWall eta scale amp) (frameProject U Z) := by
    funext Z
    exact rotatedEnvelope_eq hV Z
  rw [heq]
  unfold rotatedScaledEnvelopeGradient
  rw [← frameGradient_deriv_map]
  exact hcomp

/-- `gradPhi` is the actual Euclidean Fréchet gradient of the max-envelope. -/
def RepresentsEnvelopeGradient {dx dy : Nat}
    (F : EVec dx → EVec dy → ℝ) (gradPhi : EVec dx → EVec dx) : Prop :=
  ∀ x, HasCarmonFDerivAt (Envelope F) (evecDot (gradPhi x)) x

/-- The article's deterministic black-box lower bound, with the asymptotic
constant and the actual-envelope-gradient interpretation in the same theorem. -/
theorem article_deterministic_black_box_lower_bound_certified
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
    0 < articleOmegaC ∧
    articleOmegaC * (L * Delta * kappa / eps ^ 2) ≤
        (articleT L Delta eps * (articleN kappa + 1) : Nat) ∧
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
      RepresentsEnvelopeGradient
        (rotatedF U V
          (scaledHardF (articleT L Delta eps) (articleN kappa)
            articleLambdaWall articleEta (articleScale L eps)
            (articleAmp L eps)))
        (rotatedScaledEnvelopeGradient U
          (articleScale L eps) (articleAmp L eps)) ∧
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
  refine ⟨articleOmegaC_pos, ?_, ?_⟩
  · exact article_chain_length_lower_bound hL hDelta hkappa heps
      hkappaLarge hregime
  · obtain ⟨U, V, hU, hV, hclass, hbad⟩ :=
      article_deterministic_black_box_lower_bound hL hDelta hkappa heps
        hkappaLarge hregime hK hcapX hcapY A
    refine ⟨U, V, hU, hV, hclass, ?_, hbad⟩
    intro X
    apply rotatedScaledHardF_hasEnvelopeFDerivAt
      (hN := by
        have hN2 := articleN_two_le hkappaLarge
        omega)
      (by norm_num [articleLambdaWall])
      (by norm_num [articleEta])
      (articleScale_pos hL heps).ne'
      (articleAmp_nonneg (L := L) (eps := eps) hL.le)
      hV X

end

end NCPLVerification
