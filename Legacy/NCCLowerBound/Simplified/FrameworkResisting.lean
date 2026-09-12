import NCCLowerBound.Simplified.Framework
import NCCLowerBound.Simplified.CorrectedModel
import NCCLowerBoundVerification.Lower.MainTheorem

/-!
# Resisting-oracle completion of the typed framework

This module is independent of the particular five-component instance.  It
shows that any literal `Framework.UnscaledHardProperties` certificate at the
canonical floor dimensions produces a hard instance for every deterministic
feasible-query algorithm.  Thus the analytic construction and the resisting
lift meet at one fully typed theorem.
-/

namespace NCCLowerBound
namespace Simplified
namespace FrameworkResisting

noncomputable section

open NCCLowerBoundVerification
open NCCLowerBoundVerification.Oracle
open NCPLVerification
open Framework CorrectedModel

def strictHorizon (ell D Delta eps ell0 g0 cy cp cDelta : ℝ) : Nat :=
  frameworkH ell D Delta eps ell0 g0 cy cp cDelta - 1

def ambientPrimalDim (ell D Delta eps ell0 g0 cy cp cDelta : ℝ) : Nat :=
  3 * frameworkM Delta cDelta ell ell0 eps g0 +
    (strictHorizon ell D Delta eps ell0 g0 cy cp cDelta + 2)

def ambientDualDim (ell D Delta eps ell0 g0 cy cp cDelta : ℝ) : Nat :=
  frameworkN D cy cp ell ell0 eps g0 *
      frameworkM Delta cDelta ell ell0 eps g0 +
    (strictHorizon ell D Delta eps ell0 g0 cy cp cDelta + 2)

theorem strictHorizon_lt_frameworkH
    {ell D Delta eps ell0 g0 cy cp cDelta : ℝ}
    (hM : 1 ≤ frameworkM Delta cDelta ell ell0 eps g0) :
    strictHorizon ell D Delta eps ell0 g0 cy cp cDelta <
      frameworkH ell D Delta eps ell0 g0 cy cp cDelta := by
  unfold strictHorizon frameworkH
  have hpos : 0 < frameworkM Delta cDelta ell ell0 eps g0 *
      (frameworkN D cy cp ell ell0 eps g0 + 3) :=
    Nat.mul_pos (by omega) (by omega)
  omega

theorem half_frameworkH_le_strictHorizon
    {ell D Delta eps ell0 g0 cy cp cDelta : ℝ}
    (hM : 1 ≤ frameworkM Delta cDelta ell ell0 eps g0) :
    ((frameworkH ell D Delta eps ell0 g0 cy cp cDelta : ℝ) / 2) ≤
      (strictHorizon ell D Delta eps ell0 g0 cy cp cDelta : ℝ) := by
  have hH : 3 ≤ frameworkH ell D Delta eps ell0 g0 cy cp cDelta := by
    unfold frameworkH
    have hN : 3 ≤ frameworkN D cy cp ell ell0 eps g0 + 3 := by omega
    nlinarith
  have hHreal : (2 : ℝ) ≤
      (frameworkH ell D Delta eps ell0 g0 cy cp cDelta : ℝ) := by
    exact_mod_cast (show 2 ≤ frameworkH ell D Delta eps ell0 g0 cy cp cDelta by
      omega)
  unfold strictHorizon
  rw [Nat.cast_sub (by omega : 1 ≤
    frameworkH ell D Delta eps ell0 g0 cy cp cDelta)]
  norm_num
  linarith

/-!
## Arbitrary deterministic algorithms
-/

/--
The complete resisting lift for any certified unscaled family at the
canonical dimensions.  The returned instance lives in larger ambient
spaces, but the orthonormal product rotation preserves the primal/dual split,
the diameter ball, and every analytic class property.  The loss from `H` to
the strict horizon `H-1` costs only the displayed factor `1/2`.
-/
theorem certified_family_hard_for_algorithm
    {ell D Delta eps ell0 g0 cy cp cDelta tau0 : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps) (hell0 : 0 < ell0) (hg0 : 0 < g0)
    (hcy : 0 < cy) (hcp : 0 < cp) (hcDelta : 0 < cDelta)
    (haccuracy : eps ≤ frameworkAccuracyConstant ell0 g0 cy cp cDelta *
      min (ell * D) (Real.sqrt (ell * Delta)))
    (hterminalScale : g0 / (8 * ell0) ≤ (1 / 5 : ℝ))
    {F : UnscaledHardData
      (frameworkM Delta cDelta ell ell0 eps g0)
      (frameworkN D cy cp ell ell0 eps g0)}
    (P : UnscaledHardProperties F ell0 g0 cDelta cy cp tau0)
    (A : DeterministicAlgorithm D) :
    ∃ Q : NCCInstance
        (ambientPrimalDim ell D Delta eps ell0 g0 cy cp cDelta)
        (ambientDualDim ell D Delta eps ell0 g0 cy cp cDelta),
      IsFunctionClass ell D Delta Q ∧
      DeterministicFOComponent.FailsWithin
        (A.component
          (ambientPrimalDim ell D Delta eps ell0 g0 cy cp cDelta)
          (ambientDualDim ell D Delta eps ell0 g0 cy cp cDelta))
        Q ell eps
        (strictHorizon ell D Delta eps ell0 g0 cy cp cDelta) ∧
      (1 / 2 : ℝ) *
          (g0 ^ 3 / (1024 * cy * cp * cDelta * ell0 ^ 2) *
            (ell ^ 2 * D * Delta / eps ^ 3)) ≤
        (strictHorizon ell D Delta eps ell0 g0 cy cp cDelta : ℝ) := by
  obtain ⟨hN, hM, _hsize, _hgap, _hrate0⟩ :=
    framework_parameter_package hell hD hDelta heps hell0 hg0 hcy hcp
      hcDelta haccuracy
  obtain ⟨hclass, _hvalue, hchain, hfailure, hrate⟩ :=
    canonical_framework_reduction hell hD hDelta heps hell0 hg0 hcy hcp
      hcDelta haccuracy hterminalScale P
  let M := frameworkM Delta cDelta ell ell0 eps g0
  let N := frameworkN D cy cp ell ell0 eps g0
  let H := frameworkH ell D Delta eps ell0 g0 cy cp cDelta
  let K := strictHorizon ell D Delta eps ell0 g0 cy cp cDelta
  let DX := ambientPrimalDim ell D Delta eps ell0 g0 cy cp cDelta
  let DY := ambientDualDim ell D Delta eps ell0 g0 cy cp cDelta
  let lambda := frameworkLambda ell ell0 eps g0
  let amp := paperAmplitude ell ell0 lambda
  let P0 := scaledFiniteInstance F ell ell0 eps g0 D
  have hlambda : 0 < lambda := by
    dsimp [lambda, frameworkLambda, lowerScale]
    positivity
  have hT : 2 ≤ M + 1 := by
    dsimp [M]
    omega
  have hKM : K < (M + 1 - 1) * (N + 3) := by
    have hlt := strictHorizon_lt_frameworkH (ell := ell) (D := D)
      (Delta := Delta) (eps := eps) (ell0 := ell0) (g0 := g0)
      (cy := cy) (cp := cp) (cDelta := cDelta) hM
    dsimp [K, H, M, N] at *
    simpa [frameworkH] using hlt
  have hcapX : 3 * (M + 1 - 1) + (K + 1) < DX := by
    dsimp [DX, ambientPrimalDim, M, K]
    omega
  have hcapY : N * (M + 1 - 1) + (K + 1) < DY := by
    dsimp [DY, ambientDualDim, M, N, K]
    omega
  have hX : P0.X = Set.univ := by
    simp [P0, scaledFiniteInstance, scaleNCCInstance, finiteInstance,
      scaledDomain_univ]
  have hY : P0.Y = diameterBall (N * (M + 1 - 1)) D := by
    change scaledDomain lambda
      (diameterBall (N * (M + 1 - 1)) (D / lambda)) =
        diameterBall (N * (M + 1 - 1)) D
    exact scaledDomain_diameterBall_div hlambda
  have hx0 : P0.x0 = 0 := by
    change scaleCoords lambda (0 : UnscaledPrimal (M + 1)) = 0
    funext i
    simp [scaleCoords]
  have hchain0 : IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf P0.gradX P0.gradY) := by
    change IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf
        (scaledGradX lambda amp F.gradX)
        (scaledGradY lambda amp F.gradY))
    rw [taggedSerializedSaddleFieldOf_scaled]
    simpa [lambda, amp, M, N] using hchain
  have hfailure0 : ∀ x : UnscaledPrimal (M + 1),
      x (terminalPrimalIndex hT) = 0 →
        ¬ IsOptimizationStationary Set.univ
          (ValueOn (diameterBall (N * (M + 1 - 1)) D) P0.f)
            ell eps x := by
    intro x hx
    have hterminal : terminalStateValue x = 0 := by
      rw [terminalStateValue_eq hM]
      simpa [terminalIndex, terminalPrimalIndex, terminalMemoryIndex, M]
        using hx
    have hf := hfailure x hterminal
    rw [hY] at hf
    exact hf
  obtain ⟨Q, hQclass, hQfail, hQX, hQY, hQx0⟩ :=
    NCCLowerBoundVerification.exists_rotated_hard_instance_of_terminal
      hT (A.component DX DY) P0 hclass hX hY hx0 hchain0 hKM hcapX
        hcapY hfailure0
  refine ⟨Q, ⟨hQX, hQY, hQx0, hQclass⟩, hQfail, ?_⟩
  have hhalf := mul_le_mul_of_nonneg_left hrate
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hHK := half_frameworkH_le_strictHorizon (ell := ell) (D := D)
    (Delta := Delta) (eps := eps) (ell0 := ell0) (g0 := g0)
    (cy := cy) (cp := cp) (cDelta := cDelta) hM
  have hHK' : (1 / 2 : ℝ) *
      (frameworkH ell D Delta eps ell0 g0 cy cp cDelta : ℝ) ≤
      (strictHorizon ell D Delta eps ell0 g0 cy cp cDelta : ℝ) := by
    simpa [div_eq_mul_inv, mul_comm] using hHK
  exact hhalf.trans hHK'

end

end FrameworkResisting
end Simplified
end NCCLowerBound
