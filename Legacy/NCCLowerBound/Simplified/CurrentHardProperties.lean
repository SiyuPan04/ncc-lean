import NCCLowerBound.Simplified.CurrentTerminalTransport
import NCCLowerBound.Simplified.CurrentSmoothnessTransport

/-!
# Completed certificates for the current hard instance

This module closes the remaining cross-file clauses for
`CurrentHardData.currentHardData`.  In particular, it transports the actual
finite/unbounded value gradients to the terminal-product coordinates and
uses the deliberately slackened constant `21 * sqrt 20` to turn the
framework's non-strict size hypothesis into the strict inactivity margin
needed by the finite-ball terminal theorem.
-/

namespace NCCLowerBound
namespace Simplified
namespace CurrentHardProperties

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators
open Set
open NCCLowerBoundVerification
open CurrentHardData CurrentTerminalTransport TerminalCertificate

theorem terminalState_toTerminalPrimal {M : Nat} (hM : 1 ≤ M)
    (x : CurrentHardData.Primal M) :
    (toTerminalPrimal x).1 ⟨M - 1, by omega⟩ =
      Framework.terminalStateValue x := by
  rw [Framework.terminalStateValue_eq hM]
  rfl

/-- Exact square of the slackened maximizer-growth constant. -/
theorem currentCy_sq : currentCy ^ 2 = 8820 := by
  have hsqrt : Real.sqrt (20 : ℝ) ^ 2 = 20 :=
    Real.sq_sqrt (by norm_num)
  unfold currentCy
  nlinarith

/-- The framework size bound implies the strict margin required to identify
the finite and unbounded value gradients locally.  The strictness is exactly
the reason for using `21 * sqrt 20` instead of the raw `20 * sqrt 20` growth
constant. -/
theorem finite_terminal_strict_margin {N : Nat} (hN10 : 10 ≤ N)
    {D : ℝ} (hD : 0 < D)
    (hsize : (N : ℝ) ≤ D / (2 * currentCy * currentCp)) :
    8000 * (N : ℝ) ^ 2 * 20 ^ 2 < (D / 2) ^ 2 := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hden : 0 < 2 * currentCy * currentCp := by
    exact mul_pos (mul_pos (by norm_num) currentCy_pos) currentCp_pos
  have hlinear : (N : ℝ) * currentCy * currentCp ≤ D / 2 := by
    have hm := (le_div_iff₀ hden).mp hsize
    nlinarith
  have hleft : 0 ≤ (N : ℝ) * currentCy * currentCp := by
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) currentCy_pos.le)
      currentCp_pos.le
  have hright : 0 ≤ D / 2 := by positivity
  have hsquare : ((N : ℝ) * currentCy * currentCp) ^ 2 ≤
      (D / 2) ^ 2 := by
    exact (sq_le_sq₀ hleft hright).2 hlinear
  have hcp : currentCp ^ 2 = 400 := by norm_num [currentCp]
  have hstrict :
      8000 * (N : ℝ) ^ 2 * 20 ^ 2 <
        ((N : ℝ) * currentCy * currentCp) ^ 2 := by
    rw [mul_pow, mul_pow, currentCy_sq, hcp]
    norm_num
    nlinarith
  exact hstrict.trans_le hsquare

/-- A small actual restricted-value gradient forces all pulse coordinates
into the dimension-free radius `currentCp`. -/
theorem current_dual_inactivity {M N : Nat} (hM : 1 ≤ M)
    (hN10 : 10 ≤ N) (q : Framework.DualScope)
    (x : CurrentHardData.Primal M)
    (hterminal : Framework.terminalStateValue x ≤ (1 / 5 : ℝ))
    (hsmall : vecSq
      (valueGrad (M := M) (N := N) (by omega : 0 < N)
        terminalPhaseScale q x) ≤ currentTau0 ^ 2) :
    pulseSq x ≤ currentCp ^ 2 := by
  have hterminal' :
      (toTerminalPrimal x).1 ⟨M - 1, by omega⟩ ≤ (1 / 5 : ℝ) := by
    rw [terminalState_toTerminalPrimal hM]
    exact hterminal
  cases q with
  | finite D hD =>
      have heq := vecSq_valueGrad_finite_eq_actualGradientSq
        (M := M) hN10 terminalPhaseScale D hD x
      have hsmall' : actualGradientSq
          (terminalValue terminalPhaseScale
            (InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D))
          (toTerminalPrimal x) ≤ (1 / 4 : ℝ) ^ 2 := by
        rw [← heq]
        simpa [currentTau0] using hsmall
      have hp := finiteValue_smallGradient_pulseSq_le hM hN10 hD.le
        (toTerminalPrimal x) hsmall' hterminal'
      rw [← vecSq_toPulse]
      simpa [currentCp] using hp
  | unbounded =>
      have heq := vecSq_valueGrad_unbounded_eq_actualGradientSq
        (M := M) hN10 terminalPhaseScale x
      have hsmall' : actualGradientSq
          (terminalValue terminalPhaseScale
            (InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N)))
          (toTerminalPrimal x) ≤ (1 / 4 : ℝ) ^ 2 := by
        rw [← heq]
        simpa [currentTau0] using hsmall
      have hp := unboundedValue_smallGradient_pulseSq_le hM hN10
        (toTerminalPrimal x) hsmall' hterminal'
      rw [← vecSq_toPulse]
      simpa [currentCp] using hp

/-- Finite-ball terminal obstruction in the exact framework coordinates. -/
theorem current_terminal_finite {M N : Nat} (hM : 1 ≤ M)
    (hN10 : 10 ≤ N) (D : ℝ) (hD : 0 < D)
    (x : CurrentHardData.Primal M)
    (hsize : (N : ℝ) ≤ D / (2 * currentCy * currentCp))
    (hterminal : Framework.terminalStateValue x ≤ (1 / 5 : ℝ)) :
    currentG0 ^ 2 ≤
      vecSq (valueGrad (M := M) (N := N) (by omega : 0 < N)
        terminalPhaseScale (.finite D hD) x) := by
  have hterminal' :
      (toTerminalPrimal x).1 ⟨M - 1, by omega⟩ ≤ (1 / 5 : ℝ) := by
    rw [terminalState_toTerminalPrimal hM]
    exact hterminal
  have hmargin := finite_terminal_strict_margin hN10 hD hsize
  have hcert := finiteValue_terminal_gradientSq_lower hM hN10 hD.le
    hmargin (toTerminalPrimal x) hterminal'
  rw [vecSq_valueGrad_finite_eq_actualGradientSq
    (M := M) hN10 terminalPhaseScale D hD x]
  simpa [currentG0] using hcert

/-- Unbounded terminal obstruction in the exact framework coordinates. -/
theorem current_terminal_unbounded {M N : Nat} (hM : 1 ≤ M)
    (hN10 : 10 ≤ N) (x : CurrentHardData.Primal M)
    (hterminal : Framework.terminalStateValue x ≤ (1 / 5 : ℝ)) :
    currentG0 ^ 2 ≤
      vecSq (valueGrad (M := M) (N := N) (by omega : 0 < N)
        terminalPhaseScale .unbounded x) := by
  have hterminal' :
      (toTerminalPrimal x).1 ⟨M - 1, by omega⟩ ≤ (1 / 5 : ℝ) := by
    rw [terminalState_toTerminalPrimal hM]
    exact hterminal
  have hcert := unboundedValue_terminal_gradientSq_lower hM hN10
    (toTerminalPrimal x) hterminal'
  rw [vecSq_valueGrad_unbounded_eq_actualGradientSq
    (M := M) hN10 terminalPhaseScale x]
  simpa [currentG0] using hcert

/-- Assembly milestone: once the actual framework gradients have the
transported flat smoothness certificate, every remaining field of
`UnscaledHardProperties` follows with no further hypotheses. -/
theorem currentHardProperties_of_smoothness {M N : Nat}
    (hM : 1 ≤ M) (hN10 : 10 ≤ N)
    (hsmooth : NCPLVerification.IsJointlySmooth
      (CompositeSmoothnessAssembly.compositeEll0
        terminalPhaseScale terminalPhaseScale_pos)
      (gradX (M := M) (by omega : 0 < N) terminalPhaseScale)
      (gradY (M := M) (by omega : 0 < N) terminalPhaseScale)) :
    Framework.UnscaledHardProperties
      (currentHardData (M := M) (N := N) (by omega : 0 < N)
        terminalPhaseScale)
      (CompositeSmoothnessAssembly.compositeEll0
        terminalPhaseScale terminalPhaseScale_pos)
      currentG0 (currentCDelta terminalPhaseScale) currentCy currentCp
      currentTau0 := by
  apply currentHardProperties_of_certificates hN10 terminalPhaseScale
    (CompositeSmoothnessAssembly.compositeEll0
      terminalPhaseScale terminalPhaseScale_pos)
    terminalPhaseScale_pos
    (CompositeSmoothnessAssembly.compositeEll0_pos
      terminalPhaseScale terminalPhaseScale_pos)
    hsmooth
  · exact current_dual_inactivity hM hN10
  · exact current_terminal_finite hM hN10
  · exact current_terminal_unbounded hM hN10

/-- Complete, assumption-free C1--C4 certificate for the literal current
five-component construction. -/
theorem currentHardProperties {M N : Nat} (hM : 1 ≤ M)
    (hN10 : 10 ≤ N) :
    Framework.UnscaledHardProperties
      (currentHardData (M := M) (N := N) (by omega : 0 < N)
        terminalPhaseScale)
      (CompositeSmoothnessAssembly.compositeEll0
        terminalPhaseScale terminalPhaseScale_pos)
      currentG0 (currentCDelta terminalPhaseScale) currentCy currentCp
      currentTau0 := by
  exact currentHardProperties_of_smoothness hM hN10
    (CurrentSmoothnessTransport.current_gradients_jointlySmooth
      (M := M) hN10 terminalPhaseScale terminalPhaseScale_pos)

end

end CurrentHardProperties
end Simplified
end NCCLowerBound
