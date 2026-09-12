import NCCLowerBound.Simplified.CurrentHardProperties
import NCCLowerBound.Simplified.FrameworkResisting

/-!
# Deterministic lower bound for the literal five-component construction

This file fixes the numerical parameters of the abstract framework to the
constants certified for the construction in `CurrentHardData`.  The final
resisting-oracle theorem below uses the strict horizon `H - 1`; its explicit
rate therefore contains the factor `1 / 2` proved in `FrameworkResisting`.
-/

namespace NCCLowerBound
namespace Simplified
namespace CurrentLowerBound

noncomputable section

open NCCLowerBoundVerification
open NCCLowerBoundVerification.Oracle
open CorrectedModel Framework FrameworkResisting
open CurrentHardData CompositeSmoothnessAssembly TerminalCertificate
open CurrentHardProperties

/-! ## Fixed construction constants -/

/-- The phase scale used by the terminal obstruction. -/
def currentK : ℝ := terminalPhaseScale

theorem currentK_pos : 0 < currentK := by
  exact terminalPhaseScale_pos

/-- The dimension-independent joint-smoothness constant of the construction. -/
def currentEll0 : ℝ := compositeEll0 currentK currentK_pos

theorem currentEll0_pos : 0 < currentEll0 := by
  exact compositeEll0_pos currentK currentK_pos

/-- Accuracy constant in the regime required by both floor choices. -/
def currentAccuracyConstant : ℝ :=
  frameworkAccuracyConstant currentEll0 currentG0 currentCy currentCp
    (currentCDelta currentK)

/-- Explicit constant in front of `ell² D Delta / eps³` after replacing
the framework horizon `H` by the strict query horizon `H - 1`. -/
def currentRateConstant : ℝ :=
  (1 / 2 : ℝ) *
    (currentG0 ^ 3 /
      (1024 * currentCy * currentCp * currentCDelta currentK *
        currentEll0 ^ 2))

theorem currentAccuracyConstant_pos : 0 < currentAccuracyConstant := by
  exact frameworkAccuracyConstant_pos currentEll0_pos currentG0_pos
    currentCy_pos currentCp_pos (currentCDelta_pos currentK)

theorem currentRateConstant_pos : 0 < currentRateConstant := by
  unfold currentRateConstant
  have hnum : 0 < currentG0 ^ 3 := pow_pos currentG0_pos _
  have hden : 0 <
      1024 * currentCy * currentCp * currentCDelta currentK *
        currentEll0 ^ 2 := by
    exact mul_pos
      (mul_pos
        (mul_pos (mul_pos (by norm_num) currentCy_pos) currentCp_pos)
        (currentCDelta_pos currentK))
      (sq_pos_of_pos currentEll0_pos)
  exact mul_pos (by norm_num) (div_pos hnum hden)

/-- The terminal displacement produced by the Moreau argument stays below
the `1/5` threshold used by the terminal certificate. -/
theorem current_terminal_scale :
    currentG0 / (8 * currentEll0) ≤ (1 / 5 : ℝ) := by
  have hC := localOuterC_nonneg currentK currentK_pos
  have hEll : 20 ≤ currentEll0 := by
    unfold currentEll0 compositeEll0
    nlinarith
  have hden : 0 < 8 * currentEll0 := mul_pos (by norm_num) currentEll0_pos
  rw [div_le_iff₀ hden]
  unfold currentG0
  nlinarith

/-! ## Canonical dimensions and strict horizon -/

def currentM (ell Delta eps : ℝ) : Nat :=
  frameworkM Delta (currentCDelta currentK) ell currentEll0 eps currentG0

def currentN (ell D eps : ℝ) : Nat :=
  frameworkN D currentCy currentCp ell currentEll0 eps currentG0

def currentH (ell D Delta eps : ℝ) : Nat :=
  frameworkH ell D Delta eps currentEll0 currentG0 currentCy currentCp
    (currentCDelta currentK)

/-- The resisting lift is valid for query indices `t < H - 1`. -/
def currentStrictHorizon (ell D Delta eps : ℝ) : Nat :=
  strictHorizon ell D Delta eps currentEll0 currentG0 currentCy currentCp
    (currentCDelta currentK)

def currentAmbientPrimalDim (ell D Delta eps : ℝ) : Nat :=
  ambientPrimalDim ell D Delta eps currentEll0 currentG0 currentCy currentCp
    (currentCDelta currentK)

def currentAmbientDualDim (ell D Delta eps : ℝ) : Nat :=
  ambientDualDim ell D Delta eps currentEll0 currentG0 currentCy currentCp
    (currentCDelta currentK)

/-- Corrected threshold predicate specialized to the literal current family.
The algorithm is dimension-polymorphic, while the canonical hard dimensions
depend only on `(ell,D,Delta,eps)`. -/
def CurrentComplexityAtLeast (ell D Delta eps : ℝ) (T : Nat) : Prop :=
  ∀ A : DeterministicAlgorithm D,
    ∃ Q : NCCInstance
        (currentAmbientPrimalDim ell D Delta eps)
        (currentAmbientDualDim ell D Delta eps),
      IsFunctionClass ell D Delta Q ∧
        DeterministicFOComponent.FailsWithin
          (A.component
            (currentAmbientPrimalDim ell D Delta eps)
            (currentAmbientDualDim ell D Delta eps))
          Q ell eps T

theorem currentStrictHorizon_eq_H_sub_one (ell D Delta eps : ℝ) :
    currentStrictHorizon ell D Delta eps =
      currentH ell D Delta eps - 1 := by
  rfl

theorem current_dimensions_of_accuracy
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (haccuracy : eps ≤ currentAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    10 ≤ currentN ell D eps ∧ 1 ≤ currentM ell Delta eps := by
  obtain ⟨hN, hM, _hsize, _hgap, _hrate⟩ :=
    framework_parameter_package hell hD hDelta heps currentEll0_pos
      currentG0_pos currentCy_pos currentCp_pos
      (currentCDelta_pos currentK)
      (by simpa [currentAccuracyConstant] using haccuracy)
  exact ⟨hN, hM⟩

/-- In the stated accuracy regime the strict horizon is nonzero. -/
theorem currentStrictHorizon_pos
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (haccuracy : eps ≤ currentAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    0 < currentStrictHorizon ell D Delta eps := by
  obtain ⟨_hN, hM⟩ :=
    current_dimensions_of_accuracy hell hD hDelta heps haccuracy
  let m := currentM ell Delta eps
  let n := currentN ell D eps
  have hfactor : 3 ≤ n + 3 := by omega
  have hmul : n + 3 ≤ m * (n + 3) := by
    calc
      n + 3 = 1 * (n + 3) := by omega
      _ ≤ m * (n + 3) := Nat.mul_le_mul_right _ hM
  have hH : 3 ≤ currentH ell D Delta eps := by
    change 3 ≤ m * (n + 3)
    exact hfactor.trans hmul
  rw [currentStrictHorizon_eq_H_sub_one]
  omega

/-- The query budget is genuinely strict: it is exactly one smaller than
the serialized zero-chain horizon. -/
theorem currentStrictHorizon_lt_currentH
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (haccuracy : eps ≤ currentAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    currentStrictHorizon ell D Delta eps < currentH ell D Delta eps := by
  obtain ⟨_hN, hM⟩ :=
    current_dimensions_of_accuracy hell hD hDelta heps haccuracy
  simpa [currentStrictHorizon, currentH, currentM] using
    (strictHorizon_lt_frameworkH
      (ell := ell) (D := D) (Delta := Delta) (eps := eps)
      (ell0 := currentEll0) (g0 := currentG0) (cy := currentCy)
      (cp := currentCp) (cDelta := currentCDelta currentK) hM)

/-- Explicit cubic lower bound for the strict horizon itself. -/
theorem currentStrictHorizon_rate
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (haccuracy : eps ≤ currentAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    currentRateConstant * (ell ^ 2 * D * Delta / eps ^ 3) ≤
      (currentStrictHorizon ell D Delta eps : ℝ) := by
  obtain ⟨_hN, hM, _hsize, _hgap, hrate⟩ :=
    framework_parameter_package hell hD hDelta heps currentEll0_pos
      currentG0_pos currentCy_pos currentCp_pos
      (currentCDelta_pos currentK)
      (by simpa [currentAccuracyConstant] using haccuracy)
  have hhalf := mul_le_mul_of_nonneg_left hrate
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hstrict := half_frameworkH_le_strictHorizon
    (ell := ell) (D := D) (Delta := Delta) (eps := eps)
    (ell0 := currentEll0) (g0 := currentG0) (cy := currentCy)
    (cp := currentCp) (cDelta := currentCDelta currentK) hM
  calc
    currentRateConstant * (ell ^ 2 * D * Delta / eps ^ 3) =
        (1 / 2 : ℝ) *
          ((currentG0 ^ 3 /
              (1024 * currentCy * currentCp * currentCDelta currentK *
                currentEll0 ^ 2)) *
            (ell ^ 2 * D * Delta / eps ^ 3)) := by
              unfold currentRateConstant
              ring
    _ ≤ (1 / 2 : ℝ) *
        (frameworkH ell D Delta eps currentEll0 currentG0 currentCy
          currentCp (currentCDelta currentK) : ℝ) := hhalf
    _ ≤ (currentStrictHorizon ell D Delta eps : ℝ) := by
      simpa [currentStrictHorizon, div_eq_mul_inv, mul_comm] using hstrict

/-! ## Resisting lift of a canonical current-family certificate -/

/-- Typed endpoint once the literal C1--C4 certificate at the canonical
dimensions is supplied.  This helper makes the interface between the
analytic assembly and the resisting lift explicit. -/
theorem current_algorithm_has_hard_instance_of_properties
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (haccuracy : eps ≤ currentAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta)))
    (_hM : 1 ≤ currentM ell Delta eps)
    (hN10 : 10 ≤ currentN ell D eps)
    (P : UnscaledHardProperties
      (currentHardData
        (M := currentM ell Delta eps) (N := currentN ell D eps)
        (by omega) currentK)
      currentEll0 currentG0 (currentCDelta currentK) currentCy currentCp
      currentTau0)
    (A : DeterministicAlgorithm D) :
    ∃ Q : NCCInstance
        (currentAmbientPrimalDim ell D Delta eps)
        (currentAmbientDualDim ell D Delta eps),
      IsFunctionClass ell D Delta Q ∧
      DeterministicFOComponent.FailsWithin
        (A.component
          (currentAmbientPrimalDim ell D Delta eps)
          (currentAmbientDualDim ell D Delta eps))
        Q ell eps (currentStrictHorizon ell D Delta eps) ∧
      currentRateConstant * (ell ^ 2 * D * Delta / eps ^ 3) ≤
        (currentStrictHorizon ell D Delta eps : ℝ) := by
  obtain ⟨Q, hclass, hfail, hrate⟩ :=
    certified_family_hard_for_algorithm hell hD hDelta heps
      currentEll0_pos currentG0_pos currentCy_pos currentCp_pos
      (currentCDelta_pos currentK)
      (by simpa [currentAccuracyConstant] using haccuracy)
      current_terminal_scale P A
  refine ⟨Q, hclass, hfail, ?_⟩
  calc
    currentRateConstant * (ell ^ 2 * D * Delta / eps ^ 3) =
        (1 / 2 : ℝ) *
          ((currentG0 ^ 3 /
              (1024 * currentCy * currentCp * currentCDelta currentK *
                currentEll0 ^ 2)) *
            (ell ^ 2 * D * Delta / eps ^ 3)) := by
              unfold currentRateConstant
              ring
    _ ≤ (currentStrictHorizon ell D Delta eps : ℝ) := hrate

/-- Complete hard-instance endpoint for every corrected deterministic
dimension-polymorphic algorithm, instantiated with the literal current
five-component C1--C4 certificate. -/
theorem current_deterministic_lower_bound
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (haccuracy : eps ≤ currentAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta)))
    (A : DeterministicAlgorithm D) :
    ∃ Q : NCCInstance
        (currentAmbientPrimalDim ell D Delta eps)
        (currentAmbientDualDim ell D Delta eps),
      IsFunctionClass ell D Delta Q ∧
      DeterministicFOComponent.FailsWithin
        (A.component
          (currentAmbientPrimalDim ell D Delta eps)
          (currentAmbientDualDim ell D Delta eps))
        Q ell eps (currentStrictHorizon ell D Delta eps) ∧
      currentRateConstant * (ell ^ 2 * D * Delta / eps ^ 3) ≤
        (currentStrictHorizon ell D Delta eps : ℝ) := by
  obtain ⟨hN10, hM⟩ :=
    current_dimensions_of_accuracy hell hD hDelta heps haccuracy
  apply current_algorithm_has_hard_instance_of_properties
    hell hD hDelta heps haccuracy hM hN10
  · simpa [currentK, currentEll0] using
      (currentHardProperties hM hN10)

/-- Threshold form of the preceding algorithm-by-algorithm endpoint. -/
theorem current_complexity_lower_bound
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (haccuracy : eps ≤ currentAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    CurrentComplexityAtLeast ell D Delta eps
        (currentStrictHorizon ell D Delta eps) ∧
      currentRateConstant * (ell ^ 2 * D * Delta / eps ^ 3) ≤
        (currentStrictHorizon ell D Delta eps : ℝ) := by
  constructor
  · intro A
    obtain ⟨Q, hclass, hfail, _hrate⟩ :=
      current_deterministic_lower_bound hell hD hDelta heps haccuracy A
    exact ⟨Q, hclass, hfail⟩
  · exact currentStrictHorizon_rate hell hD hDelta heps haccuracy

/-- Canonical, unrotated reduction for the current five-component family.
This is the direct zero-respecting/coordinate-chain endpoint: it records the
actual scaled class member, exact value identity, signed zero-chain, terminal
failure, and the full (non-strict) chain-length rate in one kernel theorem. -/
theorem current_canonical_framework_reduction_of_properties
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (haccuracy : eps ≤ currentAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta)))
    (_hM : 1 ≤ currentM ell Delta eps)
    (hN10 : 10 ≤ currentN ell D eps)
    (P : UnscaledHardProperties
      (currentHardData
        (M := currentM ell Delta eps) (N := currentN ell D eps)
        (by omega) currentK)
      currentEll0 currentG0 (currentCDelta currentK) currentCy currentCp
      currentTau0) :
    let F := currentHardData
      (M := currentM ell Delta eps) (N := currentN ell D eps)
      (by omega : 0 < currentN ell D eps) currentK
    IsNCCClass ell D Delta
        (scaledFiniteInstance F ell currentEll0 eps currentG0 D) ∧
    ValueOn (scaledFiniteInstance F ell currentEll0 eps currentG0 D).Y
        (scaledFiniteInstance F ell currentEll0 eps currentG0 D).f =
      scaledFiniteValue F ell currentEll0 eps currentG0 D ∧
    NCPLVerification.IsFirstOrderZeroChain
      (scaledVectorField (frameworkLambda ell currentEll0 eps currentG0)
        (paperAmplitude ell currentEll0
          (frameworkLambda ell currentEll0 eps currentG0))
        (taggedSerializedSaddleFieldOf
          (T := currentM ell Delta eps + 1)
          (n := currentN ell D eps) F.gradX F.gradY)) ∧
    (∀ x,
      terminalStateValue x = 0 →
      ¬ IsOptimizationStationary Set.univ
        (ValueOn (scaledFiniteInstance F ell currentEll0 eps currentG0 D).Y
          (scaledFiniteInstance F ell currentEll0 eps currentG0 D).f)
        ell eps x) ∧
    currentG0 ^ 3 /
        (1024 * currentCy * currentCp * currentCDelta currentK *
          currentEll0 ^ 2) *
        (ell ^ 2 * D * Delta / eps ^ 3) ≤
      (currentH ell D Delta eps : ℝ) := by
  dsimp only
  simpa [currentM, currentN, currentH] using
    (canonical_framework_reduction hell hD hDelta heps
      currentEll0_pos currentG0_pos currentCy_pos currentCp_pos
      (currentCDelta_pos currentK)
      (by simpa [currentAccuracyConstant] using haccuracy)
      current_terminal_scale P)

/-- Assumption-free canonical zero-respecting reduction for the literal
current family.  Together with the resisting theorem above, this covers both
the coordinate-chain and arbitrary deterministic-algorithm endpoints. -/
theorem current_canonical_zero_respecting_lower_bound
    {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps)
    (haccuracy : eps ≤ currentAccuracyConstant *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    let F := currentHardData
      (M := currentM ell Delta eps) (N := currentN ell D eps)
      (by
        have hdims := current_dimensions_of_accuracy
          hell hD hDelta heps haccuracy
        omega : 0 < currentN ell D eps) currentK
    IsNCCClass ell D Delta
        (scaledFiniteInstance F ell currentEll0 eps currentG0 D) ∧
    ValueOn (scaledFiniteInstance F ell currentEll0 eps currentG0 D).Y
        (scaledFiniteInstance F ell currentEll0 eps currentG0 D).f =
      scaledFiniteValue F ell currentEll0 eps currentG0 D ∧
    NCPLVerification.IsFirstOrderZeroChain
      (scaledVectorField (frameworkLambda ell currentEll0 eps currentG0)
        (paperAmplitude ell currentEll0
          (frameworkLambda ell currentEll0 eps currentG0))
        (taggedSerializedSaddleFieldOf
          (T := currentM ell Delta eps + 1)
          (n := currentN ell D eps) F.gradX F.gradY)) ∧
    (∀ x,
      terminalStateValue x = 0 →
      ¬ IsOptimizationStationary Set.univ
        (ValueOn (scaledFiniteInstance F ell currentEll0 eps currentG0 D).Y
          (scaledFiniteInstance F ell currentEll0 eps currentG0 D).f)
        ell eps x) ∧
    currentG0 ^ 3 /
        (1024 * currentCy * currentCp * currentCDelta currentK *
          currentEll0 ^ 2) *
        (ell ^ 2 * D * Delta / eps ^ 3) ≤
      (currentH ell D Delta eps : ℝ) := by
  obtain ⟨hN10, hM⟩ :=
    current_dimensions_of_accuracy hell hD hDelta heps haccuracy
  apply current_canonical_framework_reduction_of_properties
    hell hD hDelta heps haccuracy hM hN10
  simpa [currentK, currentEll0] using
    (currentHardProperties hM hN10)

/-! ## Positive-universal-constants form -/

/-- Existential-constant statement in the exact corrected algorithm model.
The returned query budget is positive and is the strict horizon `H - 1`. -/
theorem exists_constants_current_deterministic_lower_bound :
    ∃ cacc crate : ℝ,
      0 < cacc ∧ 0 < crate ∧
      ∀ {ell D Delta eps : ℝ},
        0 < ell → 0 < D → 0 < Delta → 0 < eps →
        eps ≤ cacc * min (ell * D) (Real.sqrt (ell * Delta)) →
        ∀ A : DeterministicAlgorithm D,
          ∃ (m n T : Nat) (Q : NCCInstance m n),
            IsFunctionClass ell D Delta Q ∧
            DeterministicFOComponent.FailsWithin
              (A.component m n) Q ell eps T ∧
            0 < T ∧
            crate * (ell ^ 2 * D * Delta / eps ^ 3) ≤ (T : ℝ) := by
  refine ⟨currentAccuracyConstant, currentRateConstant,
    currentAccuracyConstant_pos, currentRateConstant_pos, ?_⟩
  intro ell D Delta eps hell hD hDelta heps haccuracy A
  obtain ⟨Q, hclass, hfail, hrate⟩ :=
    current_deterministic_lower_bound hell hD hDelta heps haccuracy A
  refine ⟨currentAmbientPrimalDim ell D Delta eps,
    currentAmbientDualDim ell D Delta eps,
    currentStrictHorizon ell D Delta eps, Q, hclass, hfail, ?_, hrate⟩
  exact currentStrictHorizon_pos hell hD hDelta heps haccuracy

/-!
The analytic certificate consumed above is
`CurrentHardProperties.currentHardProperties`; no additional analytic
assumption remains in either endpoint.
-/

end

end CurrentLowerBound
end Simplified
end NCCLowerBound
