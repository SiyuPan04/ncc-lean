import NCCLowerBound.Simplified.MoreauBridge
import NCCLowerBound.Simplified.Scaling
import NCCLowerBoundVerification.DiameterBall
import NCCLowerBoundVerification.Lower.AccuracyRegime
import NCCLowerBoundVerification.Lower.TaggedResisting

/-!
# Type-safe abstract reduction for the simplified hard instance

This file formalizes the reusable part of lines 638--860 of the manuscript.
The unscaled assumptions are properties of actual functions, actual Fréchet
gradients, actual maximizers, and actual value functions.  In particular, no
field assumes class membership, oracle failure, or the desired complexity
lower bound.

The finite and unbounded dual domains are distinguished by `DualScope`; this
avoids treating the symbol `∞` as a real number.  The lower-bound reduction
uses the finite constructor, while the unbounded clauses faithfully record
the corresponding parts of Condition C3 and C4.
-/

namespace NCCLowerBound
namespace Simplified
namespace Framework

noncomputable section

open scoped BigOperators
open NCCLowerBoundVerification

/-! ## Typed formulation of Condition C1--C4 -/

/-- A genuine sum type for either a positive finite diameter or no dual
constraint. -/
inductive DualScope where
  | finite (diameter : ℝ) (positive : 0 < diameter)
  | unbounded

/-- The dual domain represented by a `DualScope`. -/
def dualDomain (d : Nat) : DualScope → Set (EVec d)
  | .finite D _ => diameterBall d D
  | .unbounded => Set.univ

/-- The primal vector has one `(aᵢ,bᵢ,sᵢ)` triple per outer block.  This is
the same fixed coordinate permutation used by the verified resisting-oracle
library. -/
abbrev Primal (M : Nat) := UnscaledPrimal (M + 1)

/-- There are `N` dual relay coordinates per outer block. -/
abbrev Dual (M N : Nat) := UnscaledDual (M + 1) N

/-- The serialized saddle chain has order
`aᵢ,yᵢ,₁,...,yᵢ,N,bᵢ,sᵢ`. -/
abbrev ChainSpace (M N : Nat) := SerializedSpace (M + 1) N

/-- Index of the last `s` coordinate when at least one outer block exists. -/
def terminalIndex {M : Nat} (hM : 1 ≤ M) :
    Fin (3 * ((M + 1) - 1)) :=
  primalStateIndex (T := M + 1) ⟨M - 1, by omega⟩

/-- The final state coordinate, made total for `M = 0`.  All reduction
theorems establish `1 ≤ M`, so the nonempty branch is the one consumed there.
-/
def terminalStateValue {M : Nat} (x : Primal M) : ℝ :=
  if hM : 1 ≤ M then
    x (terminalIndex hM)
  else 0

theorem terminalStateValue_eq {M : Nat} (hM : 1 ≤ M) (x : Primal M) :
    terminalStateValue x =
      x (terminalIndex hM) := by
  simp [terminalStateValue, hM]

/-- Function data for one unscaled `(M,N)` hard instance.  `valueGrad q` is
not an arbitrary certificate: C1 below requires it to represent the actual
Fréchet derivative of `ValueOn (dualDomain q) f`. -/
structure UnscaledHardData (M N : Nat) where
  f : Primal M → Dual M N → ℝ
  gradX : Primal M → Dual M N → Primal M
  gradY : Primal M → Dual M N → Dual M N
  valueGrad : DualScope → Primal M → Primal M
  unconstrainedMaximizer : Primal M → Dual M N

/--
Type-safe version of Condition C1--C4.

* C1 records the actual joint derivative, dimension-free smoothness, genuine
  strong concavity, attainment, and the actual derivative of every value.
* C2 is the literal signed saddle zero-chain in the manuscript's order.
* C3 records the maximizer-growth, inactivity, and terminal certificates.
* C4 records boundedness below and the initial gap of the actual value image.

The squared Euclidean form is equivalent to the norm form and is the native
form used throughout the verification library.
-/
structure UnscaledHardProperties {M N : Nat} (F : UnscaledHardData M N)
    (ell0 g0 cDelta cy cp tau0 : ℝ) : Prop where
  ell0_pos : 0 < ell0
  g0_pos : 0 < g0
  cDelta_pos : 0 < cDelta
  cy_pos : 0 < cy
  cp_pos : 0 < cp
  tau0_pos : 0 < tau0

  /- C1: regularity and literal maximizers/value gradients. -/
  c1_gradient_representation :
    NCPLVerification.RepresentsJointGradient F.f F.gradX F.gradY
  c1_jointly_smooth :
    NCPLVerification.IsJointlySmooth ell0 F.gradX F.gradY
  c1_dual_strongly_concave :
    ∃ mu0 : ℝ, 0 < mu0 ∧
      ∀ x, StrongConcaveOn Set.univ mu0 (F.f x)
  c1_maximum_attained : ∀ q x,
    ∃ y, IsMaximizerOn (dualDomain (N * M) q) F.f x y
  c1_value_gradient : ∀ q,
    RepresentsGradient (ValueOn (dualDomain (N * M) q) F.f)
      (F.valueGrad q)

  /- C2: the actual signed joint gradient is a zero-chain. -/
  c2_saddle_zero_chain :
    NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf
        (T := M + 1) (n := N) F.gradX F.gradY)

  /- C3(a): unconstrained maximizer and its dimension-linear growth. -/
  c3_unconstrained_isMaximizer : ∀ x,
    IsMaximizerOn Set.univ F.f x (F.unconstrainedMaximizer x)
  c3_maximizer_growth : ∀ x,
    vecSq (F.unconstrainedMaximizer x) ≤
      (cy * (N : ℝ)) ^ 2 * pulseSq x

  /- C3(b): a small restricted-value gradient bounds the pulse variables. -/
  c3_dual_inactivity : ∀ q x,
    terminalStateValue x ≤ (1 / 5 : ℝ) →
    vecSq (F.valueGrad q x) ≤ tau0 ^ 2 →
    pulseSq x ≤ cp ^ 2

  /- C3(c): finite and unbounded terminal obstruction. -/
  c3_terminal_finite : ∀ (D : ℝ) (hD : 0 < D) x,
    (N : ℝ) ≤ D / (2 * cy * cp) →
    terminalStateValue x ≤ (1 / 5 : ℝ) →
    g0 ^ 2 ≤ vecSq (F.valueGrad (.finite D hD) x)
  c3_terminal_unbounded : ∀ x,
    terminalStateValue x ≤ (1 / 5 : ℝ) →
    g0 ^ 2 ≤ vecSq (F.valueGrad .unbounded x)

  /- C4: the actual infimum is meaningful and has the claimed gap. -/
  c4_value_bddBelow : ∀ q,
    BddBelow (Set.range (ValueOn (dualDomain (N * M) q) F.f))
  c4_initial_gap : ∀ q,
    ValueOn (dualDomain (N * M) q) F.f 0 -
        sInf (Set.range (ValueOn (dualDomain (N * M) q) F.f)) ≤
      cDelta * (M + 1)

/-! ## Consequences that should not be hidden inside C3 -/

theorem pulseSq_nonneg {M : Nat} (x : Primal M) : 0 ≤ pulseSq x := by
  unfold pulseSq
  exact Finset.sum_nonneg fun i _ => by positivity

/-- The two implications in C3(a,b) really imply that the unconstrained
maximizer lies in the radius-`D/2` ball. -/
theorem UnscaledHardProperties.unconstrainedMaximizer_mem_halfBall
    {M N : Nat} {F : UnscaledHardData M N}
    {ell0 g0 cDelta cy cp tau0 D : ℝ}
    (P : UnscaledHardProperties F ell0 g0 cDelta cy cp tau0)
    (hD : 0 < D) (q : DualScope) (x : Primal M)
    (hstate : terminalStateValue x ≤ (1 / 5 : ℝ))
    (hsmall : vecSq (F.valueGrad q x) ≤ tau0 ^ 2)
    (hsize : (N : ℝ) ≤ D / (2 * cy * cp)) :
    F.unconstrainedMaximizer x ∈ diameterBall (N * M) D := by
  have hpulse : pulseSq x ≤ cp ^ 2 :=
    P.c3_dual_inactivity q x hstate hsmall
  have hcyN0 : 0 ≤ cy * (N : ℝ) :=
    mul_nonneg P.cy_pos.le (Nat.cast_nonneg N)
  have hlinear : cy * (N : ℝ) * cp ≤ D / 2 := by
    have hden : 0 < 2 * cy * cp :=
      mul_pos (mul_pos (by norm_num) P.cy_pos) P.cp_pos
    have hmul := (le_div_iff₀ hden).mp hsize
    nlinarith
  have hsquare : (cy * (N : ℝ) * cp) ^ 2 ≤ (D / 2) ^ 2 := by
    exact (sq_le_sq₀ (mul_nonneg hcyN0 P.cp_pos.le)
      (div_nonneg hD.le (by norm_num))).2 hlinear
  change vecSq (F.unconstrainedMaximizer x) ≤ (D / 2) ^ 2
  calc
    vecSq (F.unconstrainedMaximizer x) ≤
        (cy * (N : ℝ)) ^ 2 * pulseSq x := P.c3_maximizer_growth x
    _ ≤ (cy * (N : ℝ)) ^ 2 * cp ^ 2 :=
      mul_le_mul_of_nonneg_left hpulse (sq_nonneg _)
    _ = (cy * (N : ℝ) * cp) ^ 2 := by ring
    _ ≤ (D / 2) ^ 2 := hsquare

/-! ## Exact analytic scaling -/

/-- The finite-radius instance whose fields are the actual C1 data. -/
def finiteInstance {M N : Nat} (F : UnscaledHardData M N) (D : ℝ) :
    NCCInstance (3 * ((M + 1) - 1)) (N * ((M + 1) - 1)) where
  X := Set.univ
  Y := diameterBall (N * M) D
  f := F.f
  gradX := F.gradX
  gradY := F.gradY
  x0 := 0

/-- C1 and C4 supply the exact `ScalingSource`; the only extra premise is an
honest numerical gap budget, not the desired scaled class conclusion. -/
theorem UnscaledHardProperties.toScalingSource
    {M N : Nat} {F : UnscaledHardData M N}
    {ell0 g0 cDelta cy cp tau0 D Delta0 : ℝ}
    (P : UnscaledHardProperties F ell0 g0 cDelta cy cp tau0)
    (hD : 0 < D) (hgapBudget : cDelta * (M + 1) ≤ Delta0) :
    ScalingSource ell0 D Delta0 (finiteInstance F D) := by
  rcases P.c1_dual_strongly_concave with ⟨mu0, hmu0, hstrong⟩
  refine
    { x0_mem := Set.mem_univ _
      X_nonempty := Set.univ_nonempty
      X_closed := isClosed_univ
      X_convex := convex_univ
      Y_nonempty := diameterBall_nonempty _ _ hD.le
      Y_closed := diameterBall_closed _ _
      Y_convex := diameterBall_convex _ _
      gradient_representation := P.c1_gradient_representation
      jointly_smooth := ?_
      dual_concave := ?_
      maximum_attained := ?_
      value_bddBelow := ?_
      initial_gap := ?_
      dual_diameter := ?_ }
  · intro x _ y _ x' _ y' _
    exact P.c1_jointly_smooth x y x' y'
  · intro x _
    have hzero : StrongConcaveOn Set.univ 0 (F.f x) :=
      (hstrong x).mono hmu0.le
    have hall : ConcaveOn ℝ Set.univ (F.f x) :=
      strongConcaveOn_zero.mp hzero
    refine ⟨diameterBall_convex _ _, ?_⟩
    intro y _ z _ a b ha hb hab
    exact hall.2 (Set.mem_univ y) (Set.mem_univ z) ha hb hab
  · intro x _
    simpa [finiteInstance, dualDomain] using
      P.c1_maximum_attained (.finite D hD) x
  · simpa [finiteInstance, dualDomain] using
      P.c4_value_bddBelow (.finite D hD)
  · have hgap := P.c4_initial_gap (.finite D hD)
    simpa [finiteInstance, dualDomain] using hgap.trans hgapBudget
  · intro y hy y' hy'
    exact diameterBall_vecSq_sub_le hD.le hy hy'

/-- Exact value identity from the genuine finite-domain maximizers in C1. -/
theorem UnscaledHardProperties.exact_scaled_value
    {M N : Nat} {F : UnscaledHardData M N}
    {ell0 g0 cDelta cy cp tau0 D ell lambda : ℝ}
    (P : UnscaledHardProperties F ell0 g0 cDelta cy cp tau0)
    (hD : 0 < D) (hell : 0 < ell) (hlambda : 0 < lambda) :
    ValueOn (scaledDomain lambda (diameterBall (N * M) D))
        (scaledObjective lambda (paperAmplitude ell ell0 lambda) F.f) =
      scaledScalar lambda (paperAmplitude ell ell0 lambda)
        (ValueOn (diameterBall (N * M) D) F.f) := by
  apply exact_value_scaling hlambda.ne'
  · unfold paperAmplitude
    exact div_nonneg (mul_nonneg hell.le (sq_nonneg lambda)) P.ell0_pos.le
  · intro x
    simpa [dualDomain] using P.c1_maximum_attained (.finite D hD) x

/-- Exact class scaling once the unscaled gap is within the target budget. -/
theorem UnscaledHardProperties.scaledInstance_isNCCClass
    {M N : Nat} {F : UnscaledHardData M N}
    {ell0 g0 cDelta cy cp tau0 ell D Delta lambda : ℝ}
    (P : UnscaledHardProperties F ell0 g0 cDelta cy cp tau0)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (hlambda : 0 < lambda)
    (hgapBudget : cDelta * (M + 1) ≤
      Delta / paperAmplitude ell ell0 lambda) :
    IsNCCClass ell D Delta
      (scaleNCCInstance lambda (paperAmplitude ell ell0 lambda)
        (finiteInstance F (D / lambda))) := by
  apply paper_scaleNCCInstance_isNCCClass hell P.ell0_pos hD hDelta hlambda
  exact P.toScalingSource (by positivity) hgapBudget

/-! ## Canonical parameters and the two floor losses -/

def frameworkLambda (ell ell0 eps g0 : ℝ) : ℝ :=
  lowerScale ell ell0 eps g0

def frameworkN (D cy cp ell ell0 eps g0 : ℝ) : Nat :=
  lowerN D cy cp ell ell0 eps g0

/-- `lowerT` is the manuscript's outer quantity before subtracting one. -/
def frameworkM (Delta cDelta ell ell0 eps g0 : ℝ) : Nat :=
  lowerT Delta cDelta ell ell0 eps g0 - 1

def frameworkH (ell D Delta eps ell0 g0 cy cp cDelta : ℝ) : Nat :=
  frameworkM Delta cDelta ell ell0 eps g0 *
    (frameworkN D cy cp ell ell0 eps g0 + 3)

def frameworkAccuracyConstant
    (ell0 g0 cy cp cDelta : ℝ) : ℝ :=
  lowerAccuracyConstant ell0 g0 cy cp cDelta

theorem frameworkAccuracyConstant_pos
    {ell0 g0 cy cp cDelta : ℝ}
    (hell0 : 0 < ell0) (hg0 : 0 < g0) (hcy : 0 < cy)
    (hcp : 0 < cp) (hcDelta : 0 < cDelta) :
    0 < frameworkAccuracyConstant ell0 g0 cy cp cDelta := by
  exact lowerAccuracyConstant_pos hell0 hg0 hcy hcp hcDelta

theorem framework_size_regime_of_accuracy
    {ell D Delta eps ell0 g0 cy cp cDelta : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps) (hell0 : 0 < ell0) (hg0 : 0 < g0)
    (hcy : 0 < cy) (hcp : 0 < cp) (hcDelta : 0 < cDelta)
    (haccuracy : eps ≤ frameworkAccuracyConstant ell0 g0 cy cp cDelta *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    20 ≤ g0 * ell * D / (8 * cy * cp * ell0 * eps) ∧
      4 ≤ g0 ^ 2 * ell * Delta /
        (32 * cDelta * ell0 * eps ^ 2) := by
  exact lower_size_regime_of_accuracy hell hD hDelta heps hell0 hg0
    hcy hcp hcDelta haccuracy

/-- The accuracy regime really makes the selected dimensions admissible:
`N ≥ 10` and `M ≥ 1`. -/
theorem framework_dimensions_of_regime
    {ell D Delta eps ell0 g0 cy cp cDelta : ℝ}
    (hell : 0 < ell) (heps : 0 < eps) (hell0 : 0 < ell0)
    (hg0 : 0 < g0) (hcy : 0 < cy) (hcp : 0 < cp)
    (hcDelta : 0 < cDelta)
    (hNregime : 20 ≤ g0 * ell * D / (8 * cy * cp * ell0 * eps))
    (hMregime : 4 ≤ g0 ^ 2 * ell * Delta /
      (32 * cDelta * ell0 * eps ^ 2)) :
    10 ≤ frameworkN D cy cp ell ell0 eps g0 ∧
      1 ≤ frameworkM Delta cDelta ell ell0 eps g0 := by
  have hNeq := lowerNArg_eq (D := D) (Cy := cy) (P1 := cp)
    hcy.ne' hcp.ne' hell.ne' hell0.ne' heps.ne' hg0.ne'
  have hMeq := lowerTArg_eq (Delta := Delta) (cDelta := cDelta)
    hcDelta.ne' hell.ne' hell0.ne' heps.ne' hg0.ne'
  have hNraw : 20 ≤ lowerNArg D cy cp ell ell0 eps g0 := by
    rw [hNeq]
    exact hNregime
  have hMraw : 4 ≤ lowerTArg Delta cDelta ell ell0 eps g0 := by
    rw [hMeq]
    exact hMregime
  have hNfloor := half_le_natFloor (by linarith :
    2 ≤ lowerNArg D cy cp ell ell0 eps g0)
  have hMfloor := half_le_natFloor (by linarith :
    2 ≤ lowerTArg Delta cDelta ell ell0 eps g0)
  constructor
  · have hreal : (10 : ℝ) ≤
        (lowerN D cy cp ell ell0 eps g0 : ℝ) := by
      change (10 : ℝ) ≤
        (⌊lowerNArg D cy cp ell ell0 eps g0⌋₊ : ℝ)
      linarith
    simpa [frameworkN] using (show 10 ≤ lowerN D cy cp ell ell0 eps g0 by
      exact_mod_cast hreal)
  · have hreal : (2 : ℝ) ≤
        (lowerT Delta cDelta ell ell0 eps g0 : ℝ) := by
      change (2 : ℝ) ≤
        (⌊lowerTArg Delta cDelta ell ell0 eps g0⌋₊ : ℝ)
      linarith
    have hnat : 2 ≤ lowerT Delta cDelta ell ell0 eps g0 := by
      exact_mod_cast hreal
    simp only [frameworkM]
    omega

/-- The inner floor is no larger than the exact finite-ball inactivity
threshold `D/(2 c_y c_p lambda)`. -/
theorem frameworkN_size_condition
    {ell D eps ell0 g0 cy cp : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps)
    (hell0 : 0 < ell0) (hg0 : 0 < g0)
    (hcy : 0 < cy) (hcp : 0 < cp) :
    (frameworkN D cy cp ell ell0 eps g0 : ℝ) ≤
      (D / frameworkLambda ell ell0 eps g0) / (2 * cy * cp) := by
  have hfloor : (lowerN D cy cp ell ell0 eps g0 : ℝ) ≤
      lowerNArg D cy cp ell ell0 eps g0 := by
    unfold lowerN
    apply Nat.floor_le
    unfold lowerNArg lowerScale
    positivity
  calc
    (frameworkN D cy cp ell ell0 eps g0 : ℝ) ≤
        lowerNArg D cy cp ell ell0 eps g0 := by
      simpa [frameworkN] using hfloor
    _ = (D / frameworkLambda ell ell0 eps g0) /
        (2 * cy * cp) := by
      unfold lowerNArg frameworkLambda
      field_simp [hcy.ne', hcp.ne']

/-- The outer floor leaves the factor-two gap slack used in the paper. -/
theorem framework_gap_budget
    {ell Delta eps ell0 g0 cDelta : ℝ}
    (hell : 0 < ell) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hell0 : 0 < ell0) (hg0 : 0 < g0) (hcDelta : 0 < cDelta)
    (hMregime : 4 ≤ g0 ^ 2 * ell * Delta /
      (32 * cDelta * ell0 * eps ^ 2)) :
    cDelta * (frameworkM Delta cDelta ell ell0 eps g0 + 1) ≤
      Delta / paperAmplitude ell ell0
        (frameworkLambda ell ell0 eps g0) := by
  have hMeq := lowerTArg_eq (Delta := Delta) (cDelta := cDelta)
    hcDelta.ne' hell.ne' hell0.ne' heps.ne' hg0.ne'
  have hraw : 4 ≤ lowerTArg Delta cDelta ell ell0 eps g0 := by
    rw [hMeq]
    exact hMregime
  have hfloorTwoReal : (2 : ℝ) ≤
      (lowerT Delta cDelta ell ell0 eps g0 : ℝ) := by
    have hhalf := half_le_natFloor (by linarith :
      2 ≤ lowerTArg Delta cDelta ell ell0 eps g0)
    change (2 : ℝ) ≤
      (⌊lowerTArg Delta cDelta ell ell0 eps g0⌋₊ : ℝ)
    linarith
  have hfloorTwo : 2 ≤ lowerT Delta cDelta ell ell0 eps g0 := by
    exact_mod_cast hfloorTwoReal
  have hcast :
      ((frameworkM Delta cDelta ell ell0 eps g0 + 1 : Nat) : ℝ) =
        (lowerT Delta cDelta ell ell0 eps g0 : ℝ) := by
    simp only [frameworkM]
    congr 1
    omega
  have hfloor : (lowerT Delta cDelta ell ell0 eps g0 : ℝ) ≤
      lowerTArg Delta cDelta ell ell0 eps g0 := by
    unfold lowerT
    apply Nat.floor_le
    unfold lowerTArg lowerScale
    positivity
  have hmul := mul_le_mul_of_nonneg_left hfloor hcDelta.le
  have hcast' :
      (frameworkM Delta cDelta ell ell0 eps g0 : ℝ) + 1 =
        (lowerT Delta cDelta ell ell0 eps g0 : ℝ) := by
    rw [← Nat.cast_one, ← Nat.cast_add, hcast]
  rw [hcast']
  calc
    cDelta * (lowerT Delta cDelta ell ell0 eps g0 : ℝ) ≤
        cDelta * lowerTArg Delta cDelta ell ell0 eps g0 := hmul
    _ = Delta /
        (2 * paperAmplitude ell ell0
          (frameworkLambda ell ell0 eps g0)) := by
      unfold lowerTArg frameworkLambda paperAmplitude lowerScale
      field_simp [hell.ne', hell0.ne', heps.ne', hg0.ne', hcDelta.ne']
    _ ≤ Delta /
        paperAmplitude ell ell0 (frameworkLambda ell ell0 eps g0) := by
      have hamp : 0 < paperAmplitude ell ell0
          (frameworkLambda ell ell0 eps g0) := by
        unfold paperAmplitude frameworkLambda lowerScale
        positivity
      have hq : 0 ≤ Delta /
          paperAmplitude ell ell0 (frameworkLambda ell ell0 eps g0) :=
        div_nonneg hDelta.le hamp.le
      calc
        Delta / (2 * paperAmplitude ell ell0
            (frameworkLambda ell ell0 eps g0)) =
          (Delta / paperAmplitude ell ell0
            (frameworkLambda ell ell0 eps g0)) / 2 := by
              field_simp [hamp.ne']
        _ ≤ _ := by linarith

/-- Both floor losses, with an explicit universal constant.  This is the
formal `M(N+3)=Omega(ell^2 D Delta / eps^3)` calculation. -/
theorem framework_chain_length_lower_of_regime
    {ell D Delta eps ell0 g0 cy cp cDelta : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps) (hell0 : 0 < ell0) (hg0 : 0 < g0)
    (hcy : 0 < cy) (hcp : 0 < cp) (hcDelta : 0 < cDelta)
    (hNregime : 20 ≤ g0 * ell * D / (8 * cy * cp * ell0 * eps))
    (hMregime : 4 ≤ g0 ^ 2 * ell * Delta /
      (32 * cDelta * ell0 * eps ^ 2)) :
    g0 ^ 3 / (1024 * cy * cp * cDelta * ell0 ^ 2) *
        (ell ^ 2 * D * Delta / eps ^ 3) ≤
      (frameworkH ell D Delta eps ell0 g0 cy cp cDelta : ℝ) := by
  simpa [frameworkH, frameworkM, frameworkN] using
    scaled_chain_length_lower hell hD hDelta heps hell0 hg0 hcy hcp
      hcDelta hNregime hMregime

theorem framework_chain_length_lower_of_accuracy
    {ell D Delta eps ell0 g0 cy cp cDelta : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps) (hell0 : 0 < ell0) (hg0 : 0 < g0)
    (hcy : 0 < cy) (hcp : 0 < cp) (hcDelta : 0 < cDelta)
    (haccuracy : eps ≤ frameworkAccuracyConstant ell0 g0 cy cp cDelta *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    g0 ^ 3 / (1024 * cy * cp * cDelta * ell0 ^ 2) *
        (ell ^ 2 * D * Delta / eps ^ 3) ≤
      (frameworkH ell D Delta eps ell0 g0 cy cp cDelta : ℝ) := by
  obtain ⟨hN, hM⟩ := framework_size_regime_of_accuracy hell hD hDelta
    heps hell0 hg0 hcy hcp hcDelta haccuracy
  exact framework_chain_length_lower_of_regime hell hD hDelta heps hell0
    hg0 hcy hcp hcDelta hN hM

/-! ## The exact Moreau terminal contradiction -/

private theorem hasEVecFDerivAt_of_representsGradient
    {m : Nat} {phi : EVec m → ℝ} {g : EVec m → EVec m}
    (hrep : RepresentsGradient phi g) (x : EVec m) :
    NCPLVerification.HasEVecFDerivAt phi
      (NCPLVerification.evecDot (g x)) x := by
  have heq : fderiv ℝ phi x = NCPLVerification.evecDot (g x) := by
    ext h
    rw [hrep.2]
    simp [NCPLVerification.evecDot_apply]
  rw [← heq]
  exact (hrep.1 x).hasFDerivAt

/-- The scaled finite-dual value used by the framework theorem. -/
def scaledFiniteValue {M N : Nat} (F : UnscaledHardData M N)
    (ell ell0 eps g0 D : ℝ) : Primal M → ℝ :=
  let lambda := frameworkLambda ell ell0 eps g0
  scaledScalar lambda (paperAmplitude ell ell0 lambda)
    (ValueOn (diameterBall (N * M) (D / lambda)) F.f)

/-- The actual scaled saddle instance paired with `scaledFiniteValue`. -/
def scaledFiniteInstance {M N : Nat} (F : UnscaledHardData M N)
    (ell ell0 eps g0 D : ℝ) :
    NCCInstance (3 * ((M + 1) - 1)) (N * ((M + 1) - 1)) :=
  let lambda := frameworkLambda ell ell0 eps g0
  scaleNCCInstance lambda (paperAmplitude ell ell0 lambda)
    (finiteInstance F (D / lambda))

/-- The value of the actual scaled saddle instance is definitionally linked,
via C1 attainment and the exact scaling theorem, to `scaledFiniteValue`. -/
theorem UnscaledHardProperties.scaledFiniteInstance_value_eq
    {M N : Nat} {F : UnscaledHardData M N}
    {ell0 g0 cDelta cy cp tau0 ell D eps : ℝ}
    (P : UnscaledHardProperties F ell0 g0 cDelta cy cp tau0)
    (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) :
    ValueOn (scaledFiniteInstance F ell ell0 eps g0 D).Y
        (scaledFiniteInstance F ell ell0 eps g0 D).f =
      scaledFiniteValue F ell ell0 eps g0 D := by
  let lambda := frameworkLambda ell ell0 eps g0
  have hlambda : 0 < lambda := by
    dsimp [lambda, frameworkLambda, lowerScale]
    exact div_pos (mul_pos (mul_pos (by norm_num) P.ell0_pos) heps)
      (mul_pos P.g0_pos hell)
  have hD0 : 0 < D / lambda := div_pos hD hlambda
  simpa [scaledFiniteInstance, scaledFiniteValue, scaleNCCInstance,
    finiteInstance, lambda] using
    P.exact_scaled_value hD0 hell hlambda

/-- Exact terminal contradiction in the corrected, type-safe model.  The
proof expands the paper's Moreau/prox argument: coordinate displacement gives
`s_M ≤ 1/5`, C3(c) gives the source gradient lower bound, exact scaling turns
it into `4 eps`, and proximal first-order optimality bounds it by `eps`. -/
theorem UnscaledHardProperties.scaled_terminal_not_OS
    {M N : Nat} {F : UnscaledHardData M N}
    {ell0 g0 cDelta cy cp tau0 ell D eps : ℝ}
    (P : UnscaledHardProperties F ell0 g0 cDelta cy cp tau0)
    (hM : 1 ≤ M) (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps)
    (hterminalScale : g0 / (8 * ell0) ≤ (1 / 5 : ℝ))
    (hsize : (N : ℝ) ≤
      (D / frameworkLambda ell ell0 eps g0) / (2 * cy * cp))
    {x : Primal M} (hxterminal : terminalStateValue x = 0) :
    ¬ IsOptimizationStationary Set.univ
      (scaledFiniteValue F ell ell0 eps g0 D) ell eps x := by
  let lambda := frameworkLambda ell ell0 eps g0
  let amp := paperAmplitude ell ell0 lambda
  let D0 := D / lambda
  have hlambda : 0 < lambda := by
    dsimp [lambda, frameworkLambda, lowerScale]
    exact div_pos (mul_pos (mul_pos (by norm_num) P.ell0_pos) heps)
      (mul_pos P.g0_pos hell)
  have hamp : 0 < amp := by
    dsimp [amp, paperAmplitude]
    exact div_pos (mul_pos hell (sq_pos_of_pos hlambda)) P.ell0_pos
  have hD0 : 0 < D0 := by
    dsimp [D0]
    exact div_pos hD hlambda
  let q : DualScope := .finite D0 hD0
  let phi0 : Primal M → ℝ := ValueOn (diameterBall (N * M) D0) F.f
  let g0fun : Primal M → Primal M := F.valueGrad q
  let phi : Primal M → ℝ := scaledScalar lambda amp phi0
  let g : Primal M → Primal M := scaledScalarGrad lambda amp g0fun
  have hrep0 : RepresentsGradient phi0 g0fun := by
    dsimp [phi0, g0fun, q]
    simpa [dualDomain] using P.c1_value_gradient (.finite D0 hD0)
  have hrep : RepresentsGradient phi g := by
    exact scaledScalar_representsGradient hrep0 lambda amp
  have hxcoord :
      x (terminalIndex hM) = 0 := by
    simpa [terminalStateValue, hM] using hxterminal
  rintro ⟨u, hu, hdist⟩
  have hr : 0 ≤ eps / (2 * ell) := by positivity
  have hucoord :
      |u (terminalIndex hM)| ≤
        eps / (2 * ell) :=
    coordinate_displacement_le hr hdist _ hxcoord
  have hratio : eps / (2 * ell * lambda) = g0 / (8 * ell0) := by
    simpa [lambda, frameworkLambda] using
      (paper_terminal_ratio (ell := ell) (ell0 := ell0)
        (eps := eps) (c0 := g0) hell.ne' P.ell0_pos.ne'
        heps.ne' P.g0_pos.ne')
  have husourceAbs :
      |unscaleCoords lambda u
          (terminalIndex hM)| ≤
        (1 / 5 : ℝ) := by
    unfold unscaleCoords
    rw [abs_div, abs_of_pos hlambda]
    calc
      |u (terminalIndex hM)| / lambda ≤
          (eps / (2 * ell)) / lambda :=
        div_le_div_of_nonneg_right hucoord hlambda.le
      _ = eps / (2 * ell * lambda) := by ring
      _ = g0 / (8 * ell0) := hratio
      _ ≤ (1 / 5 : ℝ) := hterminalScale
  have hustate : terminalStateValue (unscaleCoords lambda u) ≤
      (1 / 5 : ℝ) := by
    rw [terminalStateValue_eq hM]
    exact (le_abs_self _).trans husourceAbs
  have hsource : g0 ^ 2 ≤
      vecSq (g0fun (unscaleCoords lambda u)) := by
    have hs := P.c3_terminal_finite D0 hD0
      (unscaleCoords lambda u) (by simpa [D0, lambda] using hsize) hustate
    simpa [g0fun, q] using hs
  have hlower : (4 * eps) ^ 2 ≤ vecSq (g u) := by
    simpa [g, g0fun, amp, lambda, frameworkLambda,
      paperAmplitude_eq_lowerAmplitude] using
      (paper_scaled_gradient_threshold (ell := ell) (ell0 := ell0)
        (eps := eps) (c0 := g0) hell P.ell0_pos heps P.g0_pos
        (g := g0fun) (x := u) hsource)
  have hderiv : NCPLVerification.HasEVecFDerivAt phi
      (NCPLVerification.evecDot (g u)) u :=
    hasEVecFDerivAt_of_representsGradient hrep u
  have heq := proxPoint_gradient_equation hu hderiv
  have hgrad : g u = (-2 * ell) • (u - x) := by
    funext j
    have hj := congrFun heq j
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hj ⊢
    linarith
  have hupper : vecSq (g u) ≤ eps ^ 2 := by
    rw [hgrad, vecSq_smul']
    have hs := mul_le_mul_of_nonneg_left hdist (sq_nonneg (-2 * ell))
    calc
      (-2 * ell) ^ 2 * vecSq (u - x) ≤
          (-2 * ell) ^ 2 * (eps / (2 * ell)) ^ 2 := hs
      _ = eps ^ 2 := by field_simp [hell.ne']
  nlinarith [sq_pos_of_pos heps]

/-! ## One theorem assembling the typed reduction at the canonical floors -/

/-- The independent outputs of the abstract reduction: admissible dimensions,
the exact finite-ball size condition, the gap budget needed by scaling, and
the explicit cubic horizon lower bound. -/
theorem framework_parameter_package
    {ell D Delta eps ell0 g0 cy cp cDelta : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps) (hell0 : 0 < ell0) (hg0 : 0 < g0)
    (hcy : 0 < cy) (hcp : 0 < cp) (hcDelta : 0 < cDelta)
    (haccuracy : eps ≤ frameworkAccuracyConstant ell0 g0 cy cp cDelta *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    10 ≤ frameworkN D cy cp ell ell0 eps g0 ∧
    1 ≤ frameworkM Delta cDelta ell ell0 eps g0 ∧
    (frameworkN D cy cp ell ell0 eps g0 : ℝ) ≤
      (D / frameworkLambda ell ell0 eps g0) / (2 * cy * cp) ∧
    cDelta * (frameworkM Delta cDelta ell ell0 eps g0 + 1) ≤
      Delta / paperAmplitude ell ell0
        (frameworkLambda ell ell0 eps g0) ∧
    g0 ^ 3 / (1024 * cy * cp * cDelta * ell0 ^ 2) *
        (ell ^ 2 * D * Delta / eps ^ 3) ≤
      (frameworkH ell D Delta eps ell0 g0 cy cp cDelta : ℝ) := by
  obtain ⟨hNregime, hMregime⟩ := framework_size_regime_of_accuracy
    hell hD hDelta heps hell0 hg0 hcy hcp hcDelta haccuracy
  obtain ⟨hN, hM⟩ := framework_dimensions_of_regime hell heps hell0 hg0
    hcy hcp hcDelta hNregime hMregime
  exact ⟨hN, hM,
    frameworkN_size_condition hell hD heps hell0 hg0 hcy hcp,
    framework_gap_budget hell hDelta heps hell0 hg0 hcDelta hMregime,
    framework_chain_length_lower_of_regime hell hD hDelta heps hell0 hg0
      hcy hcp hcDelta hNregime hMregime⟩

/--
Canonical abstract framework reduction.

For the manuscript's two floor choices, C1 and C4 put the actual scaled
instance in the target class, C1 gives the exact scaled value identity, C2
preserves the saddle zero-chain, C3(c) rules out OS at every point whose
terminal state is still zero, and the horizon has the advertised cubic lower
bound with an explicit constant.  The subsequent resisting-oracle theorem may
consume these five outputs without adding any analytic assumption.
-/
theorem canonical_framework_reduction
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
    (P : UnscaledHardProperties F ell0 g0 cDelta cy cp tau0) :
    IsNCCClass ell D Delta (scaledFiniteInstance F ell ell0 eps g0 D) ∧
    ValueOn (scaledFiniteInstance F ell ell0 eps g0 D).Y
        (scaledFiniteInstance F ell ell0 eps g0 D).f =
      scaledFiniteValue F ell ell0 eps g0 D ∧
    NCPLVerification.IsFirstOrderZeroChain
      (scaledVectorField (frameworkLambda ell ell0 eps g0)
        (paperAmplitude ell ell0 (frameworkLambda ell ell0 eps g0))
        (taggedSerializedSaddleFieldOf
          (T := frameworkM Delta cDelta ell ell0 eps g0 + 1)
          (n := frameworkN D cy cp ell ell0 eps g0)
          F.gradX F.gradY)) ∧
    (∀ x,
      terminalStateValue x = 0 →
      ¬ IsOptimizationStationary Set.univ
        (ValueOn (scaledFiniteInstance F ell ell0 eps g0 D).Y
          (scaledFiniteInstance F ell ell0 eps g0 D).f) ell eps x) ∧
    g0 ^ 3 / (1024 * cy * cp * cDelta * ell0 ^ 2) *
        (ell ^ 2 * D * Delta / eps ^ 3) ≤
      (frameworkH ell D Delta eps ell0 g0 cy cp cDelta : ℝ) := by
  obtain ⟨hN, hM, hsize, hgap, hrate⟩ := framework_parameter_package
    hell hD hDelta heps hell0 hg0 hcy hcp hcDelta haccuracy
  have hvalue := P.scaledFiniteInstance_value_eq hell hD heps
  refine ⟨?_, hvalue, ?_, ?_, hrate⟩
  · unfold scaledFiniteInstance
    exact P.scaledInstance_isNCCClass hell hD hDelta
      (by
        unfold frameworkLambda lowerScale
        positivity)
      hgap
  · exact exact_scaling_preserves_zero_chain P.c2_saddle_zero_chain
  · intro x hx
    rw [hvalue]
    exact P.scaled_terminal_not_OS hM hell hD heps hterminalScale hsize hx

end

end Framework
end Simplified
end NCCLowerBound
