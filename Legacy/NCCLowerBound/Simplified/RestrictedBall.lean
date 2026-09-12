import NCCLowerBound.Simplified.CompositeProperties
import NCCLowerBoundVerification.DiameterBall

/-!
# Inactivity of the finite dual ball

This file formalises the restriction step in lines 1295--1375 of
`NC_C_Lower_Bound_simplified.tex` for the current symmetric inner relay.
The block dual variable is serialised into `EVec (M * N)`, so the feasible
set below is the actual `diameterBall` used by `ValueOn`.

The exact Green-kernel maximiser is first shown to lie in the ball whenever
the squared primal pulse satisfies the growth threshold supplied by
`InnerRelay.blockWStar_growth`.  The restricted maximum is then represented
both as an `IsGreatest` element of the genuine image set and as an exact
`ValueOn` identity.  A strict version of the threshold is open; consequently
the restricted and unconstrained values have the same Fréchet derivative
throughout that inactivity region.
-/

namespace NCCLowerBound
namespace Simplified
namespace RestrictedBall

noncomputable section

open scoped BigOperators
open Set Filter
open NCCLowerBoundVerification
open InnerRelay Composite CompositeProperties

/-! ## Type-correct primal and dual serialisation -/

/-- Three primal blocks, stored as `(s_i,a_i,b_i)` for each `i`. -/
abbrev FlatPrimal (M : Nat) := NCCLowerBoundVerification.EVec (M * 3)

/-- The `M` dual relays, each of length `N`, stored blockwise. -/
abbrev FlatDual (M N : Nat) := NCCLowerBoundVerification.EVec (M * N)

def flatState {M : Nat} (x : FlatPrimal M) : Fin M → ℝ :=
  fun i ↦ x (finProdFinEquiv (i, ⟨0, by omega⟩))

def flatEntrance {M : Nat} (x : FlatPrimal M) : Fin M → ℝ :=
  fun i ↦ x (finProdFinEquiv (i, ⟨1, by omega⟩))

def flatExit {M : Nat} (x : FlatPrimal M) : Fin M → ℝ :=
  fun i ↦ x (finProdFinEquiv (i, ⟨2, by omega⟩))

def decodePrimal {M : Nat} (x : FlatPrimal M) : PrimalPoint M :=
  (flatState x, flatEntrance x, flatExit x)

/-- Flatten a family of relay vectors without changing any coordinate. -/
def flattenBlocks {M N : Nat}
    (y : Fin M → NCCLowerBoundVerification.EVec N) : FlatDual M N :=
  fun j ↦
    let ik := finProdFinEquiv.symm j
    y ik.1 ik.2

/-- Inverse block view of a flattened dual vector. -/
def unflattenBlocks {M N : Nat} (y : FlatDual M N) :
    Fin M → NCCLowerBoundVerification.EVec N :=
  fun i k ↦ y (finProdFinEquiv (i, k))

@[simp] theorem unflattenBlocks_flattenBlocks {M N : Nat}
    (y : Fin M → NCCLowerBoundVerification.EVec N) :
    unflattenBlocks (flattenBlocks y) = y := by
  funext i k
  simp [unflattenBlocks, flattenBlocks]

@[simp] theorem flattenBlocks_unflattenBlocks {M N : Nat}
    (y : FlatDual M N) :
    flattenBlocks (unflattenBlocks y) = y := by
  funext j
  change y (finProdFinEquiv (finProdFinEquiv.symm j)) = y j
  rw [Equiv.apply_symm_apply]

/-- Flattening is an exact Euclidean isometry in squared-coordinate form. -/
theorem vecSq_flattenBlocks {M N : Nat}
    (y : Fin M → NCCLowerBoundVerification.EVec N) :
    vecSq (flattenBlocks y) = ∑ i : Fin M, vecSq (y i) := by
  unfold vecSq NCPLVerification.vecSq
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp [flattenBlocks]

/-! ## The actual restricted saddle and its exact maximiser -/

/-- The current hard objective with both sides serialised as Euclidean
vectors, so it can be passed directly to `ValueOn`. -/
def flatHardObjective {M N : Nat} (hN : 0 < N) (K : ℝ) :
    FlatPrimal M → FlatDual M N → ℝ :=
  fun x y ↦ hardObjective hN K (flatState x) (flatEntrance x) (flatExit x)
    (unflattenBlocks y)

/-- The exact blockwise Green-kernel maximiser in flattened coordinates. -/
def flatWStar {M N : Nat} (hN : 0 < N) (x : FlatPrimal M) : FlatDual M N :=
  flattenBlocks (blockWStar hN (flatEntrance x) (flatExit x))

/-- Squared Euclidean norm of the two primal pulse blocks. -/
def primalPulseSq {M : Nat} (x : FlatPrimal M) : ℝ :=
  ∑ i : Fin M, ((flatEntrance x i) ^ 2 + (flatExit x i) ^ 2)

/-- Exact unconstrained contracted value, now as a function on `FlatPrimal`. -/
def flatUnconstrainedValue {M : Nat} (K : ℝ) (x : FlatPrimal M) : ℝ :=
  unconstrainedValue K (flatState x) (flatEntrance x) (flatExit x)

/-- The finite-ball value is the literal `ValueOn` of the serialised saddle. -/
def restrictedValue {M N : Nat} (hN : 0 < N) (K D : ℝ) :
    FlatPrimal M → ℝ :=
  ValueOn (diameterBall (M * N) D) (flatHardObjective hN K)

theorem flatHardObjective_at_flatWStar {M N : Nat} (hN10 : 10 ≤ N)
    (K : ℝ) (x : FlatPrimal M) :
    flatHardObjective (by omega : 0 < N) K x
        (flatWStar (by omega : 0 < N) x) =
      flatUnconstrainedValue K x := by
  simpa [flatHardObjective, flatWStar, flatUnconstrainedValue] using
    hardObjective_at_blockWStar hN10 K (flatState x)
      (flatEntrance x) (flatExit x)

theorem flatHardObjective_le_unconstrainedValue {M N : Nat}
    (hN10 : 10 ≤ N) (K : ℝ) (x : FlatPrimal M) (y : FlatDual M N) :
    flatHardObjective (by omega : 0 < N) K x y ≤
      flatUnconstrainedValue K x := by
  exact hardObjective_le_unconstrainedValue hN10 K (flatState x)
    (flatEntrance x) (flatExit x) (unflattenBlocks y)

/-- The unconstrained maximum is a genuine greatest element of the full
serialised range. -/
theorem flatUnconstrainedValue_isGreatest {M N : Nat} (hN10 : 10 ≤ N)
    (K : ℝ) (x : FlatPrimal M) :
    IsGreatest
      (Set.range (flatHardObjective (by omega : 0 < N) K x))
      (flatUnconstrainedValue K x) := by
  constructor
  · exact ⟨flatWStar (by omega : 0 < N) x,
      flatHardObjective_at_flatWStar hN10 K x⟩
  · rintro _ ⟨y, rfl⟩
    exact flatHardObjective_le_unconstrainedValue hN10 K x y

/-! ## Growth threshold and finite-ball inactivity -/

/-- Exact squared form of the threshold under which the radius-`D/2` ball is
inactive. -/
def SatisfiesDualThreshold {M N : Nat} (D : ℝ) (x : FlatPrimal M) : Prop :=
  8000 * (N : ℝ) ^ 2 * primalPulseSq x ≤ (D / 2) ^ 2

/-- `blockWStar_growth`, transported through the block serialisation. -/
theorem flatWStar_growth {M N : Nat} (hN10 : 10 ≤ N)
    (x : FlatPrimal M) :
    vecSq (flatWStar (by omega : 0 < N) x) ≤
      8000 * (N : ℝ) ^ 2 * primalPulseSq x := by
  rw [flatWStar, vecSq_flattenBlocks]
  exact blockWStar_growth hN10 (flatEntrance x) (flatExit x)

/-- Under the pulse threshold, the unconstrained maximiser belongs to the
actual finite `diameterBall`. -/
theorem flatWStar_mem_diameterBall {M N : Nat} (hN10 : 10 ≤ N)
    {D : ℝ} {x : FlatPrimal M}
    (hthreshold : SatisfiesDualThreshold (N := N) D x) :
    flatWStar (by omega : 0 < N) x ∈ diameterBall (M * N) D := by
  change vecSq (flatWStar (by omega : 0 < N) x) ≤ (D / 2) ^ 2
  exact (flatWStar_growth hN10 x).trans hthreshold

/-- TeX-normalised sufficient conditions: the pulse norm is at most `20` and
`N ≤ D / (2 * (20 * sqrt 20) * 20)`.  The latter denominator is written as
`800 * sqrt 20` after multiplication. -/
theorem satisfiesDualThreshold_of_pulse_le_twenty {M N : Nat}
    {D : ℝ} {x : FlatPrimal M} (hD : 0 ≤ D)
    (hpulse : primalPulseSq x ≤ 20 ^ 2)
    (hsize : (N : ℝ) ≤ D / (800 * Real.sqrt 20)) :
    SatisfiesDualThreshold (N := N) D x := by
  have hsqrtPos : 0 < Real.sqrt (20 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : Real.sqrt (20 : ℝ) ^ 2 = 20 :=
    Real.sq_sqrt (by norm_num)
  have hden : 0 < 800 * Real.sqrt (20 : ℝ) := by positivity
  have hlinearRaw : (N : ℝ) * (800 * Real.sqrt 20) ≤ D :=
    (le_div_iff₀ hden).mp hsize
  have hlinear :
      (N : ℝ) * (400 * Real.sqrt 20) ≤ D / 2 := by
    nlinarith
  have hleft0 : 0 ≤ (N : ℝ) * (400 * Real.sqrt 20) := by positivity
  have hright0 : 0 ≤ D / 2 := by positivity
  have hsquare :
      ((N : ℝ) * (400 * Real.sqrt 20)) ^ 2 ≤ (D / 2) ^ 2 :=
    (sq_le_sq₀ hleft0 hright0).2 hlinear
  unfold SatisfiesDualThreshold
  calc
    8000 * (N : ℝ) ^ 2 * primalPulseSq x ≤
        8000 * (N : ℝ) ^ 2 * 20 ^ 2 := by
      exact mul_le_mul_of_nonneg_left hpulse (by positivity)
    _ = ((N : ℝ) * (400 * Real.sqrt 20)) ^ 2 := by
      nlinarith [hsqrtSq]
    _ ≤ (D / 2) ^ 2 := hsquare

/-- Literal restricted-dual-ball inactivity in the constants of the current
construction. -/
theorem flatWStar_mem_diameterBall_of_pulse_le_twenty {M N : Nat}
    (hN10 : 10 ≤ N) {D : ℝ} {x : FlatPrimal M} (hD : 0 ≤ D)
    (hpulse : primalPulseSq x ≤ 20 ^ 2)
    (hsize : (N : ℝ) ≤ D / (800 * Real.sqrt 20)) :
    flatWStar (by omega : 0 < N) x ∈ diameterBall (M * N) D :=
  flatWStar_mem_diameterBall hN10
    (satisfiesDualThreshold_of_pulse_le_twenty hD hpulse hsize)

/-- The same point is therefore an actual maximiser on the finite ball. -/
theorem flatWStar_isMaximizerOn_diameterBall {M N : Nat}
    (hN10 : 10 ≤ N) (K : ℝ) {D : ℝ} {x : FlatPrimal M}
    (hthreshold : SatisfiesDualThreshold (N := N) D x) :
    IsMaximizerOn (diameterBall (M * N) D)
      (flatHardObjective (by omega : 0 < N) K) x
      (flatWStar (by omega : 0 < N) x) := by
  refine ⟨flatWStar_mem_diameterBall hN10 hthreshold, ?_⟩
  intro y _hy
  rw [flatHardObjective_at_flatWStar hN10]
  exact flatHardObjective_le_unconstrainedValue hN10 K x y

/-- Set-level form: the contracted value is a greatest element of the actual
image of the finite ball. -/
theorem flatUnconstrainedValue_isGreatest_on_diameterBall {M N : Nat}
    (hN10 : 10 ≤ N) (K : ℝ) {D : ℝ} {x : FlatPrimal M}
    (hthreshold : SatisfiesDualThreshold (N := N) D x) :
    IsGreatest
      (flatHardObjective (by omega : 0 < N) K x ''
        diameterBall (M * N) D)
      (flatUnconstrainedValue K x) := by
  constructor
  · exact ⟨flatWStar (by omega : 0 < N) x,
      flatWStar_mem_diameterBall hN10 hthreshold,
      flatHardObjective_at_flatWStar hN10 K x⟩
  · rintro _ ⟨y, _hy, rfl⟩
    exact flatHardObjective_le_unconstrainedValue hN10 K x y

/-- Main inactivity identity: the genuine finite-ball `ValueOn` agrees
exactly with the displayed unconstrained value. -/
theorem restrictedValue_eq_unconstrainedValue_of_threshold {M N : Nat}
    (hN10 : 10 ≤ N) (K : ℝ) {D : ℝ} {x : FlatPrimal M}
    (hthreshold : SatisfiesDualThreshold (N := N) D x) :
    restrictedValue (by omega : 0 < N) K D x =
      unconstrainedValue K (flatState x) (flatEntrance x) (flatExit x) := by
  rw [show restrictedValue (by omega : 0 < N) K D x =
      ValueOn (diameterBall (M * N) D)
        (flatHardObjective (by omega : 0 < N) K) x by rfl]
  rw [value_eq_of_isMaximizerOn
    (flatWStar_isMaximizerOn_diameterBall hN10 K hthreshold)]
  exact flatHardObjective_at_flatWStar hN10 K x

/-- TeX-constant form of the exact finite-ball value identity. -/
theorem restrictedValue_eq_unconstrainedValue_of_pulse_le_twenty {M N : Nat}
    (hN10 : 10 ≤ N) (K : ℝ) {D : ℝ} {x : FlatPrimal M}
    (hD : 0 ≤ D) (hpulse : primalPulseSq x ≤ 20 ^ 2)
    (hsize : (N : ℝ) ≤ D / (800 * Real.sqrt 20)) :
    restrictedValue (by omega : 0 < N) K D x =
      unconstrainedValue K (flatState x) (flatEntrance x) (flatExit x) :=
  restrictedValue_eq_unconstrainedValue_of_threshold hN10 K
    (satisfiesDualThreshold_of_pulse_le_twenty hD hpulse hsize)

/-! ## Local derivative bridge on the strict inactivity region -/

/-- The strict growth threshold.  Its strictness is exactly what makes ball
inactivity persist on a neighbourhood. -/
def dualInactiveInterior {M N : Nat} (D : ℝ) : Set (FlatPrimal M) :=
  {x | 8000 * (N : ℝ) ^ 2 * primalPulseSq x < (D / 2) ^ 2}

theorem primalPulseSq_continuous {M : Nat} :
    Continuous (primalPulseSq (M := M)) := by
  unfold primalPulseSq flatEntrance flatExit
  fun_prop

theorem dualInactiveInterior_isOpen {M N : Nat} (D : ℝ) :
    IsOpen (dualInactiveInterior (M := M) (N := N) D) := by
  apply isOpen_lt
  · exact continuous_const.mul primalPulseSq_continuous
  · exact continuous_const

theorem satisfiesDualThreshold_of_mem_interior {M N : Nat} {D : ℝ}
    {x : FlatPrimal M} (hx : x ∈ dualInactiveInterior (N := N) D) :
    SatisfiesDualThreshold (N := N) D x :=
  hx.le

/-- On the open inactivity region, the restricted and unconstrained values
agree pointwise. -/
theorem restrictedValue_eqOn_dualInactiveInterior {M N : Nat}
    (hN10 : 10 ≤ N) (K D : ℝ) :
    Set.EqOn (restrictedValue (M := M) (by omega : 0 < N) K D)
      (flatUnconstrainedValue (M := M) K)
      (dualInactiveInterior (M := M) (N := N) D) := by
  intro x hx
  simpa [flatUnconstrainedValue] using
    restrictedValue_eq_unconstrainedValue_of_threshold hN10 K
      (satisfiesDualThreshold_of_mem_interior hx)

theorem decodePrimal_contDiff {M : Nat} :
    ContDiff ℝ (⊤ : ℕ∞) (decodePrimal (M := M)) := by
  unfold decodePrimal flatState flatEntrance flatExit
  fun_prop

theorem flatUnconstrainedValue_contDiff {M : Nat} (K : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (flatUnconstrainedValue (M := M) K) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun x : FlatPrimal M ↦
    unconstrainedValue K (flatState x) (flatEntrance x) (flatExit x))
  simpa [Function.comp_def, primalValue, decodePrimal] using
    (primalValue_contDiff (M := M) K).comp decodePrimal_contDiff

/-- In fact the finite-ball value is smooth on the whole strict inactivity
region, not just differentiable pointwise. -/
theorem restrictedValue_contDiffOn_dualInactiveInterior {M N : Nat}
    (hN10 : 10 ≤ N) (K D : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (restrictedValue (M := M) (by omega : 0 < N) K D)
      (dualInactiveInterior (M := M) (N := N) D) := by
  exact (flatUnconstrainedValue_contDiff (M := M) K).contDiffOn.congr
    (restrictedValue_eqOn_dualInactiveInterior hN10 K D)

theorem restrictedValue_contDiffAt_of_mem_interior {M N : Nat}
    (hN10 : 10 ≤ N) (K D : ℝ) {x : FlatPrimal M}
    (hx : x ∈ dualInactiveInterior (N := N) D) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (restrictedValue (by omega : 0 < N) K D) x :=
  (restrictedValue_contDiffOn_dualInactiveInterior hN10 K D x hx).contDiffAt
    ((dualInactiveInterior_isOpen (M := M) (N := N) D).mem_nhds hx)

/-- The exact value identity holds eventually around every point satisfying
the strict threshold. -/
theorem restrictedValue_eventuallyEq_flatUnconstrainedValue {M N : Nat}
    (hN10 : 10 ≤ N) (K D : ℝ) {x : FlatPrimal M}
    (hx : x ∈ dualInactiveInterior (N := N) D) :
    restrictedValue (by omega : 0 < N) K D =ᶠ[nhds x]
      flatUnconstrainedValue K := by
  filter_upwards [(dualInactiveInterior_isOpen (M := M) (N := N) D).mem_nhds hx]
    with z hz
  exact restrictedValue_eqOn_dualInactiveInterior hN10 K D hz

/-- Local derivative bridge: at every strictly inactive point the genuine
finite-ball value has exactly the unconstrained value's Fréchet derivative. -/
theorem restrictedValue_hasFDerivAt_of_mem_interior {M N : Nat}
    (hN10 : 10 ≤ N) (K D : ℝ) {x : FlatPrimal M}
    (hx : x ∈ dualInactiveInterior (N := N) D) :
    HasFDerivAt (restrictedValue (by omega : 0 < N) K D)
      (fderiv ℝ (flatUnconstrainedValue K) x) x := by
  have hdiff : Differentiable ℝ (flatUnconstrainedValue (M := M) K) :=
    (flatUnconstrainedValue_contDiff K).differentiable (by simp)
  exact (hdiff x).hasFDerivAt.congr_of_eventuallyEq
    (restrictedValue_eventuallyEq_flatUnconstrainedValue hN10 K D hx)

theorem restrictedValue_fderiv_eq_of_mem_interior {M N : Nat}
    (hN10 : 10 ≤ N) (K D : ℝ) {x : FlatPrimal M}
    (hx : x ∈ dualInactiveInterior (N := N) D) :
    fderiv ℝ (restrictedValue (by omega : 0 < N) K D) x =
      fderiv ℝ (flatUnconstrainedValue K) x :=
  (restrictedValue_hasFDerivAt_of_mem_interior hN10 K D hx).fderiv

theorem restrictedValue_differentiableAt_of_mem_interior {M N : Nat}
    (hN10 : 10 ≤ N) (K D : ℝ) {x : FlatPrimal M}
    (hx : x ∈ dualInactiveInterior (N := N) D) :
    DifferentiableAt ℝ (restrictedValue (by omega : 0 < N) K D) x :=
  (restrictedValue_hasFDerivAt_of_mem_interior hN10 K D hx).differentiableAt

end

end RestrictedBall
end Simplified
end NCCLowerBound
