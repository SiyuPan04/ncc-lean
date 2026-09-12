import NCC.Lower.Deterministic
import NCC.Lower.ScaledMembership
import NCC.Lower.TaggedSource
import NCC.Oracle.Minimax

/-!
# The current arbitrary-deterministic lower endpoint

The resisting horizon is one less than the full chain length, as required
by the generic fixed-instance resisting construction. The spare primal
coordinates in each stage absorb this difference with exactly the current
numerical constant `Parameters.c1`, not a weakened constant.
-/

namespace NCC.Lower.DeterministicLower

noncomputable section

open NCCLowerBoundVerification
open Certificates Parameters
open scoped ENNReal

def horizon (ell D Delta eps : ℝ) : ℕ :=
  NCC.chainLength (stages constants ell Delta eps) (innerLength constants ell D eps) - 1

def outputHorizon (ell D Delta eps : ℝ) : ℕ := horizon ell D Delta eps - 1

def primalDimension (ell D Delta eps : ℝ) : ℕ :=
  3 * stages constants ell Delta eps + (horizon ell D Delta eps + 2)

def dualDimension (ell D Delta eps : ℝ) : ℕ :=
  innerLength constants ell D eps * stages constants ell Delta eps +
    (horizon ell D Delta eps + 2)

/-- One objective-independent domain label, fixed before selecting the
algorithm's hard instance. Both ambient dimensions are positive. -/
def domain (ell D Delta eps : ℝ) (hD : 0 ≤ D) : Oracle.AdmissibleDomainPair where
  m := primalDimension ell D Delta eps
  n := dualDimension ell D Delta eps
  X := Set.univ
  Y := diameterBall (dualDimension ell D Delta eps) D
  zero_mem_X := Set.mem_univ _
  zero_mem_Y := zero_mem_diameterBall _ D hD
  X_closed := isClosed_univ
  X_convex := convex_univ
  Y_closed := diameterBall_closed _ D
  Y_convex := diameterBall_convex _ D

theorem dimensions_positive (ell D Delta eps : ℝ) :
    0 < primalDimension ell D Delta eps ∧ 0 < dualDimension ell D Delta eps := by
  constructor <;> simp only [primalDimension, dualDimension] <;> omega

/-- The floor slack absorbs the final strict-horizon index without losing
the manuscript's exact lower-bound constant. -/
theorem horizon_lower_with_slack {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 constants * min (ell * D) (Real.sqrt (ell * Delta))) :
    c1 constants * (ell ^ 2 * D * Delta / eps ^ 3) + 1 ≤
      (horizon ell D Delta eps : ℝ) := by
  have hM := rawM_ge_four constants hell hDelta heps hacc
  have hN := rawN_ge_twenty constants hell hD heps hacc
  have hadm := lengths_admissible constants hell hD hDelta heps hacc
  have hMf : rawM constants ell Delta eps / 2 ≤
      (stages constants ell Delta eps : ℝ) := by
    have := Nat.lt_floor_add_one (rawM constants ell Delta eps)
    change rawM constants ell Delta eps / 2 ≤
      (⌊rawM constants ell Delta eps⌋₊ : ℝ)
    linarith
  have hNf : rawN constants ell D eps ≤
      (innerLength constants ell D eps : ℝ) + 2 := by
    have := Nat.lt_floor_add_one (rawN constants ell D eps)
    change rawN constants ell D eps ≤ (⌊rawN constants ell D eps⌋₊ : ℝ) + 2
    linarith
  have hprod := mul_le_mul hMf hNf (by linarith : 0 ≤ rawN constants ell D eps)
    (Nat.cast_nonneg (stages constants ell Delta eps))
  have hm : (2 : ℝ) ≤ (stages constants ell Delta eps : ℝ) := by
    have hm4 : 4 ≤ stages constants ell Delta eps :=
      (Nat.le_floor_iff (by linarith : 0 ≤ rawM constants ell Delta eps)).2 hM
    exact_mod_cast (show 2 ≤ stages constants ell Delta eps by omega)
  have hL : 1 ≤ NCC.chainLength (stages constants ell Delta eps)
      (innerLength constants ell D eps) := NCC.chainLength_pos hadm
  calc
    _ = (rawM constants ell Delta eps / 2) * rawN constants ell D eps + 1 := by
      rw [rawM_eq constants hell heps, rawN_eq]
      unfold c1
      field_simp [ne_of_gt constants.cDelta_pos, ne_of_gt constants.ell0_pos,
        ne_of_gt heps]
      ring
    _ ≤ (stages constants ell Delta eps : ℝ) *
        ((innerLength constants ell D eps : ℝ) + 2) + 1 := by linarith [hprod]
    _ ≤ (horizon ell D Delta eps : ℝ) := by
      rw [horizon, Nat.cast_sub hL]
      simp only [NCC.chainLength, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
        Nat.cast_one]
      nlinarith

theorem horizon_lower {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 constants * min (ell * D) (Real.sqrt (ell * Delta))) :
    c1 constants * (ell ^ 2 * D * Delta / eps ^ 3) ≤
      (horizon ell D Delta eps : ℝ) := by
  linarith [horizon_lower_with_slack hell hD hDelta heps hacc]

theorem horizon_gt_one {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 constants * min (ell * D) (Real.sqrt (ell * Delta))) :
    1 < horizon ell D Delta eps := by
  have hc := c1_pos constants
  have hr : 0 < c1 constants * (ell ^ 2 * D * Delta / eps ^ 3) := by positivity
  have hs := horizon_lower_with_slack hell hD hDelta heps hacc
  have hh : (1 : ℝ) < (horizon ell D Delta eps : ℝ) := by linarith
  exact_mod_cast hh

theorem outputHorizon_lower {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 constants * min (ell * D) (Real.sqrt (ell * Delta))) :
    c1 constants * (ell ^ 2 * D * Delta / eps ^ 3) ≤
      (outputHorizon ell D Delta eps : ℝ) := by
  have hs := horizon_lower_with_slack hell hD hDelta heps hacc
  rw [outputHorizon, Nat.cast_sub (horizon_gt_one hell hD hDelta heps hacc).le]
  norm_num only [Nat.cast_one]
  linarith

/-- An actual rotated current hard instance for every deterministic causal
component. All class, gradient, zero-chain, terminal, scaling and floor
premises are proved by the current construction; none is assumed here. -/
theorem exists_current_hard_instance {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 constants * min (ell * D) (Real.sqrt (ell * Delta)))
    (A : Oracle.DeterministicFOComponent
      (Set.univ : Set (EVec (primalDimension ell D Delta eps)))
      (diameterBall (dualDimension ell D Delta eps) D)) :
    ∃ Q : NCCInstance (primalDimension ell D Delta eps) (dualDimension ell D Delta eps),
      ∃ hQ : Model.WithinClass ell D Delta Q,
        IsNCCClass ell D Delta Q ∧ Q.X = Set.univ ∧
        Q.Y = diameterBall (dualDimension ell D Delta eps) D ∧ Q.x0 = 0 ∧
        A.FailsWithin Q ell eps (horizon ell D Delta eps) ∧
        (horizon ell D Delta eps : WithTop ℕ) ≤ Oracle.queriedHittingTime A Q ell eps ∧
        ∀ t < horizon ell D Delta eps,
          ¬ Moreau.Within.IsOS hQ eps (A.queriedAt Q t).1 := by
  have hadm := lengths_admissible constants hell hD hDelta heps hacc
  have hm : 0 < stages constants ell Delta eps := by have := hadm.1; omega
  have hn : 0 < innerLength constants ell D eps := by have := hadm.2; omega
  apply Deterministic.exists_hard_instance_of_terminal
    (T := stages constants ell Delta eps + 1) (n := innerLength constants ell D eps)
    (by omega) A (TaggedSource.source (m := stages constants ell Delta eps) hn ell D eps)
    (TaggedSource.analyticClass hm hadm.2 hell hD hDelta heps
      (ScaledMembership.floor_gap hell hDelta heps)) rfl rfl rfl
    (TaggedSource.source_zeroChain hn ell D eps)
  · have hL := NCC.chainLength_pos hadm
    simpa only [horizon, NCC.chainLength, Nat.add_sub_cancel] using Nat.sub_lt hL (by omega : 0 < 1)
  · simp only [primalDimension, Nat.add_sub_cancel]
    omega
  · simp only [dualDimension, Nat.add_sub_cancel]
    omega
  · intro x hx
    exact TaggedSource.source_not_OS_terminal hm hadm.2 hell hD heps
      (innerLength_le_raw constants hell hD heps) hx

/-- The exact current finite-horizon lower bound on the literal minimax
over all finite-dimensional feasible-domain class members. -/
theorem minimaxHittingTime_lower {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 constants * min (ell * D) (Real.sqrt (ell * Delta))) :
    (horizon ell D Delta eps : WithTop ℕ) ≤
      Complexity.minimaxHittingTime ell D Delta eps := by
  apply Complexity.minimaxHittingTime_lower_of_hard_members
  intro A
  obtain ⟨P, hP, _hPA, hPX, hPY, _hPinit, _hfail, htime, _hOS⟩ :=
    exists_current_hard_instance hell hD hDelta heps hacc
      (A.component (domain ell D Delta eps hD.le))
  exact ⟨domain ell D Delta eps hD.le, P, ⟨hPX, hPY, hP⟩, htime⟩

/-- The displayed cubic lower bound, in the extended-real minimax quantity
proved equal to the source's literal infimum/supremum expression. -/
theorem current_deterministic_lower {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 constants * min (ell * D) (Real.sqrt (ell * Delta))) :
    ENNReal.ofReal (c1 constants * (ell ^ 2 * D * Delta / eps ^ 3)) ≤
      Complexity.minimaxOracleComplexity ell D Delta eps :=
  Complexity.minimaxOracleComplexity_lower_of_horizon
    (horizon_lower hell hD hDelta heps hacc)
    (minimaxHittingTime_lower hell hD hDelta heps hacc)

/-- The current construction defeats an arbitrary deterministic primal
output after `outputHorizon` replies, even if that point was never queried.
The same numerical cubic rate is below this output horizon. -/
theorem exists_current_hard_output {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ c0 constants * min (ell * D) (Real.sqrt (ell * Delta)))
    (A : Oracle.DeterministicFOComponent
      (Set.univ : Set (EVec (primalDimension ell D Delta eps)))
      (diameterBall (dualDimension ell D Delta eps) D))
    (out : Oracle.ReplyHistory (primalDimension ell D Delta eps)
      (dualDimension ell D Delta eps) (outputHorizon ell D Delta eps) →
        EVec (primalDimension ell D Delta eps)) :
    ∃ Q : NCCInstance (primalDimension ell D Delta eps) (dualDimension ell D Delta eps),
      ∃ hQ : Model.WithinClass ell D Delta Q,
        IsNCCClass ell D Delta Q ∧ Q.X = Set.univ ∧
        Q.Y = diameterBall (dualDimension ell D Delta eps) D ∧ Q.x0 = 0 ∧
        ¬ Moreau.Within.IsOS hQ eps
          (out (A.queriedTranscript Q (outputHorizon ell D Delta eps))) := by
  have hH := horizon_gt_one hell hD hDelta heps hacc
  have hK : 0 < outputHorizon ell D Delta eps := by unfold outputHorizon; omega
  have hsum : outputHorizon ell D Delta eps + 1 = horizon ell D Delta eps := by
    unfold outputHorizon
    omega
  let A' := Deterministic.appendOutput A hK out (fun _ => Set.mem_univ _)
    (zero_mem_diameterBall _ D hD.le)
  obtain ⟨Q, hQ, hQA, hQX, hQY, hQinit, hfail, _htime, _hOS⟩ :=
    exists_current_hard_instance hell hD hDelta heps hacc A'
  have hf : ¬ IsOptimizationStationary Q.X (ValueOn Q.Y Q.f) ell eps
      (out (A.queriedTranscript Q (outputHorizon ell D Delta eps))) := by
    apply Deterministic.arbitrary_output_failure A hK out (fun _ => Set.mem_univ _)
      (zero_mem_diameterBall _ D hD.le) Q ell eps
    simpa only [hsum] using hfail
  refine ⟨Q, hQ, hQA, hQX, hQY, hQinit, ?_⟩
  intro hos
  exact hf ((Moreau.Within.isOS_iff_feasible_prox hQ eps _).1 hos).2.2

theorem exists_numerical_constants :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ (ell D Delta eps : ℝ), 0 < ell → 0 < D → 0 < Delta → 0 < eps →
        eps ≤ c₀ * min (ell * D) (Real.sqrt (ell * Delta)) →
        ENNReal.ofReal (c₁ * (ell ^ 2 * D * Delta / eps ^ 3)) ≤
          Complexity.minimaxOracleComplexity ell D Delta eps := by
  exact ⟨c0 constants, c1 constants, c0_pos constants, c1_pos constants,
    fun _ _ _ _ hell hD hDelta heps hacc =>
      current_deterministic_lower hell hD hDelta heps hacc⟩

end

end NCC.Lower.DeterministicLower
