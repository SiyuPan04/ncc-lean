import NCC.Extensions.NCSCStartupProgram

/-!
# The configured NC-SC startup has no uniform cost over unbounded budgets

This is an exact query-count statement for the particular fixed-micro
initializer, not a lower bound for all NC-SC algorithms. The numerical
threshold can be combined with a family of actual initial oracle replies.
-/
namespace NCC.Extensions.NCSCStartupLower
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle RelativeFOAM RelativeFOAMContraction ProjectionGeometry
open OuterTrajectoryConcrete SharedOracle
open NCC.Upper NCC.Upper.AdaptiveMicroProgram NCC.Upper.CurrentProgram
open NCSCStartupProgram
set_option maxHeartbeats 3000000
variable {m n : Nat} {L r Delta : ℝ} {X : Set (EVec m)} {Y : Set (EVec n)}

theorem exactDepth_trace_length {α : Type} {p : Program X Y α} {k : Nat}
    (hp : ExactDepth p k) (P : NCCInstance m n) : (queryTrace P p).length = k := by
  induction hp with
  | pure a => rfl
  | query q hq next c hnext ih =>
    change (queryTrace P (next (firstOrderOracle P q))).length + 1 = c + 1
    rw [ih]

theorem callProgram_exact_count (P : NCCInstance m n) (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) Y) :
    (queryTrace P (NCSCProgram.callProgram (r := r) hL projectX projectY hpX hpY z rho S)).length =
      blockIterations (alpha L r) rho * (ProjectedMicro.feasibleMicroIterations + 1) :=
  exactDepth_trace_length
    (SharedOracle.exactDepth_blockProgram (r := r) hL projectX projectY hpX hpY z _ S) P

/-- Every fixed-micro call has its stated exact depth, regardless of later
replies. The first observed budget therefore determines the exact cost. -/
theorem initProgram_exact_count (P : NCCInstance m n) (hL : 0 < L) (hDelta : 0 < Delta)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ) :
    (queryTrace P (initProgram (r := r) hL hDelta projectX projectY hpX hpY
      hzeroX hzeroY majorant)).length =
      blockIterations (alpha L r) (factor Delta (majorant (firstOrderOracle P (0, 0)))) *
        (ProjectedMicro.feasibleMicroIterations + 1) + 1 := by
  let rho := factor Delta (majorant (firstOrderOracle P (0, 0)))
  let p := NCSCProgram.callProgram (r := r) hL projectX projectY hpX hpY 0 rho (seedState hzeroY)
  let finish (S : ValidState (m := m) Y) : Program X Y (FeasibleSnapshot X Y) :=
    .pure ⟨{ z := 0, state := S, B := Delta }, hzeroX⟩
  change (queryTrace P (p >>= finish)).length + 1 = _
  rw [queryTrace_bind, List.length_append]
  change (queryTrace P p).length + 0 + 1 = _
  rw [callProgram_exact_count]

theorem auxiliary_origin_reply (P : NCCInstance m n) (mu : ℝ) :
    firstOrderOracle (NCSC.auxiliary P mu) (0, 0) = firstOrderOracle P (0, 0) := by
  simp [firstOrderOracle, NCSC.auxiliary, quadraticCorrection, vecSq, NCPLVerification.vecSq]

/-- Adapting the original replies to the auxiliary objective changes no
query counts and does not change the observed origin budget. -/
theorem adapted_initProgram_exact_count (P : NCCInstance m n) (hL : 0 < L) (hDelta : 0 < Delta)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ) (mu : ℝ) :
    (queryTrace P (NCSCProgram.adaptProgram mu
      (initProgram (r := r) hL hDelta projectX projectY hpX hpY hzeroX hzeroY majorant))).length =
      blockIterations (alpha L r) (factor Delta (majorant (firstOrderOracle P (0, 0)))) *
        (ProjectedMicro.feasibleMicroIterations + 1) + 1 := by
  rw [NCSCProgram.queryTrace_adaptProgram, initProgram_exact_count, auxiliary_origin_reply]

/-- A sufficient observed-budget threshold for more than K macro steps.
It is a real numerical threshold, not an assigned query count. -/
def budgetThreshold (L r Delta : ℝ) (K : Nat) : ℝ :=
  Delta * Real.exp (alpha L r * ((K : ℝ) + 1))

theorem budgetThreshold_pos (hDelta : 0 < Delta) (L r : ℝ) (K : Nat) :
    0 < budgetThreshold L r Delta K :=
  mul_pos hDelta (Real.exp_pos _)

theorem blockIterations_gt_of_large_budget (hL : 0 < L) (hr : 0 < r)
    (hDelta : 0 < Delta) (K : Nat) {B : ℝ}
    (hB : budgetThreshold L r Delta K ≤ B) :
    K < blockIterations (alpha L r) (factor Delta B) := by
  let a := alpha L r
  let rho := factor Delta B
  have ha : 0 < a := alpha_pos hL hr
  have hrho : 0 < rho := factor_pos hDelta B
  have hf := factor_majorant hDelta B
  have hm := mul_le_mul_of_nonneg_left hB hrho.le
  have hexp : Real.exp (a * ((K : ℝ) + 1)) * rho ≤ 1 := by
    have hh : Delta * (Real.exp (a * ((K : ℝ) + 1)) * rho) ≤ Delta * 1 := by
      change rho * (Delta * Real.exp (a * ((K : ℝ) + 1))) ≤ rho * B at hm
      change rho * B ≤ Delta at hf
      nlinarith only [hm, hf]
    exact (mul_le_mul_iff_right₀ hDelta).1 hh
  have hlog : a * ((K : ℝ) + 1) ≤ Real.log (1 / rho) := by
    apply (Real.le_log_iff_exp_le (div_pos (by norm_num) hrho)).2
    exact (le_div_iff₀ hrho).2 hexp
  have hmul := mul_le_mul_of_nonneg_left hlog (div_pos (by norm_num : (0 : ℝ) < 2) ha).le
  have heq : 2 / a * (a * ((K : ℝ) + 1)) = 2 * ((K : ℝ) + 1) := by
    field_simp
  rw [heq] at hmul
  have hceil : 2 / a * Real.log (1 / rho) ≤ (blockIterations a rho : ℝ) := Nat.le_ceil _
  have hk : (K : ℝ) < (blockIterations a rho : ℝ) := by
    nlinarith only [hmul, hceil, Nat.cast_nonneg (α := ℝ) K]
  exact_mod_cast hk

theorem initProgram_count_gt_of_large_budget (P : NCCInstance m n)
    (hL : 0 < L) (hr : 0 < r) (hDelta : 0 < Delta)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ) (K : Nat)
    (hB : budgetThreshold L r Delta K ≤ majorant (firstOrderOracle P (0, 0))) :
    K < (queryTrace P (initProgram (r := r) hL hDelta projectX projectY hpX hpY
      hzeroX hzeroY majorant)).length := by
  rw [initProgram_exact_count]
  have hk := blockIterations_gt_of_large_budget hL hr hDelta K hB
  have hm : blockIterations (alpha L r) (factor Delta (majorant (firstOrderOracle P (0, 0)))) ≤
      blockIterations (alpha L r) (factor Delta (majorant (firstOrderOracle P (0, 0)))) *
        (ProjectedMicro.feasibleMicroIterations + 1) := by
    exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

/-- The scalar exact-cost formula is unbounded as B is allowed to grow. -/
theorem exact_cost_unbounded (hL : 0 < L) (hr : 0 < r) (hDelta : 0 < Delta) (K : Nat) :
    ∃ B : ℝ, 0 < B ∧ K < blockIterations (alpha L r) (factor Delta B) *
      (ProjectedMicro.feasibleMicroIterations + 1) + 1 := by
  refine ⟨budgetThreshold L r Delta K, budgetThreshold_pos hDelta L r K, ?_⟩
  have hk := blockIterations_gt_of_large_budget hL hr hDelta K le_rfl
  have hm : blockIterations (alpha L r) (factor Delta (budgetThreshold L r Delta K)) ≤
      blockIterations (alpha L r) (factor Delta (budgetThreshold L r Delta K)) *
        (ProjectedMicro.feasibleMicroIterations + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

/-- An actual instance family with unbounded observed budgets forces
unbounded actual traces for this one configured initialization program. -/
theorem actual_count_unbounded_of_observations {ι : Type} (family : ι → NCCInstance m n)
    (hL : 0 < L) (hr : 0 < r) (hDelta : 0 < Delta)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ)
    (hunbounded : ∀ B : ℝ, ∃ i, B ≤ majorant (firstOrderOracle (family i) (0, 0))) :
    ∀ K : Nat, ∃ i, K < (queryTrace (family i)
      (initProgram (r := r) hL hDelta projectX projectY hpX hpY hzeroX hzeroY majorant)).length := by
  intro K
  obtain ⟨i, hi⟩ := hunbounded (budgetThreshold L r Delta K)
  exact ⟨i, initProgram_count_gt_of_large_budget (family i) hL hr hDelta
    projectX projectY hpX hpY hzeroX hzeroY majorant K hi⟩

theorem adapted_actual_count_unbounded_of_observations {ι : Type}
    (family : ι → NCCInstance m n) (hL : 0 < L) (hr : 0 < r) (hDelta : 0 < Delta)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ) (mu : ℝ)
    (hunbounded : ∀ B : ℝ, ∃ i, B ≤ majorant (firstOrderOracle (family i) (0, 0))) :
    ∀ K : Nat, ∃ i, K < (queryTrace (family i) (NCSCProgram.adaptProgram mu
      (initProgram (r := r) hL hDelta projectX projectY hpX hpY hzeroX hzeroY majorant))).length := by
  intro K
  obtain ⟨i, hi⟩ := actual_count_unbounded_of_observations family hL hr hDelta
    projectX projectY hpX hpY hzeroX hzeroY majorant hunbounded K
  refine ⟨i, ?_⟩
  rwa [adapted_initProgram_exact_count, ← initProgram_exact_count (family i) hL hDelta
    projectX projectY hpX hpY hzeroX hzeroY majorant]

/-- In particular there is no global history-independent depth cap for
this configured program if its actual observed budgets are unbounded. -/
theorem no_uniform_depth_of_unbounded_observations {ι : Type}
    (family : ι → NCCInstance m n) (hL : 0 < L) (hr : 0 < r) (hDelta : 0 < Delta)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ) (mu : ℝ)
    (hunbounded : ∀ B : ℝ, ∃ i, B ≤ majorant (firstOrderOracle (family i) (0, 0))) :
    ∀ K : Nat, ¬DepthAtMost (NCSCProgram.adaptProgram mu
      (initProgram (r := r) hL hDelta projectX projectY hpX hpY hzeroX hzeroY majorant)) K := by
  intro K hdepth
  obtain ⟨i, hi⟩ := adapted_actual_count_unbounded_of_observations family hL hr hDelta
    projectX projectY hpX hpY hzeroX hzeroY majorant mu hunbounded K
  exact (not_lt_of_ge (hdepth.trace_length (family i))) hi

end
end NCC.Extensions.NCSCStartupLower
