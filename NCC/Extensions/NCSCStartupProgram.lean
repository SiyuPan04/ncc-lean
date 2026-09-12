import NCC.Extensions.NCSCProgram

/-!
# A counted fixed-curvature normalization of the initial energy

One origin reply supplies a computable bound on the true coincident-state
energy. A finite FOAM call normalizes that energy to `Delta`; its count
depends on the observed bound and is charged as an additive cost.
The numerical energy majorant is an explicit local proof obligation,
not silently inferred from a primal value gap or an absent dual radius.
-/
namespace NCC.Extensions.NCSCStartupProgram
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle RelativeFOAM RelativeFOAMContraction ProjectionGeometry
open OuterTrajectoryConcrete SharedOracle
open NCC.Upper NCC.Upper.AdaptiveMicroProgram NCC.Upper.CurrentProgram
set_option maxHeartbeats 3000000
variable {m n : Nat} {L r Delta : ℝ} {X : Set (EVec m)} {Y : Set (EVec n)}

def factor (Delta B : ℝ) : ℝ := min (1 / 2) (Delta / (2 * max 1 B))

theorem factor_pos (hDelta : 0 < Delta) (B : ℝ) : 0 < factor Delta B := by
  have hmax : 0 < max 1 B := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  exact lt_min (by norm_num) (div_pos hDelta (mul_pos (by norm_num) hmax))

theorem factor_lt_one (Delta B : ℝ) : factor Delta B < 1 :=
  (min_le_left _ _).trans_lt (by norm_num)

theorem factor_majorant (hDelta : 0 < Delta) (B : ℝ) : factor Delta B * B ≤ Delta := by
  have hp := (factor_pos hDelta B).le
  have hmax : 0 < max 1 B := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hb := mul_le_mul_of_nonneg_left (le_max_right (1 : ℝ) B) hp
  have hf := mul_le_mul_of_nonneg_right
    (show factor Delta B ≤ Delta / (2 * max 1 B) from min_le_right _ _) hmax.le
  have hc : Delta / (2 * max 1 B) * max 1 B = Delta / 2 := by
    field_simp [ne_of_gt hmax]
  rw [hc] at hf
  linarith

def seedState (hzeroY : (0 : EVec n) ∈ Y) : ValidState (m := m) Y :=
  ⟨StartupConcrete.coincidentState 0 0, hzeroY⟩

def initProgram (hL : 0 < L) (_hDelta : 0 < Delta)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ) : Program X Y (FeasibleSnapshot X Y) :=
  .query (0, 0) ⟨hzeroX, hzeroY⟩ fun reply => do
    let S ← NCSCProgram.callProgram (r := r) hL projectX projectY hpX hpY 0
      (factor Delta (majorant reply)) (seedState hzeroY)
    .pure ⟨{ z := 0, state := S, B := Delta }, hzeroX⟩

theorem initProgram_z (P : NCCInstance m n) (hL : 0 < L) (hDelta : 0 < Delta)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ) :
    (Program.eval P (initProgram (r := r) hL hDelta projectX projectY hpX hpY
      hzeroX hzeroY majorant)).1.z = 0 := by
  simp only [initProgram, Program.eval_query, Program.eval_bind, Program.eval_pure]

theorem initProgram_B (P : NCCInstance m n) (hL : 0 < L) (hDelta : 0 < Delta)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ) :
    (Program.eval P (initProgram (r := r) hL hDelta projectX projectY hpX hpY
      hzeroX hzeroY majorant)).1.B = Delta := by
  simp only [initProgram, Program.eval_query, Program.eval_bind, Program.eval_pure]

theorem initProgram_actual_count (P : NCCInstance m n) (hL : 0 < L) (hDelta : 0 < Delta)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ) :
    (queryTrace P (initProgram (r := r) hL hDelta projectX projectY hpX hpY
      hzeroX hzeroY majorant)).length ≤
      blockIterations (alpha L r) (factor Delta (majorant (firstOrderOracle P (0, 0)))) *
        (ProjectedMicro.feasibleMicroIterations + 1) + 1 := by
  let rho := factor Delta (majorant (firstOrderOracle P (0, 0)))
  let p := NCSCProgram.callProgram (r := r) hL projectX projectY hpX hpY 0 rho (seedState hzeroY)
  let finish (S : ValidState (m := m) Y) : Program X Y (FeasibleSnapshot X Y) :=
    .pure ⟨{ z := 0, state := S, B := Delta }, hzeroX⟩
  have hc := (NCSCProgram.callProgram_depth (r := r) hL projectX projectY hpX hpY 0 rho
    (seedState hzeroY)).trace_length P
  change (queryTrace P p).length ≤ blockIterations (alpha L r) rho *
    (ProjectedMicro.feasibleMicroIterations + 1) at hc
  change (queryTrace P (p >>= finish)).length + 1 ≤
    blockIterations (alpha L r) rho * (ProjectedMicro.feasibleMicroIterations + 1) + 1
  rw [queryTrace_bind, List.length_append]
  change (queryTrace P p).length + 0 + 1 ≤ _
  omega

theorem initProgram_cost (P : NCCInstance m n) (hL : 0 < L) (hr : 0 < r) (hrle : r ≤ L / 8)
    (hDelta : 0 < Delta)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ) :
    ((queryTrace P (initProgram (r := r) hL hDelta projectX projectY hpX hpY
      hzeroX hzeroY majorant)).length : ℝ) ≤
      1 + UniformCost.blockConstant (factor Delta (majorant (firstOrderOracle P (0, 0)))) *
        Real.sqrt (L / r) := by
  have hraw := initProgram_actual_count (r := r) P hL hDelta projectX projectY hpX hpY hzeroX hzeroY majorant
  have hc := (BlockCostConcrete.feasibleBlockCost_lt_sqrt_ratio hL hr hrle
    (factor_pos hDelta (majorant (firstOrderOracle P (0, 0))))
    (factor_lt_one Delta (majorant (firstOrderOracle P (0, 0))))).1.le
  rw [BlockCostConcrete.feasibleBlockCost_oracleCalls] at hc
  have hn : ((queryTrace P (initProgram (r := r) hL hDelta projectX projectY hpX hpY
      hzeroX hzeroY majorant)).length : ℝ) ≤
      (blockIterations (alpha L r) (factor Delta (majorant (firstOrderOracle P (0, 0)))) *
        (ProjectedMicro.feasibleMicroIterations + 1) + 1 : Nat) := by exact_mod_cast hraw
  simp only [Nat.cast_add, Nat.cast_one] at hn
  unfold UniformCost.blockConstant
  linarith

section Analytic
variable {f : EVec m → EVec n → ℝ}
  {hprox : HasProxEverywhere X (DualRegularizedValueOn Y f r) L}

theorem initProgram_energy (P : NCCInstance m n) (hL : 0 < L) (hr : 0 < r) (hrle : r ≤ L / 8)
    (hDelta : 0 < Delta) (sys : OuterSystem X Y f L r hprox)
    (projectY : EVec n → EVec n) (hpY : IsEuclideanProjection Y projectY)
    (hmicro : NCSCProgram.MicroRealizes P hL sys projectY hpY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ)
    (hseed : energyAt sys 0 (seedState hzeroY) ≤ majorant (firstOrderOracle P (0, 0))) :
    snapshotEnergy sys (Program.eval P (initProgram (r := r) hL hDelta sys.projectX projectY
      sys.project_spec hpY hzeroX hzeroY majorant)).1 ≤ Delta := by
  let B := majorant (firstOrderOracle P (0, 0))
  let rho := factor Delta B
  have hc := NCSCProgram.refinedState_energy (rho := rho) hL hr hrle sys
    ⟨0, seedState hzeroY, 0⟩ (factor_pos hDelta B) (factor_lt_one Delta B)
  have hb := mul_le_mul_of_nonneg_left hseed (factor_pos hDelta B).le
  have hfinal := hc.trans (hb.trans (factor_majorant hDelta B))
  simp only [initProgram, Program.eval_query, Program.eval_bind, Program.eval_pure]
  unfold snapshotEnergy
  rw [NCSCProgram.eval_callProgram_of_micro P hL sys projectY hpY hmicro]
  exact hfinal

theorem initProgram_potential_gap (P : NCCInstance m n) (hL : 0 < L) (hDelta : 0 < Delta)
    (sys : OuterSystem X Y f L r hprox)
    (projectY : EVec n → EVec n) (hpY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (majorant : OracleReply m n → ℝ) (lower : ℝ)
    (hgap : regularizedEnvelope X Y f L r hprox 0 - lower ≤ Delta) :
    snapshotPotential sys (Program.eval P (initProgram (r := r) hL hDelta sys.projectX projectY
      sys.project_spec hpY hzeroX hzeroY majorant)).1 - lower ≤ 3 * Delta := by
  unfold snapshotPotential
  rw [initProgram_z, initProgram_B]
  linarith

end Analytic
end
end NCC.Extensions.NCSCStartupProgram
