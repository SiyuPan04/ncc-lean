import NCC.Upper.CurrentRun

/-!
# Query-site traces and bounds for the current mathematical run

Each micro trace lists its initial feasible iterate and every iterate up to
the actual first successful test. Consequently its length is exactly the
data-dependent `firstStopIndex + 1`, with one evaluation reused between
successive projected updates. Macro, homotopy, and outer traces concatenate
those traces at the states of the current run.

These are semantic query-site lists: the definitions use the instance to
describe the actual iterates. Feasibility and their lengths are proved here.
This is NOT yet an `Oracle.Program` evaluation theorem, and does not claim
that arbitrary counterfactual oracle replies generate these same traces.
The missing causal-program correspondence is recorded in CURRENT_COST.md.
-/

namespace NCC.Upper.CurrentCost

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open RelativeFOAM RelativeFOAMContraction ScaledOperator SystemInstantiation
open OuterTrajectoryConcrete HomotopyRun HomotopyCost BlockCostConcrete
open AnalyticBridge CurrentRun

variable {m n : Nat} {ell D Delta eps r : ℝ} {P : NCCInstance m n}

abbrev QuerySites (m n : Nat) := List (EVec m × EVec n)

def AllFeasible (P : NCCInstance m n) (qs : QuerySites m n) : Prop :=
  ∀ q ∈ qs, q.1 ∈ P.X ∧ q.2 ∈ P.Y

theorem allFeasible_append {qs rs : QuerySites m n}
    (hqs : AllFeasible P qs) (hrs : AllFeasible P rs) :
    AllFeasible P (qs ++ rs) := by
  intro q hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hqs q hq
  · exact hrs q hq

/-- The initial `u^0` query and all tested `u^1,...,u^s` queries.
Adjacent steps reuse the query at their shared iterate. -/
def microTrace (hP : IsNCCClass ell D Delta P)
    (hr : 0 ≤ r) (hrle : r ≤ ell / 8) (z : EVec m) (S : State m n) :
    QuerySites m n :=
  (List.range (firstStopIndex hP hr hrle z S + 1)).map fun s =>
    let u := microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S s
    (unscaleX ell u, unscaleY ell u)

theorem microTrace_length (hP : IsNCCClass ell D Delta P)
    (hr : 0 ≤ r) (hrle : r ≤ ell / 8) (z : EVec m) (S : State m n) :
    (microTrace hP hr hrle z S).length = firstStopIndex hP hr hrle z S + 1 := by
  simp [microTrace]

theorem microTrace_length_le (hP : IsNCCClass ell D Delta P)
    (hr : 0 ≤ r) (hrle : r ≤ ell / 8) (z : EVec m) (S : State m n) :
    (microTrace hP hr hrle z S).length ≤ ProjectedMicro.feasibleMicroIterations + 1 := by
  rw [microTrace_length]
  exact Nat.add_le_add_right (firstStopIndex_le_universal hP hr hrle z S) 1

theorem microTrace_feasible (hP : IsNCCClass ell D Delta P)
    (hr : 0 ≤ r) (hrle : r ≤ ell / 8) (z : EVec m) (S : State m n) :
    AllFeasible P (microTrace hP hr hrle z S) := by
  intro q hq
  obtain ⟨s, _, rfl⟩ := List.mem_map.mp hq
  have hp := scaledProject_isProjection hP.ell_pos
    (chosenProjectX_spec hP) (chosenProjectY_spec hP)
  exact projectedIterate_mem _ _ _ _ hp.mem s

/-- Concatenate micro traces at the actual intermediate FOAM states. -/
def macroTrace (hP : IsNCCClass ell D Delta P)
    (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) : Nat → ValidState (m := m) P.Y → QuerySites m n
  | 0, _ => []
  | k + 1, S =>
      let sys := firstStopSystemWithProx hP hr hrle hprox
      microTrace hP hr.le hrle z S.1 ++
        macroTrace hP hr hrle hprox z k
          (foamStep ell r (sys.oracle z) (sys.oracle_feasible z) S)

theorem macroTrace_length_le (hP : IsNCCClass ell D Delta P)
    (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) (k : Nat) (S : ValidState (m := m) P.Y) :
    (macroTrace hP hr hrle hprox z k S).length ≤
      k * (ProjectedMicro.feasibleMicroIterations + 1) := by
  induction k generalizing S with
  | zero => simp [macroTrace]
  | succ k ih =>
      simp only [macroTrace, List.length_append]
      have hm := microTrace_length_le hP hr.le hrle z S.1
      have hh := ih (foamStep ell r
        ((firstStopSystemWithProx hP hr hrle hprox).oracle z)
        ((firstStopSystemWithProx hP hr hrle hprox).oracle_feasible z) S)
      calc
        _ ≤ (ProjectedMicro.feasibleMicroIterations + 1) +
            k * (ProjectedMicro.feasibleMicroIterations + 1) := Nat.add_le_add hm hh
        _ = (k + 1) * (ProjectedMicro.feasibleMicroIterations + 1) := by ring

theorem macroTrace_feasible (hP : IsNCCClass ell D Delta P)
    (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) (k : Nat) (S : ValidState (m := m) P.Y) :
    AllFeasible P (macroTrace hP hr hrle hprox z k S) := by
  induction k generalizing S with
  | zero => simp [AllFeasible, macroTrace]
  | succ k ih =>
      exact allFeasible_append (microTrace_feasible hP hr.le hrle z S.1) (ih _)

theorem level_pos (hP : IsNCCClass ell D Delta P) (j : Nat) :
    0 < Tracking.curvature (ell / 8) j :=
  curvature_pos (div_pos hP.ell_pos (by norm_num)) j

theorem level_le (hP : IsNCCClass ell D Delta P) (j : Nat) :
    Tracking.curvature (ell / 8) j ≤ ell / 8 := by
  unfold Tracking.curvature
  exact Tracking.div_pow_le_self (div_nonneg hP.ell_pos.le (by norm_num))
    (by norm_num) j

def warmStageTrace (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (j : Nat) : QuerySites m n :=
  macroTrace hP (level_pos hP (j + 1)) (level_le hP (j + 1))
    (MainTheorem.classProxFamily hP (j + 1)) P.x0
    (blockIterations (alpha ell (Tracking.curvature (ell / 8) (j + 1))) (1 / 8))
    (homotopyState (firstStopSystemFamily hP) P.x0
      (startupState (firstStopSystemFamily hP 0) hzero) j)

def warmTrace (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) : Nat → QuerySites m n
  | 0 => []
  | j + 1 => warmTrace hP hzero j ++ warmStageTrace hP hzero j

theorem warmTrace_length_le (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) :
    (warmTrace hP hzero J).length ≤ homotopyOracleCalls ell (ell / 8) (1 / 8) J := by
  induction J with
  | zero => simp [warmTrace, homotopyOracleCalls]
  | succ J ih =>
      simp only [warmTrace, List.length_append, homotopyOracleCalls,
        Finset.sum_range_succ] at ih ⊢
      exact Nat.add_le_add ih (macroTrace_length_le hP _ _ _ _ _ _)

theorem warmTrace_feasible (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (J : Nat) :
    AllFeasible P (warmTrace hP hzero J) := by
  induction J with
  | zero => simp [AllFeasible, warmTrace]
  | succ J ih => exact allFeasible_append ih (macroTrace_feasible hP _ _ _ _ _ _)

def outerStageTrace (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) (t : Nat) : QuerySites m n :=
  let J := stage hP heps
  let r := finalCurvature hP heps
  let sys := firstStopSystemFamily hP J
  let R := trajectory sys (initialSnapshot hP hzero heps) t
  let zNext := readout sys R.state
  let d := zNext - R.z
  macroTrace hP (finalCurvature_pos hP heps) (level_le hP J)
    (MainTheorem.classProxFamily hP J) zNext
    (blockIterations (alpha ell r) (1 / 400)) (coTranslateValid ell d R.state)

def outerTrace (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) : Nat → QuerySites m n
  | 0 => []
  | t + 1 => outerTrace hP hzero heps t ++ outerStageTrace hP hzero heps t

theorem outerTrace_length_le (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) (T : Nat) :
    (outerTrace hP hzero heps T).length ≤
      T * (feasibleBlockCost ell (finalCurvature hP heps) (1 / 400)).oracleCalls := by
  induction T with
  | zero => simp [outerTrace]
  | succ T ih =>
      simp only [outerTrace, List.length_append]
      have hs : (outerStageTrace hP hzero heps T).length ≤
          (feasibleBlockCost ell (finalCurvature hP heps) (1 / 400)).oracleCalls :=
        macroTrace_length_le hP _ _ _ _ _ _
      simpa [Nat.succ_mul] using Nat.add_le_add ih hs

theorem outerTrace_feasible (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) (T : Nat) :
    AllFeasible P (outerTrace hP hzero heps T) := by
  induction T with
  | zero => simp [AllFeasible, outerTrace]
  | succ T ih => exact allFeasible_append ih (macroTrace_feasible hP _ _ _ _ _ _)

def startupTrace (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) : QuerySites m n :=
  microTrace hP (div_nonneg hP.ell_pos.le (by norm_num)) le_rfl P.x0
    (startupSeed (ell := ell) hzero).1

/-- Full semantic query-site trace, using the current horizon. -/
def runTrace (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) : QuerySites m n :=
  startupTrace hP hzero ++ warmTrace hP hzero (stage hP heps) ++
    outerTrace hP hzero heps (Selection.outerIterations ell Delta eps)

theorem runTrace_feasible (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    AllFeasible P (runTrace hP hzero heps) :=
  allFeasible_append
    (allFeasible_append (microTrace_feasible hP _ _ _ _)
      (warmTrace_feasible hP hzero _)) (outerTrace_feasible hP hzero heps _)

theorem runTrace_length_le (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    (runTrace hP hzero heps).length ≤
      (ProjectedMicro.feasibleMicroIterations + 1) +
        homotopyOracleCalls ell (ell / 8) (1 / 8) (stage hP heps) +
        Selection.outerIterations ell Delta eps *
          (feasibleBlockCost ell (finalCurvature hP heps) (1 / 400)).oracleCalls := by
  simp only [runTrace, List.length_append]
  exact Nat.add_le_add
    (Nat.add_le_add (microTrace_length_le hP _ _ _ _)
      (warmTrace_length_le hP hzero _)) (outerTrace_length_le hP hzero heps _)

/-- The current horizon, including the ceiling, has a universal linear bound. -/
theorem current_horizon_upper (hell : 0 < ell) (hDelta : 0 < Delta) :
    (Selection.outerIterations ell Delta eps : ℝ) ≤
      4001 * (ell * Delta / eps ^ 2 + 1) := by
  have hA : 0 ≤ ell * Delta / eps ^ 2 :=
    div_nonneg (mul_nonneg hell.le hDelta.le) (sq_nonneg eps)
  have hceil : (Selection.outerIterations ell Delta eps : ℝ) <
      4000 * (ell * Delta / eps ^ 2 + 1) + 1 := by
    exact Nat.ceil_lt_add_one (by positivity)
  nlinarith

/-- Explicit universal constant for the semantic query-site length. -/
def traceRateConstant : ℝ :=
  (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) +
    12 * UniformCost.blockConstant (1 / 8) +
    24006 * UniformCost.blockConstant (1 / 400)

theorem traceRateConstant_pos : 0 < traceRateConstant := by
  have h8 := UniformCost.blockConstant_pos
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1)
  have h400 := UniformCost.blockConstant_pos
    (by norm_num : (0 : ℝ) < 1 / 400) (by norm_num : (1 / 400 : ℝ) < 1)
  unfold traceRateConstant
  positivity

/-- Uniform rate of the explicit first-stop query-site list. This is a
bound on `List.length`, not a claimed `Oracle.Program` cost theorem. -/
theorem runTrace_uniform_bound (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (heps : 0 < eps) :
    ((runTrace hP hzero heps).length : ℝ) ≤
      traceRateConstant *
        ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) := by
  let J := stage hP heps
  let r := finalCurvature hP heps
  let T := Selection.outerIterations ell Delta eps
  let A := ell * Delta / eps ^ 2
  let M := max 1 (ell * D / eps)
  let C8 := UniformCost.blockConstant (1 / 8)
  let C400 := UniformCost.blockConstant (1 / 400)
  have hr : 0 < r := finalCurvature_pos hP heps
  have hrle : r ≤ ell / 8 := level_le hP J
  have hA : 0 ≤ A := div_nonneg
    (mul_nonneg hP.ell_pos.le hP.Delta_pos.le) (sq_nonneg eps)
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hAp : 1 ≤ A + 1 := by linarith
  have hrate : 1 ≤ (A + 1) * M := by
    simpa using mul_le_mul hAp hM (by norm_num : (0 : ℝ) ≤ 1) (by linarith)
  have hC8 : 0 < C8 := UniformCost.blockConstant_pos (by norm_num) (by norm_num)
  have hC400 : 0 < C400 := UniformCost.blockConstant_pos (by norm_num) (by norm_num)
  have hsqrt : Real.sqrt (ell / r) ≤ 6 * M :=
    (UniformSchedule.sqrt_ratio_lt_six_max hP.ell_pos hP.D_pos heps hr
      (finalCurvature_interval hP heps).1).le
  have hblock0 := (feasibleBlockCost_lt_sqrt_ratio hP.ell_pos hr hrle
    (by norm_num : (0 : ℝ) < 1 / 400) (by norm_num : (1 / 400 : ℝ) < 1)).1.le
  have hblock : ((feasibleBlockCost ell r (1 / 400)).oracleCalls : ℝ) ≤
      6 * C400 * M := by
    calc
      _ ≤ C400 * Real.sqrt (ell / r) := hblock0
      _ ≤ C400 * (6 * M) := mul_le_mul_of_nonneg_left hsqrt hC400.le
      _ = 6 * C400 * M := by ring
  have hT : (T : ℝ) ≤ 4001 * (A + 1) :=
    current_horizon_upper hP.ell_pos hP.Delta_pos
  have houter : (T : ℝ) * ((feasibleBlockCost ell r (1 / 400)).oracleCalls : ℝ) ≤
      24006 * C400 * ((A + 1) * M) := by
    have hm := mul_le_mul hT hblock (Nat.cast_nonneg _)
      (show 0 ≤ 4001 * (A + 1) by positivity)
    calc
      _ ≤ (4001 * (A + 1)) * (6 * C400 * M) := hm
      _ = 24006 * C400 * ((A + 1) * M) := by ring
  have hhom0 := (homotopy_total_cost_le hP.ell_pos
    (div_pos hP.ell_pos (by norm_num)) le_rfl
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1) J).1
  have hhom : (homotopyOracleCalls ell (ell / 8) (1 / 8) J : ℝ) ≤
      12 * C8 * ((A + 1) * M) := by
    calc
      _ ≤ 2 * C8 * Real.sqrt (ell / r) := hhom0
      _ ≤ 2 * C8 * (6 * M) :=
        mul_le_mul_of_nonneg_left hsqrt (by positivity)
      _ = 12 * C8 * M := by ring
      _ ≤ 12 * C8 * ((A + 1) * M) := by
        have hm := mul_le_mul_of_nonneg_right hAp hM0
        exact mul_le_mul_of_nonneg_left (by simpa using hm) (by positivity)
  have hstart : (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) ≤
      (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) * ((A + 1) * M) := by
    have hm := mul_le_mul_of_nonneg_left hrate
      (show (0 : ℝ) ≤ ProjectedMicro.feasibleMicroIterations + 1 by positivity)
    simpa using hm
  have hraw : ((runTrace hP hzero heps).length : ℝ) ≤
      (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) +
        (homotopyOracleCalls ell (ell / 8) (1 / 8) J : ℝ) +
        (T : ℝ) * ((feasibleBlockCost ell r (1 / 400)).oracleCalls : ℝ) := by
    exact_mod_cast runTrace_length_le hP hzero heps
  calc
    _ ≤ (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) +
        (homotopyOracleCalls ell (ell / 8) (1 / 8) J : ℝ) +
        (T : ℝ) * ((feasibleBlockCost ell r (1 / 400)).oracleCalls : ℝ) := hraw
    _ ≤ (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) * ((A + 1) * M) +
        12 * C8 * ((A + 1) * M) + 24006 * C400 * ((A + 1) * M) :=
      add_le_add (add_le_add hstart hhom) houter
    _ = traceRateConstant * ((ell * Delta / eps ^ 2 + 1) *
        max 1 (ell * D / eps)) := by
      unfold traceRateConstant
      dsimp [A, M, C8, C400]
      ring

end
end NCC.Upper.CurrentCost
