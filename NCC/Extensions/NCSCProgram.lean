import NCC.Extensions.NCSCAuxiliary
import NCC.Extensions.GSProgram

/-!
# Fixed-curvature counted clients and exact NC-SC reply adaptation

The unbounded-dual NC-SC construction uses no diameter or homotopy.
Adding the known dual quadratic to an oracle reply simulates the
auxiliary objective exactly, with no additional query. The fixed-level
client below keeps initialization as an explicit finite program and
counts it separately. Analytic initial-energy and local-oracle
certificates must be discharged independently; no end-to-end solver
correctness is assumed here.
-/
namespace NCC.Extensions.NCSCProgram
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle RelativeFOAM RelativeFOAMContraction ProjectionGeometry
open OuterTrajectoryConcrete HomotopyRun SharedOracle
open NCC.Upper NCC.Upper.AdaptiveMicroProgram NCC.Upper.CurrentProgram
set_option maxHeartbeats 3000000
variable {m n : Nat} {L r mu : ℝ} {X : Set (EVec m)} {Y : Set (EVec n)}

/-- The known quadratic contributes only local arithmetic. -/
def adaptReply (mu : ℝ) (q : Query m n) (reply : OracleReply m n) : OracleReply m n where
  value := reply.value + quadraticCorrection mu q.2
  gradX := reply.gradX
  gradY := reply.gradY + mu • q.2

theorem adaptReply_true (P : NCCInstance m n) (mu : ℝ) (q : Query m n) :
    adaptReply mu q (firstOrderOracle P q) = firstOrderOracle (NCSC.auxiliary P mu) q := rfl

def adaptProgram {α : Type} (mu : ℝ) : Program X Y α → Program X Y α
  | .pure a => .pure a
  | .query q hq next => .query q hq (fun reply => adaptProgram mu (next (adaptReply mu q reply)))

/-- Every branch has exactly the same queried points and number of calls
as the corresponding auxiliary-oracle branch. -/
theorem adaptProgram_depth {α : Type} (mu : ℝ) {p : Program X Y α} {k : Nat}
    (hp : DepthAtMost p k) : DepthAtMost (adaptProgram mu p) k := by
  induction hp with
  | pure a k => exact DepthAtMost.pure a k
  | query q hq next k _ ih =>
      exact DepthAtMost.query q hq _ k (fun reply => ih (adaptReply mu q reply))

theorem eval_adaptProgram {α : Type} (P : NCCInstance m n) (mu : ℝ) (p : Program X Y α) :
    Program.eval P (adaptProgram mu p) = Program.eval (NCSC.auxiliary P mu) p := by
  induction p with
  | pure a => rfl
  | query q hq next ih =>
      simp only [adaptProgram, Program.eval_query, adaptReply_true]
      exact ih (firstOrderOracle (NCSC.auxiliary P mu) q)

theorem queryTrace_adaptProgram {α : Type} (P : NCCInstance m n) (mu : ℝ) (p : Program X Y α) :
    queryTrace P (adaptProgram mu p) = queryTrace (NCSC.auxiliary P mu) p := by
  induction p with
  | pure a => rfl
  | query q hq next ih =>
      change q :: queryTrace P (adaptProgram mu (next (adaptReply mu q (firstOrderOracle P q)))) = _
      rw [adaptReply_true, ih]
      rfl

theorem exactDepth_to_depth {α : Type} {p : Program X Y α} {k : Nat}
    (hp : ExactDepth p k) : DepthAtMost p k := by
  induction hp with
  | pure a => exact DepthAtMost.pure a 0
  | query q hq next k _ ih => exact DepthAtMost.query q hq next k ih

/-- The NC-SC configuration uses the proved universal fixed micro cutoff.
It has the same numerical constant cost and is not asserted to use the
NC-C client's early stopping rule. -/
def callProgram (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) Y) : Program X Y (ValidState (m := m) Y) :=
  SharedOracle.blockProgram (r := r) hL projectX projectY hpX hpY z
    (blockIterations (alpha L r) rho) S

theorem callProgram_depth (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) Y) :
    DepthAtMost (callProgram (r := r) hL projectX projectY hpX hpY z rho S)
      (blockIterations (alpha L r) rho * (ProjectedMicro.feasibleMicroIterations + 1)) :=
  exactDepth_to_depth (SharedOracle.exactDepth_blockProgram hL projectX projectY hpX hpY z _ S)

def historyProgram (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY) :
    Nat → FeasibleSnapshot X Y → Program X Y (Nat → FeasibleSnapshot X Y)
  | 0, R0 => .pure (fun _ => R0)
  | t + 1, R0 => do
    let H ← historyProgram hL projectX projectY hpX hpY t R0
    let Rnext ← SharedOracle.nextSnapshotProgram (r := r) hL projectX projectY hpX hpY (H t)
    .pure (fun i => if i = t + 1 then Rnext else H i)

theorem historyProgram_depth (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (T : Nat) (R0 : FeasibleSnapshot X Y) :
    DepthAtMost (historyProgram (r := r) hL projectX projectY hpX hpY T R0)
      (T * (blockIterations (alpha L r) (1 / 400) * (ProjectedMicro.feasibleMicroIterations + 1))) := by
  induction T with
  | zero => simpa only [historyProgram, Nat.zero_mul] using
      (DepthAtMost.pure (X := X) (Y := Y) (fun _ => R0) 0)
  | succ T ih =>
      let finish (H : Nat → FeasibleSnapshot X Y) (Rnext : FeasibleSnapshot X Y) :
          Program X Y (Nat → FeasibleSnapshot X Y) := .pure (fun i => if i = T + 1 then Rnext else H i)
      have ht (H : Nat → FeasibleSnapshot X Y) :=
        (exactDepth_to_depth (SharedOracle.exactDepth_nextSnapshotProgram (r := r)
          hL projectX projectY hpX hpY (H T))).bind (finish H) (fun _ => DepthAtMost.pure _ 0)
      have hb := ih.bind _ ht
      simpa only [historyProgram, finish, Nat.succ_mul, Nat.add_zero] using hb

/-- Initialization is a genuine supplied oracle program, not a free
initial saddle point. Its actual cost and certificate remain explicit. -/
def fixedProgram (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (initProgram : Program X Y (FeasibleSnapshot X Y))
    (T : Nat) (hT : 0 < T) (rho : ℝ) :
    Program X Y (FeasibleSnapshot X Y × ValidState (m := m) Y) := do
  let R0 ← initProgram
  let H ← historyProgram (r := r) hL projectX projectY hpX hpY T R0
  let R := GSProgram.selectSnapshot L projectX T hT H
  let S ← callProgram (r := r) hL projectX projectY hpX hpY
    R.1.z rho R.1.state
  .pure (R, S)

def fixedCount (L r : ℝ) (initialCount T : Nat) (rho : ℝ) : Nat :=
  initialCount + T * (blockIterations (alpha L r) (1 / 400) *
    (ProjectedMicro.feasibleMicroIterations + 1)) +
    blockIterations (alpha L r) rho * (ProjectedMicro.feasibleMicroIterations + 1)

theorem fixedProgram_depth (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (initProgram : Program X Y (FeasibleSnapshot X Y)) {initialCount : Nat}
    (hinit : DepthAtMost initProgram initialCount) (T : Nat) (hT : 0 < T) (rho : ℝ) :
    DepthAtMost (fixedProgram (r := r) hL projectX projectY hpX hpY initProgram T hT rho)
      (fixedCount L r initialCount T rho) := by
  let tail (H : Nat → FeasibleSnapshot X Y) :
      Program X Y (FeasibleSnapshot X Y × ValidState (m := m) Y) := do
    let R := GSProgram.selectSnapshot L projectX T hT H
    let S ← callProgram (r := r) hL projectX projectY hpX hpY
      R.1.z rho R.1.state
    .pure (R, S)
  have ht (H : Nat → FeasibleSnapshot X Y) :=
    (callProgram_depth (r := r) hL projectX projectY hpX hpY
      (GSProgram.selectSnapshot L projectX T hT H).1.z rho
      (GSProgram.selectSnapshot L projectX T hT H).1.state).bind
      (fun S => .pure (GSProgram.selectSnapshot L projectX T hT H, S))
      (fun _ => DepthAtMost.pure _ 0)
  have hh (R0 : FeasibleSnapshot X Y) :=
    (historyProgram_depth (r := r) hL projectX projectY hpX hpY T R0).bind tail ht
  have hb := hinit.bind _ hh
  simpa only [fixedProgram, tail, fixedCount, Nat.add_assoc, Nat.add_zero] using hb

/-- The initialization may itself have reply-dependent depth. Its actual
trace length is charged explicitly; no uniform depth is assumed for it. -/
theorem fixedProgram_actual_count (P : NCCInstance m n) (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (initProgram : Program X Y (FeasibleSnapshot X Y)) (T : Nat) (hT : 0 < T) (rho : ℝ) :
    (queryTrace P (fixedProgram (r := r) hL projectX projectY hpX hpY initProgram T hT rho)).length ≤
      fixedCount L r (queryTrace P initProgram).length T rho := by
  let R0 := Program.eval P initProgram
  let H := Program.eval P (historyProgram (r := r) hL projectX projectY hpX hpY T R0)
  let R := GSProgram.selectSnapshot L projectX T hT H
  have hh := (historyProgram_depth (r := r) hL projectX projectY hpX hpY T R0).trace_length P
  have hf := (callProgram_depth (r := r) hL projectX projectY hpX hpY R.1.z rho R.1.state).trace_length P
  rw [fixedProgram, queryTrace_bind, List.length_append, queryTrace_bind, List.length_append,
    queryTrace_bind, List.length_append]
  change (queryTrace P initProgram).length +
    ((queryTrace P (historyProgram (r := r) hL projectX projectY hpX hpY T R0)).length +
      ((queryTrace P (callProgram (r := r) hL projectX projectY hpX hpY R.1.z rho R.1.state)).length + 0)) ≤ _
  unfold fixedCount
  omega

theorem adapted_fixedProgram_actual_count (P : NCCInstance m n) (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (initProgram : Program X Y (FeasibleSnapshot X Y)) (T : Nat) (hT : 0 < T) (rho mu : ℝ) :
    (queryTrace P (adaptProgram mu
      (fixedProgram (r := r) hL projectX projectY hpX hpY initProgram T hT rho))).length ≤
      fixedCount L r (queryTrace P (adaptProgram mu initProgram)).length T rho := by
  rw [queryTrace_adaptProgram, queryTrace_adaptProgram]
  exact fixedProgram_actual_count (NCSC.auxiliary P mu) hL projectX projectY hpX hpY initProgram T hT rho

theorem adapted_fixedProgram_count (P : NCCInstance m n) (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (initProgram : Program X Y (FeasibleSnapshot X Y)) {initialCount : Nat}
    (hinit : DepthAtMost initProgram initialCount) (T : Nat) (hT : 0 < T) (rho : ℝ) (mu : ℝ) :
    (queryTrace P (adaptProgram mu
      (fixedProgram (r := r) hL projectX projectY hpX hpY initProgram T hT rho))).length ≤
      fixedCount L r initialCount T rho :=
  (adaptProgram_depth mu (fixedProgram_depth hL projectX projectY hpX hpY initProgram hinit T hT rho)).trace_length P

theorem adapted_fixedProgram_all_histories_feasible (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (initProgram : Program X Y (FeasibleSnapshot X Y)) (T : Nat) (hT : 0 < T) (rho mu : ℝ)
    (fallback : Query m n) (hfallback : fallback.1 ∈ X ∧ fallback.2 ∈ Y)
    (t : Nat) (history : ReplyHistory m n t) :
    let q := Program.queryAfterHistory (adaptProgram mu
      (fixedProgram (r := r) hL projectX projectY hpX hpY initProgram T hT rho)) fallback t history
    q.1 ∈ X ∧ q.2 ∈ Y :=
  Program.queryAfterHistory_mem _ fallback hfallback t history

theorem fixedCount_le (hL : 0 < L) (hr : 0 < r) (hrle : r ≤ L / 8)
    (initialCount T : Nat) {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    (fixedCount L r initialCount T rho : ℝ) ≤ (initialCount : ℝ) +
      ((T : ℝ) * UniformCost.blockConstant (1 / 400) + UniformCost.blockConstant rho) *
        Real.sqrt (L / r) := by
  have houter := (BlockCostConcrete.feasibleBlockCost_lt_sqrt_ratio hL hr hrle
    (by norm_num : (0 : ℝ) < 1 / 400) (by norm_num : (1 / 400 : ℝ) < 1)).1.le
  have hrefine := (BlockCostConcrete.feasibleBlockCost_lt_sqrt_ratio hL hr hrle hrho hrho1).1.le
  have houterT := mul_le_mul_of_nonneg_left houter (Nat.cast_nonneg T)
  rw [BlockCostConcrete.feasibleBlockCost_oracleCalls] at houterT hrefine
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at houterT hrefine
  unfold fixedCount UniformCost.blockConstant
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  nlinarith

section Execution
variable {f : EVec m → EVec n → ℝ}
  {hprox : HasProxEverywhere X (DualRegularizedValueOn Y f r) L}

/-- This is only the local micro evaluator identification. The following
lemmas derive every macrostep and retained state from it structurally.
It is not a hypothesized whole-program solver specification. -/
def MicroRealizes (P : NCCInstance m n) (hL : 0 < L)
    (sys : OuterSystem X Y f L r hprox) (projectY : EVec n → EVec n)
    (hpY : IsEuclideanProjection Y projectY) : Prop :=
  ∀ z (S : ValidState (m := m) Y),
    (Program.eval P (SharedOracle.feasibleClassMicroProgram (r := r) hL sys.projectX projectY
      sys.project_spec hpY z S.1)).1 = sys.oracle z S

theorem microRealizes_of_classOracle (P : NCCInstance m n) (hL : 0 < L)
    (sys : OuterSystem X Y f L r hprox) (projectY : EVec n → EVec n)
    (hpY : IsEuclideanProjection Y projectY)
    (horacle : ∀ z (S : ValidState (m := m) Y), sys.oracle z S =
      SystemInstantiation.classOracle P L r sys.projectX projectY z S.1) :
    MicroRealizes P hL sys projectY hpY := by
  intro z S
  rw [SharedOracle.eval_feasibleClassMicroProgram_val, horacle z S]

theorem eval_macroStepProgram_of_micro (P : NCCInstance m n) (hL : 0 < L)
    (sys : OuterSystem X Y f L r hprox) (projectY : EVec n → EVec n)
    (hpY : IsEuclideanProjection Y projectY) (hmicro : MicroRealizes P hL sys projectY hpY)
    (z : EVec m) (S : ValidState (m := m) Y) :
    Program.eval P (SharedOracle.macroStepProgram (r := r) hL sys.projectX projectY
      sys.project_spec hpY z S) = foamStep L r (sys.oracle z) (sys.oracle_feasible z) S := by
  apply Subtype.ext
  simp only [SharedOracle.macroStepProgram, Program.eval_bind, Program.eval_pure]
  rw [hmicro z S]
  rfl

theorem eval_blockProgram_of_micro (P : NCCInstance m n) (hL : 0 < L)
    (sys : OuterSystem X Y f L r hprox) (projectY : EVec n → EVec n)
    (hpY : IsEuclideanProjection Y projectY) (hmicro : MicroRealizes P hL sys projectY hpY)
    (z : EVec m) (k : Nat) (S : ValidState (m := m) Y) :
    Program.eval P (SharedOracle.blockProgram (r := r) hL sys.projectX projectY
      sys.project_spec hpY z k S) =
      ((foamStep L r (sys.oracle z) (sys.oracle_feasible z))^[k]) S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
      rw [SharedOracle.blockProgram, Program.eval_bind, ih,
        eval_macroStepProgram_of_micro P hL sys projectY hpY hmicro]
      rw [Function.iterate_succ_apply]

theorem eval_callProgram_of_micro (P : NCCInstance m n) (hL : 0 < L)
    (sys : OuterSystem X Y f L r hprox) (projectY : EVec n → EVec n)
    (hpY : IsEuclideanProjection Y projectY) (hmicro : MicroRealizes P hL sys projectY hpY)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) Y) :
    Program.eval P (callProgram (r := r) hL sys.projectX projectY
      sys.project_spec hpY z rho S) =
      ((foamStep L r (sys.oracle z) (sys.oracle_feasible z))^[blockIterations (alpha L r) rho]) S :=
  eval_blockProgram_of_micro P hL sys projectY hpY hmicro z _ S

theorem eval_nextProgram_of_micro (P : NCCInstance m n) (hL : 0 < L)
    (sys : OuterSystem X Y f L r hprox) (projectY : EVec n → EVec n)
    (hpY : IsEuclideanProjection Y projectY) (hmicro : MicroRealizes P hL sys projectY hpY)
    (R : FeasibleSnapshot X Y) :
    (Program.eval P (SharedOracle.nextSnapshotProgram (r := r) hL sys.projectX projectY
      sys.project_spec hpY R)).1 = nextSnapshot sys R.1 := by
  unfold SharedOracle.nextSnapshotProgram nextSnapshot
  simp only [Program.eval_bind, Program.eval_pure]
  rw [eval_blockProgram_of_micro P hL sys projectY hpY hmicro]
  rfl

theorem eval_historyProgram_of_micro (P : NCCInstance m n) (hL : 0 < L)
    (sys : OuterSystem X Y f L r hprox) (projectY : EVec n → EVec n)
    (hpY : IsEuclideanProjection Y projectY) (hmicro : MicroRealizes P hL sys projectY hpY)
    (T : Nat) (R0 : FeasibleSnapshot X Y) (i : Nat) (hi : i ≤ T) :
    (Program.eval P (historyProgram (r := r) hL sys.projectX projectY
      sys.project_spec hpY T R0) i).1 = trajectory sys R0.1 i := by
  induction T generalizing i with
  | zero => have hi0 : i = 0 := by omega
            subst i
            rfl
  | succ T ih =>
      simp only [historyProgram, Program.eval_bind, Program.eval_pure]
      by_cases hit : i = T + 1
      · subst i
        simp only [ite_true]
        rw [eval_nextProgram_of_micro P hL sys projectY hpY hmicro, ih T le_rfl]
        rfl
      · simp only [if_neg hit]
        exact ih i (by omega)

def selectedSnapshot (sys : OuterSystem X Y f L r hprox)
    (R0 : Snapshot (m := m) Y) (T : Nat) (hT : 0 < T) : Snapshot (m := m) Y :=
  trajectory sys R0 (Selection.selectedIndex sys R0 T hT)

def refinedState (sys : OuterSystem X Y f L r hprox)
    (R : Snapshot (m := m) Y) (rho : ℝ) : ValidState (m := m) Y :=
  ((foamStep L r (sys.oracle R.z) (sys.oracle_feasible R.z))^[blockIterations (alpha L r) rho]) R.state

theorem eval_selectedSnapshot_of_micro (P : NCCInstance m n) (hL : 0 < L)
    (sys : OuterSystem X Y f L r hprox) (projectY : EVec n → EVec n)
    (hpY : IsEuclideanProjection Y projectY) (hmicro : MicroRealizes P hL sys projectY hpY)
    (T : Nat) (hT : 0 < T) (R0 : FeasibleSnapshot X Y) :
    (GSProgram.selectSnapshot L sys.projectX T hT
      (Program.eval P (historyProgram (r := r) hL sys.projectX projectY
        sys.project_spec hpY T R0))).1 = selectedSnapshot sys R0.1 T hT := by
  let H := Program.eval P (historyProgram (r := r) hL sys.projectX projectY
    sys.project_spec hpY T R0)
  have hscores (i : Nat) (hi : i < T) :
      localScore L sys.projectX (H i).1 = AnalyticBridge.observable sys (trajectory sys R0.1 i) := by
    change AnalyticBridge.observable sys (H i).1 = _
    rw [eval_historyProgram_of_micro P hL sys projectY hpY hmicro T R0 i hi.le]
  have hsel := leastMinimizer_congr
    (fun i => localScore L sys.projectX (H i).1)
    (fun i => AnalyticBridge.observable sys (trajectory sys R0.1 i)) T hT hscores
  unfold GSProgram.selectSnapshot selectedSnapshot Selection.selectedIndex
  change (H _).1 = _
  rw [hsel, eval_historyProgram_of_micro P hL sys projectY hpY hmicro T R0 _
    (Selection.leastMinimizer_spec _ T hT).1.le]

theorem eval_fixedProgram_of_micro (P : NCCInstance m n) (hL : 0 < L)
    (sys : OuterSystem X Y f L r hprox) (projectY : EVec n → EVec n)
    (hpY : IsEuclideanProjection Y projectY) (hmicro : MicroRealizes P hL sys projectY hpY)
    (initProgram : Program X Y (FeasibleSnapshot X Y)) (T : Nat) (hT : 0 < T) (rho : ℝ) :
    let R := selectedSnapshot sys (Program.eval P initProgram).1 T hT
    let out := Program.eval P (fixedProgram (r := r) hL sys.projectX projectY
      sys.project_spec hpY initProgram T hT rho)
    out.1.1 = R ∧ out.2 = refinedState sys R rho := by
  simp only [fixedProgram, Program.eval_bind, Program.eval_pure]
  rw [eval_callProgram_of_micro P hL sys projectY hpY hmicro]
  have hs := eval_selectedSnapshot_of_micro P hL sys projectY hpY hmicro T hT
    (Program.eval P initProgram)
  exact ⟨hs, congrArg (fun R => refinedState sys R rho) hs⟩

/-- A generic honest analytic bridge: actual initial energy and actual
potential gap imply bounds for the actual minimum-Q retained state.
No dimension bound or dual radius is used. -/
theorem selectedSnapshot_bounds (hX : X.Nonempty) (hL : 0 < L) (hr : 0 < r) (hrle : r ≤ L / 8)
    (hweak : IsWeaklyConvexOn L X (DualRegularizedValueOn Y f r))
    (sys : OuterSystem X Y f L r hprox) (R0 : Snapshot (m := m) Y)
    (hE0 : snapshotEnergy sys R0 ≤ R0.B) (hB0 : 0 ≤ R0.B)
    (T : Nat) (hT : 0 < T) (lower G : ℝ)
    (hlower : ∀ z, lower ≤ regularizedEnvelope X Y f L r hprox z)
    (hgap : snapshotPotential sys R0 - lower ≤ G) :
    let R := selectedSnapshot sys R0 T hT
    snapshotEnergy sys R ≤ R.B ∧ 0 ≤ R.B ∧
      AnalyticBridge.observable sys R ≤ 4 * G / (T : ℝ) ∧
      vecSq (residualGradient hprox R.z) ≤ 32 * L * G / (T : ℝ) := by
  let R := selectedSnapshot sys R0 T hT
  have hEB := trajectory_energy_le_B hX hL hr hrle sys R0 hE0
  have hB := trajectory_B_nonneg hL.le sys R0 hB0
  have hg := Selection.selected_regularized_gradient_bound hX hL hr hrle hweak sys R0
    hE0 hB0 T hT lower hlower
  let w := fun t => snapshotPotential sys (trajectory sys R0 t)
  let q := fun t => AnalyticBridge.observable sys (trajectory sys R0 t)
  have hdescent : ∀ t, t < T → w (t + 1) - w t ≤ -(1 / 4 : ℝ) * q t := by
    intro t _
    exact AnalyticBridge.observable_descent hL hr hweak sys _ (hEB t)
  have hterminal : lower ≤ w T := by
    have hb := hB T
    have hl := hlower (trajectory sys R0 T).z
    dsimp [w, snapshotPotential]
    linarith
  have hq := Upper.selected_residual_bound w q T lower
    (q (Selection.selectedIndex sys R0 T hT)) hT hdescent hterminal
    (Selection.leastMinimizer_spec q T hT).2
  refine ⟨hEB _, hB _, hq.trans ?_, hg.trans ?_⟩
  · apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg T)
    change 4 * (snapshotPotential sys R0 - lower) ≤ _
    linarith
  · have hc : 0 ≤ 32 * L / (T : ℝ) := by positivity
    have hh := mul_le_mul_of_nonneg_left hgap hc
    convert hh using 1
    ring

theorem refinedState_energy (hL : 0 < L) (hr : 0 < r) (hrle : r ≤ L / 8)
    (sys : OuterSystem X Y f L r hprox) (R : Snapshot (m := m) Y)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    energyAt sys R.z (refinedState sys R rho) ≤ rho * snapshotEnergy sys R := by
  let st := sys.stationary R.z
  have hmin := (PointwiseConjugate.Pzr_unique_minimizer hL hr
    st.subgradient st.stationQ st.stationY).1
  have henergy (V : ValidState (m := m) Y) :
      energyAt sys R.z V = energy L r st.qStar st.yStar.1
        (PzrTotal X Y (PointwiseConjugate.decurved f L r R.z) L r)
        (PointwiseConjugate.Pzr X Y (PointwiseConjugate.decurved f L r R.z) L r
          st.qStar st.yStar) V.1 := snapshotEnergy_eq_foamEnergy sys ⟨R.z, V, 0⟩
  unfold snapshotEnergy
  rw [henergy, henergy]
  exact block_energy_contraction hL hr hrle st.qStar st.yStar hmin
    (sys.oracle R.z) (sys.oracle_feasible R.z) (sys.oracle_subgradient R.z)
    (sys.oracle_residual R.z) R.state hrho hrho1

theorem refinedState_energy_le_observable (hL : 0 < L) (hr : 0 < r) (hrle : r ≤ L / 8)
    (sys : OuterSystem X Y f L r hprox) (R : Snapshot (m := m) Y)
    (hE : snapshotEnergy sys R ≤ R.B) {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    energyAt sys R.z (refinedState sys R rho) ≤ rho * AnalyticBridge.observable sys R := by
  have hs : 0 ≤ L * vecSq (stepDisplacement sys R) :=
    mul_nonneg hL.le (Tracking.vecSq_nonneg _)
  have hBQ : R.B ≤ AnalyticBridge.observable sys R := by
    unfold AnalyticBridge.observable
    linarith
  exact (refinedState_energy hL hr hrle sys R hrho hrho1).trans
    (mul_le_mul_of_nonneg_left (hE.trans hBQ) hrho.le)

/-- The numerical fixed-r horizon has enough margin for the normal-cone
readout's anchor budget, with no curvature-dependent accuracy factor. -/
theorem horizon_gradient_budget {eps G gSq : ℝ} (hL : 0 < L) (hG : 0 < G) (heps : 0 < eps)
    (hg : gSq ≤ 32 * L * G / (Selection.outerIterations L G eps : ℝ)) :
    gSq < eps ^ 2 / 16 := by
  have hT : 0 < (Selection.outerIterations L G eps : ℝ) :=
    Nat.cast_pos.mpr (Selection.outerIterations_pos hL hG)
  have he2 := sq_pos_of_pos heps
  have hbound := mul_le_mul_of_nonneg_right
    (Selection.outerIterations_lower (ell := L) (Delta := G) (eps := eps)) he2.le
  have hc : 4000 * (L * G / eps ^ 2 + 1) * eps ^ 2 = 4000 * (L * G + eps ^ 2) := by
    field_simp
  rw [hc] at hbound
  have hg' := (le_div_iff₀ hT).1 hg
  have hprod := mul_pos hL hG
  apply (mul_lt_mul_iff_left₀ hT).1
  nlinarith

end Execution

end
end NCC.Extensions.NCSCProgram
