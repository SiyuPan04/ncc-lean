import NCC.Upper.AdaptiveMicroProgram
import NCC.Upper.CurrentCost
import NCCLowerBoundVerification.Upper.BlockCostConcrete

/-!
# Reply-driven FOAM blocks with first-success micro calls

The client is parameterized by geometry and numerical data only. It
composes the adaptive micro client, so different replies may cause
different micro lengths. Evaluation identifies the resulting state with
the current first-stop analytic system, while a compositional depth bound
controls every counterfactual reply branch.
-/

namespace NCC.Upper.AdaptiveMicroProgram

noncomputable section

open NCCLowerBoundVerification

variable {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}

theorem DepthAtMost.add {α : Type} {p : Oracle.Program X Y α} {c : Nat}
    (hp : DepthAtMost p c) (k : Nat) : DepthAtMost p (c + k) := by
  induction hp with
  | pure a c => exact DepthAtMost.pure a _
  | query q hq next c hnext ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        DepthAtMost.query q hq next (c + k) ih

theorem DepthAtMost.bind {α β : Type} {p : Oracle.Program X Y α}
    {cp ck : Nat} (hp : DepthAtMost p cp)
    (k : α → Oracle.Program X Y β) (hk : ∀ a, DepthAtMost (k a) ck) :
    DepthAtMost (p >>= k) (cp + ck) := by
  induction hp with
  | pure a c =>
      change DepthAtMost (k a) (c + ck)
      simpa [Nat.add_comm] using (hk a).add c
  | query q hq next c hnext ih =>
      change DepthAtMost (.query q hq (fun reply => next reply >>= k)) ((c + 1) + ck)
      rw [show (c + 1) + ck = (c + ck) + 1 by omega]
      exact DepthAtMost.query q hq _ (c + ck) ih

/-- Sequential composition concatenates the actual executed query lists. -/
theorem queryTrace_bind {α β : Type} (P : NCCInstance m n)
    (p : Oracle.Program X Y α) (k : α → Oracle.Program X Y β) :
    queryTrace P (p >>= k) = queryTrace P p ++ queryTrace P (k (Oracle.Program.eval P p)) := by
  induction p with
  | pure a => rfl
  | query q hq next ih =>
      change q :: queryTrace P (next (Oracle.firstOrderOracle P q) >>= k) =
        (q :: queryTrace P (next (Oracle.firstOrderOracle P q))) ++
          queryTrace P (k (Oracle.Program.eval P (next (Oracle.firstOrderOracle P q))))
      rw [ih]
      rfl

end
end NCC.Upper.AdaptiveMicroProgram

namespace NCC.Upper.AdaptiveFOAMProgram

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open RelativeFOAM RelativeFOAMContraction ProjectionGeometry
open SharedOracle SystemInstantiation OuterTrajectoryConcrete
open AnalyticBridge AdaptiveMicroProgram

variable {m n : Nat} {ell r : ℝ}
  {X : Set (EVec m)} {Y : Set (EVec n)}

/-- A macrostep contains one adaptive micro call followed by the explicit
FOAM state update. The latter requires no additional oracle access. -/
def macroStepProgram (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : ValidState (m := m) Y) :
    Oracle.Program X Y (ValidState (m := m) Y) := do
  let O ← AdaptiveMicroProgram.program (r := r) hell projectX projectY hprojX hprojY z S.1
  Oracle.Program.pure ⟨update ell r S.1 O.1, O.2⟩

/-- A fixed-anchor FOAM call with a specified number of macrosteps. -/
def blockProgram (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) : Nat → ValidState (m := m) Y →
      Oracle.Program X Y (ValidState (m := m) Y)
  | 0, S => Oracle.Program.pure S
  | k + 1, S => do
      let Snext ← macroStepProgram (r := r) hell projectX projectY hprojX hprojY z S
      blockProgram hell projectX projectY hprojX hprojY z k Snext

/-- The current contraction-factor schedule chooses its macro count from
numerical parameters, never from the objective or future oracle replies. -/
def callProgram (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) Y) :
    Oracle.Program X Y (ValidState (m := m) Y) :=
  blockProgram (r := r) hell projectX projectY hprojX hprojY z
    (blockIterations (alpha ell r) rho) S

theorem macroStepProgram_depth (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : ValidState (m := m) Y) :
    DepthAtMost (macroStepProgram (r := r) hell projectX projectY hprojX hprojY z S)
      (ProjectedMicro.feasibleMicroIterations + 1) := by
  let finish : FeasibleMicroOutput m Y → Oracle.Program X Y (ValidState (m := m) Y) :=
    fun O => .pure ⟨update ell r S.1 O.1, O.2⟩
  have hbind := (program_depth (r := r) hell projectX projectY hprojX hprojY z S.1).bind
    finish (fun _ => DepthAtMost.pure _ 0)
  simpa [macroStepProgram, finish] using hbind

theorem blockProgram_depth (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (k : Nat) (S : ValidState (m := m) Y) :
    DepthAtMost (blockProgram (r := r) hell projectX projectY hprojX hprojY z k S)
      (k * (ProjectedMicro.feasibleMicroIterations + 1)) := by
  induction k generalizing S with
  | zero => simpa [blockProgram] using (DepthAtMost.pure (X := X) (Y := Y) S 0)
  | succ k ih =>
      have hbind := (macroStepProgram_depth (r := r) hell projectX projectY
        hprojX hprojY z S).bind
        (fun Snext => blockProgram (r := r) hell projectX projectY hprojX hprojY z k Snext) ih
      simpa [blockProgram, Nat.succ_mul, Nat.add_comm] using hbind

theorem callProgram_depth (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) Y) :
    DepthAtMost (callProgram (r := r) hell projectX projectY hprojX hprojY z rho S)
      (blockIterations (alpha ell r) rho * (ProjectedMicro.feasibleMicroIterations + 1)) :=
  blockProgram_depth hell projectX projectY hprojX hprojY z _ S

/-! ## Evaluation against the actual first-stop system -/

theorem eval_macroStepProgram {D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) (S : ValidState (m := m) P.Y) :
    Oracle.Program.eval P
      (macroStepProgram (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S) =
      foamStep ell r ((firstStopSystemWithProx hP hr hrle hprox).oracle z)
        ((firstStopSystemWithProx hP hr hrle hprox).oracle_feasible z) S := by
  apply Subtype.ext
  simp only [macroStepProgram, Oracle.Program.eval_bind, Oracle.Program.eval_pure]
  rw [(program_correct hP hr.le hrle z S.1).1]
  rfl

theorem eval_blockProgram {D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) (k : Nat) (S : ValidState (m := m) P.Y) :
    Oracle.Program.eval P
      (blockProgram (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z k S) =
      ((foamStep ell r ((firstStopSystemWithProx hP hr hrle hprox).oracle z)
        ((firstStopSystemWithProx hP hr hrle hprox).oracle_feasible z))^[k]) S := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
      rw [blockProgram, Oracle.Program.eval_bind, ih, eval_macroStepProgram]
      rw [Function.iterate_succ_apply]

theorem eval_callProgram {D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) P.Y) :
    Oracle.Program.eval P
      (callProgram (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z rho S) =
      ((foamStep ell r ((firstStopSystemWithProx hP hr hrle hprox).oracle z)
        ((firstStopSystemWithProx hP hr hrle hprox).oracle_feasible z))^[
          blockIterations (alpha ell r) rho]) S :=
  eval_blockProgram hP hr hrle hprox z _ S

/-- The exact current family, including its chosen proximal-existence proof,
is the one used by the class-level output theorem. -/
theorem eval_callProgram_eq_family {D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (j : Nat)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) P.Y) :
    Oracle.Program.eval P
      (callProgram (r := Tracking.curvature (ell / 8) j) hP.ell_pos
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z rho S) =
      ((foamStep ell (Tracking.curvature (ell / 8) j)
        ((firstStopSystemFamily hP j).oracle z)
        ((firstStopSystemFamily hP j).oracle_feasible z))^[
          blockIterations (alpha ell (Tracking.curvature (ell / 8) j)) rho]) S :=
  eval_callProgram hP _ _ (MainTheorem.classProxFamily hP j) z rho S

/-- At the current outer contraction factor this is literally `runBlock`. -/
theorem eval_callProgram_eq_runBlock {D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (j : Nat)
    (z : EVec m) (S : ValidState (m := m) P.Y) :
    Oracle.Program.eval P
      (callProgram (r := Tracking.curvature (ell / 8) j) hP.ell_pos
        (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z (1 / 400) S) =
      runBlock (firstStopSystemFamily hP j) z S :=
  eval_callProgram_eq_family hP j z (1 / 400) S

set_option maxHeartbeats 2000000 in
/-- The executed call contracts the real conjugate energy. The local
normal/subgradient/residual premises come from the class-derived
first-stop system, not from an assumed program specification. -/
theorem callProgram_energy_contraction {D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) P.Y)
    (hrho : 0 < rho) (hrho1 : rho < 1) :
    energyAt (firstStopSystemWithProx hP hr hrle hprox) z
      (Oracle.Program.eval P
        (callProgram (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
          (chosenProjectX_spec hP) (chosenProjectY_spec hP) z rho S)) ≤
      rho * energyAt (firstStopSystemWithProx hP hr hrle hprox) z S := by
  let sys := firstStopSystemWithProx hP hr hrle hprox
  let st := sys.stationary z
  have hmin := (PointwiseConjugate.Pzr_unique_minimizer hP.ell_pos hr
    st.subgradient st.stationQ st.stationY).1
  have henergy (V : ValidState (m := m) P.Y) :
      energyAt sys z V =
        energy ell r st.qStar st.yStar.1
          (PzrTotal P.X P.Y (PointwiseConjugate.decurved P.f ell r z) ell r)
          (PointwiseConjugate.Pzr P.X P.Y (PointwiseConjugate.decurved P.f ell r z) ell r
            st.qStar st.yStar) V.1 :=
    snapshotEnergy_eq_foamEnergy sys ⟨z, V, 0⟩
  rw [eval_callProgram]
  change energyAt sys z _ ≤ rho * energyAt sys z S
  rw [henergy, henergy]
  exact block_energy_contraction hP.ell_pos hr hrle st.qStar st.yStar hmin
    (sys.oracle z) (sys.oracle_feasible z) (sys.oracle_subgradient z)
    (sys.oracle_residual z) S hrho hrho1

/-! ## Feasible execution and numerical count -/

/-- A macrostep's actual count is the first successful index plus its
initial query; the state update itself issues no query. -/
theorem macroStepProgram_trace_length {D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : ValidState (m := m) P.Y) :
    (queryTrace P
      (macroStepProgram (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S)).length =
      firstStopIndex hP hr.le hrle z S.1 + 1 := by
  rw [macroStepProgram, queryTrace_bind, List.length_append]
  simpa only [queryTrace, List.length_nil, Nat.add_zero] using
    (program_correct hP hr.le hrle z S.1).2

/-- The semantic first-stop block count is now the actual execution count.
This is equality of counts, not a fixed-cutoff replacement or a claim of
literal trace-list equality. -/
theorem blockProgram_trace_length_eq_macroTrace {D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) (k : Nat) (S : ValidState (m := m) P.Y) :
    (queryTrace P
      (blockProgram (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z k S)).length =
      (CurrentCost.macroTrace hP hr hrle hprox z k S).length := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
      rw [blockProgram, queryTrace_bind, List.length_append,
        macroStepProgram_trace_length hP hr hrle, eval_macroStepProgram hP hr hrle hprox,
        ih, CurrentCost.macroTrace, List.length_append, CurrentCost.microTrace_length]

theorem callProgram_runSteps (P : NCCInstance m n) (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) Y) :
    Oracle.Program.runSteps P
      (callProgram (r := r) hell projectX projectY hprojX hprojY z rho S)
        (blockIterations (alpha ell r) rho * (ProjectedMicro.feasibleMicroIterations + 1)) =
      Oracle.Program.pure (Oracle.Program.eval P
        (callProgram (r := r) hell projectX projectY hprojX hprojY z rho S)) :=
  (callProgram_depth hell projectX projectY hprojX hprojY z rho S).runSteps P

theorem callProgram_all_histories_feasible (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) Y)
    (fallback : Oracle.Query m n) (hfallback : fallback.1 ∈ X ∧ fallback.2 ∈ Y)
    (t : Nat) (history : Oracle.ReplyHistory m n t) :
    let q := Oracle.Program.queryAfterHistory
      (callProgram (r := r) hell projectX projectY hprojX hprojY z rho S)
        fallback t history
    q.1 ∈ X ∧ q.2 ∈ Y :=
  Oracle.Program.queryAfterHistory_mem _ fallback hfallback t history

theorem callProgram_trace_length_le (P : NCCInstance m n) (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) Y) :
    (queryTrace P (callProgram (r := r) hell projectX projectY hprojX hprojY z rho S)).length ≤
      blockIterations (alpha ell r) rho * (ProjectedMicro.feasibleMicroIterations + 1) :=
  (callProgram_depth hell projectX projectY hprojX hprojY z rho S).trace_length P

/-- A bound on genuine execution, obtained from a bound on all branches.
The additive one in the logarithmic factor retains validity for every
`0 < rho < 1`, including factors arbitrarily close to one. -/
theorem callProgram_trace_length_lt_sqrt_ratio (P : NCCInstance m n)
    (hell : 0 < ell) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (rho : ℝ) (S : ValidState (m := m) Y)
    (hrho : 0 < rho) (hrho1 : rho < 1) :
    ((queryTrace P (callProgram (r := r) hell projectX projectY hprojX hprojY z rho S)).length : ℝ) <
      (2 * Real.log (1 / rho) + 1) * (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) *
        Real.sqrt (ell / r) := by
  have hlen :
      ((queryTrace P (callProgram (r := r) hell projectX projectY hprojX hprojY z rho S)).length : ℝ) ≤
      ((BlockCostConcrete.feasibleBlockCost ell r rho).oracleCalls : ℝ) := by
    exact_mod_cast callProgram_trace_length_le P hell projectX projectY hprojX hprojY z rho S
  exact hlen.trans_lt
    (BlockCostConcrete.feasibleBlockCost_lt_sqrt_ratio hell hr hrle hrho hrho1).1

end
end NCC.Upper.AdaptiveFOAMProgram
