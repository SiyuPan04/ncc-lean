import NCC.Upper.AnalyticBridge
import NCCLowerBoundVerification.Upper.SharedOracle

/-!
# Capped, reply-driven first-success micro program

The program definitions receive geometry, numerical parameters, a center,
and a state. They do not receive an objective or a class-membership proof.
Each gradient used to advance or test the loop comes from a feasible local
oracle reply. The universal cap makes even counterfactual reply branches
finite. The evaluation theorem below identifies the genuine-reply output
with the current first-success mathematical oracle.
-/

namespace NCC.Upper.AdaptiveMicroProgram

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open RelativeFOAM RelativeFOAMContraction ScaledOperator ProjectionGeometry
open SharedOracle SystemInstantiation AnalyticBridge

variable {m n : Nat} {ell r : ℝ}
  {X : Set (EVec m)} {Y : Set (EVec n)}

/-- Decode a feasible tuple using just two local replies and known terms. -/
def decoded (z : EVec m) (S : State m n)
    (u v : ScaledFeasible ell X Y)
    (a b : Oracle.OracleReply m n) : FeasibleMicroOutput m Y :=
  ⟨outputFromReplies ell z u.1 v.1 a b
      (replyOperator ell r z (qCenter ell r S) (yCenter ell r S) u.1 a),
    outputFromReplies_y_mem z u v a b _⟩

/-- One more update is mandatory, even at fuel zero. Fuel counts how many
additional failed tests may be followed by another update. -/
def loop (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : State m n) :
    Nat → ScaledFeasible ell X Y → Oracle.OracleReply m n →
      Oracle.Program X Y (FeasibleMicroOutput m Y)
  | 0, u, a =>
      let v := microAdvance (r := r) hell projectX projectY hprojX hprojY
        z (qCenter ell r S) (yCenter ell r S) u a
      .query (scaledQuery v) (scaledQuery_mem v) fun b => .pure (decoded (r := r) z S u v a b)
  | fuel + 1, u, a => by
      classical
      let v := microAdvance (r := r) hell projectX projectY hprojX hprojY
        z (qCenter ell r S) (yCenter ell r S) u a
      exact .query (scaledQuery v) (scaledQuery_mem v) fun b =>
        let O := decoded (r := r) z S u v a b
        if RelativeResidual ell r S O.1 then .pure O
        else loop hell projectX projectY hprojX hprojY z S fuel v b

/-- The initial query is made once and its reply is reused by the loop. -/
def program (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : State m n) :
    Oracle.Program X Y (FeasibleMicroOutput m Y) :=
  let u := microInitial (r := r) hell projectX projectY hprojX hprojY S
  .query (scaledQuery u) (scaledQuery_mem u) fun a =>
    loop (r := r) hell projectX projectY hprojX hprojY z S
      (ProjectedMicro.feasibleMicroIterations - 1) u a

/-- Every branch has at most the indicated number of queries. Unlike the
legacy `ExactDepth`, this permits early-return branches. -/
inductive DepthAtMost : {α : Type} → Oracle.Program X Y α → Nat → Prop where
  | pure {α : Type} (a : α) (k : Nat) : DepthAtMost (.pure a) k
  | query {α : Type} (q : Oracle.Query m n) (hq : q.1 ∈ X ∧ q.2 ∈ Y)
      (next : Oracle.OracleReply m n → Oracle.Program X Y α) (k : Nat)
      (hnext : ∀ reply, DepthAtMost (next reply) k) :
      DepthAtMost (.query q hq next) (k + 1)

theorem loop_depth (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : State m n) (fuel : Nat)
    (u : ScaledFeasible ell X Y) (a : Oracle.OracleReply m n) :
    DepthAtMost (loop (r := r) hell projectX projectY hprojX hprojY z S fuel u a)
      (fuel + 1) := by
  classical
  induction fuel generalizing u a with
  | zero => exact DepthAtMost.query _ _ _ 0 (fun _ => DepthAtMost.pure _ _)
  | succ fuel ih =>
      apply DepthAtMost.query
      intro b
      dsimp only
      split
      · exact DepthAtMost.pure _ _
      · exact ih _ _

theorem program_depth (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : State m n) :
    DepthAtMost (program (r := r) hell projectX projectY hprojX hprojY z S)
      (ProjectedMicro.feasibleMicroIterations + 1) := by
  have hN : ProjectedMicro.feasibleMicroIterations - 1 + 1 =
      ProjectedMicro.feasibleMicroIterations :=
    Nat.sub_add_cancel ProjectedMicro.feasibleMicroIterations_positive
  unfold program
  apply DepthAtMost.query
  intro a
  simpa only [hN] using
    loop_depth (r := r) hell projectX projectY hprojX hprojY z S
      (ProjectedMicro.feasibleMicroIterations - 1) _ a

/-- Actual queries issued when this program is executed against an instance. -/
def queryTrace {α : Type} (P : NCCInstance m n) (p : Oracle.Program X Y α) :
    List (Oracle.Query m n) :=
  Oracle.Program.rec (motive := fun _ => List (Oracle.Query m n))
    (fun _ => []) (fun q _ _ ih => q :: ih (Oracle.firstOrderOracle P q)) p

theorem DepthAtMost.trace_length {α : Type} {p : Oracle.Program X Y α} {k : Nat}
    (hp : DepthAtMost p k) (P : NCCInstance m n) : (queryTrace P p).length ≤ k := by
  induction hp with
  | pure a k => simp [queryTrace]
  | query q hq next k hnext ih =>
      exact Nat.add_le_add_right (ih (Oracle.firstOrderOracle P q)) 1

theorem DepthAtMost.runSteps {α : Type} {p : Oracle.Program X Y α} {k : Nat}
    (hp : DepthAtMost p k) (P : NCCInstance m n) :
    Oracle.Program.runSteps P p k = Oracle.Program.pure (Oracle.Program.eval P p) := by
  induction hp with
  | pure a k => exact Oracle.Program.runSteps_pure P a k
  | query q hq next k hnext ih =>
      rw [← Oracle.Program.runSteps_oracleStep]
      exact ih (Oracle.firstOrderOracle P q)

/-- Feasibility of every actual query, independent of any class condition. -/
theorem queryTrace_feasible {α : Type} (P : NCCInstance m n)
    (p : Oracle.Program X Y α) :
    ∀ q ∈ queryTrace P p, q.1 ∈ X ∧ q.2 ∈ Y := by
  induction p with
  | pure a => simp [queryTrace]
  | query q hq next ih =>
      intro v hv
      rcases List.mem_cons.mp hv with hv | hv
      · simpa [hv] using hq
      · exact ih (Oracle.firstOrderOracle P q) v hv

/-! ## Genuine-reply correspondence at an arbitrary projected iterate -/

theorem advance_at_iterate {D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (z : EVec m) (S : State m n)
    (s : Nat) (u : ScaledFeasible ell P.X P.Y)
    (hu : u.1 = microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S s) :
    (microAdvance (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
      (chosenProjectX_spec hP) (chosenProjectY_spec hP)
      z (qCenter ell r S) (yCenter ell r S) u
      (Oracle.firstOrderOracle P (scaledQuery u))).1 =
      microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S (s + 1) := by
  rw [microAdvance_firstOrderOracle, hu]
  rfl

theorem decoded_at_iterate {D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (z : EVec m) (S : State m n)
    (s : Nat) (u v : ScaledFeasible ell P.X P.Y)
    (hu : u.1 = microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S s)
    (hv : v.1 = microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S (s + 1)) :
    (decoded (r := r) z S u v
      (Oracle.firstOrderOracle P (scaledQuery u))
      (Oracle.firstOrderOracle P (scaledQuery v))).1 =
      microOutputAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S (s + 1) := by
  have hop := replyOperator_firstOrderOracle P ell r z
    (qCenter ell r S) (yCenter ell r S) u.1
  unfold decoded outputFromReplies microOutputAt decodeOutput
  dsimp only
  simp only [scaledQuery]
  rw [hop, hu, hv]
  congr 1 <;>
    simp [ClassOperator.gradXHat, ClassOperator.gradYHat, microUAt, microBAt,
      projectedB, M0]

/-- Starting after the reply at iterate `s`, with enough remaining fuel,
the genuine-reply loop reaches exactly the first successful index. -/
theorem eval_loop_before_stop {D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) (fuel s : Nat)
    (u : ScaledFeasible ell P.X P.Y)
    (hu : u.1 = microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S s)
    (hbefore : s < firstStopIndex hP hr hrle z S)
    (hcap : firstStopIndex hP hr hrle z S ≤ s + fuel + 1) :
    (Oracle.Program.eval P
      (loop (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S fuel u
        (Oracle.firstOrderOracle P (scaledQuery u)))).1 =
        firstStopOracle hP hr hrle z S ∧
      (queryTrace P
        (loop (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
          (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S fuel u
          (Oracle.firstOrderOracle P (scaledQuery u)))).length =
        firstStopIndex hP hr hrle z S - s := by
  classical
  induction fuel generalizing s u with
  | zero =>
      let a := Oracle.firstOrderOracle P (scaledQuery u)
      let v := microAdvance (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP)
        z (qCenter ell r S) (yCenter ell r S) u a
      have hv : v.1 = microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S
          (s + 1) := advance_at_iterate hP z S s u hu
      have hO := decoded_at_iterate hP z S s u v hu hv
      have hindex : firstStopIndex hP hr hrle z S = s + 1 := by omega
      constructor
      · change (decoded (r := r) z S u v a
          (Oracle.firstOrderOracle P (scaledQuery v))).1 = _
        rw [hO, ← hindex]
        rfl
      · change 1 = firstStopIndex hP hr hrle z S - s
        omega
  | succ fuel ih =>
      let a := Oracle.firstOrderOracle P (scaledQuery u)
      let v := microAdvance (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP)
        z (qCenter ell r S) (yCenter ell r S) u a
      let b := Oracle.firstOrderOracle P (scaledQuery v)
      let O := decoded (r := r) z S u v a b
      have hv : v.1 = microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S
          (s + 1) := advance_at_iterate hP z S s u hu
      have hO : O.1 = microOutputAt P ell r (chosenProjectX hP) (chosenProjectY hP)
          z S (s + 1) := decoded_at_iterate hP z S s u v hu hv
      change (Oracle.Program.eval P
          (if RelativeResidual ell r S O.1 then Oracle.Program.pure O
            else loop (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
              (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S fuel v b)).1 = _ ∧
        (queryTrace P
          (if RelativeResidual ell r S O.1 then Oracle.Program.pure O
            else loop (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
              (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S fuel v b)).length + 1 = _
      by_cases hindex : firstStopIndex hP hr hrle z S = s + 1
      · have htest : RelativeResidual ell r S O.1 := by
          rw [hO, ← hindex]
          exact (firstStopIndex_spec hP hr hrle z S).2
        rw [if_pos htest]
        constructor
        · rw [Oracle.Program.eval_pure, hO, ← hindex]
          rfl
        · change 0 + 1 = firstStopIndex hP hr hrle z S - s
          omega
      · have hbefore' : s + 1 < firstStopIndex hP hr hrle z S := by omega
        have htest : ¬ RelativeResidual ell r S O.1 := by
          intro h
          apply firstStopIndex_minimal hP hr hrle z S (s + 1) hbefore'
          refine ⟨by omega, ?_⟩
          rwa [← hO]
        rw [if_neg htest]
        have hrec := ih (s + 1) v hv hbefore' (by omega)
        constructor
        · exact hrec.1
        · rw [hrec.2]
          omega

/-- Value and exact genuine query count for the adaptive micro client.
No instance is supplied to `program`; `P` occurs only in the evaluator. -/
theorem program_correct {D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) :
    (Oracle.Program.eval P
      (program (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S)).1 =
        firstStopOracle hP hr hrle z S ∧
      (queryTrace P
        (program (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
          (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S)).length =
        firstStopIndex hP hr hrle z S + 1 := by
  let u := microInitial (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
    (chosenProjectX_spec hP) (chosenProjectY_spec hP) S
  have hpos := (firstStopIndex_spec hP hr hrle z S).1
  have hbound := firstStopIndex_le_universal hP hr hrle z S
  have hN := ProjectedMicro.feasibleMicroIterations_positive
  have hloop := eval_loop_before_stop hP hr hrle z S
    (ProjectedMicro.feasibleMicroIterations - 1) 0 u rfl (by omega) (by omega)
  constructor
  · exact hloop.1
  · change (queryTrace P
      (loop (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S
        (ProjectedMicro.feasibleMicroIterations - 1) u
        (Oracle.firstOrderOracle P (scaledQuery u)))).length + 1 = _
    rw [hloop.2]
    simp

/-- Uniform query bound for any instance and every reply branch, requiring
only the supplied geometry rather than an analytic class premise. -/
theorem program_trace_bound (P : NCCInstance m n) (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : State m n) :
    (queryTrace P (program (r := r) hell projectX projectY hprojX hprojY z S)).length ≤
      ProjectedMicro.feasibleMicroIterations + 1 :=
  (program_depth hell projectX projectY hprojX hprojY z S).trace_length P

/-- Every next query remains feasible after an arbitrary supplied reply history. -/
theorem program_all_histories_feasible (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : State m n) (fallback : Oracle.Query m n)
    (hfallback : fallback.1 ∈ X ∧ fallback.2 ∈ Y)
    (t : Nat) (history : Oracle.ReplyHistory m n t) :
    let q := Oracle.Program.queryAfterHistory
      (program (r := r) hell projectX projectY hprojX hprojY z S) fallback t history
    q.1 ∈ X ∧ q.2 ∈ Y :=
  Oracle.Program.queryAfterHistory_mem _ fallback hfallback t history

end
end NCC.Upper.AdaptiveMicroProgram
