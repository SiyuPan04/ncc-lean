import NCCLowerBoundVerification.Oracle.Model

/-!
# Finite causal oracle programs

This module supplies the operational bridge needed by the shared-oracle
upper bound.  A `Program X Y α` may inspect an objective only by issuing a
feasible query and receiving its local first-order reply.  Its continuation
is therefore a function of that reply, not of an `NCCInstance`.

The compiler below turns such a program into the paper's infinite
`DeterministicFOComponent`: after a finite program terminates, the component
repeats one fixed feasible query forever.  Thus no semantic oracle access is
hidden in the compiled query rule.
-/

namespace NCCLowerBoundVerification
namespace Oracle

noncomputable section

universe u

/-- A finite, reply-driven computation using only feasible local first-order
queries. -/
inductive Program {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (α : Type u) where
  | pure (result : α)
  | query (point : Query m n) (point_mem : point.1 ∈ X ∧ point.2 ∈ Y)
      (next : OracleReply m n → Program X Y α)

namespace Program

variable {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
variable {α β : Type u}

/-- Monadic sequencing does not add any channel for inspecting the objective:
the second computation receives only the first computation's returned value. -/
def bind (p : Program X Y α) (k : α → Program X Y β) : Program X Y β :=
  Program.rec (motive := fun _ => Program X Y β)
    (fun a => k a)
    (fun q hq _next ih => .query q hq ih) p

instance : Monad (Program X Y) where
  pure := Program.pure
  bind := bind

/-- One feasible local first-order query. -/
def ask (q : Query m n) (hq : q.1 ∈ X ∧ q.2 ∈ Y) :
    Program X Y (OracleReply m n) :=
  .query q hq .pure

/-- Map a deterministic function over a finite oracle computation. -/
def map (f : α → β) (p : Program X Y α) : Program X Y β :=
  p >>= fun a => pure (f a)

/-- Execute a program against one instance.  The only observation of `P` is
the reply produced at the query stored in the current constructor. -/
def eval (P : NCCInstance m n) (p : Program X Y α) : α :=
  Program.rec (motive := fun _ => α)
    (fun a => a)
    (fun q _hq _next ih => ih (firstOrderOracle P q)) p

@[simp] theorem eval_pure (P : NCCInstance m n) (a : α) :
    eval P (pure a : Program X Y α) = a := rfl

@[simp] theorem eval_query (P : NCCInstance m n) (q : Query m n)
    (hq : q.1 ∈ X ∧ q.2 ∈ Y)
    (next : OracleReply m n → Program X Y α) :
    eval P (.query q hq next) = eval P (next (firstOrderOracle P q)) := rfl

@[simp] theorem eval_ask (P : NCCInstance m n) (q : Query m n)
    (hq : q.1 ∈ X ∧ q.2 ∈ Y) :
    eval P (ask q hq) = firstOrderOracle P q := rfl

theorem eval_bind (P : NCCInstance m n) (p : Program X Y α)
    (k : α → Program X Y β) :
    eval P (p >>= k) = eval P (k (eval P p)) := by
  induction p with
  | pure a => rfl
  | query q hq next ih =>
      simp only [bind, eval]
      exact ih (firstOrderOracle P q)

/-- Consume a supplied history.  If the program has already terminated,
extra replies are ignored; these correspond to the compiler's repeated
fallback queries. -/
def afterHistory (p : Program X Y α) :
    (t : Nat) → ReplyHistory m n t → Program X Y α
  | 0, _ => p
  | _ + 1, history =>
      match p with
      | .pure a => .pure a
      | .query _ _ next =>
          afterHistory (next (history 0)) _ (fun i => history i.succ)
termination_by t => t

/-- The query exposed after consuming a history, or a fixed feasible fallback
once the finite program has returned. -/
def queryAfterHistory (p : Program X Y α) (fallback : Query m n)
    (t : Nat) (history : ReplyHistory m n t) : Query m n :=
  match afterHistory p t history with
  | .pure _ => fallback
  | .query q _ _ => q

theorem queryAfterHistory_mem (p : Program X Y α) (fallback : Query m n)
    (hfallback : fallback.1 ∈ X ∧ fallback.2 ∈ Y)
    (t : Nat) (history : ReplyHistory m n t) :
    (queryAfterHistory p fallback t history).1 ∈ X ∧
      (queryAfterHistory p fallback t history).2 ∈ Y := by
  unfold queryAfterHistory
  cases h : afterHistory p t history with
  | pure a => exact hfallback
  | query q hq next => exact hq

/-- Compile a finite oracle program to a domain-wise causal component.  The
initial-query premise is semantic-free: it states that the program's first
constructor contains the full origin query. -/
def compile (p : Program X Y α) (fallback : Query m n)
    (hfallback : fallback.1 ∈ X ∧ fallback.2 ∈ Y)
    (hfirst : queryAfterHistory p fallback 0 (emptyHistory m n) = (0, 0)) :
    DeterministicFOComponent X Y where
  nextQuery := queryAfterHistory p fallback
  next_mem := queryAfterHistory_mem p fallback hfallback
  initial_query := hfirst

/-! ## Operational semantics of the compiler -/

/-- Consume one genuine reply, leaving a returned program unchanged. -/
def oracleStep (P : NCCInstance m n) (p : Program X Y α) : Program X Y α :=
  match p with
  | .pure a => .pure a
  | .query q _ next => next (firstOrderOracle P q)

/-- State of a program after `t` genuine replies (or after ignoring repeated
fallback replies once it has terminated). -/
def runSteps (P : NCCInstance m n) (p : Program X Y α) : Nat → Program X Y α
  | 0 => p
  | t + 1 => oracleStep P (runSteps P p t)

/-- Current stored query of a residual program, with a fallback after return. -/
def currentQuery (p : Program X Y α) (fallback : Query m n) : Query m n :=
  match p with
  | .pure _ => fallback
  | .query q _ _ => q

/-- The objective-driven semantic query at absolute time `t`. -/
def semanticQueryAt (P : NCCInstance m n) (p : Program X Y α)
    (fallback : Query m n) (t : Nat) : Query m n :=
  currentQuery (runSteps P p t) fallback

/-- Replies belonging to the semantic query sequence before time `t`. -/
def semanticTranscript (P : NCCInstance m n) (p : Program X Y α)
    (fallback : Query m n) (t : Nat) : ReplyHistory m n t :=
  fun i => firstOrderOracle P (semanticQueryAt P p fallback i)

@[simp] theorem runSteps_zero (P : NCCInstance m n) (p : Program X Y α) :
    runSteps P p 0 = p := rfl

@[simp] theorem runSteps_succ (P : NCCInstance m n) (p : Program X Y α)
    (t : Nat) :
    runSteps P p (t + 1) = oracleStep P (runSteps P p t) := rfl

@[simp] theorem runSteps_pure (P : NCCInstance m n) (a : α) (t : Nat) :
    runSteps P (.pure a : Program X Y α) t = .pure a := by
  induction t with
  | zero => rfl
  | succ t ih => simp [runSteps, oracleStep, ih]

theorem runSteps_oracleStep (P : NCCInstance m n) (p : Program X Y α)
    (t : Nat) :
    runSteps P (oracleStep P p) t = runSteps P p (t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [runSteps_succ, runSteps_succ, ih]

@[simp] theorem semanticQueryAt_zero (P : NCCInstance m n)
    (p : Program X Y α) (fallback : Query m n) :
    semanticQueryAt P p fallback 0 = currentQuery p fallback := rfl

theorem semanticQueryAt_oracleStep (P : NCCInstance m n)
    (p : Program X Y α) (fallback : Query m n) (t : Nat) :
    semanticQueryAt P (oracleStep P p) fallback t =
      semanticQueryAt P p fallback (t + 1) := by
  unfold semanticQueryAt
  rw [runSteps_oracleStep]

theorem semanticTranscript_tail (P : NCCInstance m n)
    (p : Program X Y α) (fallback : Query m n) (t : Nat) :
    (fun i : Fin t => semanticTranscript P p fallback (t + 1) i.succ) =
      semanticTranscript P (oracleStep P p) fallback t := by
  funext i
  unfold semanticTranscript
  rw [semanticQueryAt_oracleStep]
  congr 2

/-- Replaying the genuine semantic transcript reconstructs exactly the
residual program obtained by direct execution. -/
theorem afterHistory_semanticTranscript (P : NCCInstance m n)
    (p : Program X Y α) (fallback : Query m n) (t : Nat) :
    afterHistory p t (semanticTranscript P p fallback t) =
      runSteps P p t := by
  induction t generalizing p with
  | zero => cases p <;> simp [afterHistory]
  | succ t ih =>
      cases p with
      | pure a =>
          simp [afterHistory, oracleStep]
      | query q hq next =>
          have hhead : semanticTranscript P (.query q hq next) fallback
              (t + 1) 0 = firstOrderOracle P q := by
            rfl
          rw [afterHistory]
          rw [hhead]
          have htail := semanticTranscript_tail P (.query q hq next) fallback t
          change afterHistory (next (firstOrderOracle P q)) t
              (fun i => semanticTranscript P (.query q hq next) fallback
                (t + 1) i.succ) = _
          rw [htail]
          calc
            afterHistory (next (firstOrderOracle P q)) t
                (semanticTranscript P (oracleStep P (.query q hq next))
                  fallback t) =
              runSteps P (next (firstOrderOracle P q)) t := by
                simpa [oracleStep] using ih (next (firstOrderOracle P q))
            _ = runSteps P (.query q hq next) (t + 1) := by
              simpa [oracleStep] using
                runSteps_oracleStep P (.query q hq next) t

/-- The compiler exposes the same time-`t` query as direct program
execution when fed the semantic transcript. -/
theorem queryAfterHistory_semanticTranscript (P : NCCInstance m n)
    (p : Program X Y α) (fallback : Query m n) (t : Nat) :
    queryAfterHistory p fallback t (semanticTranscript P p fallback t) =
      semanticQueryAt P p fallback t := by
  unfold queryAfterHistory semanticQueryAt
  rw [afterHistory_semanticTranscript]
  cases runSteps P p t <;> rfl

/-- Direct execution and execution after any finite number of steps return
the same result. -/
theorem eval_oracleStep (P : NCCInstance m n) (p : Program X Y α) :
    eval P (oracleStep P p) = eval P p := by
  cases p <;> rfl

theorem eval_runSteps (P : NCCInstance m n) (p : Program X Y α) (t : Nat) :
    eval P (runSteps P p t) = eval P p := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [runSteps_succ, eval_oracleStep, ih]

/-- On every instance, the recursively generated transcript of the compiled
domain component is exactly the direct semantics of the finite program. -/
theorem queriedAt_compile_eq_semanticQueryAt
    (P : NCCInstance m n) (p : Program X Y α) (fallback : Query m n)
    (hfallback : fallback.1 ∈ X ∧ fallback.2 ∈ Y)
    (hfirst : queryAfterHistory p fallback 0 (emptyHistory m n) = (0, 0))
    (t : Nat) :
    DeterministicFOComponent.queriedAt
        (compile p fallback hfallback hfirst) P t =
      semanticQueryAt P p fallback t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
      rw [DeterministicFOComponent.queriedAt_eq_nextQuery]
      change queryAfterHistory p fallback t
        (DeterministicFOComponent.queriedTranscript
          (compile p fallback hfallback hfirst) P t) = _
      have htranscript :
          DeterministicFOComponent.queriedTranscript
              (compile p fallback hfallback hfirst) P t =
            semanticTranscript P p fallback t := by
        funext i
        unfold DeterministicFOComponent.queriedTranscript
          DeterministicFOComponent.replyAt semanticTranscript
        congr 1
        exact ih i i.isLt
      rw [htranscript]
      exact queryAfterHistory_semanticTranscript P p fallback t

/-- A useful endpoint form: if the residual program at time `t` begins with
query `q`, the compiled component really issues `q` at that time. -/
theorem queriedAt_compile_eq_of_runSteps_query
    (P : NCCInstance m n) (p : Program X Y α) (fallback q : Query m n)
    (hfallback : fallback.1 ∈ X ∧ fallback.2 ∈ Y)
    (hfirst : queryAfterHistory p fallback 0 (emptyHistory m n) = (0, 0))
    (t : Nat) (hq : ∃ hmem next, runSteps P p t = .query q hmem next) :
    DeterministicFOComponent.queriedAt
        (compile p fallback hfallback hfirst) P t = q := by
  rw [queriedAt_compile_eq_semanticQueryAt]
  rcases hq with ⟨hmem, next, hq⟩
  unfold semanticQueryAt
  rw [hq]
  rfl

@[simp] theorem afterHistory_zero (p : Program X Y α)
    (history : ReplyHistory m n 0) : afterHistory p 0 history = p := by
  simp [afterHistory]

@[simp] theorem queryAfterHistory_zero (p : Program X Y α)
    (fallback : Query m n) :
    queryAfterHistory p fallback 0 (emptyHistory m n) =
      match p with
      | .pure _ => fallback
      | .query q _ _ => q := by
  cases p <;> simp [queryAfterHistory, afterHistory]

end Program

end

end Oracle
end NCCLowerBoundVerification
