import NCCLowerBoundVerification.Oracle.Program
import NCCLowerBoundVerification.Oracle.Complexity
import NCCLowerBoundVerification.Upper.DeterministicOutput

/-!
# Flattening the upper method into the shared local oracle

`SystemInstantiation.classOracle` is a finite projected recurrence.  This
module exposes every evaluation in that recurrence as an `Oracle.Program.ask`
constructor.  Consequently the eventual full schedule can be compiled to a
single domain-wise causal component without giving its query rule an
`NCCInstance` or a class-membership proof.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace SharedOracle

noncomputable section

open Oracle
open RelativeFOAM ProjectionGeometry ScaledOperator ProjectedMicro
open SystemInstantiation ClassOperator

abbrev ScaledFeasible {m n : Nat} (ell : ℝ)
    (X : Set (EVec m)) (Y : Set (EVec n)) :=
  {u : Pair m n // u ∈ scaledSet ell X Y}

/-- Decode a feasible packed point into the actual local-oracle query. -/
def scaledQuery {m n : Nat} {ell : ℝ} {X : Set (EVec m)}
    {Y : Set (EVec n)} (u : ScaledFeasible ell X Y) : Oracle.Query m n :=
  (unscaleX ell u.1, unscaleY ell u.1)

theorem scaledQuery_mem {m n : Nat} {ell : ℝ} {X : Set (EVec m)}
    {Y : Set (EVec n)} (u : ScaledFeasible ell X Y) :
    (scaledQuery u).1 ∈ X ∧ (scaledQuery u).2 ∈ Y :=
  u.2

/-- The scaled saddle operator reconstructed from one oracle reply and the
known affine terms of the proximal subproblem. -/
def replyOperator {m n : Nat} (ell r : ℝ) (z qg : EVec m)
    (yg : EVec n) (u : Pair m n) (reply : Oracle.OracleReply m n) :
    Pair m n :=
  let x := unscaleX ell u
  let y := unscaleY ell u
  pack
    (scaleRoot ell •
      ((reply.gradX + ell • x - (2 * ell) • z) +
        (ell / 2) • (x - ell⁻¹ • qg)))
    (scaleRoot ell •
      (-reply.gradY + r • y + (gamma ell)⁻¹ • (y - yg)))

theorem replyOperator_firstOrderOracle {m n : Nat}
    (P : NCCInstance m n) (ell r : ℝ) (z qg : EVec m) (yg : EVec n)
    (u : Pair m n) :
    replyOperator ell r z qg yg u
        (Oracle.firstOrderOracle P (unscaleX ell u, unscaleY ell u)) =
      scaledOperator ell r qg yg
        (gradXHat P ell z) (gradYHat P ell z) u := by
  rfl

/-- One reply-driven projected update.  Projection feasibility is the only
property needed to construct the next query. -/
def microAdvance {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z qg : EVec m) (yg : EVec n)
    (u : ScaledFeasible ell X Y) (reply : Oracle.OracleReply m n) :
    ScaledFeasible ell X Y :=
  let next := scaledProject ell projectX projectY
    (u.1 - (M0 ^ 2)⁻¹ • replyOperator ell r z qg yg u.1 reply)
  ⟨next, by
    change unscaleX ell next ∈ X ∧ unscaleY ell next ∈ Y
    rw [unscaleX_scaledProject hell, unscaleY_scaledProject hell]
    exact ⟨hprojX.mem _, hprojY.mem _⟩⟩

/-- `k` consecutive projected updates, each represented by one genuine local
oracle query. -/
def microIterateProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z qg : EVec m) (yg : EVec n) :
    Nat → ScaledFeasible ell X Y →
      Oracle.Program X Y (ScaledFeasible ell X Y)
  | 0, u => pure u
  | k + 1, u => do
      let reply ← Oracle.Program.ask (scaledQuery u) (scaledQuery_mem u)
      microIterateProgram (r := r) hell projectX projectY hprojX hprojY
        z qg yg k
        (microAdvance (r := r) hell projectX projectY hprojX hprojY
          z qg yg u reply)

/-- The first projected point of the micro recurrence. -/
def microInitial {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (S : State m n) : ScaledFeasible ell X Y :=
  let u := scaledProject ell projectX projectY
    (scaledCenter ell (qCenter ell r S) (yCenter ell r S))
  ⟨u, by
    change unscaleX ell u ∈ X ∧ unscaleY ell u ∈ Y
    rw [unscaleX_scaledProject hell, unscaleY_scaledProject hell]
    exact ⟨hprojX.mem _, hprojY.mem _⟩⟩

/-- Decode the last projected point and its projection normal using the final
oracle reply. -/
def outputFromReplies {m n : Nat} (ell : ℝ) (z : EVec m)
    (uPrev uFinal : Pair m n) (replyPrev replyFinal : Oracle.OracleReply m n)
    (operatorPrev : Pair m n) : MicroOutput m n :=
  let b := (M0 ^ 2) •
    (uPrev - (M0 ^ 2)⁻¹ • operatorPrev - uFinal)
  let x := unscaleX ell uFinal
  let y := unscaleY ell uFinal
  { xFast := x
    yFastNext := y
    qFastNext := replyFinal.gradX + ell • x - (2 * ell) • z +
      unscaledNormalX ell b
    wFastNext := -replyFinal.gradY + unscaledNormalY ell b }

/-- The exact `N+1`-query program implementing one
`SystemInstantiation.classOracle` call. -/
def classMicroProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : State m n) : Oracle.Program X Y (MicroOutput m n) := do
  let qg := qCenter ell r S
  let yg := yCenter ell r S
  let u0 := microInitial (r := r) hell projectX projectY hprojX hprojY S
  let uPrev ← microIterateProgram (r := r) hell projectX projectY hprojX hprojY
    z qg yg (feasibleMicroIterations - 1) u0
  let replyPrev ← Oracle.Program.ask (scaledQuery uPrev) (scaledQuery_mem uPrev)
  let opPrev := replyOperator ell r z qg yg uPrev.1 replyPrev
  let uFinal := microAdvance (r := r) hell projectX projectY hprojX hprojY
    z qg yg uPrev replyPrev
  let replyFinal ← Oracle.Program.ask (scaledQuery uFinal) (scaledQuery_mem uFinal)
  pure (outputFromReplies ell z uPrev.1 uFinal.1 replyPrev replyFinal opPrev)

/-! ## Exact semantics of one micro solve -/

/-- Direct execution of one reply-driven update is the projected update used
by `classOracle`. -/
theorem microAdvance_firstOrderOracle {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (P : NCCInstance m n) (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z qg : EVec m) (yg : EVec n) (u : ScaledFeasible ell X Y) :
    (microAdvance (r := r) hell projectX projectY hprojX hprojY
        z qg yg u (Oracle.firstOrderOracle P (scaledQuery u))).1 =
      scaledProject ell projectX projectY
        (u.1 - (M0 ^ 2)⁻¹ •
          scaledOperator ell r qg yg
            (gradXHat P ell z) (gradYHat P ell z) u.1) := by
  unfold microAdvance
  dsimp only
  change scaledProject ell projectX projectY
      (u.1 - (M0 ^ 2)⁻¹ •
        replyOperator ell r z qg yg u.1
          (Oracle.firstOrderOracle P
            (unscaleX ell u.1, unscaleY ell u.1))) = _
  rw [replyOperator_firstOrderOracle]

/-- Pure recurrence obtained by interpreting all asks against one instance. -/
def semanticMicroIterate {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (P : NCCInstance m n) (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z qg : EVec m) (yg : EVec n) :
    Nat → ScaledFeasible ell X Y → ScaledFeasible ell X Y
  | 0, u => u
  | k + 1, u =>
      semanticMicroIterate (r := r) P hell projectX projectY hprojX hprojY z qg yg k
        (microAdvance (r := r) hell projectX projectY hprojX hprojY
          z qg yg u (Oracle.firstOrderOracle P (scaledQuery u)))

theorem eval_microIterateProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (P : NCCInstance m n) (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z qg : EVec m) (yg : EVec n) (k : Nat)
    (u : ScaledFeasible ell X Y) :
    Oracle.Program.eval P
        (microIterateProgram (r := r) hell projectX projectY hprojX hprojY
          z qg yg k u) =
      semanticMicroIterate (r := r) P hell projectX projectY hprojX hprojY
        z qg yg k u := by
  induction k generalizing u with
  | zero =>
      change Oracle.Program.eval P
        (pure u : Oracle.Program X Y (ScaledFeasible ell X Y)) = u
      exact Oracle.Program.eval_pure P u
  | succ k ih =>
      simp only [microIterateProgram, Oracle.Program.eval_bind,
        Oracle.Program.eval_ask, semanticMicroIterate]
      exact ih _

/-- If the supplied point is projected iterate `s`, then `k` interpreted
updates produce projected iterate `s+k`. -/
theorem semanticMicroIterate_eq_projectedIterate {m n : Nat}
    {ell r : ℝ} {X : Set (EVec m)} {Y : Set (EVec n)}
    (P : NCCInstance m n) (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z qg : EVec m) (yg : EVec n) (uMinusOne : Pair m n)
    (s k : Nat) (u : ScaledFeasible ell X Y)
    (hu : u.1 = projectedIterate (scaledProject ell projectX projectY)
      (scaledOperator ell r qg yg (gradXHat P ell z) (gradYHat P ell z))
      (M0 ^ 2)⁻¹ uMinusOne s) :
    (semanticMicroIterate (r := r) P hell projectX projectY hprojX hprojY
        z qg yg k u).1 =
      projectedIterate (scaledProject ell projectX projectY)
        (scaledOperator ell r qg yg (gradXHat P ell z) (gradYHat P ell z))
        (M0 ^ 2)⁻¹ uMinusOne (s + k) := by
  induction k generalizing s u with
  | zero => simpa [semanticMicroIterate] using hu
  | succ k ih =>
      rw [semanticMicroIterate]
      have hnext :
          (microAdvance (r := r) hell projectX projectY hprojX hprojY
            z qg yg u (Oracle.firstOrderOracle P (scaledQuery u))).1 =
            projectedIterate (scaledProject ell projectX projectY)
              (scaledOperator ell r qg yg
                (gradXHat P ell z) (gradYHat P ell z))
              (M0 ^ 2)⁻¹ uMinusOne (s + 1) := by
        rw [microAdvance_firstOrderOracle]
        rw [hu]
        rfl
      have hrec := ih (s + 1)
        (microAdvance (r := r) hell projectX projectY hprojX hprojY
          z qg yg u (Oracle.firstOrderOracle P (scaledQuery u))) hnext
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrec

/-- The reply-driven micro program is extensionally identical to the
projected recurrence packaged by `SystemInstantiation.classOracle`. -/
theorem eval_classMicroProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (P : NCCInstance m n) (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : State m n) :
    Oracle.Program.eval P
        (classMicroProgram (r := r) hell projectX projectY hprojX hprojY z S) =
      classOracle P ell r projectX projectY z S := by
  let qg := qCenter ell r S
  let yg := yCenter ell r S
  let uMinusOne := scaledCenter ell qg yg
  let u0 := microInitial (r := r) hell projectX projectY hprojX hprojY S
  let uPrev := semanticMicroIterate (r := r) P hell projectX projectY
    hprojX hprojY z qg yg (feasibleMicroIterations - 1) u0
  let A := scaledOperator ell r qg yg
    (gradXHat P ell z) (gradYHat P ell z)
  have hu0 : u0.1 = projectedIterate
      (scaledProject ell projectX projectY) A (M0 ^ 2)⁻¹ uMinusOne 0 := by
    rfl
  have hprev : uPrev.1 = projectedIterate
      (scaledProject ell projectX projectY) A (M0 ^ 2)⁻¹ uMinusOne
        (feasibleMicroIterations - 1) := by
    dsimp only [uPrev]
    simpa [A, uMinusOne] using
      (semanticMicroIterate_eq_projectedIterate
        (P := P) (r := r) hell projectX projectY hprojX hprojY
        z qg yg uMinusOne 0 (feasibleMicroIterations - 1) u0 hu0)
  have hN : feasibleMicroIterations - 1 + 1 = feasibleMicroIterations := by
    have hpos := feasibleMicroIterations_positive
    omega
  have hfinal :
      (microAdvance (r := r) hell projectX projectY hprojX hprojY z qg yg
        uPrev (Oracle.firstOrderOracle P (scaledQuery uPrev))).1 =
        projectedIterate (scaledProject ell projectX projectY) A
          (M0 ^ 2)⁻¹ uMinusOne feasibleMicroIterations := by
    rw [microAdvance_firstOrderOracle]
    rw [hprev]
    change projectedIterate (scaledProject ell projectX projectY) A
      (M0 ^ 2)⁻¹ uMinusOne ((feasibleMicroIterations - 1) + 1) = _
    rw [hN]
  have hop : replyOperator ell r z qg yg uPrev.1
      (Oracle.firstOrderOracle P (scaledQuery uPrev)) = A uPrev.1 := by
    change replyOperator ell r z qg yg uPrev.1
      (Oracle.firstOrderOracle P
        (unscaleX ell uPrev.1, unscaleY ell uPrev.1)) = _
    simpa [A] using replyOperator_firstOrderOracle P ell r z qg yg uPrev.1
  have hqueryFinal : scaledQuery
      (microAdvance (r := r) hell projectX projectY hprojX hprojY
        z qg yg uPrev (Oracle.firstOrderOracle P (scaledQuery uPrev))) =
      (unscaleX ell (projectedIterate (scaledProject ell projectX projectY) A
          (M0 ^ 2)⁻¹ uMinusOne feasibleMicroIterations),
       unscaleY ell (projectedIterate (scaledProject ell projectX projectY) A
          (M0 ^ 2)⁻¹ uMinusOne feasibleMicroIterations)) := by
    change (unscaleX ell
        (microAdvance (r := r) hell projectX projectY hprojX hprojY
          z qg yg uPrev (Oracle.firstOrderOracle P (scaledQuery uPrev))).1,
      unscaleY ell
        (microAdvance (r := r) hell projectX projectY hprojX hprojY
          z qg yg uPrev (Oracle.firstOrderOracle P (scaledQuery uPrev))).1) = _
    exact congrArg (fun v : Pair m n =>
      (unscaleX ell v, unscaleY ell v)) hfinal
  rw [show Oracle.Program.eval P
      (classMicroProgram (r := r) hell projectX projectY hprojX hprojY z S) =
      let replyPrev := Oracle.firstOrderOracle P (scaledQuery uPrev)
      let operatorPrev := replyOperator ell r z qg yg uPrev.1 replyPrev
      let uFinal := microAdvance (r := r) hell projectX projectY hprojX hprojY
        z qg yg uPrev replyPrev
      let replyFinal := Oracle.firstOrderOracle P (scaledQuery uFinal)
      outputFromReplies ell z uPrev.1 uFinal.1 replyPrev replyFinal
        operatorPrev by
        simp only [classMicroProgram, Oracle.Program.eval_bind,
          Oracle.Program.eval_ask]
        rw [eval_microIterateProgram]
        rfl]
  dsimp only
  unfold classOracle classMicroU classMicroB
  unfold outputFromReplies decodeOutput
  dsimp only
  rw [hqueryFinal, hop, hfinal, hprev]
  congr 1 <;>
    simp [A, qg, yg, uMinusOne, scaledQuery,
      gradXHat, gradYHat, projectedB, M0, hN]

/-! ## Feasible and fixed-depth program combinators -/

/-- A micro output together with the feasibility needed by the next FOAM
state.  Keeping this proof in the return type makes counterfactual reply
branches feasible as required by `DeterministicFOComponent.next_mem`. -/
abbrev FeasibleMicroOutput (m : Nat) {n : Nat} (Y : Set (EVec n)) :=
  {O : MicroOutput m n // O.yFastNext ∈ Y}

/-- Feasibility of the decoded dual point follows from the scaled product
projection, independently of what values or gradients the oracle returned. -/
theorem outputFromReplies_y_mem {m n : Nat} {ell : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)} (z : EVec m)
    (uPrev uFinal : ScaledFeasible ell X Y)
    (replyPrev replyFinal : Oracle.OracleReply m n) (operatorPrev : Pair m n) :
    (outputFromReplies ell z uPrev.1 uFinal.1 replyPrev replyFinal
      operatorPrev).yFastNext ∈ Y := by
  exact uFinal.2.2

/-- Feasibility-strengthened version of `classMicroProgram`, with exactly the
same queries and numerical output. -/
def feasibleClassMicroProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : State m n) :
    Oracle.Program X Y (FeasibleMicroOutput m Y) := do
  let qg := qCenter ell r S
  let yg := yCenter ell r S
  let u0 := microInitial (r := r) hell projectX projectY hprojX hprojY S
  let uPrev ← microIterateProgram (r := r) hell projectX projectY hprojX hprojY
    z qg yg (feasibleMicroIterations - 1) u0
  let replyPrev ← Oracle.Program.ask (scaledQuery uPrev) (scaledQuery_mem uPrev)
  let opPrev := replyOperator ell r z qg yg uPrev.1 replyPrev
  let uFinal := microAdvance (r := r) hell projectX projectY hprojX hprojY
    z qg yg uPrev replyPrev
  let replyFinal ← Oracle.Program.ask (scaledQuery uFinal) (scaledQuery_mem uFinal)
  Oracle.Program.pure
    ⟨outputFromReplies ell z uPrev.1 uFinal.1 replyPrev replyFinal opPrev,
    outputFromReplies_y_mem z uPrev uFinal replyPrev replyFinal opPrev⟩

theorem eval_feasibleClassMicroProgram_val {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (P : NCCInstance m n) (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : State m n) :
    (Oracle.Program.eval P
      (feasibleClassMicroProgram (r := r) hell projectX projectY
        hprojX hprojY z S)).1 =
      classOracle P ell r projectX projectY z S := by
  let qg := qCenter ell r S
  let yg := yCenter ell r S
  let u0 := microInitial (r := r) hell projectX projectY hprojX hprojY S
  let uPrev := semanticMicroIterate (r := r) P hell projectX projectY
    hprojX hprojY z qg yg (feasibleMicroIterations - 1) u0
  let replyPrev := Oracle.firstOrderOracle P (scaledQuery uPrev)
  let opPrev := replyOperator ell r z qg yg uPrev.1 replyPrev
  let uFinal := microAdvance (r := r) hell projectX projectY hprojX hprojY
    z qg yg uPrev replyPrev
  let replyFinal := Oracle.firstOrderOracle P (scaledQuery uFinal)
  let O := outputFromReplies ell z uPrev.1 uFinal.1 replyPrev replyFinal opPrev
  have hplain : O = classOracle P ell r projectX projectY z S := by
    have h := eval_classMicroProgram (r := r) P hell projectX projectY
      hprojX hprojY z S
    simp only [classMicroProgram, Oracle.Program.eval_bind,
      Oracle.Program.eval_ask] at h
    rw [eval_microIterateProgram] at h
    change Oracle.Program.eval P (Oracle.Program.pure O) = _ at h
    rw [Oracle.Program.eval_pure] at h
    exact h
  have hfeasible :
      Oracle.Program.eval P
        (feasibleClassMicroProgram (r := r) hell projectX projectY
          hprojX hprojY z S) =
        (⟨O, outputFromReplies_y_mem z uPrev uFinal replyPrev replyFinal opPrev⟩ :
          FeasibleMicroOutput m Y) := by
    simp only [feasibleClassMicroProgram, Oracle.Program.eval_bind,
      Oracle.Program.eval_ask]
    rw [eval_microIterateProgram]
    rw [Oracle.Program.eval_pure]
  rw [hfeasible]
  exact hplain

/-- Every reply branch of a program has the same finite number of genuine
queries. -/
inductive ExactDepth {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)} :
    {α : Type} → Oracle.Program X Y α → Nat → Prop where
  | pure (a : α) : ExactDepth (Oracle.Program.pure a) 0
  | query (q : Oracle.Query m n) (hq : q.1 ∈ X ∧ q.2 ∈ Y)
      (next : Oracle.OracleReply m n → Oracle.Program X Y α) (k : Nat)
      (hnext : ∀ reply, ExactDepth (next reply) k) :
      ExactDepth (.query q hq next) (k + 1)

theorem ExactDepth.bind {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {α β : Type} {p : Oracle.Program X Y α} {cp ck : Nat}
    (hp : ExactDepth p cp) (k : α → Oracle.Program X Y β)
    (hk : ∀ a, ExactDepth (k a) ck) : ExactDepth (p >>= k) (cp + ck) := by
  induction hp with
  | pure a =>
      change ExactDepth (k a) (0 + ck)
      simpa using hk a
  | query q hq next c hnext ih =>
      change ExactDepth (.query q hq (fun reply => next reply >>= k))
        ((c + 1) + ck)
      rw [show (c + 1) + ck = (c + ck) + 1 by omega]
      exact ExactDepth.query q hq (fun reply => next reply >>= k) (c + ck)
        (fun reply => ih reply)

theorem ExactDepth.runSteps_bind {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} {α β : Type}
    {p : Oracle.Program X Y α} {cp : Nat} (hp : ExactDepth p cp)
    (P : NCCInstance m n) (k : α → Oracle.Program X Y β) :
    Oracle.Program.runSteps P (p >>= k) cp =
      k (Oracle.Program.eval P p) := by
  induction hp with
  | pure a => rfl
  | query q hq next c hnext ih =>
      change Oracle.Program.runSteps P
        (.query q hq (fun reply => next reply >>= k)) (c + 1) = _
      rw [← Oracle.Program.runSteps_oracleStep]
      change Oracle.Program.runSteps P
        (next (Oracle.firstOrderOracle P q) >>= k) c =
          k (Oracle.Program.eval P (next (Oracle.firstOrderOracle P q)))
      exact ih (Oracle.firstOrderOracle P q)

theorem ExactDepth.runSteps {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} {α : Type}
    {p : Oracle.Program X Y α} {cp : Nat} (hp : ExactDepth p cp)
    (P : NCCInstance m n) :
    Oracle.Program.runSteps P p cp =
      Oracle.Program.pure (Oracle.Program.eval P p) := by
  induction hp with
  | pure a => rfl
  | query q hq next c hnext ih =>
      rw [← Oracle.Program.runSteps_oracleStep]
      change Oracle.Program.runSteps P
        (next (Oracle.firstOrderOracle P q)) c =
          Oracle.Program.pure
            (Oracle.Program.eval P (next (Oracle.firstOrderOracle P q)))
      exact ih (Oracle.firstOrderOracle P q)

theorem exactDepth_ask {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    (q : Oracle.Query m n) (hq : q.1 ∈ X ∧ q.2 ∈ Y) :
    ExactDepth (Oracle.Program.ask q hq) 1 := by
  exact ExactDepth.query q hq (fun reply => Oracle.Program.pure reply) 0
    (fun reply => ExactDepth.pure reply)

theorem exactDepth_microIterateProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z qg : EVec m) (yg : EVec n) (k : Nat)
    (u : ScaledFeasible ell X Y) :
    ExactDepth
      (microIterateProgram (r := r) hell projectX projectY hprojX hprojY
        z qg yg k u) k := by
  induction k generalizing u with
  | zero => exact ExactDepth.pure u
  | succ k ih =>
      apply ExactDepth.query
      intro reply
      exact ih _

theorem exactDepth_feasibleClassMicroProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : State m n) :
    ExactDepth
      (feasibleClassMicroProgram (r := r) hell projectX projectY
        hprojX hprojY z S) (feasibleMicroIterations + 1) := by
  unfold feasibleClassMicroProgram
  let qg := qCenter ell r S
  let yg := yCenter ell r S
  let u0 := microInitial (r := r) hell projectX projectY hprojX hprojY S
  have hiter := exactDepth_microIterateProgram (r := r) hell projectX projectY
    hprojX hprojY z qg yg (feasibleMicroIterations - 1) u0
  let continuation : ScaledFeasible ell X Y →
      Oracle.Program X Y (FeasibleMicroOutput m Y) := fun uPrev => do
    let replyPrev ← Oracle.Program.ask (scaledQuery uPrev) (scaledQuery_mem uPrev)
    let opPrev := replyOperator ell r z qg yg uPrev.1 replyPrev
    let uFinal := microAdvance (r := r) hell projectX projectY hprojX hprojY
      z qg yg uPrev replyPrev
    let replyFinal ← Oracle.Program.ask (scaledQuery uFinal) (scaledQuery_mem uFinal)
    Oracle.Program.pure
      ⟨outputFromReplies ell z uPrev.1 uFinal.1 replyPrev replyFinal opPrev,
      outputFromReplies_y_mem z uPrev uFinal replyPrev replyFinal opPrev⟩
  have hcontinuation : ∀ uPrev, ExactDepth (continuation uPrev) 2 := by
    intro uPrev
    let rest : Oracle.OracleReply m n →
        Oracle.Program X Y (FeasibleMicroOutput m Y) := fun replyPrev =>
      let opPrev := replyOperator ell r z qg yg uPrev.1 replyPrev
      let uFinal := microAdvance (r := r) hell projectX projectY hprojX hprojY
        z qg yg uPrev replyPrev
      do
        let replyFinal ← Oracle.Program.ask (scaledQuery uFinal)
          (scaledQuery_mem uFinal)
        Oracle.Program.pure
          ⟨outputFromReplies ell z uPrev.1 uFinal.1 replyPrev replyFinal opPrev,
          outputFromReplies_y_mem z uPrev uFinal replyPrev replyFinal opPrev⟩
    have hrest : ∀ replyPrev, ExactDepth (rest replyPrev) 1 := by
      intro replyPrev
      let opPrev := replyOperator ell r z qg yg uPrev.1 replyPrev
      let uFinal := microAdvance (r := r) hell projectX projectY hprojX hprojY
        z qg yg uPrev replyPrev
      have hq := exactDepth_ask (scaledQuery uFinal) (scaledQuery_mem uFinal)
      have hpure : ∀ replyFinal : Oracle.OracleReply m n,
          ExactDepth
            (Oracle.Program.pure
              (⟨outputFromReplies ell z uPrev.1 uFinal.1 replyPrev replyFinal opPrev,
                outputFromReplies_y_mem z uPrev uFinal replyPrev replyFinal opPrev⟩ :
                FeasibleMicroOutput m Y)) 0 :=
        fun replyFinal => ExactDepth.pure (X := X) (Y := Y) _
      simpa [rest, opPrev, uFinal] using hq.bind _ hpure
    have hfirst := (exactDepth_ask (scaledQuery uPrev) (scaledQuery_mem uPrev)).bind
      rest hrest
    simpa [continuation, rest] using hfirst
  have hall := hiter.bind continuation hcontinuation
  change ExactDepth
    (microIterateProgram (r := r) hell projectX projectY hprojX hprojY
      z qg yg (feasibleMicroIterations - 1) u0 >>= continuation)
      (feasibleMicroIterations + 1)
  convert hall using 1
  have hpos := feasibleMicroIterations_positive
  omega

/-! ## Reply-driven FOAM blocks -/

/-- The analytic outer system with caller-supplied, domain-only projections.
Its executable oracle is exactly the program semantics above; class proofs
occur only in this correctness witness, never in the query program. -/
def outerSystemWithProjections {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (hr : 0 < r) (hrle : r ≤ ell / 8)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection P.X projectX)
    (hprojY : IsEuclideanProjection P.Y projectY)
    (hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell) :
    OuterTrajectoryConcrete.OuterSystem P.X P.Y P.f ell r hexistsR := by
  let oracle : EVec m → RelativeFOAMContraction.ValidState (m := m) P.Y →
      MicroOutput m n := fun z S =>
    classOracle P ell r projectX projectY z S.1
  have horacleFeasible : ∀ z S, (oracle z S).yFastNext ∈ P.Y := by
    intro z S
    exact classOracle_feasible hP hr.le hrle hprojX hprojY z S.1
  exact {
    projectX := projectX
    project_spec := hprojX
    gamma_bounded := gammaBddAbove_of_class hP
    stationary := stationaryAt_of_class hP hr hrle hprojX hprojY hexistsR
    oracle := oracle
    oracle_feasible := horacleFeasible
    oracle_subgradient := fun z S =>
      classOracle_subgradient hP hr.le hrle hprojX hprojY z S.1
        (horacleFeasible z S)
    oracle_residual := fun z S =>
      classOracle_residual hP hr.le hrle hprojX hprojY z S.1 }

/-- One executable FOAM macrostep. -/
def macroStepProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : RelativeFOAMContraction.ValidState (m := m) Y) :
    Oracle.Program X Y (RelativeFOAMContraction.ValidState (m := m) Y) := do
  let O ← feasibleClassMicroProgram (r := r) hell projectX projectY
    hprojX hprojY z S.1
  Oracle.Program.pure ⟨update ell r S.1 O.1, O.2⟩

theorem eval_macroStepProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (P : NCCInstance m n) (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : RelativeFOAMContraction.ValidState (m := m) Y) :
    (Oracle.Program.eval P
      (macroStepProgram (r := r) hell projectX projectY hprojX hprojY z S)).1 =
      update ell r S.1 (classOracle P ell r projectX projectY z S.1) := by
  simp only [macroStepProgram, Oracle.Program.eval_bind]
  rw [Oracle.Program.eval_pure]
  change update ell r S.1
      (Oracle.Program.eval P
        (feasibleClassMicroProgram (r := r) hell projectX projectY
          hprojX hprojY z S.1)).1 = _
  rw [eval_feasibleClassMicroProgram_val]

theorem exactDepth_macroStepProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (S : RelativeFOAMContraction.ValidState (m := m) Y) :
    ExactDepth
      (macroStepProgram (r := r) hell projectX projectY hprojX hprojY z S)
      (feasibleMicroIterations + 1) := by
  let continuation : FeasibleMicroOutput m Y →
      Oracle.Program X Y (RelativeFOAMContraction.ValidState (m := m) Y) :=
    fun O => Oracle.Program.pure ⟨update ell r S.1 O.1, O.2⟩
  have hpure : ∀ O, ExactDepth (continuation O) 0 :=
    fun O => ExactDepth.pure (X := X) (Y := Y) _
  have hbind := (exactDepth_feasibleClassMicroProgram (r := r) hell
    projectX projectY hprojX hprojY z S.1).bind continuation hpure
  simpa [macroStepProgram, continuation] using hbind

/-- Iterate a fixed-anchor FOAM macrostep `k` times. -/
def blockProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) : Nat →
      RelativeFOAMContraction.ValidState (m := m) Y →
      Oracle.Program X Y (RelativeFOAMContraction.ValidState (m := m) Y)
  | 0, S => Oracle.Program.pure S
  | k + 1, S => do
      let Snext ← macroStepProgram (r := r) hell projectX projectY
        hprojX hprojY z S
      blockProgram (r := r) hell projectX projectY hprojX hprojY z k Snext

theorem eval_blockProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (P : NCCInstance m n) (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (k : Nat)
    (S : RelativeFOAMContraction.ValidState (m := m) Y) :
    (Oracle.Program.eval P
      (blockProgram (r := r) hell projectX projectY hprojX hprojY z k S)).1 =
      ((fun V : State m n =>
        update ell r V (classOracle P ell r projectX projectY z V))^[k]) S.1 := by
  induction k generalizing S with
  | zero =>
      change (Oracle.Program.eval P (Oracle.Program.pure S)).1 = S.1
      rw [Oracle.Program.eval_pure]
  | succ k ih =>
      rw [blockProgram, Oracle.Program.eval_bind]
      rw [ih]
      rw [eval_macroStepProgram]
      rw [Function.iterate_succ_apply]

theorem exactDepth_blockProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (k : Nat)
    (S : RelativeFOAMContraction.ValidState (m := m) Y) :
    ExactDepth
      (blockProgram (r := r) hell projectX projectY hprojX hprojY z k S)
      (k * (feasibleMicroIterations + 1)) := by
  induction k generalizing S with
  | zero =>
      simpa [blockProgram] using
        (ExactDepth.pure (X := X) (Y := Y) S)
  | succ k ih =>
      unfold blockProgram
      have hmacro := exactDepth_macroStepProgram (r := r) hell projectX projectY
        hprojX hprojY z S
      have hbind := hmacro.bind
        (fun Snext => blockProgram (r := r) hell projectX projectY
          hprojX hprojY z k Snext)
        (fun Snext => ih Snext)
      simpa [Nat.succ_mul, Nat.add_comm] using hbind

/-! ## Startup and homotopy schedule -/

set_option linter.defProp false in
def sharedProxFamily {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P) :
    HomotopyRun.ProxFamily P.X P.Y P.f ell (ell / 8) :=
  MainTheorem.classProxFamily hP

def sharedSystemFamily {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection P.X projectX)
    (hprojY : IsEuclideanProjection P.Y projectY) :
    HomotopyRun.SystemFamily P.X P.Y P.f ell (ell / 8)
      (sharedProxFamily hP) := fun j =>
  outerSystemWithProjections hP
    (HomotopyCost.curvature_pos (div_pos hP.ell_pos (by norm_num)) j)
    (by
      unfold Tracking.curvature
      exact Tracking.div_pow_le_self
        (div_nonneg hP.ell_pos.le (by norm_num)) (by norm_num) j)
    projectX projectY hprojX hprojY (sharedProxFamily hP j)

@[simp] theorem sharedSystemFamily_oracle {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection P.X projectX)
    (hprojY : IsEuclideanProjection P.Y projectY) (j : Nat)
    (z : EVec m) (S : RelativeFOAMContraction.ValidState (m := m) P.Y) :
    (sharedSystemFamily hP projectX projectY hprojX hprojY j).oracle z S =
      classOracle P ell (Tracking.curvature (ell / 8) j)
        projectX projectY z S.1 := by
  rfl

def sharedStartupSeed {m n : Nat} {Y : Set (EVec n)}
    (hzero : (0 : EVec n) ∈ Y) :
    RelativeFOAMContraction.ValidState (m := m) Y :=
  ⟨StartupConcrete.coincidentState 0 0, hzero⟩

/-- Startup is one micro solve followed by the paper's coincident-state reset. -/
def startupProgram {m n : Nat} {ell : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzero : (0 : EVec n) ∈ Y) :
    Oracle.Program X Y (RelativeFOAMContraction.ValidState (m := m) Y) := do
  let O ← feasibleClassMicroProgram (r := ell / 8) hell projectX projectY
    hprojX hprojY 0 (sharedStartupSeed hzero).1
  Oracle.Program.pure
    ⟨StartupConcrete.coincidentState O.1.qFastNext O.1.yFastNext, O.2⟩

/-- Semantic startup equality stated against the supplied-projection system.
The class parameters are explicit here; the program itself contains none of
them except the numerical `ell`. -/
theorem eval_startupProgram_eq_system {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection P.X projectX)
    (hprojY : IsEuclideanProjection P.Y projectY)
    (hzero : (0 : EVec n) ∈ P.Y) (hx0 : P.x0 = 0) :
    Oracle.Program.eval P
        (startupProgram hP.ell_pos projectX projectY hprojX hprojY hzero) =
      HomotopyRun.startupState
        (sharedSystemFamily hP projectX projectY hprojX hprojY 0) hzero := by
  apply Subtype.ext
  simp only [startupProgram, Oracle.Program.eval_bind, Oracle.Program.eval_pure,
    HomotopyRun.startupState_val]
  rw [eval_feasibleClassMicroProgram_val]
  rw [sharedSystemFamily_oracle]
  simp [HomotopyRun.startupSeed, sharedStartupSeed, Tracking.curvature, hx0]

theorem exactDepth_startupProgram {m n : Nat} {ell : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzero : (0 : EVec n) ∈ Y) :
    ExactDepth (startupProgram hell projectX projectY hprojX hprojY hzero)
      (feasibleMicroIterations + 1) := by
  let continuation : FeasibleMicroOutput m Y →
      Oracle.Program X Y (RelativeFOAMContraction.ValidState (m := m) Y) :=
    fun O => Oracle.Program.pure
      ⟨StartupConcrete.coincidentState O.1.qFastNext O.1.yFastNext, O.2⟩
  have hpure : ∀ O, ExactDepth (continuation O) 0 :=
    fun O => ExactDepth.pure (X := X) (Y := Y) _
  have hbind := (exactDepth_feasibleClassMicroProgram (r := ell / 8) hell
    projectX projectY hprojX hprojY 0 (sharedStartupSeed hzero).1).bind
      continuation hpure
  simpa [startupProgram, continuation] using hbind

def causalHomotopyCalls (ell : ℝ) : Nat → Nat
  | 0 => 0
  | j + 1 => causalHomotopyCalls ell j +
      blockIterations (alpha ell (Tracking.curvature (ell / 8) (j + 1)))
        (1 / 8 : ℝ) * (feasibleMicroIterations + 1)

/-- Reply-driven execution of homotopy stages `1,...,J`. -/
def homotopyProgram {m n : Nat} {ell : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) : Nat →
      RelativeFOAMContraction.ValidState (m := m) Y →
      Oracle.Program X Y (RelativeFOAMContraction.ValidState (m := m) Y)
  | 0, S => Oracle.Program.pure S
  | j + 1, S => do
      let Sold ← homotopyProgram hell projectX projectY hprojX hprojY z j S
      let rj := Tracking.curvature (ell / 8) (j + 1)
      blockProgram (r := rj) hell projectX projectY hprojX hprojY z
        (blockIterations (alpha ell rj) (1 / 8 : ℝ)) Sold

theorem exactDepth_homotopyProgram {m n : Nat} {ell : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (z : EVec m) (J : Nat)
    (S : RelativeFOAMContraction.ValidState (m := m) Y) :
    ExactDepth
      (homotopyProgram hell projectX projectY hprojX hprojY z J S)
      (causalHomotopyCalls ell J) := by
  induction J generalizing S with
  | zero =>
      simpa [homotopyProgram, causalHomotopyCalls] using
        (ExactDepth.pure (X := X) (Y := Y) S)
  | succ j ih =>
      unfold homotopyProgram causalHomotopyCalls
      let rj := Tracking.curvature (ell / 8) (j + 1)
      let K := blockIterations (alpha ell rj) (1 / 8 : ℝ)
      have hbind := (ih S).bind
        (fun Sold => blockProgram (r := rj) hell projectX projectY
          hprojX hprojY z K Sold)
        (fun Sold => exactDepth_blockProgram (r := rj) hell projectX projectY
          hprojX hprojY z K Sold)
      simpa [rj, K] using hbind

theorem causalHomotopyCalls_eq (ell : ℝ) (J : Nat) :
    causalHomotopyCalls ell J =
      HomotopyCost.homotopyOracleCalls ell (ell / 8) (1 / 8) J := by
  induction J with
  | zero => simp [causalHomotopyCalls, HomotopyCost.homotopyOracleCalls]
  | succ j ih =>
      rw [causalHomotopyCalls, ih]
      unfold HomotopyCost.homotopyOracleCalls
      rw [Finset.sum_range_succ]
      simp [
        BlockCostConcrete.feasibleBlockCost, RelativeFOAM.blockCost,
        RelativeFOAM.projectedMicroCost]

theorem eval_macroStepProgram_eq_system {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection P.X projectX)
    (hprojY : IsEuclideanProjection P.Y projectY)
    (j : Nat) (z : EVec m)
    (S : RelativeFOAMContraction.ValidState (m := m) P.Y) :
    Oracle.Program.eval P
        (macroStepProgram (r := Tracking.curvature (ell / 8) j)
          hP.ell_pos projectX projectY hprojX hprojY z S) =
      RelativeFOAMContraction.foamStep ell (Tracking.curvature (ell / 8) j)
        ((sharedSystemFamily hP projectX projectY hprojX hprojY j).oracle z)
        ((sharedSystemFamily hP projectX projectY hprojX hprojY j).oracle_feasible z)
        S := by
  apply Subtype.ext
  rw [eval_macroStepProgram]
  rfl

theorem eval_blockProgram_eq_system {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection P.X projectX)
    (hprojY : IsEuclideanProjection P.Y projectY)
    (j : Nat) (z : EVec m) (k : Nat)
    (S : RelativeFOAMContraction.ValidState (m := m) P.Y) :
    Oracle.Program.eval P
        (blockProgram (r := Tracking.curvature (ell / 8) j)
          hP.ell_pos projectX projectY hprojX hprojY z k S) =
      ((RelativeFOAMContraction.foamStep ell
        (Tracking.curvature (ell / 8) j)
        ((sharedSystemFamily hP projectX projectY hprojX hprojY j).oracle z)
        ((sharedSystemFamily hP projectX projectY hprojX hprojY j).oracle_feasible z))^[k]) S := by
  induction k generalizing S with
  | zero =>
      change Oracle.Program.eval P (Oracle.Program.pure S) = S
      rw [Oracle.Program.eval_pure]
  | succ k ih =>
      rw [blockProgram, Oracle.Program.eval_bind, ih]
      rw [eval_macroStepProgram_eq_system]
      rw [Function.iterate_succ_apply]

theorem eval_homotopyProgram_eq_system {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection P.X projectX)
    (hprojY : IsEuclideanProjection P.Y projectY)
    (z : EVec m) (J : Nat)
    (S : RelativeFOAMContraction.ValidState (m := m) P.Y) :
    Oracle.Program.eval P
        (homotopyProgram hP.ell_pos projectX projectY hprojX hprojY z J S) =
      HomotopyRun.homotopyState
        (sharedSystemFamily hP projectX projectY hprojX hprojY) z S J := by
  induction J generalizing S with
  | zero =>
      change Oracle.Program.eval P (Oracle.Program.pure S) = S
      rw [Oracle.Program.eval_pure]
  | succ j ih =>
      rw [homotopyProgram, Oracle.Program.eval_bind, ih]
      rw [HomotopyRun.homotopyState_succ]
      exact eval_blockProgram_eq_system hP projectX projectY hprojX hprojY
        (j + 1) z _ _

/-! ## Outer trajectory and explicit finite argmin -/

abbrev FeasibleSnapshot {m n : Nat} (X : Set (EVec m))
    (Y : Set (EVec n)) :=
  {R : OuterTrajectoryConcrete.Snapshot (m := m) Y // R.z ∈ X}

abbrev FeasibleTrajectory {m n : Nat} (T : Nat) (X : Set (EVec m))
    (Y : Set (EVec n)) := Fin T → FeasibleSnapshot X Y

/-- One outer transition.  Its readout projection is domain-feasible before
any oracle reply is inspected. -/
def nextSnapshotProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (R : FeasibleSnapshot X Y) :
    Oracle.Program X Y (FeasibleSnapshot X Y) :=
  let zNext := projectX ((-ell⁻¹) • R.1.state.1.qFast)
  let d := zNext - R.1.z
  let shifted := OuterTrajectoryConcrete.coTranslateValid ell d R.1.state
  do
    let stateNext ← blockProgram (r := r) hell projectX projectY hprojX hprojY
      zNext (blockIterations (alpha ell r) (1 / 400 : ℝ)) shifted
    Oracle.Program.pure
      ⟨{ z := zNext
         state := stateNext
         B := Tracking.nextMajorant (1 / 400) ell (vecSq d) R.1.B },
       hprojX.mem _⟩

theorem exactDepth_nextSnapshotProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (R : FeasibleSnapshot X Y) :
    ExactDepth
      (nextSnapshotProgram (r := r) hell projectX projectY hprojX hprojY R)
      (blockIterations (alpha ell r) (1 / 400 : ℝ) *
        (feasibleMicroIterations + 1)) := by
  let zNext := projectX ((-ell⁻¹) • R.1.state.1.qFast)
  let d := zNext - R.1.z
  let shifted := OuterTrajectoryConcrete.coTranslateValid ell d R.1.state
  let K := blockIterations (alpha ell r) (1 / 400 : ℝ)
  let continuation : RelativeFOAMContraction.ValidState (m := m) Y →
      Oracle.Program X Y (FeasibleSnapshot X Y) := fun stateNext =>
    Oracle.Program.pure
      ⟨{ z := zNext
         state := stateNext
         B := Tracking.nextMajorant (1 / 400) ell (vecSq d) R.1.B },
       hprojX.mem _⟩
  have hpure : ∀ S, ExactDepth (continuation S) 0 :=
    fun S => ExactDepth.pure (X := X) (Y := Y) _
  have hbind := (exactDepth_blockProgram (r := r) hell projectX projectY
    hprojX hprojY zNext K shifted).bind continuation hpure
  simpa [nextSnapshotProgram, zNext, d, shifted, K, continuation] using hbind

theorem eval_nextSnapshotProgram_eq_system {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection P.X projectX)
    (hprojY : IsEuclideanProjection P.Y projectY)
    (J : Nat) (R : FeasibleSnapshot P.X P.Y) :
    (Oracle.Program.eval P
      (nextSnapshotProgram (r := Tracking.curvature (ell / 8) J)
        hP.ell_pos projectX projectY hprojX hprojY R)).1 =
      OuterTrajectoryConcrete.nextSnapshot
        (sharedSystemFamily hP projectX projectY hprojX hprojY J) R.1 := by
  unfold nextSnapshotProgram OuterTrajectoryConcrete.nextSnapshot
    OuterTrajectoryConcrete.readout OuterTrajectoryConcrete.runBlock
  simp only [Oracle.Program.eval_bind, Oracle.Program.eval_pure]
  rw [eval_blockProgram_eq_system]
  rfl

/-- `T` visible snapshots, using only `T-1` outer transitions. -/
def trajectoryProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY) :
    (T : Nat) → FeasibleSnapshot X Y →
      Oracle.Program X Y (FeasibleTrajectory T X Y)
  | 0, _R => Oracle.Program.pure (fun i => Fin.elim0 i)
  | 1, R => Oracle.Program.pure (fun _ => R)
  | k + 2, R => do
      let Rnext ← nextSnapshotProgram (r := r) hell projectX projectY
        hprojX hprojY R
      let tail ← trajectoryProgram (r := r) hell projectX projectY
        hprojX hprojY (k + 1) Rnext
      Oracle.Program.pure (Fin.cons R tail)

def outerPrefixCalls (ell r : ℝ) (T : Nat) : Nat :=
  (T - 1) * blockIterations (alpha ell r) (1 / 400 : ℝ) *
    (feasibleMicroIterations + 1)

theorem exactDepth_trajectoryProgram {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (T : Nat) (R : FeasibleSnapshot X Y) :
    ExactDepth
      (trajectoryProgram (r := r) hell projectX projectY hprojX hprojY T R)
      (outerPrefixCalls ell r T) := by
  cases T with
  | zero =>
      simpa [trajectoryProgram, outerPrefixCalls] using
        (ExactDepth.pure (X := X) (Y := Y) (fun i : Fin 0 => Fin.elim0 i))
  | succ T =>
      cases T with
      | zero =>
          simpa [trajectoryProgram, outerPrefixCalls] using
            (ExactDepth.pure (X := X) (Y := Y) (fun _ : Fin 1 => R))
      | succ k =>
          let C := blockIterations (alpha ell r) (1 / 400 : ℝ) *
            (feasibleMicroIterations + 1)
          let continuation : FeasibleSnapshot X Y →
              Oracle.Program X Y (FeasibleTrajectory (k + 2) X Y) :=
            fun Rnext => do
              let tail ← trajectoryProgram (r := r) hell projectX projectY
                hprojX hprojY (k + 1) Rnext
              Oracle.Program.pure (Fin.cons R tail)
          have htail : ∀ Rnext, ExactDepth (continuation Rnext)
              (outerPrefixCalls ell r (k + 1)) := by
            intro Rnext
            let finish : FeasibleTrajectory (k + 1) X Y →
                Oracle.Program X Y (FeasibleTrajectory (k + 2) X Y) :=
              fun tail => Oracle.Program.pure (Fin.cons R tail)
            have hpure : ∀ tail, ExactDepth (finish tail) 0 :=
              fun tail => ExactDepth.pure (X := X) (Y := Y) _
            have hb := (exactDepth_trajectoryProgram (r := r) hell projectX
              projectY hprojX hprojY (k + 1) Rnext).bind finish hpure
            simpa [continuation, finish] using hb
          have hall := (exactDepth_nextSnapshotProgram (r := r) hell projectX
            projectY hprojX hprojY R).bind continuation htail
          simpa [trajectoryProgram, continuation, outerPrefixCalls,
            Nat.succ_sub_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
            Nat.add_mul, Nat.mul_assoc, C] using hall

theorem trajectory_nextSnapshot {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterTrajectoryConcrete.OuterSystem X Y f ell r hexistsR)
    (R : OuterTrajectoryConcrete.Snapshot (m := m) Y) (t : Nat) :
    OuterTrajectoryConcrete.trajectory sys
        (OuterTrajectoryConcrete.nextSnapshot sys R) t =
      OuterTrajectoryConcrete.trajectory sys R (t + 1) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [OuterTrajectoryConcrete.trajectory_succ,
        OuterTrajectoryConcrete.trajectory_succ, ih]

theorem eval_trajectoryProgram_at {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection P.X projectX)
    (hprojY : IsEuclideanProjection P.Y projectY)
    (J T : Nat) (R : FeasibleSnapshot P.X P.Y) (i : Fin T) :
    (Oracle.Program.eval P
      (trajectoryProgram (r := Tracking.curvature (ell / 8) J)
        hP.ell_pos projectX projectY hprojX hprojY T R) i).1 =
      OuterTrajectoryConcrete.trajectory
        (sharedSystemFamily hP projectX projectY hprojX hprojY J) R.1 i.1 := by
  cases T with
  | zero => exact Fin.elim0 i
  | succ T =>
      cases T with
      | zero =>
          have hi : i = 0 := Fin.eq_zero i
          subst i
          change R.1 = _
          rfl
      | succ k =>
          let Rnext : FeasibleSnapshot P.X P.Y :=
            Oracle.Program.eval P
              (nextSnapshotProgram (r := Tracking.curvature (ell / 8) J)
                hP.ell_pos projectX projectY hprojX hprojY R)
          simp only [trajectoryProgram, Oracle.Program.eval_bind,
            Oracle.Program.eval_pure]
          refine Fin.cases ?_ (fun j => ?_) i
          · rfl
          · have ih := eval_trajectoryProgram_at hP projectX projectY hprojX hprojY
              J (k + 1) Rnext j
            rw [Fin.cons_succ]
            rw [ih]
            have hnext : Rnext.1 = OuterTrajectoryConcrete.nextSnapshot
                (sharedSystemFamily hP projectX projectY hprojX hprojY J) R.1 := by
              exact eval_nextSnapshotProgram_eq_system hP projectX projectY
                hprojX hprojY J R
            rw [hnext]
            exact trajectory_nextSnapshot
              (sharedSystemFamily hP projectX projectY hprojX hprojY J) R.1 j.1

/-- Explicit earliest-minimum scan over `0,...,k`.  This definition is plain
recursion on real certificate values; it contains no objective or proof. -/
def earliestMinIndex : (k : Nat) → (Fin (k + 1) → ℝ) → Fin (k + 1)
  | 0, _score => 0
  | k + 1, score =>
      let old := earliestMinIndex k (fun i => score i.castSucc)
      let last := Fin.last (k + 1)
      if score last < score old.castSucc then last else old.castSucc

theorem earliestMinIndex_minimal (k : Nat) (score : Fin (k + 1) → ℝ) :
    ∀ i, score (earliestMinIndex k score) ≤ score i := by
  induction k with
  | zero =>
      intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact le_rfl
  | succ k ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [earliestMinIndex]
        split_ifs with h
        · exact le_rfl
        · exact le_of_not_gt h
      · simp only [earliestMinIndex]
        split_ifs with h
        · exact (le_of_lt h).trans (ih (fun t => score t.castSucc) j)
        · exact ih (fun t => score t.castSucc) j

def computableCertificate {m n : Nat} (ell : ℝ)
    (projectX : EVec m → EVec m)
    {Y : Set (EVec n)} (R : OuterTrajectoryConcrete.Snapshot (m := m) Y) : ℝ :=
  Tracking.certificate ell
    (vecSq (projectX ((-ell⁻¹) • R.state.1.qFast) - R.z)) R.B

def selectedTrajectoryIndex {m n : Nat} {T : Nat} (hT : 0 < T)
    {X : Set (EVec m)} {Y : Set (EVec n)} (ell : ℝ)
    (projectX : EVec m → EVec m) (data : FeasibleTrajectory T X Y) : Fin T := by
  cases T with
  | zero => omega
  | succ k =>
      exact earliestMinIndex k (fun i => computableCertificate ell projectX (data i).1)

theorem selectedTrajectoryIndex_minimal {m n : Nat} {T : Nat} (hT : 0 < T)
    {X : Set (EVec m)} {Y : Set (EVec n)} (ell : ℝ)
    (projectX : EVec m → EVec m) (data : FeasibleTrajectory T X Y) (i : Fin T) :
    computableCertificate ell projectX (data (selectedTrajectoryIndex hT ell projectX data)).1 ≤
      computableCertificate ell projectX (data i).1 := by
  cases T with
  | zero => omega
  | succ k =>
      exact earliestMinIndex_minimal k
        (fun j => computableCertificate ell projectX (data j).1) i

/-! ## The complete domain-only program -/

def scheduleTarget (ell D eps : ℝ) : ℝ :=
  UniformSchedule.targetCurvature ell D eps

def scheduleStage (ell D eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (heps : 0 < eps) : Nat :=
  HomotopySchedule.homotopyStage (ell / 8) (scheduleTarget ell D eps)
    (div_pos hell (by norm_num))
    (by simpa [scheduleTarget] using
      UniformSchedule.targetCurvature_pos hell hD heps)

def scheduleCurvature (ell D eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (heps : 0 < eps) : ℝ :=
  Tracking.curvature (ell / 8) (scheduleStage ell D eps hell hD heps)

def scheduleIterations (ell D Delta eps : ℝ) (hell : 0 < ell)
    (hD : 0 < D) (heps : 0 < eps) : Nat :=
  UniformSchedule.paperOuterIterations ell Delta
    (scheduleCurvature ell D eps hell hD heps) D eps

theorem scheduleCurvature_pos {ell D eps : ℝ} (hell : 0 < ell)
    (hD : 0 < D) (heps : 0 < eps) :
    0 < scheduleCurvature ell D eps hell hD heps := by
  exact HomotopyCost.curvature_pos (div_pos hell (by norm_num)) _

theorem scheduleCurvature_le {ell D eps : ℝ} (hell : 0 < ell)
    (hD : 0 < D) (heps : 0 < eps) :
    scheduleCurvature ell D eps hell hD heps ≤ ell / 8 := by
  unfold scheduleCurvature Tracking.curvature
  exact Tracking.div_pow_le_self (div_nonneg hell.le (by norm_num))
    (by norm_num) _

theorem scheduleIterations_pos {ell D Delta eps : ℝ} (hell : 0 < ell)
    (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps) :
    0 < scheduleIterations ell D Delta eps hell hD heps := by
  exact UniformSchedule.paperOuterIterations_pos hell hDelta
    (scheduleCurvature_pos hell hD heps).le heps

def prefixCalls (ell D Delta eps : ℝ) (hell : 0 < ell)
    (hD : 0 < D) (heps : 0 < eps) : Nat :=
  let J := scheduleStage ell D eps hell hD heps
  let r := scheduleCurvature ell D eps hell hD heps
  let T := scheduleIterations ell D Delta eps hell hD heps
  1 + (feasibleMicroIterations + 1) + causalHomotopyCalls ell J +
    outerPrefixCalls ell r T

/-- Everything before the final compatibility query.  The first ask is the
paper-mandated full origin and is deliberately ignored. -/
def schedulePrefixProgram {m n : Nat} (ell D Delta eps : ℝ)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    Oracle.Program X Y (FeasibleSnapshot X Y) := do
  let _originReply ← Oracle.Program.ask ((0 : EVec m), (0 : EVec n))
    ⟨hzeroX, hzeroY⟩
  let startup ← startupProgram hell projectX projectY hprojX hprojY hzeroY
  let J := scheduleStage ell D eps hell hD heps
  let r := scheduleCurvature ell D eps hell hD heps
  let T := scheduleIterations ell D Delta eps hell hD heps
  let hT := scheduleIterations_pos hell hD hDelta heps
  let finalState ← homotopyProgram hell projectX projectY hprojX hprojY 0 J startup
  let R0 : FeasibleSnapshot X Y :=
    ⟨{ z := 0
       state := finalState
       B := Tracking.homotopyMajorant (ell / 8) (D ^ 2)
        (8 * (Delta + (ell / 8) * D ^ 2)) J }, hzeroX⟩
  let data ← trajectoryProgram (r := r) hell projectX projectY hprojX hprojY T R0
  Oracle.Program.pure (data (selectedTrajectoryIndex hT ell projectX data))

/-- Add the unique final query whose primal coordinate is the deterministic
earliest-minimum certificate anchor. -/
def sharedOracleProgram {m n : Nat} (ell D Delta eps : ℝ)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    Oracle.Program X Y (EVec m) := do
  let selected ← schedulePrefixProgram ell D Delta eps hell hD hDelta heps
    projectX projectY hprojX hprojY hzeroX hzeroY
  let _reply ← Oracle.Program.ask (selected.1.z, (0 : EVec n))
    ⟨selected.2, hzeroY⟩
  Oracle.Program.pure selected.1.z

def sharedOracleCalls (ell D Delta eps : ℝ) (hell : 0 < ell)
    (hD : 0 < D) (heps : 0 < eps) : Nat :=
  prefixCalls ell D Delta eps hell hD heps + 1

theorem exactDepth_schedulePrefixProgram {m n : Nat}
    (ell D Delta eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    ExactDepth
      (schedulePrefixProgram ell D Delta eps hell hD hDelta heps
        projectX projectY hprojX hprojY hzeroX hzeroY)
      (prefixCalls ell D Delta eps hell hD heps) := by
  let J := scheduleStage ell D eps hell hD heps
  let r := scheduleCurvature ell D eps hell hD heps
  let T := scheduleIterations ell D Delta eps hell hD heps
  let hT := scheduleIterations_pos hell hD hDelta heps
  let origin := Oracle.Program.ask ((0 : EVec m), (0 : EVec n))
    ⟨hzeroX, hzeroY⟩
  let start := startupProgram hell projectX projectY hprojX hprojY hzeroY
  have horigin : ExactDepth origin 1 := exactDepth_ask _ _
  have hstart : ExactDepth start (feasibleMicroIterations + 1) :=
    exactDepth_startupProgram hell projectX projectY hprojX hprojY hzeroY
  let afterOrigin : Oracle.OracleReply m n →
      Oracle.Program X Y (FeasibleSnapshot X Y) := fun _ => do
    let startup ← start
    let finalState ← homotopyProgram hell projectX projectY hprojX hprojY 0 J startup
    let R0 : FeasibleSnapshot X Y :=
      ⟨{ z := 0
         state := finalState
         B := Tracking.homotopyMajorant (ell / 8) (D ^ 2)
          (8 * (Delta + (ell / 8) * D ^ 2)) J }, hzeroX⟩
    let data ← trajectoryProgram (r := r) hell projectX projectY hprojX hprojY T R0
    Oracle.Program.pure (data (selectedTrajectoryIndex hT ell projectX data))
  have hafterOrigin : ∀ reply, ExactDepth (afterOrigin reply)
      ((feasibleMicroIterations + 1) + causalHomotopyCalls ell J +
        outerPrefixCalls ell r T) := by
    intro reply
    let afterStart : RelativeFOAMContraction.ValidState (m := m) Y →
        Oracle.Program X Y (FeasibleSnapshot X Y) := fun startup => do
      let finalState ← homotopyProgram hell projectX projectY hprojX hprojY 0 J startup
      let R0 : FeasibleSnapshot X Y :=
        ⟨{ z := 0
           state := finalState
           B := Tracking.homotopyMajorant (ell / 8) (D ^ 2)
            (8 * (Delta + (ell / 8) * D ^ 2)) J }, hzeroX⟩
      let data ← trajectoryProgram (r := r) hell projectX projectY hprojX hprojY T R0
      Oracle.Program.pure (data (selectedTrajectoryIndex hT ell projectX data))
    have hafterStart : ∀ startup, ExactDepth (afterStart startup)
        (causalHomotopyCalls ell J + outerPrefixCalls ell r T) := by
      intro startup
      let afterHom : RelativeFOAMContraction.ValidState (m := m) Y →
          Oracle.Program X Y (FeasibleSnapshot X Y) := fun finalState =>
        let R0 : FeasibleSnapshot X Y :=
          ⟨{ z := 0
             state := finalState
             B := Tracking.homotopyMajorant (ell / 8) (D ^ 2)
              (8 * (Delta + (ell / 8) * D ^ 2)) J }, hzeroX⟩
        do
          let data ← trajectoryProgram (r := r) hell projectX projectY
            hprojX hprojY T R0
          Oracle.Program.pure
            (data (selectedTrajectoryIndex hT ell projectX data))
      have hafterHom : ∀ finalState, ExactDepth (afterHom finalState)
          (outerPrefixCalls ell r T) := by
        intro finalState
        let R0 : FeasibleSnapshot X Y :=
          ⟨{ z := 0
             state := finalState
             B := Tracking.homotopyMajorant (ell / 8) (D ^ 2)
              (8 * (Delta + (ell / 8) * D ^ 2)) J }, hzeroX⟩
        let finish : FeasibleTrajectory T X Y →
            Oracle.Program X Y (FeasibleSnapshot X Y) := fun data =>
          Oracle.Program.pure
            (data (selectedTrajectoryIndex hT ell projectX data))
        have hpure : ∀ data, ExactDepth (finish data) 0 :=
          fun data => ExactDepth.pure (X := X) (Y := Y) _
        have hb := (exactDepth_trajectoryProgram (r := r) hell projectX
          projectY hprojX hprojY T R0).bind finish hpure
        simpa [afterHom, R0, finish] using hb
      have hb := (exactDepth_homotopyProgram hell projectX projectY
        hprojX hprojY 0 J startup).bind afterHom hafterHom
      simpa [afterStart, afterHom] using hb
    have hb := hstart.bind afterStart hafterStart
    simpa [afterOrigin, afterStart, start, Nat.add_assoc] using hb
  have hall := horigin.bind afterOrigin hafterOrigin
  simpa [schedulePrefixProgram, prefixCalls, origin, afterOrigin, start,
    J, r, T, hT, Nat.add_assoc] using hall

theorem exactDepth_sharedOracleProgram {m n : Nat}
    (ell D Delta eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    ExactDepth
      (sharedOracleProgram ell D Delta eps hell hD hDelta heps
        projectX projectY hprojX hprojY hzeroX hzeroY)
      (sharedOracleCalls ell D Delta eps hell hD heps) := by
  let finish : FeasibleSnapshot X Y → Oracle.Program X Y (EVec m) :=
    fun selected => do
      let _reply ← Oracle.Program.ask (selected.1.z, (0 : EVec n))
        ⟨selected.2, hzeroY⟩
      Oracle.Program.pure selected.1.z
  have hfinish : ∀ selected, ExactDepth (finish selected) 1 := by
    intro selected
    have hq := exactDepth_ask (selected.1.z, (0 : EVec n))
      ⟨selected.2, hzeroY⟩
    have hpure : ∀ _reply : Oracle.OracleReply m n,
        ExactDepth (Oracle.Program.pure selected.1.z :
          Oracle.Program X Y (EVec m)) 0 :=
      fun _ => ExactDepth.pure (X := X) (Y := Y) _
    simpa [finish] using hq.bind _ hpure
  have hall := (exactDepth_schedulePrefixProgram ell D Delta eps hell hD
    hDelta heps projectX projectY hprojX hprojY hzeroX hzeroY).bind
      finish hfinish
  simpa [sharedOracleProgram, sharedOracleCalls, finish] using hall

theorem sharedOracleProgram_firstQuery {m n : Nat}
    (ell D Delta eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    Oracle.Program.queryAfterHistory
      (sharedOracleProgram ell D Delta eps hell hD hDelta heps
        projectX projectY hprojX hprojY hzeroX hzeroY)
      ((0 : EVec m), (0 : EVec n)) 0 (Oracle.emptyHistory m n) =
        ((0 : EVec m), (0 : EVec n)) := by
  simp [Oracle.Program.queryAfterHistory_zero, sharedOracleProgram,
    schedulePrefixProgram, Oracle.Program.ask, Oracle.Program.bind]
  change ((0 : EVec m), (0 : EVec n)) = ((0 : EVec m), (0 : EVec n))
  rfl

def domainProjectX (Q : Oracle.AdmissibleDomainPair) :
    EVec Q.m → EVec Q.m :=
  Classical.choose (ProjectionExistence.exists_euclideanProjection
    ⟨0, Q.zero_mem_X⟩ Q.X_closed Q.X_convex)

def domainProjectY (Q : Oracle.AdmissibleDomainPair) :
    EVec Q.n → EVec Q.n :=
  Classical.choose (ProjectionExistence.exists_euclideanProjection
    ⟨0, Q.zero_mem_Y⟩ Q.Y_closed Q.Y_convex)

theorem domainProjectX_spec (Q : Oracle.AdmissibleDomainPair) :
    IsEuclideanProjection Q.X (domainProjectX Q) :=
  Classical.choose_spec (ProjectionExistence.exists_euclideanProjection
    ⟨0, Q.zero_mem_X⟩ Q.X_closed Q.X_convex)

theorem domainProjectY_spec (Q : Oracle.AdmissibleDomainPair) :
    IsEuclideanProjection Q.Y (domainProjectY Q) :=
  Classical.choose_spec (ProjectionExistence.exists_euclideanProjection
    ⟨0, Q.zero_mem_Y⟩ Q.Y_closed Q.Y_convex)

def sharedComponent (ell D Delta eps : ℝ) (hell : 0 < ell)
    (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (Q : Oracle.AdmissibleDomainPair) :
    Oracle.DeterministicFOComponent Q.X Q.Y :=
  Oracle.Program.compile
    (sharedOracleProgram ell D Delta eps hell hD hDelta heps
      (domainProjectX Q) (domainProjectY Q)
      (domainProjectX_spec Q) (domainProjectY_spec Q)
      Q.zero_mem_X Q.zero_mem_Y)
    ((0 : EVec Q.m), (0 : EVec Q.n)) ⟨Q.zero_mem_X, Q.zero_mem_Y⟩
    (sharedOracleProgram_firstQuery ell D Delta eps hell hD hDelta heps
      (domainProjectX Q) (domainProjectY Q)
      (domainProjectX_spec Q) (domainProjectY_spec Q)
      Q.zero_mem_X Q.zero_mem_Y)

/-- The promised domain-wise algorithm.  Inspecting this definition shows
that its component is a compiled `Program`: only the domain, numerical class
parameters, and the finite reply history occur in `nextQuery`. -/
def sharedDomainAlgorithm (ell D Delta eps : ℝ) (hell : 0 < ell)
    (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps) :
    Oracle.DomainWiseDeterministicAlgorithm where
  component Q := sharedComponent ell D Delta eps hell hD hDelta heps Q

theorem queriedAt_sharedComponent_final {m n : Nat}
    (ell D Delta eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y)
    (P : NCCInstance m n) :
    let pref := schedulePrefixProgram ell D Delta eps hell hD hDelta heps
      projectX projectY hprojX hprojY hzeroX hzeroY
    let full := sharedOracleProgram ell D Delta eps hell hD hDelta heps
      projectX projectY hprojX hprojY hzeroX hzeroY
    let fallback : Oracle.Query m n := (0, 0)
    let component := Oracle.Program.compile full fallback ⟨hzeroX, hzeroY⟩
      (sharedOracleProgram_firstQuery ell D Delta eps hell hD hDelta heps
        projectX projectY hprojX hprojY hzeroX hzeroY)
    Oracle.DeterministicFOComponent.queriedAt component P
        (prefixCalls ell D Delta eps hell hD heps) =
      ((Oracle.Program.eval P pref).1.z, (0 : EVec n)) := by
  dsimp only
  let pref := schedulePrefixProgram ell D Delta eps hell hD hDelta heps
    projectX projectY hprojX hprojY hzeroX hzeroY
  let finish : FeasibleSnapshot X Y → Oracle.Program X Y (EVec m) :=
    fun selected => do
      let _reply ← Oracle.Program.ask (selected.1.z, (0 : EVec n))
        ⟨selected.2, hzeroY⟩
      Oracle.Program.pure selected.1.z
  have hp := exactDepth_schedulePrefixProgram ell D Delta eps hell hD hDelta
    heps projectX projectY hprojX hprojY hzeroX hzeroY
  have hrun : Oracle.Program.runSteps P (pref >>= finish)
      (prefixCalls ell D Delta eps hell hD heps) =
      finish (Oracle.Program.eval P pref) := hp.runSteps_bind P finish
  apply Oracle.Program.queriedAt_compile_eq_of_runSteps_query
  refine ⟨⟨(Oracle.Program.eval P pref).2, hzeroY⟩,
    (fun _reply => Oracle.Program.pure (Oracle.Program.eval P pref).1.z), ?_⟩
  change Oracle.Program.runSteps P (pref >>= finish)
      (prefixCalls ell D Delta eps hell hD heps) = _
  rw [hrun]
  rfl

/-! ## Correctness of the explicit minimum certificate -/

/-- The deterministic-output proof works for every finite certificate
minimizer, not only the choice-based minimizer used in the earlier interface. -/
theorem minimumCertificateAnchor_is_OS {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r D eps lower : ℝ} {T : Nat}
    (hX : X.Nonempty) (hell : 0 < ell) (hr : 0 < r)
    (hrle : r ≤ ell / 8) (heps : 0 ≤ eps)
    (hweak : IsWeaklyConvexOn ell X (ValueOn Y f))
    (hweakR : IsWeaklyConvexOn ell X (DualRegularizedValueOn Y f r))
    (hexists : HasProxEverywhere X (ValueOn Y f) ell)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (hYnorm : ∀ y ∈ Y, vecSq y ≤ D ^ 2)
    (hmax : ∀ x, ∃ y, IsMaximizerOn Y f x y)
    (hmaxR : ∀ x, ∃ y, IsMaximizerOn Y
      (fun u v => f u v - r / 2 * vecSq v) x y)
    (sys : OuterTrajectoryConcrete.OuterSystem X Y f ell r hexistsR)
    (R0 : OuterTrajectoryConcrete.Snapshot (m := m) Y)
    (hE0 : OuterTrajectoryConcrete.snapshotEnergy sys R0 ≤ R0.B)
    (hB0 : 0 ≤ R0.B) (hT : 0 < T)
    (hlower : ∀ z, lower ≤
      OuterTrajectoryConcrete.regularizedEnvelope X Y f ell r hexistsR z)
    (hcertificateBudget :
      (32 * ell / T) *
        (OuterTrajectoryConcrete.snapshotPotential sys R0 - lower) ≤ eps ^ 2 / 4)
    (hbiasBudget : 2 * ell * r * D ^ 2 ≤ eps ^ 2 / 4)
    (ts : Fin T)
    (hminimal : ∀ s : Fin T,
      OuterTrajectoryConcrete.stepCertificate sys
          (OuterTrajectoryConcrete.trajectory sys R0 ts.1) ≤
        OuterTrajectoryConcrete.stepCertificate sys
          (OuterTrajectoryConcrete.trajectory sys R0 s.1)) :
    IsOptimizationStationary X (ValueOn Y f) ell eps
      (OuterTrajectoryConcrete.trajectory sys R0 ts.1).z := by
  obtain ⟨t, ht, hsmall⟩ :=
    OuterTrajectoryConcrete.exists_small_trajectory_certificate
      hX hell hr hrle hweakR sys R0 hE0 hB0 hT hlower
  let ti : Fin T := ⟨t, ht⟩
  have hmin := hminimal ti
  have hnonneg (j : Nat) :
      0 ≤ OuterTrajectoryConcrete.stepCertificate sys
        (OuterTrajectoryConcrete.trajectory sys R0 j) := by
    unfold OuterTrajectoryConcrete.stepCertificate Tracking.certificate
    have hBj : 0 ≤ (OuterTrajectoryConcrete.trajectory sys R0 j).B :=
      OuterTrajectoryConcrete.trajectory_B_nonneg hell.le sys R0 hB0 j
    have hd : 0 ≤ vecSq
        (OuterTrajectoryConcrete.stepDisplacement sys
          (OuterTrajectoryConcrete.trajectory sys R0 j)) :=
      Tracking.vecSq_nonneg _
    positivity
  have hsq :
      OuterTrajectoryConcrete.stepCertificate sys
          (OuterTrajectoryConcrete.trajectory sys R0 ts.1) ^ 2 ≤
        OuterTrajectoryConcrete.stepCertificate sys
          (OuterTrajectoryConcrete.trajectory sys R0 ti.1) ^ 2 := by
    nlinarith [hnonneg ts.1, hnonneg ti.1]
  have hcert :
      OuterTrajectoryConcrete.stepCertificate sys
          (OuterTrajectoryConcrete.trajectory sys R0 ts.1) ^ 2 ≤ eps ^ 2 / 4 :=
    hsq.trans (hsmall.trans hcertificateBudget)
  exact OuterTrajectoryConcrete.original_OS_of_small_certificate
    hell hr heps hweak hweakR hexists hYnorm hmax hmaxR sys
    (OuterTrajectoryConcrete.trajectory sys R0 ts.1)
    (OuterTrajectoryConcrete.trajectory_B_nonneg hell.le sys R0 hB0 ts.1)
    (OuterTrajectoryConcrete.trajectory_energy_le_B hX hell hr hrle sys R0 hE0 ts.1)
    hcert hbiasBudget

set_option maxHeartbeats 3000000 in
/- The reply-driven prefix returns the same explicit earliest certificate
minimizer as the analytical homotopy/outer trajectory.  In particular, the
selected index is computed only from the finite transcript. -/
theorem eval_schedulePrefixProgram_is_OS {m n : Nat}
    {ell D Delta eps : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzeroY : (0 : EVec n) ∈ P.Y)
    (hx0 : P.x0 = 0) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection P.X projectX)
    (hprojY : IsEuclideanProjection P.Y projectY)
    (hzeroX : (0 : EVec m) ∈ P.X) :
    IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (Oracle.Program.eval P
        (schedulePrefixProgram ell D Delta eps hP.ell_pos hP.D_pos
          hP.Delta_pos heps projectX projectY hprojX hprojY
          hzeroX hzeroY)).1.z := by
  let systems := sharedSystemFamily hP projectX projectY hprojX hprojY
  let J := scheduleStage ell D eps hP.ell_pos hP.D_pos heps
  let r := scheduleCurvature ell D eps hP.ell_pos hP.D_pos heps
  let T := scheduleIterations ell D Delta eps hP.ell_pos hP.D_pos heps
  have hT : 0 < T := by
    dsimp [T]
    exact scheduleIterations_pos hP.ell_pos hP.D_pos hP.Delta_pos heps
  let S0 : RelativeFOAMContraction.ValidState (m := m) P.Y :=
    HomotopyRun.startupState (systems 0) hzeroY
  let B0 : ℝ := 8 * (Delta + (ell / 8) * D ^ 2)
  let R0 : OuterTrajectoryConcrete.Snapshot (m := m) P.Y :=
    HomotopyRun.homotopySnapshot (D := D) (B0 := B0)
      systems P.x0 S0 J
  let R0f : FeasibleSnapshot P.X P.Y :=
    ⟨R0, by simpa [R0, hx0] using hzeroX⟩
  let data : FeasibleTrajectory T P.X P.Y :=
    Oracle.Program.eval P
      (trajectoryProgram (r := r) hP.ell_pos projectX projectY
        hprojX hprojY T R0f)
  let ts : Fin T := selectedTrajectoryIndex hT ell projectX data
  have hprefix :
      (Oracle.Program.eval P
        (schedulePrefixProgram ell D Delta eps hP.ell_pos hP.D_pos
          hP.Delta_pos heps projectX projectY hprojX hprojY
          hzeroX hzeroY)).1 = (data ts).1 := by
    simp only [schedulePrefixProgram, Oracle.Program.eval_bind,
      Oracle.Program.eval_ask, Oracle.Program.eval_pure]
    rw [eval_startupProgram_eq_system hP projectX projectY hprojX hprojY
      hzeroY hx0]
    rw [eval_homotopyProgram_eq_system hP projectX projectY hprojX hprojY]
    let Rprog : FeasibleSnapshot P.X P.Y :=
      ⟨{ z := 0
         state := HomotopyRun.homotopyState systems 0 S0 J
         B := Tracking.homotopyMajorant (ell / 8) (D ^ 2) B0 J }, hzeroX⟩
    have hRprog : Rprog = R0f := by
      apply Subtype.ext
      simp [Rprog, R0f, R0, S0, B0, HomotopyRun.homotopySnapshot, hx0]
    change (Oracle.Program.eval P
      (trajectoryProgram (r := r) hP.ell_pos projectX projectY
        hprojX hprojY T Rprog)
      (selectedTrajectoryIndex _ ell projectX
        (Oracle.Program.eval P
          (trajectoryProgram (r := r) hP.ell_pos projectX projectY
            hprojX hprojY T Rprog)))).1 = (data ts).1
    rw [hRprog]
  have hAt (i : Fin T) :
      (data i).1 = OuterTrajectoryConcrete.trajectory (systems J) R0 i.1 := by
    dsimp only [data]
    simpa only [systems, r, scheduleCurvature] using
      (eval_trajectoryProgram_at hP projectX projectY hprojX hprojY
        J T R0f i)
  have hminimal (s : Fin T) :
      OuterTrajectoryConcrete.stepCertificate (systems J)
          (OuterTrajectoryConcrete.trajectory (systems J) R0 ts.1) ≤
        OuterTrajectoryConcrete.stepCertificate (systems J)
          (OuterTrajectoryConcrete.trajectory (systems J) R0 s.1) := by
    rw [← hAt ts, ← hAt s]
    simpa [computableCertificate, OuterTrajectoryConcrete.stepCertificate,
      OuterTrajectoryConcrete.stepDisplacement, OuterTrajectoryConcrete.readout,
      systems, sharedSystemFamily, outerSystemWithProjections] using
      (selectedTrajectoryIndex_minimal hT ell projectX data s)
  have hr : 0 < r := by
    dsimp [r]
    exact scheduleCurvature_pos hP.ell_pos hP.D_pos heps
  have hrupper : r ≤ UniformSchedule.targetCurvature ell D eps := by
    dsimp [r, scheduleCurvature, J, scheduleStage, scheduleTarget]
    exact HomotopySchedule.homotopyStage_spec
      (div_pos hP.ell_pos (by norm_num))
      (UniformSchedule.targetCurvature_pos hP.ell_pos hP.D_pos heps)
  have hrle : r ≤ ell / 8 := by
    dsimp [r]
    exact scheduleCurvature_le hP.ell_pos hP.D_pos heps
  have hinit := HomotopyRun.initialized_homotopy_snapshot hP hzeroY systems J
  have hE0 : OuterTrajectoryConcrete.snapshotEnergy (systems J) R0 ≤ R0.B := by
    simpa [R0, S0, B0] using hinit.1
  have hB0 : 0 ≤ R0.B := by
    simpa [R0, S0, B0] using hinit.2.1
  have hBupper : R0.B ≤ 15 * (Delta + r * D ^ 2) := by
    simpa [R0, S0, B0, r, J, scheduleCurvature] using hinit.2.2
  have hpotential :
      OuterTrajectoryConcrete.snapshotPotential (systems J) R0 -
          InitialGapBounds.regularizedClassLower P r D ≤
        31 * (Delta + r * D ^ 2) := by
    exact InitialGapBounds.initial_snapshot_potential_bound hP hzeroY hr.le
      (systems J) R0 (by simp [R0]) hBupper
  have hcoeff : 0 ≤ 32 * ell / (T : ℝ) := by
    have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
    exact div_nonneg (mul_nonneg (by norm_num) hP.ell_pos.le) hTreal.le
  have hcertificateCompare :
      32 * ell / (T : ℝ) *
          (OuterTrajectoryConcrete.snapshotPotential (systems J) R0 -
            InitialGapBounds.regularizedClassLower P r D) ≤
        32 * ell / (T : ℝ) * (31 * (Delta + r * D ^ 2)) :=
    mul_le_mul_of_nonneg_left hpotential hcoeff
  have hTpaper : T =
      UniformSchedule.paperOuterIterations ell Delta r D eps := by
    rfl
  have hcertificate :
      32 * ell / (T : ℝ) *
          (OuterTrajectoryConcrete.snapshotPotential (systems J) R0 -
            InitialGapBounds.regularizedClassLower P r D) ≤ eps ^ 2 / 4 := by
    have hcomparePaper := hcertificateCompare
    rw [hTpaper] at hcomparePaper
    exact le_of_lt (UniformSchedule.paper_certificate_budget hP.ell_pos
      hP.Delta_pos hr.le heps hcomparePaper)
  have hbias : 2 * ell * r * D ^ 2 ≤ eps ^ 2 / 4 :=
    UniformSchedule.homotopy_output_bias_budget hP.ell_pos hP.D_pos heps
      hr hrupper
  have hweak : IsWeaklyConvexOn ell P.X (ValueOn P.Y P.f) := by
    simpa [IsWeaklyConvexOn, quadraticCorrection] using hP.value_weakConvexity
  have hweakR : IsWeaklyConvexOn ell P.X
      (DualRegularizedValueOn P.Y P.f r) :=
    NCCLowerBoundVerification.Upper.IsNCCClass.regularizedValue_weaklyConvex hP
  let hexists : HasProxEverywhere P.X (ValueOn P.Y P.f) ell :=
    NCCLowerBoundVerification.Upper.IsNCCClass.value_hasProxEverywhere hP
  have hlower : ∀ z, InitialGapBounds.regularizedClassLower P r D ≤
      OuterTrajectoryConcrete.regularizedEnvelope P.X P.Y P.f ell r
        (sharedProxFamily hP J) z := by
    intro z
    exact InitialGapBounds.regularizedClassLower_le_envelope hP hzeroY hr.le
      hP.ell_pos.le (sharedProxFamily hP J) z
  have hYnorm : ∀ y ∈ P.Y, vecSq y ≤ D ^ 2 :=
    NCCLowerBoundVerification.Upper.IsNCCClass.dual_vecSq_le hP hzeroY
  have hmax : ∀ x, ∃ y, IsMaximizerOn P.Y P.f x y :=
    NCCLowerBoundVerification.Upper.IsNCCClass.maximum_attained_everywhere hP
  have hmaxR : ∀ x, ∃ y, IsMaximizerOn P.Y
      (fun u v => P.f u v - r / 2 * vecSq v) x y :=
    NCCLowerBoundVerification.Upper.IsNCCClass.regularized_maximum_attained hP
  have hselected := minimumCertificateAnchor_is_OS hP.X_nonempty hP.ell_pos
    hr hrle heps.le hweak hweakR hexists hYnorm hmax hmaxR
    (systems J) R0 hE0 hB0 hT hlower hcertificate hbias ts hminimal
  rw [hprefix]
  rw [hAt ts]
  exact hselected

/-! ## Literal query budget -/

/-- A `rho = 1/400` outer block contains at least two macrosteps.  This small
lower bound is what lets the first outer block in the printed accounting pay
for both the causal startup solve and the mandatory origin query. -/
theorem two_le_outerBlockIterations {ell r : ℝ} (hell : 0 < ell)
    (hr : 0 < r) (hrle : r ≤ ell / 8) :
    2 ≤ blockIterations (alpha ell r) (1 / 400 : ℝ) := by
  let a := alpha ell r
  have ha : 0 < a := by
    dsimp [a]
    exact alpha_pos hell hr
  have ha1 : a ≤ 1 := by
    dsimp [a]
    exact alpha_le_one hell hr.le hrle
  have hlog : (1 : ℝ) ≤ Real.log 400 := by
    rw [← Real.exp_le_exp]
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 400)]
    exact (le_of_lt Real.exp_one_lt_three).trans (by norm_num)
  have htwoDiv : (2 : ℝ) ≤ 2 / a := by
    rw [le_div_iff₀ ha]
    nlinarith
  have harg : (2 : ℝ) ≤ 2 / a * Real.log (1 / (1 / 400 : ℝ)) := by
    rw [show (1 / (1 / 400 : ℝ)) = 400 by norm_num]
    calc
      (2 : ℝ) ≤ 2 / a := htwoDiv
      _ = 2 / a * 1 := by ring
      _ ≤ 2 / a * Real.log 400 :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
  have hceil : 2 / a * Real.log (1 / (1 / 400 : ℝ)) ≤
      (blockIterations a (1 / 400 : ℝ) : ℝ) :=
    Nat.le_ceil _
  have hreal : (2 : ℝ) ≤
      (blockIterations a (1 / 400 : ℝ) : ℝ) := harg.trans hceil
  exact_mod_cast hreal

/-- The exact causal query count fits inside the already published assembled
cost: the executable outer prefix uses `T-1` blocks, leaving one block to
absorb startup and the origin query. -/
theorem sharedOracleCalls_le_assembledCost
    (ell D Delta eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps) :
    sharedOracleCalls ell D Delta eps hell hD heps ≤
      (UniformCost.assembledCost ell (ell / 8)
        (scheduleCurvature ell D eps hell hD heps)
        (scheduleStage ell D eps hell hD heps)
        (scheduleIterations ell D Delta eps hell hD heps)).oracleCalls := by
  let J := scheduleStage ell D eps hell hD heps
  let r := scheduleCurvature ell D eps hell hD heps
  let T := scheduleIterations ell D Delta eps hell hD heps
  let M := feasibleMicroIterations + 1
  let K := blockIterations (alpha ell r) (1 / 400 : ℝ)
  let C := K * M
  let H := causalHomotopyCalls ell J
  have hr : 0 < r := by
    dsimp [r]
    exact scheduleCurvature_pos hell hD heps
  have hrle : r ≤ ell / 8 := by
    dsimp [r]
    exact scheduleCurvature_le hell hD heps
  have hK : 2 ≤ K := by
    dsimp [K]
    exact two_le_outerBlockIterations hell hr hrle
  have hM : 1 ≤ M := by
    dsimp [M]
    omega
  have hstartup : 1 + M ≤ C := by
    calc
      1 + M ≤ 2 * M := by omega
      _ ≤ K * M := Nat.mul_le_mul_right M hK
      _ = C := rfl
  have hT : 0 < T := by
    dsimp [T]
    exact scheduleIterations_pos hell hD hDelta heps
  have hTsplit : T = (T - 1) + 1 := by omega
  have hshared :
      sharedOracleCalls ell D Delta eps hell hD heps =
        1 + M + H + (T - 1) * C + 1 := by
    simp [sharedOracleCalls, prefixCalls, outerPrefixCalls,
      J, r, T, M, K, C, H, Nat.mul_assoc]
  have hcost :
      (UniformCost.assembledCost ell (ell / 8) r J T).oracleCalls =
        H + T * C + 1 := by
    simp only [UniformCost.assembledCost,
      OuterTrajectoryConcrete.outerTrajectoryCost_oracleCalls]
    rw [← causalHomotopyCalls_eq ell J]
    simp [H, C, K, M, Nat.mul_assoc, Nat.add_assoc]
  change sharedOracleCalls ell D Delta eps hell hD heps ≤
    (UniformCost.assembledCost ell (ell / 8) r J T).oracleCalls
  rw [hshared, hcost]
  calc
    1 + M + H + (T - 1) * C + 1 =
        H + (T - 1) * C + (1 + M) + 1 := by omega
    _ ≤ H + (T - 1) * C + C + 1 := by omega
    _ = H + T * C + 1 := by
      rw [hTsplit]
      simp [Nat.add_mul, Nat.add_assoc]

/-! ## Domain-free success theorem -/

/-- Transport the prefix theorem across the domain equalities carried by a
member of the domain-labelled class. -/
theorem eval_schedulePrefixProgram_is_OS_of_matches {m n : Nat}
    {ell D Delta eps : ℝ} {P : NCCInstance m n}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hPX : P.X = X) (hPY : P.Y = Y)
    (hP : IsNCCClass ell D Delta P) (hx0 : P.x0 = 0) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (Oracle.Program.eval P
        (schedulePrefixProgram ell D Delta eps hP.ell_pos hP.D_pos
          hP.Delta_pos heps projectX projectY hprojX hprojY
          hzeroX hzeroY)).1.z := by
  subst X
  subst Y
  exact eval_schedulePrefixProgram_is_OS hP hzeroY hx0 heps
    projectX projectY hprojX hprojY hzeroX

/-- The compiled causal component reaches its explicit selected anchor before
the published assembled oracle horizon, uniformly over every objective on
the same admissible domains. -/
theorem sharedDomainAlgorithm_solvesWithin
    (ell D Delta eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps) :
    Oracle.SolvesWithin
      (sharedDomainAlgorithm ell D Delta eps hell hD hDelta heps)
      ell D Delta eps
      (UniformCost.assembledCost ell (ell / 8)
        (scheduleCurvature ell D eps hell hD heps)
        (scheduleStage ell D eps hell hD heps)
        (scheduleIterations ell D Delta eps hell hD heps)).oracleCalls := by
  intro Q P hmember
  rcases hmember with ⟨hPX, hPY, hx0, hP⟩
  let t := prefixCalls ell D Delta eps hell hD heps
  let budget := (UniformCost.assembledCost ell (ell / 8)
    (scheduleCurvature ell D eps hell hD heps)
    (scheduleStage ell D eps hell hD heps)
    (scheduleIterations ell D Delta eps hell hD heps)).oracleCalls
  have hcalls : sharedOracleCalls ell D Delta eps hell hD heps ≤ budget := by
    dsimp [budget]
    exact sharedOracleCalls_le_assembledCost ell D Delta eps hell hD hDelta heps
  have htFull : t < sharedOracleCalls ell D Delta eps hell hD heps := by
    simp [t, sharedOracleCalls]
  have ht : t < budget := htFull.trans_le hcalls
  refine ⟨t, ht, ?_⟩
  have hquery := queriedAt_sharedComponent_final ell D Delta eps hell hD
    hDelta heps (domainProjectX Q) (domainProjectY Q)
    (domainProjectX_spec Q) (domainProjectY_spec Q)
    Q.zero_mem_X Q.zero_mem_Y P
  have hquery' :
      Oracle.DeterministicFOComponent.queriedAt
          (sharedComponent ell D Delta eps hell hD hDelta heps Q) P t =
        ((Oracle.Program.eval P
          (schedulePrefixProgram ell D Delta eps hell hD hDelta heps
            (domainProjectX Q) (domainProjectY Q)
            (domainProjectX_spec Q) (domainProjectY_spec Q)
            Q.zero_mem_X Q.zero_mem_Y)).1.z, (0 : EVec Q.n)) := by
    simpa [sharedComponent, t] using hquery
  unfold Oracle.DeterministicFOComponent.HitsAt
  change IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
    ((Oracle.DeterministicFOComponent.queriedAt
      (sharedComponent ell D Delta eps hell hD hDelta heps Q) P t).1)
  rw [hquery']
  exact eval_schedulePrefixProgram_is_OS_of_matches hPX hPY hP hx0 heps
    (domainProjectX Q) (domainProjectY Q)
    (domainProjectX_spec Q) (domainProjectY_spec Q)
    Q.zero_mem_X Q.zero_mem_Y

/-- A single domain-wise causal algorithm witnesses the formal upper oracle
complexity threshold. -/
theorem complexityAtMost_sharedOracle
    (ell D Delta eps : ℝ) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps) :
    Oracle.ComplexityAtMost ell D Delta eps
      (UniformCost.assembledCost ell (ell / 8)
        (scheduleCurvature ell D eps hell hD heps)
        (scheduleStage ell D eps hell hD heps)
        (scheduleIterations ell D Delta eps hell hD heps)).oracleCalls := by
  exact ⟨sharedDomainAlgorithm ell D Delta eps hell hD hDelta heps,
    sharedDomainAlgorithm_solvesWithin ell D Delta eps hell hD hDelta heps⟩

end

end SharedOracle
end Upper
end NCCLowerBoundVerification
