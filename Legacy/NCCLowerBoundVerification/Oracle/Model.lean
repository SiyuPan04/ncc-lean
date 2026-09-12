import NCCLowerBoundVerification.Basic

/-!
# The deterministic local first-order oracle model

This module formalizes Definitions `def:oracle` and `def:det-alg` of
`Upper+Lower_unified_lower.tex`.

At time `t`, a domain component receives a value of type
`ReplyHistory m n t = Fin t → OracleReply m n`.  Thus its next query can use
exactly the replies numbered `0, ..., t - 1`; it cannot inspect the objective
in any other way.  Causality is consequently enforced by the type rather than
asserted as an external predicate.

The paper additionally calls the causal maps measurable.  The finite-horizon
deterministic lower-bound argument uses only causality and feasibility, not
measurability.  We therefore retain precisely those operational properties and
avoid unrelated measure-theoretic proof obligations.
-/

namespace NCCLowerBoundVerification
namespace Oracle

noncomputable section

/-- A feasible point at which a local first-order oracle may be queried. -/
abbrev Query (m n : Nat) := EVec m × EVec n

/-- The three pieces of information returned by the paper's local oracle. -/
structure OracleReply (m n : Nat) where
  value : ℝ
  gradX : EVec m
  gradY : EVec n

/-- Definition `def:oracle`: value and both partial gradients at one query. -/
def firstOrderOracle {m n : Nat} (P : NCCInstance m n)
    (q : Query m n) : OracleReply m n where
  value := P.f q.1 q.2
  gradX := P.gradX q.1 q.2
  gradY := P.gradY q.1 q.2

@[simp] theorem firstOrderOracle_value {m n : Nat} (P : NCCInstance m n)
    (q : Query m n) : (firstOrderOracle P q).value = P.f q.1 q.2 := rfl

@[simp] theorem firstOrderOracle_gradX {m n : Nat} (P : NCCInstance m n)
    (q : Query m n) : (firstOrderOracle P q).gradX = P.gradX q.1 q.2 := rfl

@[simp] theorem firstOrderOracle_gradY {m n : Nat} (P : NCCInstance m n)
    (q : Query m n) : (firstOrderOracle P q).gradY = P.gradY q.1 q.2 := rfl

/-- The complete information available immediately before query `t`. -/
abbrev ReplyHistory (m n t : Nat) := Fin t → OracleReply m n

/-- The unique empty oracle history. -/
def emptyHistory (m n : Nat) : ReplyHistory m n 0 :=
  Fin.elim0

/--
One component of a domain-wise deterministic first-order algorithm.

The component is indexed only by the two domains, not by an objective.  Its
query rule receives only a finite oracle history.  Requiring `next_mem` for
every possible history ensures that all queries, including counterfactual
ones, are feasible.  The last field implements the paper's full primal--dual
origin initialization.
-/
structure DeterministicFOComponent {m n : Nat}
    (X : Set (EVec m)) (Y : Set (EVec n)) where
  nextQuery : (t : Nat) → ReplyHistory m n t → Query m n
  next_mem : ∀ (t : Nat) (history : ReplyHistory m n t),
    (nextQuery t history).1 ∈ X ∧ (nextQuery t history).2 ∈ Y
  initial_query : nextQuery 0 (emptyHistory m n) = (0, 0)

namespace DeterministicFOComponent

variable {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}

/--
The recursively generated queried iterate.  Recursive calls are only at
indices stored in `Fin t`, hence strictly before `t`.
-/
def queriedAt (A : DeterministicFOComponent X Y) (P : NCCInstance m n)
    (t : Nat) : Query m n :=
  A.nextQuery t fun i => firstOrderOracle P (queriedAt A P i)
termination_by t
decreasing_by exact i.isLt

/-- The oracle reply observed at a recursively generated queried iterate. -/
def replyAt (A : DeterministicFOComponent X Y) (P : NCCInstance m n)
    (t : Nat) : OracleReply m n :=
  firstOrderOracle P (queriedAt A P t)

/-- The queried oracle transcript strictly before time `t`. -/
def queriedTranscript (A : DeterministicFOComponent X Y) (P : NCCInstance m n)
    (t : Nat) : ReplyHistory m n t :=
  fun i => replyAt A P i

/-- Unfolding the recursion exposes exactly the causal history seen at `t`. -/
theorem queriedAt_eq_nextQuery (A : DeterministicFOComponent X Y)
    (P : NCCInstance m n) (t : Nat) :
    queriedAt A P t = A.nextQuery t (queriedTranscript A P t) := by
  rw [queriedAt]
  rfl

/-- Every recursively generated query is feasible for the component's domains. -/
theorem queriedAt_mem (A : DeterministicFOComponent X Y)
    (P : NCCInstance m n) (t : Nat) :
    (queriedAt A P t).1 ∈ X ∧ (queriedAt A P t).2 ∈ Y := by
  rw [queriedAt_eq_nextQuery]
  exact A.next_mem t (queriedTranscript A P t)

/-- The recursively generated trajectory starts at the full origin. -/
@[simp] theorem queriedAt_zero (A : DeterministicFOComponent X Y)
    (P : NCCInstance m n) : queriedAt A P 0 = (0, 0) := by
  rw [queriedAt]
  convert A.initial_query

/-- Compatibility of a domain component with a problem instance. -/
def MatchesInstance (_A : DeterministicFOComponent X Y)
    (P : NCCInstance m n) : Prop :=
  P.X = X ∧ P.Y = Y

/-- A compatible component's queried iterates are feasible for the instance. -/
theorem queriedAt_mem_instance (A : DeterministicFOComponent X Y)
    (P : NCCInstance m n) (hmatch : MatchesInstance A P) (t : Nat) :
    (queriedAt A P t).1 ∈ P.X ∧ (queriedAt A P t).2 ∈ P.Y := by
  rw [hmatch.1, hmatch.2]
  exact queriedAt_mem A P t

/-- The primal coordinate queried at time `t` satisfies the paper's OS test. -/
def HitsAt (A : DeterministicFOComponent X Y) (P : NCCInstance m n)
    (ell eps : ℝ) (t : Nat) : Prop :=
  IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
    (queriedAt A P t).1

/-- Some one of the first `T` queried primal iterates passes the OS test. -/
def HitsWithin (A : DeterministicFOComponent X Y) (P : NCCInstance m n)
    (ell eps : ℝ) (T : Nat) : Prop :=
  ∃ t < T, HitsAt A P ell eps t

/-- None of the first `T` queried primal iterates passes the OS test. -/
def FailsWithin (A : DeterministicFOComponent X Y) (P : NCCInstance m n)
    (ell eps : ℝ) (T : Nat) : Prop :=
  ∀ t < T, ¬ HitsAt A P ell eps t

/-- Failure for a finite query budget is exactly the negation of hitting. -/
theorem failsWithin_iff_not_hitsWithin (A : DeterministicFOComponent X Y)
    (P : NCCInstance m n) (ell eps : ℝ) (T : Nat) :
    FailsWithin A P ell eps T ↔ ¬ HitsWithin A P ell eps T := by
  constructor
  · intro hfail ⟨t, ht, hhit⟩
    exact hfail t ht hhit
  · intro hnot t ht hhit
    exact hnot ⟨t, ht, hhit⟩

/-- The trajectory eventually queries a primal point passing the OS test. -/
def EventuallyHits (A : DeterministicFOComponent X Y) (P : NCCInstance m n)
    (ell eps : ℝ) : Prop :=
  ∃ t, HitsAt A P ell eps t

end DeterministicFOComponent

end

end Oracle
end NCCLowerBoundVerification
