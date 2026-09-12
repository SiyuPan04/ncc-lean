import NCCLowerBoundVerification.Oracle.Complexity

/-!
# Raw causal maps and all-history feasibility

The manuscript requires feasible actual oracle runs. The typed algorithm
model additionally requires feasibility on every finite reply history,
including counterfactual histories. `originRepair` makes that strengthening
without changing any feasible actual run: only an infeasible proposed query
is replaced by the known feasible origin. All values and both gradients in
the actual transcript are therefore preserved exactly.
-/

namespace NCC.Lower.UniformResisting

noncomputable section

set_option backward.isDefEq.respectTransparency false

open NCCLowerBoundVerification Oracle

/-- A raw deterministic rule with the manuscript's full-origin start, but
without a counterfactual-history feasibility requirement. -/
structure RawComponent (m n : ℕ) where
  nextQuery : (t : ℕ) → ReplyHistory m n t → Query m n
  initial_query : nextQuery 0 (emptyHistory m n) = (0, 0)

namespace RawComponent

def queriedAt {m n : ℕ} (A : RawComponent m n) (P : NCCInstance m n) (t : ℕ) : Query m n :=
  A.nextQuery t (fun i => firstOrderOracle P (queriedAt A P i))
termination_by t
decreasing_by exact i.isLt

def queriedTranscript {m n : ℕ} (A : RawComponent m n) (P : NCCInstance m n) (t : ℕ) :
    ReplyHistory m n t := fun i => firstOrderOracle P (A.queriedAt P i)

theorem queriedAt_eq_nextQuery {m n : ℕ} (A : RawComponent m n) (P : NCCInstance m n) (t : ℕ) :
    A.queriedAt P t = A.nextQuery t (A.queriedTranscript P t) := by
  rw [queriedAt]
  rfl

@[simp] theorem queriedAt_zero {m n : ℕ} (A : RawComponent m n) (P : NCCInstance m n) :
    A.queriedAt P 0 = (0, 0) := by
  rw [queriedAt]
  convert A.initial_query

def FeasibleOn {m n : ℕ} (A : RawComponent m n) (P : NCCInstance m n)
    (X : Set (EVec m)) (Y : Set (EVec n)) : Prop :=
  ∀ t, (A.queriedAt P t).1 ∈ X ∧ (A.queriedAt P t).2 ∈ Y

/-- Repair uses the known domains and a finite reply history only. -/
def originRepair {m n : ℕ} (A : RawComponent m n)
    {X : Set (EVec m)} {Y : Set (EVec n)} (hx0 : (0 : EVec m) ∈ X) (hy0 : (0 : EVec n) ∈ Y) :
    DeterministicFOComponent X Y := by
  classical
  exact {
    nextQuery := fun t hist =>
      if (A.nextQuery t hist).1 ∈ X ∧ (A.nextQuery t hist).2 ∈ Y
      then A.nextQuery t hist else (0, 0)
    next_mem := by
      intro t hist
      split_ifs with h
      · exact h
      · exact ⟨hx0, hy0⟩
    initial_query := by simp [A.initial_query, hx0, hy0] }

theorem originRepair_nextQuery_of_feasible {m n : ℕ} (A : RawComponent m n)
    {X : Set (EVec m)} {Y : Set (EVec n)} (hx0 : (0 : EVec m) ∈ X) (hy0 : (0 : EVec n) ∈ Y)
    (t : ℕ) (hist : ReplyHistory m n t)
    (h : (A.nextQuery t hist).1 ∈ X ∧ (A.nextQuery t hist).2 ∈ Y) :
    (A.originRepair hx0 hy0).nextQuery t hist = A.nextQuery t hist := by
  simp [originRepair, h]

/-- Finite-horizon equality needs feasibility only during that same
horizon, and does not impose any condition on other objectives or runs. -/
theorem originRepair_queriedAt_eq_of_feasible_before {m n K : ℕ} (A : RawComponent m n)
    {X : Set (EVec m)} {Y : Set (EVec n)} (hx0 : (0 : EVec m) ∈ X) (hy0 : (0 : EVec n) ∈ Y)
    (P : NCCInstance m n)
    (hfeasible : ∀ t < K, (A.queriedAt P t).1 ∈ X ∧ (A.queriedAt P t).2 ∈ Y)
    {t : ℕ} (ht : t < K) : (A.originRepair hx0 hy0).queriedAt P t = A.queriedAt P t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
      have hhist : (A.originRepair hx0 hy0).queriedTranscript P t = A.queriedTranscript P t := by
        funext i
        change firstOrderOracle P ((A.originRepair hx0 hy0).queriedAt P i) =
          firstOrderOracle P (A.queriedAt P i)
        rw [ih i i.isLt (i.isLt.trans ht)]
      rw [DeterministicFOComponent.queriedAt_eq_nextQuery, hhist, queriedAt_eq_nextQuery]
      apply originRepair_nextQuery_of_feasible
      exact (queriedAt_eq_nextQuery A P t) ▸ hfeasible t ht

theorem originRepair_queriedAt_eq {m n : ℕ} (A : RawComponent m n)
    {X : Set (EVec m)} {Y : Set (EVec n)} (hx0 : (0 : EVec m) ∈ X) (hy0 : (0 : EVec n) ∈ Y)
    (P : NCCInstance m n) (hfeasible : A.FeasibleOn P X Y) (t : ℕ) :
    (A.originRepair hx0 hy0).queriedAt P t = A.queriedAt P t :=
  originRepair_queriedAt_eq_of_feasible_before A hx0 hy0 P
    (fun s _ => hfeasible s) (Nat.lt_succ_self t)

theorem originRepair_queriedTranscript_eq {m n : ℕ} (A : RawComponent m n)
    {X : Set (EVec m)} {Y : Set (EVec n)} (hx0 : (0 : EVec m) ∈ X) (hy0 : (0 : EVec n) ∈ Y)
    (P : NCCInstance m n) (hfeasible : A.FeasibleOn P X Y) (t : ℕ) :
    (A.originRepair hx0 hy0).queriedTranscript P t = A.queriedTranscript P t := by
  funext i
  change firstOrderOracle P ((A.originRepair hx0 hy0).queriedAt P i) =
    firstOrderOracle P (A.queriedAt P i)
  rw [originRepair_queriedAt_eq A hx0 hy0 P hfeasible]

end RawComponent

/-- The raw maps form one family indexed by known domains, not objectives. -/
structure RawDomainWiseAlgorithm where
  component : (Q : AdmissibleDomainPair) → RawComponent Q.m Q.n

def repairAlgorithm (A : RawDomainWiseAlgorithm) : DomainWiseDeterministicAlgorithm where
  component Q := (A.component Q).originRepair Q.zero_mem_X Q.zero_mem_Y

theorem repairAlgorithm_queriedAt_eq (A : RawDomainWiseAlgorithm) (Q : AdmissibleDomainPair)
    (P : NCCInstance Q.m Q.n) (hfeasible : (A.component Q).FeasibleOn P Q.X Q.Y) (t : ℕ) :
    ((repairAlgorithm A).component Q).queriedAt P t = (A.component Q).queriedAt P t :=
  RawComponent.originRepair_queriedAt_eq _ Q.zero_mem_X Q.zero_mem_Y P hfeasible t

/-- One repaired algorithm works simultaneously for every domain and every
objective on which the original raw actual run was feasible. -/
theorem exists_all_history_feasible_equivalent (A : RawDomainWiseAlgorithm) :
    ∃ B : DomainWiseDeterministicAlgorithm,
      ∀ (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
        (A.component Q).FeasibleOn P Q.X Q.Y →
        ∀ t, (B.component Q).queriedAt P t = (A.component Q).queriedAt P t :=
  ⟨repairAlgorithm A, repairAlgorithm_queriedAt_eq A⟩

theorem repairAlgorithm_failure_transfer (A : RawDomainWiseAlgorithm) (Q : AdmissibleDomainPair)
    (P : NCCInstance Q.m Q.n) (hfeasible : (A.component Q).FeasibleOn P Q.X Q.Y)
    {ell eps : ℝ} {K : ℕ}
    (hfail : ((repairAlgorithm A).component Q).FailsWithin P ell eps K) :
    ∀ t < K, ¬ IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      ((A.component Q).queriedAt P t).1 := by
  intro t ht
  have h := hfail t ht
  change ¬ IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
    (((repairAlgorithm A).component Q).queriedAt P t).1 at h
  rw [repairAlgorithm_queriedAt_eq A Q P hfeasible t] at h
  exact h

end

end NCC.Lower.UniformResisting
