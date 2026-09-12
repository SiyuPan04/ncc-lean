import NCCLowerBoundVerification.Oracle.Model

/-!
# Domain-free deterministic complexity

The TeX takes an infimum over domain-wise algorithms and a supremum over the
disjoint union of domain-labelled problems.  For the finite upper and lower
bounds it is cleaner—and avoids arithmetic with `∞`—to use the equivalent
threshold predicates below:

* `ComplexityAtMost ... T` says that one objective-independent domain-wise
  algorithm hits every class member among its first `T` queries;
* `ComplexityAtLeast ... K` says that every such algorithm has a class member
  on which its first `K` queries all fail.

The domains, and their proofs of admissibility, are the only input to an
algorithm component.  In particular, neither an objective nor a proof that it
belongs to the class can occur in the component's query rule.
-/

namespace NCCLowerBoundVerification
namespace Oracle

noncomputable section

/-- A domain label in the disjoint union defining the paper's
`F_domain`.  The origins are included because every domain-free trajectory is
initialized at the full primal-dual origin. -/
structure AdmissibleDomainPair where
  m : Nat
  n : Nat
  X : Set (EVec m)
  Y : Set (EVec n)
  zero_mem_X : (0 : EVec m) ∈ X
  zero_mem_Y : (0 : EVec n) ∈ Y
  X_closed : IsClosed X
  X_convex : Convex ℝ X
  Y_closed : IsClosed Y
  Y_convex : Convex ℝ Y

/-- A single collection of causal components, one for every admissible domain
label.  This is Definition `def:det-alg` without its unused measurability
clause; causality is enforced by each component's reply-history type. -/
structure DomainWiseDeterministicAlgorithm where
  component : (Q : AdmissibleDomainPair) →
    DeterministicFOComponent Q.X Q.Y

/-- Membership in the domain-labelled disjoint union `F_domain`. -/
def IsDomainFreeMember (ell D Delta : ℝ) (Q : AdmissibleDomainPair)
    (P : NCCInstance Q.m Q.n) : Prop :=
  P.X = Q.X ∧ P.Y = Q.Y ∧ P.x0 = 0 ∧ IsNCCClass ell D Delta P

/-- Literal queried-iterate hitting time from the TeX, with `⊤` for a
trajectory that never hits. -/
def queriedHittingTime {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    (A : DeterministicFOComponent X Y) (P : NCCInstance m n)
    (ell eps : ℝ) : WithTop Nat := by
  classical
  exact if h : A.EventuallyHits P ell eps then
      (Nat.find h : WithTop Nat)
    else
      ⊤

theorem queriedHittingTime_lt_iff {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (A : DeterministicFOComponent X Y) (P : NCCInstance m n)
    (ell eps : ℝ) (T : Nat) :
    queriedHittingTime A P ell eps < (T : WithTop Nat) ↔
      A.HitsWithin P ell eps T := by
  classical
  constructor
  · intro htime
    by_cases h : A.EventuallyHits P ell eps
    · have hfind : Nat.find h < T := by
        simpa [queriedHittingTime, h] using htime
      exact ⟨Nat.find h, hfind, Nat.find_spec h⟩
    · simp [queriedHittingTime, h] at htime
  · rintro ⟨t, ht, hhit⟩
    have h : A.EventuallyHits P ell eps := ⟨t, hhit⟩
    have hmin : Nat.find h ≤ t := Nat.find_min' h hhit
    have hfind : Nat.find h < T := hmin.trans_lt ht
    simpa [queriedHittingTime, h] using hfind

theorem IsDomainFreeMember.matchesInstance {ell D Delta : ℝ}
    {Q : AdmissibleDomainPair} {P : NCCInstance Q.m Q.n}
    (A : DeterministicFOComponent Q.X Q.Y)
    (hP : IsDomainFreeMember ell D Delta Q P) :
    DeterministicFOComponent.MatchesInstance A P := by
  exact ⟨hP.1, hP.2.1⟩

/-- One fixed algorithm succeeds uniformly on the domain-free class within a
literal number of local-oracle queries. -/
def SolvesWithin (A : DomainWiseDeterministicAlgorithm)
    (ell D Delta eps : ℝ) (T : Nat) : Prop :=
  ∀ (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
    IsDomainFreeMember ell D Delta Q P →
      DeterministicFOComponent.HitsWithin (A.component Q) P ell eps T

/-- Threshold form of the upper deterministic oracle complexity. -/
def ComplexityAtMost (ell D Delta eps : ℝ) (T : Nat) : Prop :=
  ∃ A : DomainWiseDeterministicAlgorithm,
    SolvesWithin A ell D Delta eps T

/-- Threshold form of the lower deterministic oracle complexity. -/
def ComplexityAtLeast (ell D Delta eps : ℝ) (K : Nat) : Prop :=
  ∀ A : DomainWiseDeterministicAlgorithm,
    ∃ (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
      IsDomainFreeMember ell D Delta Q P ∧
        DeterministicFOComponent.FailsWithin (A.component Q) P ell eps K

/-- The lower threshold is exactly a uniform negation of solving within the
same strict horizon. -/
theorem complexityAtLeast_iff {ell D Delta eps : ℝ} {K : Nat} :
    ComplexityAtLeast ell D Delta eps K ↔
      ∀ A : DomainWiseDeterministicAlgorithm,
        ¬ SolvesWithin A ell D Delta eps K := by
  constructor
  · intro hlower A hsolve
    obtain ⟨Q, P, hmem, hfail⟩ := hlower A
    exact (DeterministicFOComponent.failsWithin_iff_not_hitsWithin
      (A.component Q) P ell eps K).1 hfail (hsolve Q P hmem)
  · intro h A
    by_contra hnone
    push Not at hnone
    apply h A
    intro Q P hmem
    by_contra hnot
    have hfail : DeterministicFOComponent.FailsWithin
        (A.component Q) P ell eps K :=
      (DeterministicFOComponent.failsWithin_iff_not_hitsWithin
        (A.component Q) P ell eps K).2 hnot
    exact hnone Q P hmem hfail

end

end Oracle
end NCCLowerBoundVerification
