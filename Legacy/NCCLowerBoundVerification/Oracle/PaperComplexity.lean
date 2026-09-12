import NCCLowerBoundVerification.PaperClass
import NCCLowerBoundVerification.Oracle.Complexity

/-!
# Domain-free complexity for the literal paper class

`Oracle.Complexity` is the internal analytic formulation used by the upper
bound.  This module states the same threshold predicates for Definition 2.1's
neighborhood-`C^1` class and proves that the analytic upper theorem transfers
through observationally equivalent global representatives.
-/

namespace NCCLowerBoundVerification
namespace Oracle

noncomputable section

/-- Membership in the paper's domain-labelled disjoint union. -/
def IsPaperDomainFreeMember (ell D Delta : ℝ) (Q : AdmissibleDomainPair)
    (P : NCCInstance Q.m Q.n) : Prop :=
  P.X = Q.X ∧ P.Y = Q.Y ∧ P.x0 = 0 ∧ IsPaperNCCClass ell D Delta P

/-- One fixed causal domain-wise algorithm succeeds on every literal paper
class member within the strict query horizon. -/
def PaperSolvesWithin (A : DomainWiseDeterministicAlgorithm)
    (ell D Delta eps : ℝ) (T : Nat) : Prop :=
  ∀ (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
    IsPaperDomainFreeMember ell D Delta Q P →
      DeterministicFOComponent.HitsWithin (A.component Q) P ell eps T

/-- Threshold form of the upper complexity in the exact class from the TeX. -/
def PaperComplexityAtMost (ell D Delta eps : ℝ) (T : Nat) : Prop :=
  ∃ A : DomainWiseDeterministicAlgorithm,
    PaperSolvesWithin A ell D Delta eps T

/-- Threshold form of the lower complexity in the exact class from the TeX. -/
def PaperComplexityAtLeast (ell D Delta eps : ℝ) (K : Nat) : Prop :=
  ∀ A : DomainWiseDeterministicAlgorithm,
    ∃ (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
      IsPaperDomainFreeMember ell D Delta Q P ∧
        DeterministicFOComponent.FailsWithin (A.component Q) P ell eps K

/-- The paper lower threshold is equivalently the assertion that no single
domain-wise causal algorithm solves all paper instances within that horizon. -/
theorem paperComplexityAtLeast_iff {ell D Delta eps : ℝ} {K : Nat} :
    PaperComplexityAtLeast ell D Delta eps K ↔
      ∀ A : DomainWiseDeterministicAlgorithm,
        ¬ PaperSolvesWithin A ell D Delta eps K := by
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

/-- A solver for every global analytic representative also solves every
neighborhood-`C^1` paper instance, because its feasible transcript and OS
predicate are invariant under globalization. -/
theorem paperSolvesWithin_of_solvesWithin
    (A : DomainWiseDeterministicAlgorithm) {ell D Delta eps : ℝ} {T : Nat}
    (hsolve : SolvesWithin A ell D Delta eps T) :
    PaperSolvesWithin A ell D Delta eps T := by
  intro Q P hP
  obtain ⟨hPX, hPY, hx0, hclass⟩ := hP
  obtain ⟨G⟩ := exists_paperGlobalization hclass
  have hglobalMember : IsDomainFreeMember ell D Delta Q G.globalized :=
    ⟨G.X_eq.trans hPX, G.Y_eq.trans hPY, G.x0_eq.trans hx0, G.class_mem⟩
  obtain ⟨t, ht, hhit⟩ := hsolve Q G.globalized hglobalMember
  refine ⟨t, ht, ?_⟩
  have horacle : ∀ x ∈ Q.X, ∀ y ∈ Q.Y,
      firstOrderOracle G.globalized (x, y) = firstOrderOracle P (x, y) := by
    intro x hx y hy
    exact G.oracle_eq_on x (by simpa only [hPX] using hx)
      y (by simpa only [hPY] using hy)
  have hquery : ∀ s,
      DeterministicFOComponent.queriedAt (A.component Q) G.globalized s =
        DeterministicFOComponent.queriedAt (A.component Q) P s :=
    DeterministicFOComponent.queriedAt_eq_of_oracle_eq_on
      (A.component Q) G.globalized P horacle
  unfold DeterministicFOComponent.HitsAt at hhit ⊢
  have hhit' :
      IsOptimizationStationary P.X
        (ValueOn G.globalized.Y G.globalized.f) ell eps
        (DeterministicFOComponent.queriedAt (A.component Q) P t).1 := by
    have htmp :
        IsOptimizationStationary P.X
          (ValueOn G.globalized.Y G.globalized.f) ell eps
          (DeterministicFOComponent.queriedAt
            (A.component Q) G.globalized t).1 := by
      simpa only [G.X_eq] using hhit
    rw [hquery t] at htmp
    exact htmp
  exact (isOptimizationStationary_congr G.value_eq_on).mp hhit'

/-- The internal global-representative upper bound therefore implies the
literal shared-oracle upper bound claimed in the paper. -/
theorem paperComplexityAtMost_of_complexityAtMost
    {ell D Delta eps : ℝ} {T : Nat}
    (h : ComplexityAtMost ell D Delta eps T) :
    PaperComplexityAtMost ell D Delta eps T := by
  obtain ⟨A, hA⟩ := h
  exact ⟨A, paperSolvesWithin_of_solvesWithin A hA⟩

end

end Oracle
end NCCLowerBoundVerification
