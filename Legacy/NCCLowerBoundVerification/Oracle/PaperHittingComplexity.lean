import NCCLowerBoundVerification.Oracle.MeasurableModel

/-!
# Infimum--supremum hitting-time complexity

The finite theorems are most conveniently proved with the threshold
predicates in `PaperComplexity`.  This file also defines the literal extended
natural infimum--supremum from the TeX and proves that the measurable threshold
statements give its corresponding upper and lower inequalities.
-/

namespace NCCLowerBoundVerification
namespace Oracle

noncomputable section

/-- A member of the domain-labelled paper class, retaining its domain label. -/
def PaperMember (ell D Delta : ℝ) :=
  Σ Q : AdmissibleDomainPair,
    {P : NCCInstance Q.m Q.n //
      IsPaperDomainFreeMember ell D Delta Q P}

/-- Worst queried-iterate hitting time of one measurable domain-wise
algorithm over the literal paper class. -/
def measurablePaperWorstHittingTime
    (A : MeasurableDomainWiseDeterministicAlgorithm)
    (ell D Delta eps : ℝ) : WithTop Nat :=
  ⨆ I : PaperMember ell D Delta,
    queriedHittingTime (A.component I.1) I.2.1 ell eps

/-- The paper's deterministic complexity: infimum over measurable algorithms
of the supremum over the domain-labelled function class. -/
def measurablePaperHittingComplexity
    (ell D Delta eps : ℝ) : WithTop Nat :=
  ⨅ A : MeasurableDomainWiseDeterministicAlgorithm,
    measurablePaperWorstHittingTime A ell D Delta eps

/-- A uniform measurable solver gives the expected upper inequality for the
literal infimum--supremum complexity. -/
theorem measurablePaperHittingComplexity_le_of_atMost
    {ell D Delta eps : ℝ} {T : Nat}
    (h : MeasurablePaperComplexityAtMost ell D Delta eps T) :
    measurablePaperHittingComplexity ell D Delta eps ≤ (T : WithTop Nat) := by
  obtain ⟨A, hsolve⟩ := h
  apply (iInf_le
    (fun B : MeasurableDomainWiseDeterministicAlgorithm =>
      measurablePaperWorstHittingTime B ell D Delta eps) A).trans
  apply iSup_le
  rintro ⟨Q, P, hP⟩
  have hhit : (A.component Q).HitsWithin P ell eps T :=
    hsolve Q P hP
  exact (queriedHittingTime_lt_iff (A.component Q) P ell eps T).2 hhit |>.le

/-- A hard member for every measurable algorithm gives the expected lower
inequality for the literal infimum--supremum complexity. -/
theorem le_measurablePaperHittingComplexity_of_atLeast
    {ell D Delta eps : ℝ} {K : Nat}
    (h : MeasurablePaperComplexityAtLeast ell D Delta eps K) :
    (K : WithTop Nat) ≤ measurablePaperHittingComplexity ell D Delta eps := by
  apply le_iInf
  intro A
  obtain ⟨Q, P, hP, hfail⟩ := h A
  let I : PaperMember ell D Delta := ⟨Q, P, hP⟩
  apply (show (K : WithTop Nat) ≤
      queriedHittingTime (A.component Q) P ell eps by
    apply le_of_not_gt
    intro hlt
    have hhit : (A.component Q).HitsWithin P ell eps K :=
      (queriedHittingTime_lt_iff (A.component Q) P ell eps K).1 hlt
    exact (DeterministicFOComponent.failsWithin_iff_not_hitsWithin
      (A.component Q) P ell eps K).1 hfail hhit).trans
  exact le_iSup (fun J : PaperMember ell D Delta =>
    queriedHittingTime (A.component J.1) J.2.1 ell eps) I

end

end Oracle
end NCCLowerBoundVerification
