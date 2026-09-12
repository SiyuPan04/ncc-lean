import NCC.Moreau.Within
import NCCLowerBoundVerification.Oracle.Complexity

/-!
# Literal domain-labelled minimax queried hitting time

The class is the current feasible-domain `WithinClass`. The algorithm's
component receives only the domain label, never the objective or a class
membership certificate. Its causal queries see the actual local oracle.
The supremum ranges over the disjoint union of all finite dimensions and
admissible domains; the infimum ranges over objective-independent domain-wise
deterministic algorithms. Hitting indices start at zero, with top for no hit.

The algorithm type imposes causality and feasibility for every history,
exactly as the current source definition. Neither the current source nor
this type requires a separate measurability condition.
-/

namespace NCC.Complexity

noncomputable section

open NCCLowerBoundVerification
open scoped ENNReal

/-- Domain-labelled membership uses the current within-domain class, not
the older neighborhood/global class. Origin initialization is in the class. -/
def WithinDomainMember (ell D Delta : ℝ) (Q : Oracle.AdmissibleDomainPair)
    (P : NCCInstance Q.m Q.n) : Prop :=
  P.X = Q.X ∧ P.Y = Q.Y ∧ Model.WithinClass ell D Delta P

/-- Literal worst-case queried hitting index. On the subtype's members,
proximal OS agrees with the actual differentiable-envelope OS predicate. -/
def worstCaseHittingTime (A : Oracle.DomainWiseDeterministicAlgorithm)
    (ell D Delta eps : ℝ) : WithTop ℕ :=
  ⨆ Q : Oracle.AdmissibleDomainPair,
    ⨆ P : {P : NCCInstance Q.m Q.n // WithinDomainMember ell D Delta Q P},
      Oracle.queriedHittingTime (A.component Q) P.val ell eps

/-- The literal infimum-over-algorithms/supremum-over-instances quantity. -/
def minimaxHittingTime (ell D Delta eps : ℝ) : WithTop ℕ :=
  ⨅ A : Oracle.DomainWiseDeterministicAlgorithm, worstCaseHittingTime A ell D Delta eps

/-- The same complexity in extended nonnegative real units, for direct
comparison with the real-valued bounds displayed in the manuscript. -/
def minimaxOracleComplexity (ell D Delta eps : ℝ) : ℝ≥0∞ :=
  ENat.toENNReal (minimaxHittingTime ell D Delta eps)

set_option backward.isDefEq.respectTransparency false in
theorem minimaxOracleComplexity_eq (ell D Delta eps : ℝ) :
    minimaxOracleComplexity ell D Delta eps =
      ⨅ A : Oracle.DomainWiseDeterministicAlgorithm,
        ⨆ Q : Oracle.AdmissibleDomainPair,
          ⨆ P : {P : NCCInstance Q.m Q.n // WithinDomainMember ell D Delta Q P},
            ENat.toENNReal (Oracle.queriedHittingTime (A.component Q) P.val ell eps) := by
  change ENat.toENNReal
      (⨅ A : Oracle.DomainWiseDeterministicAlgorithm,
        ⨆ Q : Oracle.AdmissibleDomainPair,
          ⨆ P : {P : NCCInstance Q.m Q.n // WithinDomainMember ell D Delta Q P},
            (Oracle.queriedHittingTime (A.component Q) P.val ell eps : ℕ∞)) = _
  simp only [ENat.toENNReal_iInf, ENat.toENNReal_iSup]

theorem minimaxOracleComplexity_lower_of_horizon {ell D Delta eps r : ℝ} {K : ℕ}
    (hr : r ≤ (K : ℝ))
    (hK : (K : WithTop ℕ) ≤ minimaxHittingTime ell D Delta eps) :
    ENNReal.ofReal r ≤ minimaxOracleComplexity ell D Delta eps := by
  have hk := ENat.toENNReal_mono hK
  calc
    ENNReal.ofReal r ≤ ENNReal.ofReal (K : ℝ) := ENNReal.ofReal_le_ofReal hr
    _ = (K : ℝ≥0∞) := by simp
    _ ≤ _ := hk

theorem minimaxOracleComplexity_upper_of_horizon {ell D Delta eps : ℝ} {K : ℕ}
    (hK : minimaxHittingTime ell D Delta eps ≤ (K : WithTop ℕ)) :
    minimaxOracleComplexity ell D Delta eps ≤ (K : ℝ≥0∞) :=
  ENat.toENNReal_mono hK

theorem hitsAt_iff_actualOS {ell D Delta eps : ℝ} (heps : 0 < eps)
    (A : Oracle.DomainWiseDeterministicAlgorithm) (Q : Oracle.AdmissibleDomainPair)
    (P : NCCInstance Q.m Q.n) (hP : WithinDomainMember ell D Delta Q P) (t : ℕ) :
    (A.component Q).HitsAt P ell eps t ↔
      Moreau.Within.IsOS hP.2.2 eps ((A.component Q).queriedAt P t).1 := by
  rw [Moreau.Within.isOS_iff_feasible_prox]
  have hx := ((A.component Q).queriedAt_mem_instance P ⟨hP.1, hP.2.1⟩ t).1
  simp only [heps, hx, true_and, Oracle.DeterministicFOComponent.HitsAt]

/-- Every finite strict comparison of the minimax model's hitting time is
exactly the comparison obtained from the true Moreau-envelope gradient. -/
theorem queriedHittingTime_lt_iff_actualOS {ell D Delta eps : ℝ} (heps : 0 < eps)
    (A : Oracle.DomainWiseDeterministicAlgorithm) (Q : Oracle.AdmissibleDomainPair)
    (P : NCCInstance Q.m Q.n) (hP : WithinDomainMember ell D Delta Q P) (K : ℕ) :
    Oracle.queriedHittingTime (A.component Q) P ell eps < (K : WithTop ℕ) ↔
      ∃ t < K, Moreau.Within.IsOS hP.2.2 eps ((A.component Q).queriedAt P t).1 := by
  rw [Oracle.queriedHittingTime_lt_iff]
  simp only [Oracle.DeterministicFOComponent.HitsWithin,
    hitsAt_iff_actualOS heps A Q P hP]

theorem minimaxHittingTime_lower_of_hard_members {ell D Delta eps : ℝ} {K : ℕ}
    (hhard : ∀ A : Oracle.DomainWiseDeterministicAlgorithm,
      ∃ (Q : Oracle.AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
        WithinDomainMember ell D Delta Q P ∧
        (K : WithTop ℕ) ≤ Oracle.queriedHittingTime (A.component Q) P ell eps) :
    (K : WithTop ℕ) ≤ minimaxHittingTime ell D Delta eps := by
  apply le_iInf
  intro A
  obtain ⟨Q, P, hP, htime⟩ := hhard A
  exact le_iSup_of_le Q (le_iSup_of_le (⟨P, hP⟩ :
    {P : NCCInstance Q.m Q.n // WithinDomainMember ell D Delta Q P}) htime)

theorem minimaxHittingTime_upper_of_algorithm {ell D Delta eps : ℝ} {K : ℕ}
    (hsolver : ∃ A : Oracle.DomainWiseDeterministicAlgorithm,
      ∀ (Q : Oracle.AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
        WithinDomainMember ell D Delta Q P →
        Oracle.queriedHittingTime (A.component Q) P ell eps ≤ (K : WithTop ℕ)) :
    minimaxHittingTime ell D Delta eps ≤ (K : WithTop ℕ) := by
  obtain ⟨A, hA⟩ := hsolver
  apply iInf_le_of_le A
  apply iSup_le
  intro Q
  apply iSup_le
  intro P
  exact hA Q P.val P.property

end

end NCC.Complexity
