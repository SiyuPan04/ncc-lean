import NCCLowerBoundVerification.Oracle.PaperComplexity

/-!
# Measurability refinement of the deterministic oracle model

The lower-bound development deliberately quantifies the larger class of all
causal domain-wise rules.  The paper additionally asks every finite-history
query map to be Borel measurable.  This file records that literal subclass
and relates its threshold predicates to the stronger causal formulation.
-/

namespace NCCLowerBoundVerification
namespace Oracle

noncomputable section

/-- Euclidean coding of one local-oracle reply. -/
def OracleReply.toProduct {m n : Nat} (r : OracleReply m n) :
    ℝ × EVec m × EVec n := (r.value, r.gradX, r.gradY)

/-- The measurable structure pulled back from the finite-dimensional
Euclidean product of the value and the two gradient vectors. -/
instance oracleReplyMeasurableSpace (m n : Nat) :
    MeasurableSpace (OracleReply m n) :=
  MeasurableSpace.comap OracleReply.toProduct inferInstance

/-- Literal measurability clause for one causal domain component. -/
def DeterministicFOComponent.IsMeasurable {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (A : DeterministicFOComponent X Y) : Prop :=
  ∀ t, Measurable (A.nextQuery t)

/-- Definition `def:det-alg`, including both causal dependence and the
measurability clause. -/
structure MeasurableDomainWiseDeterministicAlgorithm where
  component : (Q : AdmissibleDomainPair) →
    DeterministicFOComponent Q.X Q.Y
  measurable_component : ∀ Q, (component Q).IsMeasurable

/-- Forgetting measurability embeds the paper's algorithm class into the
larger causal class used by the information-theoretic lower proof. -/
def MeasurableDomainWiseDeterministicAlgorithm.toCausal
    (A : MeasurableDomainWiseDeterministicAlgorithm) :
    DomainWiseDeterministicAlgorithm where
  component := A.component

/-- Uniform success for a measurable domain-wise algorithm. -/
def MeasurablePaperSolvesWithin
    (A : MeasurableDomainWiseDeterministicAlgorithm)
    (ell D Delta eps : ℝ) (T : Nat) : Prop :=
  ∀ (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
    IsPaperDomainFreeMember ell D Delta Q P →
      DeterministicFOComponent.HitsWithin (A.component Q) P ell eps T

/-- Upper threshold over the literal measurable algorithm class. -/
def MeasurablePaperComplexityAtMost
    (ell D Delta eps : ℝ) (T : Nat) : Prop :=
  ∃ A : MeasurableDomainWiseDeterministicAlgorithm,
    MeasurablePaperSolvesWithin A ell D Delta eps T

/-- Lower threshold over the literal measurable algorithm class. -/
def MeasurablePaperComplexityAtLeast
    (ell D Delta eps : ℝ) (K : Nat) : Prop :=
  ∀ A : MeasurableDomainWiseDeterministicAlgorithm,
    ∃ (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
      IsPaperDomainFreeMember ell D Delta Q P ∧
        DeterministicFOComponent.FailsWithin
          (A.component Q) P ell eps K

/-- A lower bound proved for all causal rules is stronger than the same lower
bound for the measurable subclass stated in the paper. -/
theorem measurablePaperComplexityAtLeast_of_paperComplexityAtLeast
    {ell D Delta eps : ℝ} {K : Nat}
    (h : PaperComplexityAtLeast ell D Delta eps K) :
    MeasurablePaperComplexityAtLeast ell D Delta eps K := by
  intro A
  exact h A.toCausal

/-- A measurable algorithm's success statement is definitionally the causal
success statement of its forgetful image. -/
theorem measurablePaperSolvesWithin_iff
    (A : MeasurableDomainWiseDeterministicAlgorithm)
    {ell D Delta eps : ℝ} {T : Nat} :
    MeasurablePaperSolvesWithin A ell D Delta eps T ↔
      PaperSolvesWithin A.toCausal ell D Delta eps T := by
  rfl

end

end Oracle
end NCCLowerBoundVerification
