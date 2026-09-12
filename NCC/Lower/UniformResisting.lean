import NCC.Lower.UniformResisting.Realization
import NCC.Lower.UniformResisting.BallLabel
import NCC.Lower.UniformResisting.RawMaps

/-!
# The single domain-wise uniform resisting algorithm

This is the quantifier order of `lem:resisting-oracle`: the horizon and
deterministic algorithm are supplied first, then one zero-respecting
domain-wise deterministic algorithm is constructed. Its projected transcript
identity holds for every positive ball diameter and every base oracle.

Only the known domain label is inspected when selecting a component. The
positive diameter of a positive-dimensional ball is determined by that label.
All other domains receive the origin-only component, as in the manuscript.
No objective or objective-dependent existence choice enters the simulator.
-/

namespace NCC.Lower.UniformResisting

noncomputable section

set_option backward.isDefEq.respectTransparency false

open NCCLowerBoundVerification Oracle
open NCPLVerification (IsOrthonormalFrame frameProject)

def transportComponent {m n : ℕ} {X X' : Set (EVec m)} {Y Y' : Set (EVec n)}
    (A : DeterministicFOComponent X Y) (hX : X = X') (hY : Y = Y') :
    DeterministicFOComponent X' Y' where
  nextQuery := A.nextQuery
  next_mem := by intro t hist; simpa [hX, hY] using A.next_mem t hist
  initial_query := A.initial_query

@[simp] theorem transportComponent_queriedAt {m n : ℕ}
    {X X' : Set (EVec m)} {Y Y' : Set (EVec n)}
    (A : DeterministicFOComponent X Y) (hX : X = X') (hY : Y = Y')
    (P : NCCInstance m n) (t : ℕ) :
    (transportComponent A hX hY).queriedAt P t = A.queriedAt P t := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
      rw [DeterministicFOComponent.queriedAt_eq_nextQuery,
        DeterministicFOComponent.queriedAt_eq_nextQuery A]
      change A.nextQuery t _ = A.nextQuery t _
      congr 1
      funext i
      change firstOrderOracle P ((transportComponent A hX hY).queriedAt P i) =
        firstOrderOracle P (A.queriedAt P i)
      rw [ih i i.isLt]

theorem transportComponent_zeroRespecting {m n : ℕ}
    {X X' : Set (EVec m)} {Y Y' : Set (EVec n)}
    (A : DeterministicFOComponent X Y) (hX : X = X') (hY : Y = Y')
    (P : NCCInstance m n) (hz : A.IsZeroRespectingOn P) :
    (transportComponent A hX hY).IsZeroRespectingOn P := by
  simpa only [DeterministicFOComponent.IsZeroRespectingOn, transportComponent_queriedAt] using hz

def originComponent (Q : AdmissibleDomainPair) : DeterministicFOComponent Q.X Q.Y where
  nextQuery := fun _ _ => (0, 0)
  next_mem := fun _ _ => ⟨Q.zero_mem_X, Q.zero_mem_Y⟩
  initial_query := rfl

@[simp] theorem originComponent_queriedAt (Q : AdmissibleDomainPair)
    (P : NCCInstance Q.m Q.n) (t : ℕ) : (originComponent Q).queriedAt P t = (0, 0) := by
  rw [DeterministicFOComponent.queriedAt_eq_nextQuery]
  rfl

theorem originComponent_zeroRespecting (Q : AdmissibleDomainPair)
    (P : NCCInstance Q.m Q.n) : (originComponent Q).IsZeroRespectingOn P := by
  intro t i hi
  simp [originComponent_queriedAt, standardJointQuery] at hi

def IsPositiveBallLabel (Q : AdmissibleDomainPair) : Prop :=
  0 < Q.n ∧ Q.X = Set.univ ∧ ∃ D : ℝ, 0 < D ∧ Q.Y = diameterBall Q.n D

def chosenDiameter (Q : AdmissibleDomainPair) (hQ : IsPositiveBallLabel Q) : ℝ :=
  hQ.2.2.choose

theorem chosenDiameter_spec (Q : AdmissibleDomainPair) (hQ : IsPositiveBallLabel Q) :
    0 < chosenDiameter Q hQ ∧ Q.Y = diameterBall Q.n (chosenDiameter Q hQ) :=
  hQ.2.2.choose_spec

theorem chosenDiameter_ballLabel {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 < D)
    (hQ : IsPositiveBallLabel (ballLabel m n D)) :
    chosenDiameter (ballLabel m n D) hQ = D := by
  exact diameterBall_parameter_unique hn (chosenDiameter_spec _ hQ).1 hD
    (chosenDiameter_spec _ hQ).2.symm

def domainComponent (K : ℕ) (A : DomainWiseDeterministicAlgorithm) (Q : AdmissibleDomainPair) :
    DeterministicFOComponent Q.X Q.Y := by
  classical
  exact if hQ : IsPositiveBallLabel Q then
    transportComponent
      (simulator (A.component (ballLabel (Q.m + K) (Q.n + K) (chosenDiameter Q hQ))))
      hQ.2.1.symm (chosenDiameter_spec Q hQ).2.symm
  else originComponent Q

/-- The simulator as one algorithm over every admissible domain label. -/
def uniformAlgorithm (K : ℕ) (A : DomainWiseDeterministicAlgorithm) :
    DomainWiseDeterministicAlgorithm where
  component := domainComponent K A

theorem uniformAlgorithm_zeroRespecting (K : ℕ) (A : DomainWiseDeterministicAlgorithm) :
    (uniformAlgorithm K A).IsZeroRespecting := by
  intro Q P _
  change (domainComponent K A Q).IsZeroRespectingOn P
  unfold domainComponent
  split_ifs with hQ
  · exact transportComponent_zeroRespecting _ _ _ P (simulator_zeroRespecting _ P)
  · exact originComponent_zeroRespecting Q P

theorem uniformAlgorithm_ball_queriedAt (K : ℕ) (A : DomainWiseDeterministicAlgorithm)
    {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 < D)
    (P : NCCInstance m n) (t : ℕ) :
    ((uniformAlgorithm K A).component (ballLabel m n D)).queriedAt P t =
      (simulator (A.component (ballLabel (m + K) (n + K) D))).queriedAt P t := by
  have hQ : IsPositiveBallLabel (ballLabel m n D) := ⟨hn, rfl, D, hD, rfl⟩
  change (domainComponent K A (ballLabel m n D)).queriedAt P t = _
  rw [domainComponent, dif_pos hQ, transportComponent_queriedAt]
  rw [chosenDiameter_ballLabel hn hD hQ]
  rfl

/-- `lem:resisting-oracle`, with its literal uniform quantifier order and
exact ambient dimensions. The base dual dimension is positive, as required
by the manuscript's convention `m,n ∈ ℕ` (positive integers). The theorem
also permits the harmless degenerate base primal dimension zero.

The algebraic statement holds for every local oracle record `P`; in
particular it holds when its fields are the value and genuine derivatives
of any smooth saddle function on the indicated ball domain. -/
theorem finite_horizon_resisting_oracle (K : ℕ) (A : DomainWiseDeterministicAlgorithm) :
    ∃ Z : DomainWiseDeterministicAlgorithm, Z.IsZeroRespecting ∧
      ∀ (m n : ℕ), 0 < n → ∀ (D : ℝ), 0 < D → ∀ P : NCCInstance m n,
        ∃ (U : Fin m → EVec (m + K)) (V : Fin n → EVec (n + K)),
          IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
          ∀ t < K, (Z.component (ballLabel m n D)).queriedAt P t =
            (frameProject U ((A.component (ballLabel (m + K) (n + K) D)).queriedAt
              (rotatedNCCInstance D U V P) t).1,
             frameProject V ((A.component (ballLabel (m + K) (n + K) D)).queriedAt
              (rotatedNCCInstance D U V P) t).2) := by
  refine ⟨uniformAlgorithm K A, uniformAlgorithm_zeroRespecting K A, ?_⟩
  intro m n hn D hD P
  obtain ⟨U, V, hU, hV, hrun⟩ :=
    uniform_component_realization (A.component (ballLabel (m + K) (n + K) D)) P
  refine ⟨U, V, hU, hV, ?_⟩
  intro t ht
  rw [uniformAlgorithm_ball_queriedAt K A hn hD]
  exact hrun t ht

end

end NCC.Lower.UniformResisting
