import NCCLowerBoundVerification.Oracle.Complexity
import NCCLowerBoundVerification.Oracle.ZeroChain

/-!
# Domain-wise zero-respecting deterministic algorithms

This file formalizes Definition `def:zr-alg` from
`Upper+Lower_unified_lower.tex`.  The standard joint coordinate order is

`x₀, ..., xₘ₋₁, y₀, ..., yₙ₋₁`,

and the corresponding saddle response is `(gradX, -gradY)`.  A domain-wise
algorithm is zero-respecting when, on every objective whose domains match the
chosen domain label, its actual recursively generated query trajectory is
zero-respecting for that saddle field.
-/

namespace NCCLowerBoundVerification
namespace Oracle

noncomputable section

/-! ## The standard joint coordinate order -/

/-- Concatenate a primal and a dual vector, with every primal coordinate
before every dual coordinate. -/
def standardJointVector {m n : Nat} (x : EVec m) (y : EVec n) :
    EVec (m + n) :=
  Fin.append x y

/-- Decode the primal prefix of a vector in the standard joint order. -/
def standardPrimalPart {m n : Nat} (z : EVec (m + n)) : EVec m :=
  fun i => z (Fin.castAdd n i)

/-- Decode the dual suffix of a vector in the standard joint order. -/
def standardDualPart {m n : Nat} (z : EVec (m + n)) : EVec n :=
  fun j => z (Fin.natAdd m j)

@[simp] theorem standardPrimalPart_standardJointVector {m n : Nat}
    (x : EVec m) (y : EVec n) :
    standardPrimalPart (standardJointVector x y) = x := by
  funext i
  simp [standardPrimalPart, standardJointVector]

@[simp] theorem standardDualPart_standardJointVector {m n : Nat}
    (x : EVec m) (y : EVec n) :
    standardDualPart (standardJointVector x y) = y := by
  funext j
  simp [standardDualPart, standardJointVector]

@[simp] theorem standardJointVector_parts {m n : Nat}
    (z : EVec (m + n)) :
    standardJointVector (standardPrimalPart z) (standardDualPart z) = z := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [standardJointVector, standardPrimalPart, standardDualPart]

@[simp] theorem standardJointVector_zero {m n : Nat} :
    standardJointVector (0 : EVec m) (0 : EVec n) = 0 := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;>
    simp [standardJointVector]

/-- A feasible oracle query written in the standard joint coordinate order. -/
def standardJointQuery {m n : Nat} (q : Query m n) : EVec (m + n) :=
  standardJointVector q.1 q.2

@[simp] theorem standardPrimalPart_standardJointQuery {m n : Nat}
    (q : Query m n) :
    standardPrimalPart (standardJointQuery q) = q.1 := by
  simp [standardJointQuery]

@[simp] theorem standardDualPart_standardJointQuery {m n : Nat}
    (q : Query m n) :
    standardDualPart (standardJointQuery q) = q.2 := by
  simp [standardJointQuery]

/-- The saddle vector field `(gradX, -gradY)` in the standard joint order. -/
def standardSaddleField {m n : Nat} (P : NCCInstance m n) :
    EVec (m + n) → EVec (m + n) := fun z =>
  standardJointVector
    (P.gradX (standardPrimalPart z) (standardDualPart z))
    (-P.gradY (standardPrimalPart z) (standardDualPart z))

@[simp] theorem standardSaddleField_standardJointQuery {m n : Nat}
    (P : NCCInstance m n) (q : Query m n) :
    standardSaddleField P (standardJointQuery q) =
      standardJointVector (P.gradX q.1 q.2) (-P.gradY q.1 q.2) := by
  simp [standardSaddleField]

/-! ## Component-wise and domain-wise zero-respecting predicates -/

namespace DeterministicFOComponent

variable {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}

/-- The actual trajectory of a component is zero-respecting on one matching
objective.  Causality remains enforced by `DeterministicFOComponent` itself. -/
def IsZeroRespectingOn (A : DeterministicFOComponent X Y)
    (P : NCCInstance m n) : Prop :=
  NCPLVerification.QueriesAreZeroRespecting
    (standardSaddleField P)
    (fun t => standardJointQuery (A.queriedAt P t))

/-- Restrict a globally zero-respecting actual trajectory to a finite query
horizon, in the exact form consumed by `sequential_discovery`. -/
theorem finiteStandardQueriesAreZeroRespecting
    (A : DeterministicFOComponent X Y) (P : NCCInstance m n)
    (hzero : A.IsZeroRespectingOn P) (horizon : Nat) :
    FiniteQueriesAreZeroRespecting
      (standardSaddleField P)
      (fun t => standardJointQuery (A.queriedAt P t)) horizon :=
  finiteQueriesAreZeroRespecting_of_global hzero

/-- `lem:sequential-discovery` applied directly to the actual query trajectory
of a zero-respecting component. -/
theorem standardSequentialDiscovery
    (A : DeterministicFOComponent X Y) (P : NCCInstance m n)
    (hzero : A.IsZeroRespectingOn P)
    (hchain : IsFirstOrderSaddleZeroChain (standardSaddleField P))
    {horizon t : Nat} (ht : t < horizon) (hdim : t ≤ m + n) :
    SupportedInPrefix t (standardJointQuery (A.queriedAt P t)) := by
  exact sequential_discovery hchain
    (A.finiteStandardQueriesAreZeroRespecting P hzero horizon)
    t ht hdim

end DeterministicFOComponent

namespace DomainWiseDeterministicAlgorithm

/-- Definition `def:zr-alg`: every component, on every objective with the
same labelled domains, generates an actual zero-respecting trajectory. -/
def IsZeroRespecting (A : DomainWiseDeterministicAlgorithm) : Prop :=
  ∀ (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
    (A.component Q).MatchesInstance P →
      (A.component Q).IsZeroRespectingOn P

end DomainWiseDeterministicAlgorithm

/-- The domain-wise zero-respecting subclass `A_zr`. -/
def ZeroRespectingDomainWiseDeterministicAlgorithm :=
  {A : DomainWiseDeterministicAlgorithm // A.IsZeroRespecting}

namespace ZeroRespectingDomainWiseDeterministicAlgorithm

/-- Forget the zero-respecting certificate. -/
def toDeterministicAlgorithm
    (A : ZeroRespectingDomainWiseDeterministicAlgorithm) :
    DomainWiseDeterministicAlgorithm :=
  A.1

/-- The component selected at a domain label is zero-respecting on every
matching instance. -/
theorem component_zeroRespectingOn
    (A : ZeroRespectingDomainWiseDeterministicAlgorithm)
    (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n)
    (hmatch : (A.1.component Q).MatchesInstance P) :
    (A.1.component Q).IsZeroRespectingOn P :=
  A.2 Q P hmatch

/-- Sequential discovery for a member of the domain-wise class, with no
additional trajectory hypothesis. -/
theorem standardSequentialDiscovery
    (A : ZeroRespectingDomainWiseDeterministicAlgorithm)
    (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n)
    (hmatch : (A.1.component Q).MatchesInstance P)
    (hchain : IsFirstOrderSaddleZeroChain (standardSaddleField P))
    {horizon t : Nat} (ht : t < horizon) (hdim : t ≤ Q.m + Q.n) :
    SupportedInPrefix t
      (standardJointQuery ((A.1.component Q).queriedAt P t)) := by
  exact (A.1.component Q).standardSequentialDiscovery P
    (A.component_zeroRespectingOn Q P hmatch) hchain ht hdim

end ZeroRespectingDomainWiseDeterministicAlgorithm

/-! ## A generic `thm:zr` wrapper -/

/-- Every matching zero-respecting component fails during the stated query
horizon.  This is the singleton-instance threshold form of the paper's
`T_epsilon(A_zr, {f}) ≥ K`. -/
def ZeroRespectingHittingTimeAtLeast {m n : Nat}
    (P : NCCInstance m n) (ell eps : ℝ) (K : Nat) : Prop :=
  ∀ {X : Set (EVec m)} {Y : Set (EVec n)}
      (A : DeterministicFOComponent X Y),
    A.MatchesInstance P → A.IsZeroRespectingOn P →
      A.FailsWithin P ell eps K

/-- `lem:chain-criterion` specialized to the standard primal-then-dual
coordinate order.  The dual dimension is written as `n + 1` so the joint
space has the literal successor form expected by the finite zero-chain
theorem. -/
theorem zeroRespectingHittingTimeAtLeast_of_standardZeroChain
    {m n : Nat} (P : NCCInstance m (n + 1)) {ell eps r : ℝ}
    (hchain : IsFirstOrderSaddleZeroChain
      (standardSaddleField (m := m) (n := n + 1) P))
    (hr : 0 ≤ r)
    (hfailure : ∀ z : EVec (m + (n + 1)),
      standardPrimalPart (m := m) (n := n + 1) z ∈ P.X →
      standardDualPart (m := m) (n := n + 1) z ∈ P.Y →
      z (Fin.last (m + n)) ≤ r →
        ¬ IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
          (standardPrimalPart (m := m) (n := n + 1) z)) :
    ZeroRespectingHittingTimeAtLeast P ell eps (m + n + 1) := by
  intro X Y A hmatch hzero
  let query : Nat → EVec (m + (n + 1)) :=
    fun t => standardJointQuery (m := m) (n := n + 1) (A.queriedAt P t)
  have hfinite : FiniteQueriesAreZeroRespecting
      (standardSaddleField (m := m) (n := n + 1) P)
      query (m + n + 1) := by
    exact A.finiteStandardQueriesAreZeroRespecting P hzero (m + n + 1)
  have hfeasible : ∀ t, t < m + n + 1 →
      standardPrimalPart (m := m) (n := n + 1) (query t) ∈ P.X ∧
        standardDualPart (m := m) (n := n + 1) (query t) ∈ P.Y := by
    intro t _ht
    have hmem := A.queriedAt_mem_instance P hmatch t
    simpa [query] using hmem
  have hlower := queried_iterate_lower_bound_of_zero_chain
    (d := m + n)
    (Primal := EVec m)
    (G := standardSaddleField (m := m) (n := n + 1) P)
    (query := query)
    (primal := standardPrimalPart (m := m) (n := n + 1))
    (Feasible := fun z =>
      standardPrimalPart (m := m) (n := n + 1) z ∈ P.X ∧
        standardDualPart (m := m) (n := n + 1) z ∈ P.Y)
    (IsStationary := fun x =>
      IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps x)
    (r := r) hchain hfinite hfeasible hr (by
      intro z hz hlast
      exact hfailure z hz.1 hz.2 hlast)
  intro t ht
  unfold DeterministicFOComponent.HitsAt
  have htLower := hlower t ht
  simpa [query] using htLower

/-- A domain-wise member inherits the generic singleton lower bound directly
from its defining zero-respecting certificate. -/
theorem ZeroRespectingHittingTimeAtLeast.domainWise
    {Q : AdmissibleDomainPair} {P : NCCInstance Q.m Q.n}
    {ell eps : ℝ} {K : Nat}
    (h : ZeroRespectingHittingTimeAtLeast P ell eps K)
    (A : ZeroRespectingDomainWiseDeterministicAlgorithm)
    (hmatch : (A.1.component Q).MatchesInstance P) :
    (A.1.component Q).FailsWithin P ell eps K := by
  exact h (A.1.component Q) hmatch
    (A.component_zeroRespectingOn Q P hmatch)

end

end Oracle
end NCCLowerBoundVerification
