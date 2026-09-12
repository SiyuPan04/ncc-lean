import NCC.Extensions.NCSCDomain
import NCC.Extensions.NCSCGSTheorem

/-!
# A domain-wise intrinsic NC-SC GS algorithm

The component constructor receives numerical parameters and the domain label,
never an objective or class membership proof. Its count is instance-dependent
only through the explicitly observed initialization cost.
-/
namespace NCC.Extensions.NCSCGSUniform
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle SharedOracle NCC.Upper NCC.Upper.AdaptiveMicroProgram
set_option maxHeartbeats 3000000
variable {ell mu Delta : ℝ}

def domainRun (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    (eps : ℝ) (Q : AdmissibleDomainPair) : Program Q.X Q.Y (Query Q.m Q.n) := do
  let out ← NCSCDomain.domainRun hell hmu hDelta eps
    (GSRun.refinementFactor (NCSC.internalSmoothness ell mu) mu) Q
  GSProgram.readoutProgram (NCSC.internalSmoothness ell mu) 0
    (domainProjectX Q) (domainProjectY Q) (domainProjectX_spec Q) (domainProjectY_spec Q)
    out.1.1.z out.2

def domainComponent (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    (eps : ℝ) (Q : AdmissibleDomainPair) : DeterministicFOComponent Q.X Q.Y :=
  NCSCQueryWrapper.component (domainRun hell hmu hDelta eps Q)
    (domainProjectX Q) (domainProjectY Q) (domainProjectX_spec Q) (domainProjectY_spec Q)
    Q.zero_mem_X Q.zero_mem_Y

/-- One causal algorithm over all admissible domains. -/
def algorithm (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    (eps : ℝ) : DomainWiseDeterministicAlgorithm where
  component Q := domainComponent hell hmu hDelta eps Q

theorem domainRun_matches (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    (eps : ℝ) (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n)
    (h : NCSC.NCSCClass ell mu Delta P) (hX : P.X = Q.X) (hY : P.Y = Q.Y) :
    HEq (domainRun hell hmu hDelta eps Q) (NCSCGSTheorem.run h eps) := by
  cases Q with
  | mk m n X Y hx0 hy0 hXc hXv hYc hYv =>
    cases P with
    | mk X' Y' f gx gy x0 =>
      dsimp only at hX hY
      subst X'
      subst Y'
      rfl

/-- The domain-only algorithm reaches a genuinely queried GS pair at the
square-root-conditioned leading rate, with the additive costs exposed. -/
theorem algorithm_queried_isGS (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    (hmuell : mu ≤ ell) {eps : ℝ} (heps : 0 < eps)
    (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n)
    (h : NCSC.NCSCClass ell mu Delta P) (hX : P.X = Q.X) (hY : P.Y = Q.Y) :
    ∃ t : Nat,
      (t + 1 : ℝ) ≤ NCSCTheorem.startupCost h +
        (4001 * UniformCost.blockConstant (1 / 400) +
          UniformCost.blockConstant (GSRun.refinementFactor (NCSC.internalSmoothness ell mu) mu)) *
          Real.sqrt (NCSC.internalSmoothness ell mu / mu) +
        256064 * UniformCost.blockConstant (1 / 400) *
          (ell * (3 * Delta) / eps ^ 2) * Real.sqrt (ell / mu) + 3 ∧
      IsGS P eps
        (((algorithm hell hmu hDelta eps).component Q).queriedAt P t).1
        (((algorithm hell hmu hDelta eps).component Q).queriedAt P t).2 := by
  cases Q with
  | mk m n X Y hx0 hy0 hXc hXv hYc hYv =>
    cases P with
    | mk X' Y' f gx gy x0 =>
      dsimp only at hX hY
      subst X'
      subst Y'
      exact NCSCGSTheorem.queried_isGS h hmuell heps

end
end NCC.Extensions.NCSCGSUniform
