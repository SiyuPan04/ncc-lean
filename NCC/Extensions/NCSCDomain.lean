import NCC.Extensions.NCSCUniform
import NCC.Extensions.NCSCQueryWrapper

/-! One genuine domain-wise NC-SC algorithm. Its rule takes only domains,
numerical parameters, and reply histories, never an objective or class proof. -/
namespace NCC.Extensions.NCSCDomain
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle SharedOracle ProjectionGeometry
open NCC.Upper NCC.Upper.AdaptiveMicroProgram
open NCC.Extensions.NCSC
set_option maxHeartbeats 3000000

variable {ell mu Delta : ℝ}

theorem internal_pos (hell : 0 < ell) (hmu : 0 < mu) : 0 < internalSmoothness ell mu := by
  unfold internalSmoothness
  positivity

def domainInitializer (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    (Q : AdmissibleDomainPair) : Program Q.X Q.Y (FeasibleSnapshot Q.X Q.Y) :=
  NCSCStartupProgram.initProgram (r := mu) (internal_pos hell hmu) hDelta
    (domainProjectX Q) (domainProjectY Q) (domainProjectX_spec Q) (domainProjectY_spec Q)
    Q.zero_mem_X Q.zero_mem_Y (NCSCTheorem.majorant ell mu)

def domainRun (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    (eps rho : ℝ) (Q : AdmissibleDomainPair) :
    Program Q.X Q.Y (FeasibleSnapshot Q.X Q.Y × RelativeFOAMContraction.ValidState (m := Q.m) Q.Y) :=
  NCSCProgram.adaptProgram mu
    (NCSCProgram.fixedProgram (r := mu) (internal_pos hell hmu)
      (domainProjectX Q) (domainProjectY Q) (domainProjectX_spec Q) (domainProjectY_spec Q)
      (domainInitializer hell hmu hDelta Q) (NCSCTheorem.horizon ell Delta eps mu)
      (Selection.outerIterations_pos (internal_pos hell hmu) (by linarith)) rho)

theorem domainRun_matches (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    (eps rho : ℝ) (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n)
    (hP : NCSCClass ell mu Delta P) (hX : P.X = Q.X) (hY : P.Y = Q.Y) :
    HEq (domainRun hell hmu hDelta eps rho Q) (NCSCTheorem.run hP eps rho) := by
  cases Q with
  | mk m n X Y hx hy hcX hvX hcY hvY =>
    cases P with
    | mk X' Y' f gx gy x0 =>
      dsimp only at hX hY
      subst X'
      subst Y'
      rfl

def domainClient (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    (eps rho : ℝ) (Q : AdmissibleDomainPair) : Program Q.X Q.Y (Query Q.m Q.n) := do
  let out ← domainRun hell hmu hDelta eps rho Q
  .pure (out.1.1.z, 0)

theorem domainClient_correct (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    {eps : ℝ} (heps : 0 < eps) (rho : ℝ) (Q : AdmissibleDomainPair)
    (P : NCCInstance Q.m Q.n) (hP : NCSCClass ell mu Delta P)
    (hX : P.X = Q.X) (hY : P.Y = Q.Y) :
    let q := Program.eval P (domainClient hell hmu hDelta eps rho Q)
    (q.1 ∈ Q.X ∧ q.2 ∈ Q.Y) ∧ NCSC.IsOS hP eps q.1 := by
  cases Q with
  | mk m n X Y hx hy hcX hvX hcY hvY =>
    cases P with
    | mk X' Y' f gx gy x0 =>
      dsimp only at hX hY
      subst X'
      subst Y'
      simp only [domainClient, Program.eval_bind, Program.eval_pure]
      exact ⟨⟨(Program.eval _ (NCSCTheorem.run hP eps rho)).1.2, hy⟩,
        NCSCTheorem.run_isOS hP heps rho⟩

theorem domainClient_count (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    (eps : ℝ) {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) (hmuell : mu ≤ ell)
    (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n)
    (hP : NCSCClass ell mu Delta P) (hX : P.X = Q.X) (hY : P.Y = Q.Y) :
    ((queryTrace P (domainClient hell hmu hDelta eps rho Q)).length : ℝ) ≤
      NCSCTheorem.startupCost hP +
        (4001 * UniformCost.blockConstant (1 / 400) + UniformCost.blockConstant rho) *
          Real.sqrt (internalSmoothness ell mu / mu) +
        256064 * UniformCost.blockConstant (1 / 400) *
          (ell * (3 * Delta) / eps ^ 2) * Real.sqrt (ell / mu) := by
  cases Q with
  | mk m n X Y hx hy hcX hvX hcY hvY =>
    cases P with
    | mk X' Y' f gx gy x0 =>
      dsimp only at hX hY
      subst X'
      subst Y'
      rw [domainClient, queryTrace_bind, List.length_append]
      change (((queryTrace _ (NCSCTheorem.run hP eps rho)).length + 0 : ℕ) : ℝ) ≤ _
      simpa only [Nat.add_zero] using NCSCTheorem.run_count hP hmuell eps hrho hrho1

def domainComponent (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    (eps rho : ℝ) (Q : AdmissibleDomainPair) : DeterministicFOComponent Q.X Q.Y :=
  NCSCQueryWrapper.component (domainClient hell hmu hDelta eps rho Q)
    (domainProjectX Q) (domainProjectY Q) (domainProjectX_spec Q) (domainProjectY_spec Q)
    Q.zero_mem_X Q.zero_mem_Y

def domainAlgorithm (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    (eps rho : ℝ) : DomainWiseDeterministicAlgorithm where
  component Q := domainComponent hell hmu hDelta eps rho Q

theorem domainAlgorithm_queried_OS (hell : 0 < ell) (hmu : 0 < mu) (hDelta : 0 < Delta)
    {eps : ℝ} (heps : 0 < eps) {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1)
    (hmuell : mu ≤ ell) (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n)
    (hP : NCSCClass ell mu Delta P) (hX : P.X = Q.X) (hY : P.Y = Q.Y) :
    ∃ t : ℕ, (t + 1 : ℝ) ≤ NCSCTheorem.startupCost hP +
      (4001 * UniformCost.blockConstant (1 / 400) + UniformCost.blockConstant rho) *
        Real.sqrt (internalSmoothness ell mu / mu) +
      256064 * UniformCost.blockConstant (1 / 400) *
        (ell * (3 * Delta) / eps ^ 2) * Real.sqrt (ell / mu) + 2 ∧
      NCSC.IsOS hP eps (((domainAlgorithm hell hmu hDelta eps rho).component Q).queriedAt P t).1 := by
  have hcorrect := domainClient_correct hell hmu hDelta heps rho Q P hP hX hY
  obtain ⟨t, ht, hstat⟩ := NCSCQueryWrapper.queried_witness_of_output P
    (domainClient hell hmu hDelta eps rho Q)
    (domainProjectX Q) (domainProjectY Q) (domainProjectX_spec Q) (domainProjectY_spec Q)
    Q.zero_mem_X Q.zero_mem_Y (fun q => NCSC.IsOS hP eps q.1) hcorrect.1 hcorrect.2
  refine ⟨t, ?_, hstat⟩
  have hc := domainClient_count hell hmu hDelta eps hrho hrho1 hmuell Q P hP hX hY
  have ht' : (t : ℝ) + 1 =
      ((queryTrace P (domainClient hell hmu hDelta eps rho Q)).length : ℝ) + 2 := by
    exact_mod_cast ht
  linarith

end
end NCC.Extensions.NCSCDomain
