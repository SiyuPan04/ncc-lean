import NCC.Extensions.NCSCGSProgram
import NCC.Extensions.NCSCTheorem
import NCC.Extensions.NCSCQueryWrapper

/-!
# Closed NC-SC GS guarantee and explicit counted rate

The origin reply determines a finite energy-normalization call. The rest
is fixed-curvature tracking, one refinement, and one original-gradient
projected readout. There is no bounded-dual assumption and no homotopy.
The observed initialization cost remains explicit in the rate.
-/
namespace NCC.Extensions.NCSCGSTheorem
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle OuterTrajectoryConcrete SharedOracle
open NCC.Upper NCC.Upper.AdaptiveMicroProgram
set_option maxHeartbeats 3000000
variable {m n : Nat} {ell mu Delta : ℝ} {P : NCCInstance m n}

def run (h : NCSC.NCSCClass ell mu Delta P) (eps : ℝ) : Program P.X P.Y (Query m n) := do
  let out ← NCSCTheorem.run h eps (GSRun.refinementFactor (NCSC.internalSmoothness ell mu) mu)
  GSProgram.readoutProgram (NCSC.internalSmoothness ell mu) 0
    (NCSCSystem.system h).projectX (NCSCExecution.projectY h)
    (NCSCSystem.system h).project_spec (NCSCExecution.projectY_spec h) out.1.1.z out.2

theorem run_hasGSWitness (h : NCSC.NCSCClass ell mu Delta P) {eps : ℝ} (heps : 0 < eps) :
    HasGSWitness P eps (Program.eval P (run h eps)).1 (Program.eval P (run h eps)).2 := by
  apply NCSCGSProgram.program_hasGSWitness h (NCSCTheorem.initializer h)
    (show 0 < 3 * Delta by linarith [h.Delta_pos]) heps
  · rw [NCSCTheorem.initializer_B]
    exact NCSCTheorem.initializer_energy h
  · rw [NCSCTheorem.initializer_B]
    exact h.Delta_pos.le
  · exact NCSCTheorem.initializer_gap h

theorem run_isGS (h : NCSC.NCSCClass ell mu Delta P) {eps : ℝ} (heps : 0 < eps) :
    IsGS P eps (Program.eval P (run h eps)).1 (Program.eval P (run h eps)).2 :=
  (run_hasGSWitness h heps).isGS

theorem run_all_histories_feasible (h : NCSC.NCSCClass ell mu Delta P) (eps : ℝ)
    (t : Nat) (history : ReplyHistory m n t) :
    let q := Program.queryAfterHistory (run h eps) (0, 0) t history
    q.1 ∈ P.X ∧ q.2 ∈ P.Y :=
  Program.queryAfterHistory_mem _ (0, 0) ⟨h.primal_origin, h.dual_origin⟩ t history

/-- The exact leading term is epsilon^{-2} and square-root conditioned.
The origin-normalization and final-refinement costs are additive and
independent of epsilon, but not uniform over the initial oracle reply. -/
theorem run_count (h : NCSC.NCSCClass ell mu Delta P) (hmuell : mu ≤ ell) (eps : ℝ) :
    ((queryTrace P (run h eps)).length : ℝ) ≤ NCSCTheorem.startupCost h +
      (4001 * UniformCost.blockConstant (1 / 400) +
        UniformCost.blockConstant (GSRun.refinementFactor (NCSC.internalSmoothness ell mu) mu)) *
        Real.sqrt (NCSC.internalSmoothness ell mu / mu) +
      256064 * UniformCost.blockConstant (1 / 400) *
        (ell * (3 * Delta) / eps ^ 2) * Real.sqrt (ell / mu) + 1 := by
  let rho := GSRun.refinementFactor (NCSC.internalSmoothness ell mu) mu
  let p := NCSCTheorem.run h eps rho
  have hc := NCSCTheorem.run_count h hmuell eps
    (GSRun.refinementFactor_pos (NCSC.internalSmoothness_pos h) h.mu_pos)
    (GSRun.refinementFactor_lt_one (NCSC.internalSmoothness_pos h) (NCSC.intrinsic_parameter_le h))
  have hr := (GSProgram.readoutProgram_depth (NCSC.internalSmoothness ell mu) 0
    (NCSCSystem.system h).projectX (NCSCExecution.projectY h)
    (NCSCSystem.system h).project_spec (NCSCExecution.projectY_spec h)
    (Program.eval P p).1.1.z (Program.eval P p).2).trace_length P
  rw [run, queryTrace_bind, List.length_append, Nat.cast_add]
  change ((queryTrace P p).length : ℝ) +
    ((queryTrace P (GSProgram.readoutProgram (NCSC.internalSmoothness ell mu) 0
      (NCSCSystem.system h).projectX (NCSCExecution.projectY h)
      (NCSCSystem.system h).project_spec (NCSCExecution.projectY_spec h)
      (Program.eval P p).1.1.z (Program.eval P p).2)).length : ℝ) ≤ _
  have hrr := Nat.cast_le (α := ℝ).mpr hr
  change ((queryTrace P p).length : ℝ) ≤ _ at hc
  norm_num only [Nat.cast_one] at hrr
  linarith

def component (h : NCSC.NCSCClass ell mu Delta P) (eps : ℝ) :
    DeterministicFOComponent P.X P.Y :=
  NCSCQueryWrapper.component (run h eps)
    (NCSCSystem.system h).projectX (NCSCExecution.projectY h)
    (NCSCSystem.system h).project_spec (NCSCExecution.projectY_spec h)
    h.primal_origin h.dual_origin

/-- A stationarity witness is an actually queried pair, at the genuine
observed trace length. The two wrapper queries are explicitly charged. -/
theorem queried_isGS (h : NCSC.NCSCClass ell mu Delta P) (hmuell : mu ≤ ell)
    {eps : ℝ} (heps : 0 < eps) :
    ∃ t : Nat,
      (t + 1 : ℝ) ≤ NCSCTheorem.startupCost h +
        (4001 * UniformCost.blockConstant (1 / 400) +
          UniformCost.blockConstant (GSRun.refinementFactor (NCSC.internalSmoothness ell mu) mu)) *
          Real.sqrt (NCSC.internalSmoothness ell mu / mu) +
        256064 * UniformCost.blockConstant (1 / 400) *
          (ell * (3 * Delta) / eps ^ 2) * Real.sqrt (ell / mu) + 3 ∧
      IsGS P eps ((component h eps).queriedAt P t).1 ((component h eps).queriedAt P t).2 := by
  have hw := run_hasGSWitness h heps
  obtain ⟨t, ht, hg⟩ := NCSCQueryWrapper.queried_witness_of_output P (run h eps)
    (NCSCSystem.system h).projectX (NCSCExecution.projectY h)
    (NCSCSystem.system h).project_spec (NCSCExecution.projectY_spec h)
    h.primal_origin h.dual_origin (fun q => IsGS P eps q.1 q.2)
    ⟨hw.2.1, hw.2.2.1⟩ hw.isGS
  refine ⟨t, ?_, hg⟩
  have htr := congrArg (fun k : Nat => (k : ℝ)) ht
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at htr
  have hc := run_count h hmuell eps
  linarith

end
end NCC.Extensions.NCSCGSTheorem
