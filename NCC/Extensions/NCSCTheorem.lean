import NCC.Extensions.NCSCExecution
import NCC.Extensions.NCSCInitialBudget
import NCC.Extensions.NCSCStartupProgram
import NCC.Extensions.NCSCCost

/-!
# Actual NC-SC OS algorithm with explicit initialization cost

All objective-dependent startup data come from a single feasible oracle reply.
The warm-up normalizes the true tracking energy to Delta. The leading rate
is square-root conditioned, while the additive observed initialization and
final refinement costs remain explicit.
-/
namespace NCC.Extensions.NCSCTheorem
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle OuterTrajectoryConcrete SharedOracle
open NCC.Upper NCC.Upper.AdaptiveMicroProgram
open NCC.Extensions.NCSC
set_option maxHeartbeats 3000000

variable {m n : ℕ} {ell mu Delta : ℝ} {P : NCCInstance m n}

def majorant (ell mu : ℝ) (reply : OracleReply m n) : ℝ :=
  NCSCInitialBudget.budget ell mu reply.gradX reply.gradY

def initializer (h : NCSCClass ell mu Delta P) : Program P.X P.Y (FeasibleSnapshot P.X P.Y) :=
  NCSCStartupProgram.initProgram (r := mu) (internalSmoothness_pos h) h.Delta_pos
    (NCSCSystem.system h).projectX (NCSCExecution.projectY h)
    (NCSCSystem.system h).project_spec (NCSCExecution.projectY_spec h)
    h.primal_origin h.dual_origin (majorant ell mu)

theorem initializer_energy (h : NCSCClass ell mu Delta P) :
    snapshotEnergy (NCSCSystem.system h)
      (Program.eval (auxiliary P mu) (initializer h)).1 ≤ Delta := by
  apply NCSCStartupProgram.initProgram_energy (auxiliary P mu)
    (internalSmoothness_pos h) h.mu_pos (intrinsic_parameter_le h) h.Delta_pos
    (NCSCSystem.system h) (NCSCExecution.projectY h) (NCSCExecution.projectY_spec h)
    (NCSCExecution.microRealizes h) h.primal_origin h.dual_origin (majorant ell mu)
  simpa only [majorant, firstOrderOracle, auxiliary, smul_zero, add_zero,
    snapshotEnergy, NCSCInitialBudget.initialSnapshot, NCSCInitialBudget.originState,
    NCSCStartupProgram.seedState] using
    NCSCInitialBudget.initial_energy_bound h (NCSCSystem.system h)

theorem initializer_B (h : NCSCClass ell mu Delta P) :
      (Program.eval (auxiliary P mu) (initializer h)).1.B = Delta :=
  NCSCStartupProgram.initProgram_B (auxiliary P mu) (internalSmoothness_pos h) h.Delta_pos
    (NCSCSystem.system h).projectX (NCSCExecution.projectY h)
    (NCSCSystem.system h).project_spec (NCSCExecution.projectY_spec h)
    h.primal_origin h.dual_origin (majorant ell mu)

theorem initializer_z (h : NCSCClass ell mu Delta P) :
      (Program.eval (auxiliary P mu) (initializer h)).1.z = 0 :=
  NCSCStartupProgram.initProgram_z (auxiliary P mu) (internalSmoothness_pos h) h.Delta_pos
    (NCSCSystem.system h).projectX (NCSCExecution.projectY h)
    (NCSCSystem.system h).project_spec (NCSCExecution.projectY_spec h)
    h.primal_origin h.dual_origin (majorant ell mu)

theorem initializer_gap (h : NCSCClass ell mu Delta P) :
    snapshotPotential (NCSCSystem.system h)
      (Program.eval (auxiliary P mu) (initializer h)).1 -
        (ValueOn P.Y P.f 0 - Delta) ≤ 3 * Delta := by
  apply NCSCStartupProgram.initProgram_potential_gap (auxiliary P mu)
    (internalSmoothness_pos h) h.Delta_pos (NCSCSystem.system h)
    (NCSCExecution.projectY h) (NCSCExecution.projectY_spec h)
    h.primal_origin h.dual_origin (majorant ell mu) (ValueOn P.Y P.f 0 - Delta)
  have hp := (selectedProx_spec (NCSCSystem.intrinsicProx h) 0).2 0 h.primal_origin
  have he : regularizedEnvelope P.X P.Y (auxiliary P mu).f
      (internalSmoothness ell mu) mu (NCSCSystem.intrinsicProx h) 0 ≤ ValueOn P.Y P.f 0 := by
    simpa only [regularizedEnvelope, moreauEnvelope, proxObjective,
      auxiliary_regularized_value, sub_self, vecSq, NCPLVerification.vecSq,
      Pi.zero_apply, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero,
      mul_zero, add_zero] using hp
  linarith

def horizon (ell Delta eps : ℝ) (mu : ℝ) : ℕ :=
  Selection.outerIterations (internalSmoothness ell mu) (3 * Delta) eps

theorem horizon_pos (h : NCSCClass ell mu Delta P) (eps : ℝ) :
    0 < horizon ell Delta eps mu :=
  Selection.outerIterations_pos (internalSmoothness_pos h) (by linarith [h.Delta_pos])

def run (h : NCSCClass ell mu Delta P) (eps rho : ℝ) :=
  NCSCExecution.program h (initializer h) (horizon ell Delta eps mu) (horizon_pos h eps) rho

theorem run_isOS (h : NCSCClass ell mu Delta P) {eps : ℝ} (heps : 0 < eps) (rho : ℝ) :
    NCSC.IsOS h eps (Program.eval P (run h eps rho)).1.1.z := by
  apply NCSCExecution.program_isOS h (initializer h) heps
  · rw [initializer_B]
    exact initializer_energy h
  · rw [initializer_B]
    exact h.Delta_pos.le
  · exact initializer_gap h
  · exact NCSCExecution.horizon_budget (internalSmoothness_pos h)
      (by linarith [h.Delta_pos]) heps

def observedBudget (_h : NCSCClass ell mu Delta P) : ℝ :=
  NCSCInitialBudget.budget ell mu (P.gradX 0 0) (P.gradY 0 0)

def startupCost (h : NCSCClass ell mu Delta P) : ℝ :=
  1 + UniformCost.blockConstant (NCSCStartupProgram.factor Delta (observedBudget h)) *
    Real.sqrt (internalSmoothness ell mu / mu)

theorem initializer_count (h : NCSCClass ell mu Delta P) :
    ((queryTrace P (NCSCProgram.adaptProgram mu (initializer h))).length : ℝ) ≤ startupCost h := by
  rw [NCSCProgram.queryTrace_adaptProgram]
  have hc := NCSCStartupProgram.initProgram_cost (auxiliary P mu)
    (internalSmoothness_pos h) h.mu_pos (intrinsic_parameter_le h) h.Delta_pos
    (NCSCSystem.system h).projectX (NCSCExecution.projectY h)
    (NCSCSystem.system h).project_spec (NCSCExecution.projectY_spec h)
    h.primal_origin h.dual_origin (majorant ell mu)
  simpa only [initializer, startupCost, observedBudget, majorant, firstOrderOracle,
    auxiliary, smul_zero, add_zero] using hc

/-- Actual original-oracle query count. The observed startup logarithm and
the final refinement term are visible, not absorbed into the leading rate. -/
theorem run_count (h : NCSCClass ell mu Delta P) (hmuell : mu ≤ ell)
    (eps : ℝ) {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    ((queryTrace P (run h eps rho)).length : ℝ) ≤ startupCost h +
      (4001 * UniformCost.blockConstant (1 / 400) + UniformCost.blockConstant rho) *
        Real.sqrt (internalSmoothness ell mu / mu) +
      256064 * UniformCost.blockConstant (1 / 400) *
        (ell * (3 * Delta) / eps ^ 2) * Real.sqrt (ell / mu) := by
  have hc := NCSCProgram.adapted_fixedProgram_actual_count (r := mu) P (internalSmoothness_pos h)
    (NCSCSystem.system h).projectX (NCSCExecution.projectY h)
    (NCSCSystem.system h).project_spec (NCSCExecution.projectY_spec h)
    (initializer h) (horizon ell Delta eps mu) (horizon_pos h eps) rho mu
  have hcr := Nat.cast_le (α := ℝ).mpr hc
  have hb := NCSCCost.fixedCount_sqrt_kappa h.ell_pos h.mu_pos hmuell
    (show 0 < 3 * Delta by linarith [h.Delta_pos])
    (queryTrace P (NCSCProgram.adaptProgram mu (initializer h))).length hrho hrho1 (eps := eps)
  have hi := initializer_count h
  have htotal := hcr.trans hb
  change ((queryTrace P (run h eps rho)).length : ℝ) ≤ _ at htotal
  unfold NCSCCost.additiveCost at htotal
  linarith

end
end NCC.Extensions.NCSCTheorem
