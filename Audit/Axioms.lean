import NCC
import Lean.Util.CollectAxioms

/-!
This audit checks the dependency axioms of every theorem and definition in namespace `NCC`.
It rejects `sorryAx` and any project-specific axiom, allowing only Lean's
standard logical foundations. It does NOT prove that explicit hypotheses in
the theorem types hold for the paper's functions or algorithm.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  let mut definitions : Nat := 0
  for (name, info) in env.constants.toList do
    if (`NCC).isPrefixOf name then
      match info with
      | .axiomInfo _ => throwError "Project-specific axiom: {name}"
      | .thmInfo _ =>
          let axioms ← Lean.collectAxioms name
          for ax in axioms do
            unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
              throwError "Theorem {name} depends on disallowed axiom {ax}"
          count := count + 1
      | .defnInfo _ | .opaqueInfo _ =>
          let axioms ← Lean.collectAxioms name
          for ax in axioms do
            unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
              throwError "Definition {name} depends on disallowed axiom {ax}"
          definitions := definitions + 1
      | _ => pure ()
  if count == 0 then
    throwError "No NCC theorem declarations were audited"
  logInfo m!"Axiom audit passed for {count} NCC theorem declarations and {definitions} definitions."

#print axioms NCC.Lower.no_stationarity_before_terminal
#print axioms NCC.Lower.frontier_small_gradient_impossible
#print axioms NCC.Moreau.initial_gradient_bound_of_proximal_inequality
#print axioms NCC.Upper.selected_gradient_squared_bound
#print axioms NCC.Lower.ZeroRespecting.current_zeroRespecting_lower
#print axioms NCC.Lower.DeterministicLower.current_deterministic_lower
#print axioms NCC.Upper.Theorem.minimaxOracleComplexity_upper
#print axioms NCC.MainResults.matching_oracle_complexity
#print axioms NCC.MainResults.source_matching_oracle_complexity
#print axioms NCC.Complexity.PositiveDimension.minimaxOracleComplexity_eq
#print axioms NCC.Complexity.PositiveDimension.oracleComplexity_bounds
#print axioms NCC.Extensions.GSRate.nc_c_gs_complexity
#print axioms NCC.Extensions.NCSCInitialization.arbitrarily_large_dual_initialization
#print axioms NCC.Lower.UniformResisting.finite_horizon_resisting_oracle
#print axioms NCC.Extensions.NCSCGSReadout.readout_hasGSWitness
#print axioms NCC.Lower.UniformResisting.exists_all_history_feasible_equivalent
#print axioms NCC.Extensions.NCSC.gradient_le_internal_residual
#print axioms NCC.Extensions.NCSC.dual_set_eq_origin_of_smoothness_lt
#print axioms NCC.Extensions.NCSCTheorem.run_isOS
#print axioms NCC.Extensions.NCSCTheorem.run_count
#print axioms NCC.Construction.q_positive_iteratedDeriv_bounded
#print axioms NCC.Construction.e_s_positive_iteratedDeriv_bounded
#print axioms NCC.Construction.e_nu_positive_iteratedDeriv_bounded
#print axioms NCC.Extensions.NCSCDomain.domainAlgorithm_queried_OS
#print axioms NCC.Extensions.NCSCGSTheorem.queried_isGS
#print axioms NCC.Extensions.NCSCGSUniform.algorithm_queried_isGS
#print axioms NCC.Lower.WithinRotation.class_rotate
#print axioms NCC.Lower.WithinRotation.gradient_covariance
#print axioms NCC.Construction.BoundaryInactivity.restricted_value_and_gradient_identity
#print axioms NCC.Upper.ExactStartup.startup_state_construction
#print axioms NCC.Upper.ExactResidual.residual_comparison
#print axioms NCC.Upper.ExactResidual.evaluated_program_gradient_bound
#print axioms NCC.Extensions.NCSCStartupLower.adapted_initProgram_exact_count
#print axioms NCC.Extensions.NCSCQuadraticClass.class_mem
#print axioms NCC.Extensions.NCSCQuadraticClass.observed_budget_unbounded
#print axioms NCC.Extensions.NCSCQuadraticStartup.quadratic_initializer_exact_count
#print axioms NCC.Extensions.NCSCQuadraticStartup.no_uniform_run_completion_bound
#print axioms NCC.Extensions.NCSCZeroChainObstruction.fixed_conditioned_GS_obstruction
#print axioms NCC.Extensions.NCSCRotation.class_rotate
#print axioms NCC.Extensions.NCSCRotation.isGS_projects
#print axioms NCC.Extensions.NCSCDeterministicObstruction.fixed_conditioned_arbitrary_deterministic
#print axioms NCC.Extensions.NCSCDeterministicObstruction.positive_domainwise_no_finite_GS_cap
