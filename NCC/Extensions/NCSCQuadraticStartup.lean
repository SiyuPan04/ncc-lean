import NCC.Extensions.NCSCQuadraticClass
import NCC.Extensions.NCSCStartupLower

/-!
# Unbounded completion cost of the configured startup on an actual class

The fixed-parameter translated quadratics belong to NCSCClass 1 1 1.
Their initial observed budgets equal 3*c^2. The configured initializer,
and hence the full tracked run containing it, therefore have unbounded
completion query counts. The same objective-independent program is used
throughout the family.

These are completion counts, not earliest OS/GS hitting times. In fact
these objectives are independent of x, so they cannot establish an OS
hitting-time lower bound. No all-algorithms lower bound is claimed.
-/
namespace NCC.Extensions.NCSCQuadraticStartup
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle RelativeFOAM SharedOracle OuterTrajectoryConcrete
open NCC.Upper.AdaptiveMicroProgram NCSCQuadraticClass
set_option maxHeartbeats 3000000

theorem initializer_exact_count {m n : Nat} {ell mu Delta : ℝ} {P : NCCInstance m n}
    (h : NCSC.NCSCClass ell mu Delta P) :
    (queryTrace P (NCSCProgram.adaptProgram mu (NCSCTheorem.initializer h))).length =
      blockIterations (alpha (NCSC.internalSmoothness ell mu) mu)
        (NCSCStartupProgram.factor Delta (NCSCTheorem.observedBudget h)) *
          (ProjectedMicro.feasibleMicroIterations + 1) + 1 :=
  NCSCStartupLower.adapted_initProgram_exact_count P (NCSC.internalSmoothness_pos h) h.Delta_pos
    (NCSCSystem.system h).projectX (NCSCExecution.projectY h)
    (NCSCSystem.system h).project_spec (NCSCExecution.projectY_spec h)
    h.primal_origin h.dual_origin (NCSCTheorem.majorant ell mu) mu

theorem quadratic_initializer_exact_count (c : ℝ) :
    (queryTrace (quadratic c)
      (NCSCProgram.adaptProgram 1 (NCSCTheorem.initializer (class_mem c)))).length =
      blockIterations (alpha 16 1) (NCSCStartupProgram.factor 1 (3 * c ^ 2)) *
        (ProjectedMicro.feasibleMicroIterations + 1) + 1 := by
  rw [initializer_exact_count, observed_budget]
  norm_num [NCSC.internalSmoothness]

/-- No hidden objective dependence occurs in the projection choices or
program construction. Only the true replies vary along the family. -/
theorem initializer_same_program (c : ℝ) :
    NCSCProgram.adaptProgram 1 (NCSCTheorem.initializer (class_mem c)) =
      NCSCProgram.adaptProgram 1 (NCSCTheorem.initializer (class_mem 0)) := by
  rfl

theorem initializer_completion_unbounded (K : Nat) :
    ∃ c : ℝ, K < (queryTrace (quadratic c)
      (NCSCProgram.adaptProgram 1 (NCSCTheorem.initializer (class_mem c)))).length := by
  obtain ⟨c, hc⟩ := observed_budget_unbounded (NCSCStartupLower.budgetThreshold 16 1 1 K)
  rw [observed_budget] at hc
  have hk := NCSCStartupLower.blockIterations_gt_of_large_budget
    (by norm_num : (0 : ℝ) < 16) (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (0 : ℝ) < 1) K hc
  refine ⟨c, ?_⟩
  rw [quadratic_initializer_exact_count]
  have hm : blockIterations (alpha 16 1) (NCSCStartupProgram.factor 1 (3 * c ^ 2)) ≤
      blockIterations (alpha 16 1) (NCSCStartupProgram.factor 1 (3 * c ^ 2)) *
        (ProjectedMicro.feasibleMicroIterations + 1) :=
    Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  omega

theorem one_initializer_completion_unbounded (K : Nat) :
    ∃ c : ℝ, K < (queryTrace (quadratic c)
      (NCSCProgram.adaptProgram 1 (NCSCTheorem.initializer (class_mem 0)))).length := by
  obtain ⟨c, hc⟩ := initializer_completion_unbounded K
  exact ⟨c, hc⟩

/-- The initializer is an actual prefix of the adapted full run. -/
theorem initializer_count_le_run_count {m n : Nat} {ell mu Delta : ℝ} {P : NCCInstance m n}
    (h : NCSC.NCSCClass ell mu Delta P) (eps rho : ℝ) :
    (queryTrace P (NCSCProgram.adaptProgram mu (NCSCTheorem.initializer h))).length ≤
      (queryTrace P (NCSCTheorem.run h eps rho)).length := by
  unfold NCSCTheorem.run NCSCExecution.program
  rw [NCSCProgram.queryTrace_adaptProgram, NCSCProgram.queryTrace_adaptProgram,
    NCSCProgram.fixedProgram, queryTrace_bind, List.length_append]
  omega

theorem run_completion_unbounded (eps rho : ℝ) (K : Nat) :
    ∃ c : ℝ, K < (queryTrace (quadratic c) (NCSCTheorem.run (class_mem c) eps rho)).length := by
  obtain ⟨c, hc⟩ := initializer_completion_unbounded K
  exact ⟨c, hc.trans_le (initializer_count_le_run_count (class_mem c) eps rho)⟩

theorem run_same_program (c eps rho : ℝ) :
    NCSCTheorem.run (class_mem c) eps rho = NCSCTheorem.run (class_mem 0) eps rho := by
  rfl

theorem one_run_completion_unbounded (eps rho : ℝ) (K : Nat) :
    ∃ c : ℝ, K < (queryTrace (quadratic c) (NCSCTheorem.run (class_mem 0) eps rho)).length := by
  obtain ⟨c, hc⟩ := run_completion_unbounded eps rho K
  exact ⟨c, hc⟩

/-- Even with ell=mu=Delta=1 and fixed epsilon/refinement parameters,
this one program has no uniform completion-query budget on the class. -/
theorem no_uniform_run_completion_bound (eps rho : ℝ) :
    ¬∃ K : Nat, ∀ c : ℝ,
      (queryTrace (quadratic c) (NCSCTheorem.run (class_mem 0) eps rho)).length ≤ K := by
  rintro ⟨K, hK⟩
  obtain ⟨c, hc⟩ := one_run_completion_unbounded eps rho K
  exact (not_lt_of_ge (hK c)) hc

end
end NCC.Extensions.NCSCQuadraticStartup
