import NCC.Upper.WithinProgram
import NCC.Oracle.Minimax

/-!
# Domain-wise causal queried-iterate upper bound

The component is constructed from known domains, their projections, and
numerical parameters only. An origin query is prepended to the current
adaptive client, and its projected output is queried last. These two
explicit calls enforce the queried-iterate convention and cost at most
two additional local oracle evaluations.

The target algorithm type here enforces causality, feasible queries after
every history, and the initial origin. The current manuscript's
`def:deterministic-algorithm` requires maps from reply histories, with no
measurability clause. No separate measurability property is claimed here.
-/

namespace NCC.Upper.Theorem

noncomputable section

open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle ProjectionGeometry SharedOracle AdaptiveMicroProgram
open scoped ENNReal

set_option maxHeartbeats 3000000

variable {m n : Nat} {ell D Delta eps : ℝ}
  {X : Set (EVec m)} {Y : Set (EVec n)}

/-- The exact number of replies used by a finite program, not a uniform
cap, suffices to reach its continuation. This permits adaptive depth. -/
theorem runSteps_bind_actual {α β : Type} (P : NCCInstance m n)
    (p : Program X Y α) (k : α → Program X Y β) :
    Program.runSteps P (p >>= k) (queryTrace P p).length = k (Program.eval P p) := by
  induction p with
  | pure a => rfl
  | query q hq next ih =>
      change Program.runSteps P (.query q hq (fun reply => next reply >>= k))
        ((queryTrace P (next (firstOrderOracle P q))).length + 1) = _
      rw [← Program.runSteps_oracleStep]
      exact ih (firstOrderOracle P q)

theorem queryTrace_query {α : Type} (P : NCCInstance m n)
    (q : Query m n) (hq : q.1 ∈ X ∧ q.2 ∈ Y)
    (next : OracleReply m n → Program X Y α) :
    queryTrace P (.query q hq next) = q :: queryTrace P (next (firstOrderOracle P q)) := rfl

theorem queryTrace_pure {α : Type} (P : NCCInstance m n) (a : α) :
    queryTrace P (.pure a : Program X Y α) = [] := rfl

def wrappedProgram (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    Program X Y (EVec m) :=
  .query (0, 0) ⟨hzeroX, hzeroY⟩ fun _ => do
    let x ← CurrentProgram.program hell hD hDelta heps projectX projectY
      hprojX hprojY 0 hzeroX hzeroY
    Program.query (projectX x, 0) ⟨hprojX.mem x, hzeroY⟩ (fun _ => .pure x)

theorem wrappedProgram_first (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    Program.queryAfterHistory
      (wrappedProgram hell hD hDelta heps projectX projectY hprojX hprojY hzeroX hzeroY)
      (0, 0) 0 (emptyHistory m n) = (0, 0) := by
  simp only [Program.queryAfterHistory_zero, wrappedProgram]

def component (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    DeterministicFOComponent X Y :=
  Program.compile
    (wrappedProgram hell hD hDelta heps projectX projectY hprojX hprojY hzeroX hzeroY)
    (0, 0) ⟨hzeroX, hzeroY⟩
    (wrappedProgram_first hell hD hDelta heps projectX projectY hprojX hprojY hzeroX hzeroY)

/-- The final query occurs at time `N+1`, where `N` is the actual adaptive
client count. There is no fixed-depth or padded-continuation assumption. -/
theorem component_final_query (P : NCCInstance m n)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    let client := CurrentProgram.program hell hD hDelta heps projectX projectY
      hprojX hprojY 0 hzeroX hzeroY
    DeterministicFOComponent.queriedAt
      (component hell hD hDelta heps projectX projectY hprojX hprojY hzeroX hzeroY) P
        ((queryTrace P client).length + 1) = (Program.eval P client, 0) := by
  dsimp only
  let client := CurrentProgram.program hell hD hDelta heps projectX projectY
    hprojX hprojY 0 hzeroX hzeroY
  let finish : EVec m → Program X Y (EVec m) := fun x =>
    .query (projectX x, 0) ⟨hprojX.mem x, hzeroY⟩ (fun _ => .pure x)
  have hquery : DeterministicFOComponent.queriedAt
      (component hell hD hDelta heps projectX projectY hprojX hprojY hzeroX hzeroY) P
        ((queryTrace P client).length + 1) = (projectX (Program.eval P client), 0) := by
    apply Program.queriedAt_compile_eq_of_runSteps_query
    refine ⟨⟨hprojX.mem _, hzeroY⟩, (fun _ => .pure (Program.eval P client)), ?_⟩
    rw [← Program.runSteps_oracleStep]
    exact runSteps_bind_actual P client finish
  have hx := CurrentProgram.eval_program_mem P hell hD hDelta heps projectX projectY
    hprojX hprojY 0 hzeroX hzeroY
  have hfix := ProjectedMicro.projection_fixed_of_mem hprojX hx
  simpa only [client, hfix] using hquery

theorem wrappedProgram_trace_length (P : NCCInstance m n)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    (queryTrace P
      (wrappedProgram hell hD hDelta heps projectX projectY hprojX hprojY hzeroX hzeroY)).length =
      (queryTrace P (CurrentProgram.program hell hD hDelta heps projectX projectY
        hprojX hprojY 0 hzeroX hzeroY)).length + 2 := by
  unfold wrappedProgram
  rw [queryTrace_query, List.length_cons, queryTrace_bind, List.length_append,
    queryTrace_query, List.length_cons, queryTrace_pure, List.length_nil]

/-- The known-domain projection equals every projection satisfying the
variational characterization; source-class membership is not a client input. -/
theorem projection_eq {d : Nat} {C : Set (EVec d)} {p q : EVec d → EVec d}
    (hp : IsEuclideanProjection C p) (hq : IsEuclideanProjection C q) : p = q := by
  funext z
  exact eq_projection_of_normal hp (hq.mem z) (hq.normal z)

theorem client_correct_of_matches {P : NCCInstance m n}
    (hPX : P.X = X) (hPY : P.Y = Y) (hP : WithinClass ell D Delta P) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    let client := CurrentProgram.program hP.ell_pos hP.D_pos hP.Delta_pos heps
      projectX projectY hprojX hprojY 0 hzeroX hzeroY
    Moreau.Within.IsOS hP eps (Program.eval P client) ∧
      ((queryTrace P client).length : ℝ) ≤ CurrentCost.traceRateConstant *
        ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) := by
  subst X
  subst Y
  have hpx := projection_eq hprojX (WithinSystem.chosenProjectX_spec hP)
  have hpy := projection_eq hprojY (WithinSystem.chosenProjectY_spec hP)
  subst projectX
  subst projectY
  simpa only [hP.initialization] using WithinProgram.feasible_program_correct hP heps

def uniformRate (ell D Delta eps : ℝ) : ℝ :=
  (ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)

theorem uniformRate_ge_one (hell : 0 < ell) (hDelta : 0 < Delta) :
    1 ≤ uniformRate ell D Delta eps := by
  have hA0 : 0 ≤ ell * Delta / eps ^ 2 := by positivity
  have hA : 1 ≤ ell * Delta / eps ^ 2 + 1 := by linarith
  have hM : 1 ≤ max 1 (ell * D / eps) := le_max_left _ _
  simpa only [uniformRate, one_mul] using mul_le_mul hA hM (by norm_num : (0 : ℝ) ≤ 1)
    (by linarith : 0 ≤ ell * Delta / eps ^ 2 + 1)

def queryBudget (ell D Delta eps : ℝ) : Nat :=
  ⌈(CurrentCost.traceRateConstant + 2) * uniformRate ell D Delta eps⌉₊

/-- The wrapper's two additional queries are included in the actual count. -/
theorem wrappedProgram_uniform_query_bound {P : NCCInstance m n}
    (hPX : P.X = X) (hPY : P.Y = Y) (hP : WithinClass ell D Delta P) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    ((queryTrace P
      (wrappedProgram hP.ell_pos hP.D_pos hP.Delta_pos heps projectX projectY
        hprojX hprojY hzeroX hzeroY)).length : ℝ) ≤
      (CurrentCost.traceRateConstant + 2) * uniformRate ell D Delta eps := by
  have hc := (client_correct_of_matches hPX hPY hP heps projectX projectY
    hprojX hprojY hzeroX hzeroY).2
  have hr := uniformRate_ge_one (D := D) (eps := eps) hP.ell_pos hP.Delta_pos
  rw [wrappedProgram_trace_length]
  simp only [Nat.cast_add, Nat.cast_ofNat]
  change _ ≤ (CurrentCost.traceRateConstant + 2) *
    ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps))
  dsimp only [uniformRate] at hr
  nlinarith

theorem component_hitsWithin_of_matches {P : NCCInstance m n}
    (hPX : P.X = X) (hPY : P.Y = Y) (hP : WithinClass ell D Delta P) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    DeterministicFOComponent.HitsWithin
      (component hP.ell_pos hP.D_pos hP.Delta_pos heps
        projectX projectY hprojX hprojY hzeroX hzeroY) P ell eps
      (queryBudget ell D Delta eps) := by
  let client := CurrentProgram.program hP.ell_pos hP.D_pos hP.Delta_pos heps
    projectX projectY hprojX hprojY 0 hzeroX hzeroY
  let N := (queryTrace P client).length
  have hspec := client_correct_of_matches hPX hPY hP heps projectX projectY
    hprojX hprojY hzeroX hzeroY
  have hrate := uniformRate_ge_one (D := D) (eps := eps) hP.ell_pos hP.Delta_pos
  have hN : (N + 2 : ℝ) ≤ (CurrentCost.traceRateConstant + 2) * uniformRate ell D Delta eps := by
    have hc : (N : ℝ) ≤ CurrentCost.traceRateConstant * uniformRate ell D Delta eps := hspec.2
    nlinarith
  have hbudget : N + 2 ≤ queryBudget ell D Delta eps := by
    have hh := hN.trans (Nat.le_ceil ((CurrentCost.traceRateConstant + 2) * uniformRate ell D Delta eps))
    exact_mod_cast hh
  refine ⟨N + 1, by omega, ?_⟩
  unfold DeterministicFOComponent.HitsAt
  rw [component_final_query]
  exact (Moreau.Within.isOS_iff_feasible_prox hP eps _).1 hspec.1 |>.2.2

def domainComponent (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (Q : AdmissibleDomainPair) : DeterministicFOComponent Q.X Q.Y :=
  component hell hD hDelta heps (domainProjectX Q) (domainProjectY Q)
    (domainProjectX_spec Q) (domainProjectY_spec Q) Q.zero_mem_X Q.zero_mem_Y

/-- One algorithm across all domain labels; no objective or class proof
is an argument to any component's query rule. -/
def domainAlgorithm (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps) :
    DomainWiseDeterministicAlgorithm where
  component Q := domainComponent hell hD hDelta heps Q

theorem domainAlgorithm_hitsWithin (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps) (Q : AdmissibleDomainPair)
    (P : NCCInstance Q.m Q.n) (hPX : P.X = Q.X) (hPY : P.Y = Q.Y)
    (hP : WithinClass ell D Delta P) :
    DeterministicFOComponent.HitsWithin ((domainAlgorithm hell hD hDelta heps).component Q)
      P ell eps (queryBudget ell D Delta eps) :=
  component_hitsWithin_of_matches hPX hPY hP heps (domainProjectX Q) (domainProjectY Q)
    (domainProjectX_spec Q) (domainProjectY_spec Q) Q.zero_mem_X Q.zero_mem_Y

theorem exists_domain_algorithm_uniform (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps) :
    ∃ A : DomainWiseDeterministicAlgorithm,
      ∀ (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
        P.X = Q.X → P.Y = Q.Y → WithinClass ell D Delta P →
          queriedHittingTime (A.component Q) P ell eps < (queryBudget ell D Delta eps : WithTop Nat) := by
  refine ⟨domainAlgorithm hell hD hDelta heps, ?_⟩
  intro Q P hPX hPY hP
  apply (queriedHittingTime_lt_iff _ _ _ _ _).2
  exact domainAlgorithm_hitsWithin hell hD hDelta heps Q P hPX hPY hP

/-- The same counted client bounds the source-class infimum-over-algorithms,
supremum-over-domains-and-instances hitting-time functional. -/
theorem minimaxHittingTime_upper (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps) :
    NCC.Complexity.minimaxHittingTime ell D Delta eps ≤
      (queryBudget ell D Delta eps : WithTop Nat) := by
  apply NCC.Complexity.minimaxHittingTime_upper_of_algorithm
  obtain ⟨A, hA⟩ := exists_domain_algorithm_uniform hell hD hDelta heps
  refine ⟨A, ?_⟩
  intro Q P hP
  exact (hA Q P hP.1 hP.2.1 hP.2.2).le

theorem queryBudget_le_rate (hell : 0 < ell) (hDelta : 0 < Delta) :
    (queryBudget ell D Delta eps : ℝ) ≤
      (CurrentCost.traceRateConstant + 3) * uniformRate ell D Delta eps := by
  have hr := uniformRate_ge_one (D := D) (eps := eps) hell hDelta
  have hc := CurrentCost.traceRateConstant_pos
  have hb : 0 ≤ (CurrentCost.traceRateConstant + 2) * uniformRate ell D Delta eps := by
    exact mul_nonneg (by linarith) (by linarith)
  have hceil := (Nat.ceil_lt_add_one hb).le
  change (queryBudget ell D Delta eps : ℝ) ≤ _ at hceil
  nlinarith

/-- The literal source-class minimax complexity has the displayed real
uniform upper rate, including all wrapper queries and integer rounding. -/
theorem minimaxOracleComplexity_upper (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps) :
    NCC.Complexity.minimaxOracleComplexity ell D Delta eps ≤
      ENNReal.ofReal ((CurrentCost.traceRateConstant + 3) * uniformRate ell D Delta eps) := by
  have hnat := NCC.Complexity.minimaxOracleComplexity_upper_of_horizon
    (minimaxHittingTime_upper hell hD hDelta heps)
  calc
    _ ≤ (queryBudget ell D Delta eps : ℝ≥0∞) := hnat
    _ = ENNReal.ofReal (queryBudget ell D Delta eps : ℝ) := by simp
    _ ≤ _ := ENNReal.ofReal_le_ofReal (queryBudget_le_rate hell hDelta)

end
end NCC.Upper.Theorem
