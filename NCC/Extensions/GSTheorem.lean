import NCC.Extensions.GSProgram
import NCC.Upper.Theorem

/-!
# A genuine feasible deterministic GS oracle algorithm

The known-domain client is compiled after an initial origin query and
before a final query at its projected returned pair. Thus the certified
game-stationary pair is an actual queried iterate. No exact saddle
witness or objective gradient is used to construct any query rule.
-/
namespace NCC.Extensions.GSTheorem
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle ProjectionGeometry SharedOracle
open NCC.Upper NCC.Upper.AdaptiveMicroProgram
set_option maxHeartbeats 3000000
variable {m n : Nat} {ell D Delta eps : ℝ}
  {X : Set (EVec m)} {Y : Set (EVec n)}

def wrappedProgram (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) : Program X Y (Query m n) :=
  .query (0, 0) ⟨hzeroX, hzeroY⟩ fun _ => do
    let q ← GSProgram.fullProgram hell hD hDelta heps projectX projectY hprojX hprojY
      0 hzeroX hzeroY
    .query (projectX q.1, projectY q.2) ⟨hprojX.mem _, hprojY.mem _⟩ (fun _ => .pure q)

theorem wrappedProgram_first (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
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

theorem component_final_query (P : NCCInstance m n)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    let p := GSProgram.fullProgram hell hD hDelta heps projectX projectY hprojX hprojY
      0 hzeroX hzeroY
    (component hell hD hDelta heps projectX projectY hprojX hprojY hzeroX hzeroY).queriedAt P
      ((queryTrace P p).length + 1) = (projectX (Program.eval P p).1, projectY (Program.eval P p).2) := by
  dsimp only
  let p := GSProgram.fullProgram hell hD hDelta heps projectX projectY hprojX hprojY
    0 hzeroX hzeroY
  let finish (q : Query m n) : Program X Y (Query m n) :=
    .query (projectX q.1, projectY q.2) ⟨hprojX.mem _, hprojY.mem _⟩ (fun _ => .pure q)
  apply Program.queriedAt_compile_eq_of_runSteps_query
  refine ⟨⟨hprojX.mem _, hprojY.mem _⟩, (fun _ => .pure (Program.eval P p)), ?_⟩
  rw [← Program.runSteps_oracleStep]
  exact Upper.Theorem.runSteps_bind_actual P p finish

theorem wrappedProgram_trace_length (P : NCCInstance m n)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    (queryTrace P
      (wrappedProgram hell hD hDelta heps projectX projectY hprojX hprojY hzeroX hzeroY)).length =
      (queryTrace P (GSProgram.fullProgram hell hD hDelta heps projectX projectY hprojX hprojY
        0 hzeroX hzeroY)).length + 2 := by
  unfold wrappedProgram
  rw [Upper.Theorem.queryTrace_query, List.length_cons, queryTrace_bind, List.length_append,
    Upper.Theorem.queryTrace_query, List.length_cons, Upper.Theorem.queryTrace_pure, List.length_nil]

theorem client_hasGSWitness_of_matches {P : NCCInstance m n}
    (hPX : P.X = X) (hPY : P.Y = Y) (hP : WithinClass ell D Delta P) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    let out := Program.eval P (GSProgram.fullProgram hP.ell_pos hP.D_pos hP.Delta_pos heps
      projectX projectY hprojX hprojY 0 hzeroX hzeroY)
    HasGSWitness P eps out.1 out.2 := by
  subst X
  subst Y
  have hpx := Upper.Theorem.projection_eq hprojX (WithinSystem.chosenProjectX_spec hP)
  have hpy := Upper.Theorem.projection_eq hprojY (WithinSystem.chosenProjectY_spec hP)
  subst projectX
  subst projectY
  simpa only [hP.initialization] using GSProgram.fullProgram_hasGSWitness hP hzeroY heps

def queryBudget (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps) (Delta : ℝ) : Nat :=
  GSProgram.fullNumericalCount hell hD heps Delta + 2

theorem wrappedProgram_actual_count (P : NCCInstance m n)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    (queryTrace P
      (wrappedProgram hell hD hDelta heps projectX projectY hprojX hprojY hzeroX hzeroY)).length ≤
      queryBudget hell hD heps Delta := by
  rw [wrappedProgram_trace_length]
  exact Nat.add_le_add_right (GSProgram.fullProgram_actual_count P hell hD hDelta heps
    projectX projectY hprojX hprojY 0 hzeroX hzeroY) 2

theorem component_hitsGS_of_matches {P : NCCInstance m n}
    (hPX : P.X = X) (hPY : P.Y = Y) (hP : WithinClass ell D Delta P) (heps : 0 < eps)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    ∃ t < queryBudget hP.ell_pos hP.D_pos heps Delta,
      let q := (component hP.ell_pos hP.D_pos hP.Delta_pos heps projectX projectY
        hprojX hprojY hzeroX hzeroY).queriedAt P t
      HasGSWitness P eps q.1 q.2 := by
  let p := GSProgram.fullProgram hP.ell_pos hP.D_pos hP.Delta_pos heps projectX projectY
    hprojX hprojY 0 hzeroX hzeroY
  have hgs := client_hasGSWitness_of_matches hPX hPY hP heps projectX projectY
    hprojX hprojY hzeroX hzeroY
  have hcount := GSProgram.fullProgram_actual_count P hP.ell_pos hP.D_pos hP.Delta_pos heps
    projectX projectY hprojX hprojY 0 hzeroX hzeroY
  change (queryTrace P p).length ≤ _ at hcount
  change HasGSWitness P eps (Program.eval P p).1 (Program.eval P p).2 at hgs
  refine ⟨(queryTrace P p).length + 1, by unfold queryBudget; omega, ?_⟩
  rw [component_final_query]
  have hx := hgs.2.1
  have hy := hgs.2.2.1
  rw [hPX] at hx
  rw [hPY] at hy
  rw [ProjectedMicro.projection_fixed_of_mem hprojX hx,
    ProjectedMicro.projection_fixed_of_mem hprojY hy]
  exact hgs

def domainAlgorithm (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps) :
    DomainWiseDeterministicAlgorithm where
  component Q := component hell hD hDelta heps (domainProjectX Q) (domainProjectY Q)
    (domainProjectX_spec Q) (domainProjectY_spec Q) Q.zero_mem_X Q.zero_mem_Y

theorem exists_domain_algorithm_uniform (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps) :
    ∃ A : DomainWiseDeterministicAlgorithm,
      ∀ (Q : AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
        P.X = Q.X → P.Y = Q.Y → WithinClass ell D Delta P →
          ∃ t < queryBudget hell hD heps Delta,
            HasGSWitness P eps ((A.component Q).queriedAt P t).1 ((A.component Q).queriedAt P t).2 := by
  refine ⟨domainAlgorithm hell hD hDelta heps, ?_⟩
  intro Q P hPX hPY hP
  exact component_hitsGS_of_matches hPX hPY hP heps (domainProjectX Q) (domainProjectY Q)
    (domainProjectX_spec Q) (domainProjectY_spec Q) Q.zero_mem_X Q.zero_mem_Y

end
end NCC.Extensions.GSTheorem
