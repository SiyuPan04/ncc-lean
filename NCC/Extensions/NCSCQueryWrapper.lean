import NCC.Upper.Theorem

/-!
# Querying an adaptive program's output

No depth bound uniform over all reply histories is assumed. The client may
choose its finite initialization length from its first reply. We prepend
the required origin and query the projected output after its actual trace.
-/
namespace NCC.Extensions.NCSCQueryWrapper
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle ProjectionGeometry SharedOracle NCC.Upper
open NCC.Upper.AdaptiveMicroProgram

variable {m n : ℕ} {X : Set (EVec m)} {Y : Set (EVec n)}

def wrappedProgram (client : Program X Y (Query m n))
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hx0 : (0 : EVec m) ∈ X) (hy0 : (0 : EVec n) ∈ Y) : Program X Y (Query m n) :=
  .query (0, 0) ⟨hx0, hy0⟩ fun _ => do
    let q ← client
    Program.query (projectX q.1, projectY q.2) ⟨hpX.mem _, hpY.mem _⟩
      (fun _ => .pure (projectX q.1, projectY q.2))

theorem wrappedProgram_first (client : Program X Y (Query m n))
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hx0 : (0 : EVec m) ∈ X) (hy0 : (0 : EVec n) ∈ Y) :
    Program.queryAfterHistory (wrappedProgram client projectX projectY hpX hpY hx0 hy0)
      (0, 0) 0 (emptyHistory m n) = (0, 0) := by
  simp only [Program.queryAfterHistory_zero, wrappedProgram]

def component (client : Program X Y (Query m n))
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hx0 : (0 : EVec m) ∈ X) (hy0 : (0 : EVec n) ∈ Y) :
    DeterministicFOComponent X Y :=
  Program.compile (wrappedProgram client projectX projectY hpX hpY hx0 hy0)
    (0, 0) ⟨hx0, hy0⟩ (wrappedProgram_first client projectX projectY hpX hpY hx0 hy0)

theorem component_final_query (P : NCCInstance m n) (client : Program X Y (Query m n))
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hx0 : (0 : EVec m) ∈ X) (hy0 : (0 : EVec n) ∈ Y) :
    (component client projectX projectY hpX hpY hx0 hy0).queriedAt P
      ((queryTrace P client).length + 1) =
        (projectX (Program.eval P client).1, projectY (Program.eval P client).2) := by
  let finish : Query m n → Program X Y (Query m n) := fun q =>
    .query (projectX q.1, projectY q.2) ⟨hpX.mem _, hpY.mem _⟩
      (fun _ => .pure (projectX q.1, projectY q.2))
  apply Program.queriedAt_compile_eq_of_runSteps_query
  refine ⟨⟨hpX.mem _, hpY.mem _⟩,
    (fun _ => .pure (projectX (Program.eval P client).1, projectY (Program.eval P client).2)), ?_⟩
  rw [← Program.runSteps_oracleStep]
  exact Theorem.runSteps_bind_actual P client finish

theorem component_final_query_of_feasible (P : NCCInstance m n)
    (client : Program X Y (Query m n))
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hx0 : (0 : EVec m) ∈ X) (hy0 : (0 : EVec n) ∈ Y)
    (hfeasible : (Program.eval P client).1 ∈ X ∧ (Program.eval P client).2 ∈ Y) :
    (component client projectX projectY hpX hpY hx0 hy0).queriedAt P
      ((queryTrace P client).length + 1) = Program.eval P client := by
  rw [component_final_query,
    ProjectedMicro.projection_fixed_of_mem hpX hfeasible.1,
    ProjectedMicro.projection_fixed_of_mem hpY hfeasible.2]

theorem wrappedProgram_trace_length (P : NCCInstance m n)
    (client : Program X Y (Query m n))
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hx0 : (0 : EVec m) ∈ X) (hy0 : (0 : EVec n) ∈ Y) :
    (queryTrace P (wrappedProgram client projectX projectY hpX hpY hx0 hy0)).length =
      (queryTrace P client).length + 2 := by
  unfold wrappedProgram
  rw [Theorem.queryTrace_query, List.length_cons, queryTrace_bind, List.length_append,
    Theorem.queryTrace_query, List.length_cons, Theorem.queryTrace_pure, List.length_nil]

/-- Transfer any correctness predicate on a feasible returned pair to an
actual queried pair, counting the origin and final output queries. -/
theorem queried_witness_of_output (P : NCCInstance m n)
    (client : Program X Y (Query m n))
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (hx0 : (0 : EVec m) ∈ X) (hy0 : (0 : EVec n) ∈ Y)
    (predicate : Query m n → Prop)
    (hfeasible : (Program.eval P client).1 ∈ X ∧ (Program.eval P client).2 ∈ Y)
    (houtput : predicate (Program.eval P client)) :
    ∃ t : ℕ, t + 1 = (queryTrace P client).length + 2 ∧
      predicate ((component client projectX projectY hpX hpY hx0 hy0).queriedAt P t) := by
  refine ⟨(queryTrace P client).length + 1, by omega, ?_⟩
  rwa [component_final_query_of_feasible P client projectX projectY hpX hpY hx0 hy0 hfeasible]

end
end NCC.Extensions.NCSCQueryWrapper
