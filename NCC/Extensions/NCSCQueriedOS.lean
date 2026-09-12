import NCC.Extensions.NCSCTheorem

/-! A final feasible query makes the returned actual OS point a queried point.
It costs exactly one extra original first-order oracle call. -/
namespace NCC.Extensions.NCSCQueriedOS
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper Oracle
open NCC.Upper.AdaptiveMicroProgram
open NCC.Extensions.NCSC
set_option maxHeartbeats 3000000

variable {m n : ℕ} {ell mu Delta : ℝ} {P : NCCInstance m n}

def queriedRun (h : NCSCClass ell mu Delta P) (eps rho : ℝ) : Program P.X P.Y (EVec m) := do
  let out ← NCSCTheorem.run h eps rho
  .query (out.1.1.z, 0) ⟨out.1.2, h.dual_origin⟩ fun _ => .pure out.1.1.z

theorem eval_queriedRun (h : NCSCClass ell mu Delta P) (eps rho : ℝ) :
    Program.eval P (queriedRun h eps rho) =
      (Program.eval P (NCSCTheorem.run h eps rho)).1.1.z := by
  simp only [queriedRun, Program.eval_bind, Program.eval_query, Program.eval_pure]

theorem queriedRun_isOS (h : NCSCClass ell mu Delta P) {eps : ℝ}
    (heps : 0 < eps) (rho : ℝ) : NCSC.IsOS h eps (Program.eval P (queriedRun h eps rho)) := by
  rw [eval_queriedRun]
  exact NCSCTheorem.run_isOS h heps rho

theorem queryTrace_queriedRun (h : NCSCClass ell mu Delta P) (eps rho : ℝ) :
    queryTrace P (queriedRun h eps rho) = queryTrace P (NCSCTheorem.run h eps rho) ++
      [((Program.eval P (NCSCTheorem.run h eps rho)).1.1.z, 0)] := by
  rw [queriedRun, queryTrace_bind]
  rfl

theorem queryTrace_length (h : NCSCClass ell mu Delta P) (eps rho : ℝ) :
    (queryTrace P (queriedRun h eps rho)).length =
      (queryTrace P (NCSCTheorem.run h eps rho)).length + 1 := by
  rw [queryTrace_queriedRun, List.length_append]
  rfl

theorem output_is_queried (h : NCSCClass ell mu Delta P) (eps rho : ℝ) :
    (Program.eval P (queriedRun h eps rho), 0) ∈ queryTrace P (queriedRun h eps rho) := by
  rw [eval_queriedRun, queryTrace_queriedRun]
  exact List.mem_append_right _ (by simp)

theorem all_histories_feasible (h : NCSCClass ell mu Delta P) (eps rho : ℝ)
    (t : ℕ) (history : ReplyHistory m n t) :
    let q := Program.queryAfterHistory (queriedRun h eps rho) (0, 0) t history
    q.1 ∈ P.X ∧ q.2 ∈ P.Y :=
  Program.queryAfterHistory_mem _ _ ⟨h.primal_origin, h.dual_origin⟩ t history

end
end NCC.Extensions.NCSCQueriedOS
