import NCC.Moreau.Analytic
import NCC.Upper.CurrentRun

/-!
# Transporting the output guarantee to the current class

A neighborhood-C¹ representative is globalized without changing any feasible
value or gradient. The current mathematical run is then constructed on that
representative. Its output is proved feasible and OS for the original value.

This is not yet the counted-oracle main theorem. In particular, the remaining
oracle-program proof must establish that execution only uses feasible replies
and is independent of the choice of global representative. We expose that
choice below instead of silently identifying the two executions.
-/

namespace NCC.Upper.ClassRun

noncomputable section

open NCCLowerBoundVerification

variable {m n : Nat} {ell D Delta eps : ℝ} {P : NCCInstance m n}

def representative (h : Model.InClass ell D Delta P) :
    PaperGlobalization ell D Delta P := Classical.choice h.globalization

theorem representative_dual_origin (h : Model.InClass ell D Delta P) :
    (0 : EVec n) ∈ (representative h).globalized.Y := by
  rw [(representative h).Y_eq]
  exact h.dual_origin

def output (h : Model.InClass ell D Delta P) (heps : 0 < eps) : EVec m :=
  CurrentRun.output (representative h).class_mem (representative_dual_origin h) heps

theorem output_isOS (h : Model.InClass ell D Delta P) (heps : 0 < eps) :
    Moreau.IsOS h eps (output h heps) := by
  let G := representative h
  have hx := CurrentRun.output_mem G.class_mem (representative_dual_origin h) heps
  have hos := CurrentRun.output_is_OS G.class_mem (representative_dual_origin h) heps
  rw [G.X_eq] at hx hos
  have hs : IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (output h heps) :=
    (isOptimizationStationary_congr G.value_eq_on).mp hos
  exact (Moreau.isOS_iff_feasible_prox h eps (output h heps)).mpr ⟨heps, hx, hs⟩

/-- The auxiliary representative gives exactly the supplied feasible reply. -/
theorem feasible_oracle_eq (h : Model.InClass ell D Delta P)
    {x : EVec m} {y : EVec n} (hx : x ∈ P.X) (hy : y ∈ P.Y) :
    Oracle.firstOrderOracle (representative h).globalized (x, y) =
      Oracle.firstOrderOracle P (x, y) :=
  (representative h).oracle_eq_on x hx y hy

end

end NCC.Upper.ClassRun
