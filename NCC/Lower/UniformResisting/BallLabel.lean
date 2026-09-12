import NCCLowerBoundVerification.Oracle.Complexity
import NCCLowerBoundVerification.DiameterBall

/-!
# Known ball domains and their diameter labels

In positive dual dimension the positive diameter is determined by the
feasible set itself. Thus choosing an algorithm component by that diameter
does not require access to its objective.
-/
namespace NCC.Lower.UniformResisting
noncomputable section

open NCCLowerBoundVerification

theorem diameterBall_parameter_unique {n : ℕ} (hn : 0 < n)
    {D E : ℝ} (hD : 0 < D) (hE : 0 < E)
    (heq : diameterBall n D = diameterBall n E) : D = E := by
  let i : Fin n := ⟨0, hn⟩
  have hs (c : ℝ) : vecSq (Pi.single i c : EVec n) = c ^ 2 := by
    unfold vecSq NCPLVerification.vecSq
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · simp
  have hmem (c : ℝ) : (Pi.single i (c / 2) : EVec n) ∈ diameterBall n c := by
    change vecSq (Pi.single i (c / 2)) ≤ (c / 2) ^ 2
    rw [hs]
  have hDE := hmem D
  rw [heq] at hDE
  have hED := hmem E
  rw [← heq] at hED
  change vecSq (Pi.single i (D / 2)) ≤ (E / 2) ^ 2 at hDE
  change vecSq (Pi.single i (E / 2)) ≤ (D / 2) ^ 2 at hED
  rw [hs] at hDE hED
  nlinarith

def ballLabel (m n : ℕ) (D : ℝ) : Oracle.AdmissibleDomainPair where
  m := m
  n := n
  X := Set.univ
  Y := diameterBall n D
  zero_mem_X := Set.mem_univ _
  zero_mem_Y := by simp [diameterBall, vecSq, NCPLVerification.vecSq, sq_nonneg]
  X_closed := isClosed_univ
  X_convex := convex_univ
  Y_closed := diameterBall_closed n D
  Y_convex := diameterBall_convex n D

end
end NCC.Lower.UniformResisting
