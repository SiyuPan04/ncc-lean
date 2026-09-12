import NCC.Construction.Terminal
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The exact feasible-maximizer clause, including the ball boundary

This proves the last clause of `prop:function-class` under its literal
non-strict hypothesis. Local inactivity is unnecessary: the constrained
and unconstrained differentiable values touch at any feasible free maximizer.
-/
namespace NCC.Construction.BoundaryInactivity
noncomputable section
open NCCLowerBoundVerification Set Filter
open Composite Terminal Frontier

theorem fderiv_eq_of_le_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (hle : ∀ y, f y ≤ g y) (heq : f x = g x) :
    fderiv ℝ f x = fderiv ℝ g x := by
  have hmin : IsLocalMin (fun y => g y - f y) x := by
    apply Filter.Eventually.of_forall
    intro y
    change g x - f x ≤ g y - f y
    rw [heq, sub_self]
    exact sub_nonneg.mpr (hle y)
  have hz := hmin.hasFDerivAt_eq_zero (hg.hasFDerivAt.sub hf.hasFDerivAt)
  exact (sub_eq_zero.mp hz).symm

theorem inner_value_le_explicit {m n : ℕ} (hn : 10 ≤ n) (D : ℝ)
    (p : Inner.Pulse m) : Inner.V (by omega : 0 < n) D p ≤ innerExplicit p := by
  apply csSup_le
  · exact ⟨_, ⟨0, by simp [Inner.dualBall, vecSq, NCPLVerification.vecSq]; positivity, rfl⟩⟩
  · rintro _ ⟨y, _, rfl⟩
    exact (freeMaximizer_maximal (by omega) p y).trans_eq (freeMaximizer_value hn p)

theorem inner_value_eq_of_feasible {m n : ℕ} (hn : 10 ≤ n) {D : ℝ}
    {p : Inner.Pulse m}
    (hfeas : freeMaximizer (by omega : 0 < n) p ∈ Inner.dualBall m n D) :
    Inner.V (by omega : 0 < n) D p = innerExplicit p := by
  have hm : IsMaximizerOn (Inner.dualBall m n D) (Inner.objective (by omega : 0 < n)) p
      (freeMaximizer (by omega) p) :=
    ⟨hfeas, fun y _ => freeMaximizer_maximal (by omega) p y⟩
  exact (value_eq_of_isMaximizerOn hm).trans (freeMaximizer_value hn p)

theorem inner_fderiv_eq_of_feasible {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    {p : Inner.Pulse m}
    (hfeas : freeMaximizer (by omega : 0 < n) p ∈ Inner.dualBall m n D) :
    fderiv ℝ (Inner.V (by omega : 0 < n) D) p = fderiv ℝ innerExplicit p :=
  fderiv_eq_of_le_of_eq (Inner.V_differentiable (by omega) hD p)
    (innerExplicit_contDiff.differentiable (by simp) p)
    (inner_value_le_explicit hn D) (inner_value_eq_of_feasible hn hfeas)

def freeValue {m n : ℕ} (hn : 0 < n) : Primal m → ℝ :=
  ValueOn Set.univ (objective hn)

theorem freeValue_eq_explicit {m n : ℕ} (hn : 10 ≤ n) (x : Primal m) :
    freeValue (by omega : 0 < n) x = explicitValue x := by
  have hm : IsMaximizerOn Set.univ (objective (by omega : 0 < n)) x
      (freeMaximizer (by omega) (pulse x)) := by
    refine ⟨Set.mem_univ _, ?_⟩
    intro y _
    rw [objective_split, objective_split]
    linarith [freeMaximizer_maximal (by omega : 0 < n) (pulse x) y]
  rw [freeValue, value_eq_of_isMaximizerOn hm, objective_split,
    freeMaximizer_value hn, explicitValue]

theorem explicitValue_differentiable {m : ℕ} :
    Differentiable ℝ (explicitValue : Primal m → ℝ) :=
  (outer_flat_contDiff.differentiable (by simp)).add
    ((innerExplicit_contDiff.differentiable (by simp)).comp
      (pulse_contDiff.differentiable (by simp)))

theorem value_le_explicit {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (x : Primal m) : value (by omega : 0 < n) D x ≤ explicitValue x := by
  rw [value_split (by omega) hD, explicitValue]
  linarith [inner_value_le_explicit hn D (pulse x)]

theorem value_eq_explicit_of_feasible {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    {x : Primal m}
    (hfeas : freeMaximizer (by omega : 0 < n) (pulse x) ∈ Inner.dualBall m n D) :
    value (by omega : 0 < n) D x = explicitValue x := by
  rw [value_split (by omega) hD, explicitValue, inner_value_eq_of_feasible hn hfeas]

theorem value_fderiv_eq_explicit_of_feasible {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    {x : Primal m}
    (hfeas : freeMaximizer (by omega : 0 < n) (pulse x) ∈ Inner.dualBall m n D) :
    fderiv ℝ (value (by omega : 0 < n) D) x = fderiv ℝ explicitValue x :=
  fderiv_eq_of_le_of_eq (value_differentiable (by omega) hD x)
    (explicitValue_differentiable x) (value_le_explicit hn hD)
    (value_eq_explicit_of_feasible hn hD hfeas)

/-- Literal non-strict radius condition from the manuscript. In particular
the equality case is included, without claiming equality on a neighborhood. -/
theorem restricted_value_and_gradient_identity {m n : ℕ} (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 < D) (x : Primal m)
    (hbound : Inner.norm₂ (freeMaximizer (by omega : 0 < n) (pulse x)) ≤ D / 2) :
    value (by omega : 0 < n) D x = freeValue (by omega : 0 < n) x ∧
      gradient (value (by omega : 0 < n) D) x = gradient (freeValue (by omega : 0 < n)) x := by
  have hfeas : freeMaximizer (by omega : 0 < n) (pulse x) ∈ Inner.dualBall m n D := by
    change vecSq _ ≤ (D / 2) ^ 2
    have hs := norm₂_sq (freeMaximizer (by omega : 0 < n) (pulse x))
    have hnrm := norm₂_nonneg (freeMaximizer (by omega : 0 < n) (pulse x))
    nlinarith
  have he : freeValue (m := m) (by omega : 0 < n) = explicitValue := by
    funext z
    exact freeValue_eq_explicit hn z
  rw [he]
  refine ⟨value_eq_explicit_of_feasible hn hD.le hfeas, ?_⟩
  funext i
  change (fderiv ℝ (value (by omega : 0 < n) D) x) _ = (fderiv ℝ explicitValue x) _
  rw [value_fderiv_eq_explicit_of_feasible hn hD.le hfeas]

end
end NCC.Construction.BoundaryInactivity
