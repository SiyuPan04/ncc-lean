import NCC.Extensions.NCSCTheorem
import NCC.Extensions.NCSCInitialization

/-! An actual fixed-parameter NC-SC family with unbounded observed startup
budget. The objective is independent of its primal coordinate. -/
namespace NCC.Extensions.NCSCQuadraticClass
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle NCC.Extensions.NCSC

def quadratic (c : ℝ) : NCCInstance 1 1 where
  X := Set.univ
  Y := Set.univ
  f := fun _ y => -(1 / 2 : ℝ) * (y 0 - c) ^ 2
  gradX := fun _ _ => 0
  gradY := fun _ y _ => c - y 0
  x0 := 0

theorem gradient_representation (c : ℝ) : Model.RepresentsJointGradientWithin (quadratic c) := by
  intro x _ y _
  have hc := (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 1) y).comp (x, y)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y)))
  have hf := ((hc.sub_const c).pow 2).const_mul (-(1 / 2 : ℝ))
  convert! hf.hasFDerivWithinAt using 1
  apply ContinuousLinearMap.ext
  rintro ⟨dx, dy⟩
  simp [quadratic, Model.jointGradientCLM, residualCLM_apply, eDot,
    ContinuousLinearMap.comp_apply]
  ring

theorem jointly_smooth (c : ℝ) : Model.JointlySmoothWithin 1 (quadratic c) := by
  intro x _ y _ u _ v _
  simp [quadratic, jointSq, vecSq, NCPLVerification.vecSq]
  nlinarith [sq_nonneg (x 0 - u 0)]

theorem dual_stronglyConcave (c : ℝ) (x : EVec 1) :
    ConcaveOn ℝ Set.univ (fun y => (quadratic c).f x y + quadraticCorrection 1 y) := by
  have he : (fun y => (quadratic c).f x y + quadraticCorrection 1 y) =
      (fun y : EVec 1 => c * y 0 - c ^ 2 / 2) := by
    funext y
    simp [quadratic, quadraticCorrection, vecSq, NCPLVerification.vecSq]
    ring
  rw [he]
  refine ⟨convex_univ, ?_⟩
  intro y _ v _ a b _ _ hab
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have ha : a = 1 - b := by linarith
  rw [ha]
  ring_nf
  exact le_rfl

theorem value_zero (c : ℝ) (x : EVec 1) : ValueOn (quadratic c).Y (quadratic c).f x = 0 := by
  have hm : IsMaximizerOn (quadratic c).Y (quadratic c).f x (fun _ => c) := by
    refine ⟨Set.mem_univ _, ?_⟩
    intro y _
    simp only [quadratic, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]
    nlinarith [sq_nonneg (y 0 - c)]
  rw [value_eq_of_isMaximizerOn hm]
  simp [quadratic]

theorem class_mem (c : ℝ) : NCSCClass 1 1 1 (quadratic c) where
  ell_pos := by norm_num
  mu_pos := by norm_num
  Delta_pos := by norm_num
  primal_origin := Set.mem_univ _
  dual_origin := Set.mem_univ _
  initialization := rfl
  X_closed := isClosed_univ
  X_convex := convex_univ
  Y_closed := isClosed_univ
  Y_convex := convex_univ
  gradient_representation := gradient_representation c
  jointly_smooth := jointly_smooth c
  dual_stronglyConcave := fun x _ => dual_stronglyConcave c x
  initial_gap_pointwise := by intro x _; rw [value_zero, value_zero]; norm_num

theorem observed_budget (c : ℝ) : NCSCTheorem.observedBudget (class_mem c) = 3 * c ^ 2 := by
  simp [NCSCTheorem.observedBudget, NCSCInitialBudget.budget, NCSCInitialBudget.gapBudget,
    quadratic, internalSmoothness, vecSq, NCPLVerification.vecSq]
  ring

theorem observed_budget_unbounded (B : ℝ) :
    ∃ c : ℝ, B ≤ NCSCTheorem.observedBudget (class_mem c) := by
  refine ⟨|B| + 1, ?_⟩
  rw [observed_budget]
  nlinarith [abs_nonneg B, le_abs_self B, sq_nonneg (|B| + 1)]

end
end NCC.Extensions.NCSCQuadraticClass
