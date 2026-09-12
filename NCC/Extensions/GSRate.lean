import NCC.Extensions.GSTheorem
import NCC.Extensions.GSCost

/-!
# Numerical GS regularization and horizon bounds

These bounds apply to the actual counted client and its queried-output
wrapper. Constants depend on the fixed class parameters, not on tolerance,
dimension, objective, or replies.
-/
namespace NCC.Extensions.GSRate
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open NCC.Upper RelativeFOAM RelativeFOAMContraction
set_option maxHeartbeats 3000000
variable {ell D Delta eps : ℝ}

def curvatureFloor (ell D : ℝ) : ℝ := min (ell / 32) (1 / (256 * D))

theorem curvatureFloor_pos (hell : 0 < ell) (hD : 0 < D) :
    0 < curvatureFloor ell D :=
  lt_min (div_pos hell (by norm_num)) (div_pos (by norm_num) (mul_pos (by norm_num) hD))

theorem finalCurvature_lower (hell : 0 < ell) (hD : 0 < D)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    curvatureFloor ell D * eps ≤ GSRun.finalCurvature hell hD heps := by
  let a := curvatureFloor ell D
  have ha : 0 < a := curvatureFloor_pos hell hD
  have hleft : a ≤ ell / 32 := min_le_left _ _
  have hright : a ≤ 1 / (256 * D) := min_le_right _ _
  have h1 : a * eps ≤ ell / 32 :=
    (mul_le_mul_of_nonneg_left heps1 ha.le).trans (by simpa using hleft)
  have h2 := mul_le_mul_of_nonneg_right hright heps.le
  have htarget : 4 * (a * eps) ≤ GSRun.target ell D eps := by
    apply le_min
    · linarith
    · have heq : 4 * ((1 / (256 * D)) * eps) = eps / (64 * D) := by ring
      rw [← heq]
      linarith
  have hr := (GSRun.finalCurvature_interval hell hD heps).1
  change a * eps ≤ _
  linarith

def horizonConstant (ell D Delta : ℝ) : ℝ :=
  4001 * (4 * ell * (Delta + (ell / 8) * D ^ 2) + 1)

theorem horizonConstant_pos (hell : 0 < ell) (hDelta : 0 < Delta) :
    0 < horizonConstant ell D Delta := by
  unfold horizonConstant
  positivity

theorem horizon_upper (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (GSRun.horizon ell D Delta (eps / 2) (GSRun.stage hell hD heps) : ℝ) ≤
      horizonConstant ell D Delta / eps ^ 2 := by
  let J := GSRun.stage hell hD heps
  let r := GSRun.finalCurvature hell hD heps
  let H := GSRun.mass ell D Delta J
  have hr : 0 < r := GSRun.finalCurvature_pos hell hD heps
  have hrle : r ≤ ell / 8 := (GSRun.finalCurvature_interval hell hD heps).2.trans (min_le_left _ _)
  have hH : 0 < H := add_pos_of_pos_of_nonneg hDelta (mul_nonneg hr.le (sq_nonneg D))
  have hT := CurrentCost.current_horizon_upper (eps := eps / 2) hell hH
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hcancel : 4001 * (ell * H / (eps / 2) ^ 2 + 1) * eps ^ 2 =
      4001 * (4 * ell * H + eps ^ 2) := by
    field_simp [ne_of_gt heps]
    ring
  apply (le_div_iff₀ heps2).2
  have ht := mul_le_mul_of_nonneg_right hT heps2.le
  rw [hcancel] at ht
  have hmass : H ≤ Delta + (ell / 8) * D ^ 2 :=
    add_le_add_right (mul_le_mul_of_nonneg_right hrle (sq_nonneg D)) Delta
  have hm := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 4 * ell by positivity)
  have he1 : eps ^ 2 ≤ 1 := by nlinarith
  unfold horizonConstant
  change (GSRun.horizon ell D Delta (eps / 2) J : ℝ) * eps ^ 2 ≤ _
  change (GSRun.horizon ell D Delta (eps / 2) J : ℝ) * eps ^ 2 ≤ _ at ht
  nlinarith

theorem blockConstant_le_reciprocal {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    UniformCost.blockConstant rho ≤
      (3 * (ProjectedMicro.feasibleMicroIterations + 1 : ℝ)) / rho := by
  have hlog := Real.log_le_sub_one_of_pos (one_div_pos.mpr hrho)
  have hN : 0 ≤ (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) := by positivity
  have hrec : 1 ≤ 1 / rho := (one_le_div hrho).2 hrho1.le
  have hfactor : 2 * Real.log (1 / rho) + 1 ≤ 3 / rho := by
    have heq : 3 / rho = 3 * (1 / rho) := by ring
    rw [heq]
    linarith
  have hm := mul_le_mul_of_nonneg_right hfactor hN
  calc
    _ ≤ (3 / rho) * (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) := hm
    _ = _ := by ring

def rateConstant (ell D Delta : ℝ) : ℝ :=
  GSCost.rateConstant ell (curvatureFloor ell D) (horizonConstant ell D Delta)
    (ProjectedMicro.feasibleMicroIterations + 4 : ℝ)
    (2 * UniformCost.blockConstant (1 / 8)) (UniformCost.blockConstant (1 / 400))
    (3 * (ProjectedMicro.feasibleMicroIterations + 1 : ℝ))

theorem rateConstant_pos (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) :
    0 < rateConstant ell D Delta := by
  have ha := curvatureFloor_pos hell hD
  have hb := horizonConstant_pos (D := D) hell hDelta
  have hw := UniformCost.blockConstant_pos
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1)
  have ho := UniformCost.blockConstant_pos
    (by norm_num : (0 : ℝ) < 1 / 400) (by norm_num : (1 / 400 : ℝ) < 1)
  unfold rateConstant GSCost.rateConstant
  positivity

/-- The actual complete queried-output budget obeys the eps^(-5/2)
leading bound for every positive tolerance at most one. -/
theorem queryBudget_leading_bound (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta)
    (heps : 0 < eps) (heps1 : eps ≤ 1) :
    (GSTheorem.queryBudget hell hD heps Delta : ℝ) ≤
      rateConstant ell D Delta / (eps ^ 2 * Real.sqrt eps) := by
  let J := GSRun.stage hell hD heps
  let r := GSRun.finalCurvature hell hD heps
  let T := GSRun.horizon ell D Delta (eps / 2) J
  let rho := GSRun.refinementFactor ell r
  have hr : 0 < r := GSRun.finalCurvature_pos hell hD heps
  have hrle : r ≤ ell / 8 := (GSRun.finalCurvature_interval hell hD heps).2.trans (min_le_left _ _)
  have hrho : 0 < rho := GSRun.refinementFactor_pos hell hr
  have hrho1 : rho < 1 := GSRun.refinementFactor_lt_one hell hrle
  have hc := GSProgram.numericalCount_le hell J T hrho hrho1
  have hlog := blockConstant_le_reciprocal hrho hrho1
  have hlog' := mul_le_mul_of_nonneg_right hlog (Real.sqrt_nonneg (ell / r))
  have hraw : (GSTheorem.queryBudget hell hD heps Delta : ℝ) ≤
      (ProjectedMicro.feasibleMicroIterations + 4 : ℝ) +
      (2 * UniformCost.blockConstant (1 / 8) + (T : ℝ) * UniformCost.blockConstant (1 / 400) +
        (3 * (ProjectedMicro.feasibleMicroIterations + 1 : ℝ)) / rho) * Real.sqrt (ell / r) := by
    change ((GSProgram.numericalCount ell J T rho + 1 + 2 : Nat) : ℝ) ≤ _
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    change (GSProgram.numericalCount ell J T rho : ℝ) ≤
      (ProjectedMicro.feasibleMicroIterations + 1 : ℝ) +
      (2 * UniformCost.blockConstant (1 / 8) + (T : ℝ) * UniformCost.blockConstant (1 / 400) +
        UniformCost.blockConstant rho) * Real.sqrt (ell / r) at hc
    nlinarith
  have hw := UniformCost.blockConstant_pos
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1)
  have ho := UniformCost.blockConstant_pos
    (by norm_num : (0 : ℝ) < 1 / 400) (by norm_num : (1 / 400 : ℝ) < 1)
  exact GSCost.count_le hell (curvatureFloor_pos hell hD)
    (horizonConstant_pos (D := D) hell hDelta).le (by positivity)
    (mul_nonneg (by norm_num) hw.le) ho.le (by positivity) heps heps1
    (finalCurvature_lower hell hD heps heps1) rfl
    (horizon_upper hell hD hDelta heps heps1) hraw

/-- For each requested accuracy there is a single domain-wise algorithm
whose genuine queried GS pair is reached within the eps^(-5/2) count.
The positive constant is independent of accuracy, objective and dimension. -/
theorem exists_algorithm_leading_rate (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∃ A : Oracle.DomainWiseDeterministicAlgorithm,
        ∀ (Q : Oracle.AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
          P.X = Q.X → P.Y = Q.Y → NCC.Model.WithinClass ell D Delta P →
            ∃ t : Nat, ((t + 1 : Nat) : ℝ) ≤ C / (eps ^ 2 * Real.sqrt eps) ∧
              HasGSWitness P eps ((A.component Q).queriedAt P t).1 ((A.component Q).queriedAt P t).2 := by
  refine ⟨rateConstant ell D Delta, rateConstant_pos hell hD hDelta, ?_⟩
  intro eps heps heps1
  obtain ⟨A, hA⟩ := GSTheorem.exists_domain_algorithm_uniform hell hD hDelta heps
  refine ⟨A, ?_⟩
  intro Q P hPX hPY hP
  obtain ⟨t, ht, hgs⟩ := hA Q P hPX hPY hP
  refine ⟨t, ?_, hgs⟩
  have hc : ((t + 1 : Nat) : ℝ) ≤ (GSTheorem.queryBudget hell hD heps Delta : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt ht
  exact hc.trans (queryBudget_leading_bound hell hD hDelta heps heps1)

/-- The NC-C GS extension in the cited distance-to-normal-cone convention.
The counted iterate is queried and uses only feasible local first-order
replies. The epsilon exponent is exactly 5/2, without a multiplying log. -/
theorem nc_c_gs_complexity (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) :
    ∃ C : ℝ, 0 < C ∧ ∀ eps : ℝ, 0 < eps → eps ≤ 1 →
      ∃ A : Oracle.DomainWiseDeterministicAlgorithm,
        ∀ (Q : Oracle.AdmissibleDomainPair) (P : NCCInstance Q.m Q.n),
          P.X = Q.X → P.Y = Q.Y → NCC.Model.WithinClass ell D Delta P →
            ∃ t : Nat, ((t + 1 : Nat) : ℝ) ≤ C / (eps ^ 2 * Real.sqrt eps) ∧
              IsGS P eps ((A.component Q).queriedAt P t).1 ((A.component Q).queriedAt P t).2 := by
  obtain ⟨C, hC, hA⟩ := exists_algorithm_leading_rate hell hD hDelta
  refine ⟨C, hC, ?_⟩
  intro eps heps heps1
  obtain ⟨A, hA⟩ := hA eps heps heps1
  refine ⟨A, ?_⟩
  intro Q P hPX hPY hP
  obtain ⟨t, ht, hgs⟩ := hA Q P hPX hPY hP
  exact ⟨t, ht, hgs.isGS⟩

end
end NCC.Extensions.GSRate
