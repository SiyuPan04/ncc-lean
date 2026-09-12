import NCC.Construction.Composite
import NCCLowerBound.Simplified.CompositeSmoothnessAssembly

/-!
# Uniform regularity of the literal current composite objective

The current state/entrance/exit order is definitionally the legacy flat
`(s_i,a_i,b_i)` order. The current phase potential is not the old one:
`objective_eq_old_add_correction` proves the exact separable correction.
Only after that identity do we reuse the old sparse smoothness estimate.
-/

namespace NCC.Construction.Regularity

noncomputable section

open scoped BigOperators NNReal
open NCCLowerBoundVerification
open Composite

namespace Old
export NCCLowerBound.Simplified.RestrictedBall (flatHardObjective flatState flatEntrance flatExit)
export NCCLowerBound.Simplified.CompositeSmoothness
  (flatJointObjective flatPrimalGradient flatDualGradient flatJointObjective_contDiff
    flatGradient_represents_fderiv phasePotential_actual_second_deriv_bounded)
export NCCLowerBound.Simplified.CompositeSmoothnessAssembly
  (compositeEll0 compositeEll0_pos flatActualGradients_jointlySmooth)
end Old

def phaseCorrection (t : ℝ) : ℝ :=
  R Outer.c_R t - NCCLowerBound.Simplified.phasePotential Outer.c_R t

def correction {m : ℕ} (x : Primal m) : ℝ := ∑ i : Fin m, phaseCorrection (state x i)

theorem objective_eq_old_add_correction {m n : ℕ} (hn : 0 < n)
    (x : Primal m) (y : Dual m n) :
    objective hn x y = Old.flatHardObjective hn Outer.c_R x y + correction x := by
  unfold objective Old.flatHardObjective NCCLowerBound.Simplified.Composite.hardObjective
    NCCLowerBound.Simplified.Composite.outerComponent
    NCCLowerBound.Simplified.Composite.phaseComponent
    NCCLowerBound.Simplified.Composite.orderingComponent
    NCCLowerBound.Simplified.Composite.entranceComponent
    NCCLowerBound.Simplified.Composite.exitComponent
    NCCLowerBound.Simplified.InnerRelay.innerComponent correction phaseCorrection
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Inner.H_eq_old, Outer.C_en_eq_old, Outer.C_ex_eq_old, Outer.C_st_eq_old]
  rw [show Old.flatState x = state x from rfl,
    show Old.flatEntrance x = entrance x from rfl,
    show Old.flatExit x = exit x from rfl]
  change _ = NCCLowerBound.Simplified.phasePotential Outer.c_R (state x i) +
    NCCLowerBound.Simplified.Composite.orderingSummand (state x) i +
    NCCLowerBound.Simplified.Composite.entranceSummand (state x) (entrance x) i +
    NCCLowerBound.Simplified.Composite.exitSummand (state x) (exit x) i +
    NCCLowerBound.Simplified.InnerRelay.correctedH hn (entrance x i) (exit x i)
      (fun j => y (finProdFinEquiv (i, j))) +
    (R Outer.c_R (state x i) - NCCLowerBound.Simplified.phasePotential Outer.c_R (state x i))
  ring

theorem phaseCorrection_contDiff : ContDiff ℝ (⊤ : ℕ∞) phaseCorrection :=
  (R_contDiff Outer.c_R).sub (NCCLowerBound.Simplified.phasePotential_contDiff Outer.c_R)

theorem correction_contDiff {m : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (correction : Primal m → ℝ) := by
  apply ContDiff.sum
  intro i _
  exact phaseCorrection_contDiff.comp (by unfold state; fun_prop)

theorem objective_contDiff {m n : ℕ} (hn : 0 < n) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (objective (m := m) hn)) := by
  have heq : Function.uncurry (objective (m := m) hn) =
      fun z => Old.flatJointObjective hn Outer.c_R z + correction z.1 := by
    funext z
    exact objective_eq_old_add_correction hn z.1 z.2
  rw [heq]
  exact (Old.flatJointObjective_contDiff hn Outer.c_R).add
    (correction_contDiff.comp contDiff_fst)

theorem phaseCorrection_second_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv (deriv phaseCorrection) t| ≤ C := by
  obtain ⟨A, hA0, hA⟩ := R_second_derivative_bounded Outer.c_R
  obtain ⟨B, hB0, hB⟩ := Old.phasePotential_actual_second_deriv_bounded Outer.c_R
  refine ⟨A + B, add_nonneg hA0 hB0, ?_⟩
  intro t
  have hR := R_contDiff Outer.c_R
  have hP := NCCLowerBound.Simplified.phasePotential_contDiff Outer.c_R
  have heq : deriv phaseCorrection = fun u =>
      deriv (R Outer.c_R) u - deriv (NCCLowerBound.Simplified.phasePotential Outer.c_R) u := by
    funext u
    exact deriv_sub (hR.differentiable (by simp) u) (hP.differentiable (by simp) u)
  rw [heq]
  change |deriv (deriv (R Outer.c_R) -
    deriv (NCCLowerBound.Simplified.phasePotential Outer.c_R)) t| ≤ A + B
  rw [deriv_sub
    ((contDiff_infty_iff_deriv.mp hR).2.differentiable (by simp) t)
    ((contDiff_infty_iff_deriv.mp hP).2.differentiable (by simp) t)]
  exact (abs_sub _ _).trans (add_le_add (hA t) (hB t))

def correctionBound : ℝ := Classical.choose phaseCorrection_second_bounded

theorem correctionBound_nonneg : 0 ≤ correctionBound :=
  (Classical.choose_spec phaseCorrection_second_bounded).1

theorem correctionBound_spec (t : ℝ) : |deriv (deriv phaseCorrection) t| ≤ correctionBound :=
  (Classical.choose_spec phaseCorrection_second_bounded).2 t

theorem phaseCorrection_deriv_lipschitz :
    LipschitzWith ⟨correctionBound, correctionBound_nonneg⟩ (deriv phaseCorrection) := by
  apply lipschitzWith_of_nnnorm_deriv_le
  · exact (contDiff_infty_iff_deriv.mp phaseCorrection_contDiff).2.differentiable (by simp)
  · intro t
    exact_mod_cast correctionBound_spec t

def correctionGradient {m : ℕ} (x : Primal m) : Primal m :=
  primal (fun i => deriv phaseCorrection (state x i)) 0 0

theorem correctionGradient_dot {m : ℕ} (x d : Primal m) :
    (∑ j, correctionGradient x j * d j) =
      ∑ i : Fin m, deriv phaseCorrection (state x i) * state d i := by
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [correctionGradient, primal, state]

theorem correction_hasFDerivAt {m : ℕ} (x : Primal m) :
    HasFDerivAt correction (Upper.residualCLM (correctionGradient x)) x := by
  have hterm (i : Fin m) : HasFDerivAt (fun u : Primal m => phaseCorrection (state u i))
      (deriv phaseCorrection (state x i) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m * 3) => ℝ)
          (finProdFinEquiv (i, (0 : Fin 3)))) x := by
    have hd := (phaseCorrection_contDiff.differentiable (by simp) (state x i)).hasDerivAt
    convert! hd.comp_hasFDerivAt x
      (hasFDerivAt_apply (𝕜 := ℝ) (finProdFinEquiv (i, (0 : Fin 3))) x) using 1
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
  convert! hsum using 1
  ext d
  simp only [Upper.residualCLM_apply, Upper.eDot, correctionGradient_dot,
    sum_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply]
  rfl

theorem correctionGradient_sq_sub_le {m : ℕ} (x r : Primal m) :
    vecSq (correctionGradient x - correctionGradient r) ≤
      correctionBound ^ 2 * vecSq (x - r) := by
  have hscalar (i : Fin m) :
      (deriv phaseCorrection (state x i) - deriv phaseCorrection (state r i)) ^ 2 ≤
        correctionBound ^ 2 * (state x i - state r i) ^ 2 := by
    have hl := phaseCorrection_deriv_lipschitz.dist_le_mul (state x i) (state r i)
    simp only [Real.dist_eq] at hl
    have hs := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg correctionBound_nonneg (abs_nonneg _))).2 hl
    simpa only [mul_pow, sq_abs] using hs
  have hstate : (∑ i : Fin m, (state x i - state r i) ^ 2) ≤ vecSq (x - r) := by
    unfold vecSq NCPLVerification.vecSq
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro i _
    exact Finset.single_le_sum (fun j _ => sq_nonneg
      (x (finProdFinEquiv (i, j)) - r (finProdFinEquiv (i, j)))) (Finset.mem_univ (0 : Fin 3))
  calc
    vecSq (correctionGradient x - correctionGradient r) =
        ∑ i : Fin m, (deriv phaseCorrection (state x i) - deriv phaseCorrection (state r i)) ^ 2 := by
      unfold vecSq NCPLVerification.vecSq
      rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      simp [correctionGradient, primal, Fin.sum_univ_succ]
    _ ≤ ∑ i : Fin m, correctionBound ^ 2 * (state x i - state r i) ^ 2 :=
      Finset.sum_le_sum (fun i _ => hscalar i)
    _ = correctionBound ^ 2 * ∑ i : Fin m, (state x i - state r i) ^ 2 :=
      (Finset.mul_sum ..).symm
    _ ≤ correctionBound ^ 2 * vecSq (x - r) :=
      mul_le_mul_of_nonneg_left hstate (sq_nonneg _)

def gradientX {m n : ℕ} (hn : 0 < n) (x : Primal m) (y : Dual m n) : Primal m :=
  Old.flatPrimalGradient hn Outer.c_R x y + correctionGradient x

def gradientY {m n : ℕ} (hn : 0 < n) (x : Primal m) (y : Dual m n) : Dual m n :=
  Old.flatDualGradient hn Outer.c_R x y

/-- The corrected fields represent the full derivative in every joint direction. -/
theorem gradient_represents_fderiv {m n : ℕ} (hn : 0 < n) :
    NCPLVerification.RepresentsJointGradient (objective (m := m) hn)
      (gradientX hn) (gradientY hn) := by
  refine ⟨(objective_contDiff hn).differentiable (by simp), ?_⟩
  intro x y dx dy
  have hold := Old.flatGradient_represents_fderiv (M := m) hn Outer.c_R
  have hc := (correction_hasFDerivAt x).comp (x, y)
    (ContinuousLinearMap.fst ℝ (Primal m) (Dual m n)).hasFDerivAt
  have hs := (hold.1 (x, y)).hasFDerivAt.add hc
  have heq : Function.uncurry (objective (m := m) hn) =
      fun z => Function.uncurry (Old.flatHardObjective hn Outer.c_R) z + correction z.1 := by
    funext z
    exact objective_eq_old_add_correction hn z.1 z.2
  rw [heq]
  change (fderiv ℝ (Function.uncurry (Old.flatHardObjective hn Outer.c_R) +
    correction ∘ (ContinuousLinearMap.fst ℝ (Primal m) (Dual m n))) (x, y)) (dx, dy) = _
  rw [hs.fderiv]
  change fderiv ℝ (Function.uncurry (Old.flatHardObjective hn Outer.c_R)) (x, y) (dx, dy) +
    (∑ j, correctionGradient x j * dx j) = _
  rw [hold.2 x y dx dy]
  simp only [gradientX, gradientY, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  ring

theorem gradientX_eq_actual {m n : ℕ} (hn : 0 < n) (x : Primal m) (y : Dual m n) :
    gradientX hn x y = ambientGradX (Function.uncurry (objective hn)) x y := by
  funext i
  have h := (gradient_represents_fderiv (m := m) hn).2 x y
    (NCPLVerification.evecBasis i) 0
  simpa [ambientGradX, NCPLVerification.evecBasis] using h.symm

theorem gradientY_eq_actual {m n : ℕ} (hn : 0 < n) (x : Primal m) (y : Dual m n) :
    gradientY hn x y = ambientGradY (Function.uncurry (objective hn)) x y := by
  funext i
  have h := (gradient_represents_fderiv (m := m) hn).2 x y
    0 (NCPLVerification.evecBasis i)
  simpa [ambientGradY, NCPLVerification.evecBasis] using h.symm

private theorem c_R_pos : 0 < Outer.c_R := by linarith [Outer.c_R_ge_twenty_five]

/-- One fixed constant, with no dependence on either chain dimension. -/
def ell₀ : ℝ := 2 * (Old.compositeEll0 Outer.c_R c_R_pos + correctionBound + 1)

theorem ell₀_pos : 0 < ell₀ := by
  unfold ell₀
  linarith [Old.compositeEll0_pos Outer.c_R c_R_pos, correctionBound_nonneg]

theorem gradients_jointlySmooth {m n : ℕ} (hn : 10 ≤ n) :
    NCPLVerification.IsJointlySmooth ell₀
      (gradientX (m := m) (by omega : 0 < n)) (gradientY (by omega : 0 < n)) := by
  intro x y r v
  let L := Old.compositeEll0 Outer.c_R c_R_pos
  let O := Old.flatPrimalGradient (by omega : 0 < n) Outer.c_R x y -
    Old.flatPrimalGradient (by omega : 0 < n) Outer.c_R r v
  let Z := Old.flatDualGradient (by omega : 0 < n) Outer.c_R x y -
    Old.flatDualGradient (by omega : 0 < n) Outer.c_R r v
  let C := correctionGradient x - correctionGradient r
  have ho := Old.flatActualGradients_jointlySmooth (M := m) hn Outer.c_R c_R_pos x y r v
  change vecSq O + vecSq Z ≤ L ^ 2 * (vecSq (x - r) + vecSq (y - v)) at ho
  have hc := correctionGradient_sq_sub_le x r
  change vecSq C ≤ correctionBound ^ 2 * vecSq (x - r) at hc
  have ha := NCPLVerification.vecSq_add_le_two O C
  change vecSq (O + C) ≤ 2 * vecSq O + 2 * vecSq C at ha
  have hZ0 := vecSq_nonneg Z
  have hx0 := vecSq_nonneg (x - r)
  have hy0 := vecSq_nonneg (y - v)
  have hL0 : 0 < L := Old.compositeEll0_pos Outer.c_R c_R_pos
  have hconst : 2 * L ^ 2 + 2 * correctionBound ^ 2 ≤ ell₀ ^ 2 := by
    unfold ell₀
    change 2 * L ^ 2 + 2 * correctionBound ^ 2 ≤ (2 * (L + correctionBound + 1)) ^ 2
    nlinarith [correctionBound_nonneg]
  have hmul := mul_le_mul_of_nonneg_right hconst (add_nonneg hx0 hy0)
  have hcy : 0 ≤ correctionBound ^ 2 * vecSq (y - v) := mul_nonneg (sq_nonneg _) hy0
  have heq : gradientX (by omega : 0 < n) x y - gradientX (by omega : 0 < n) r v = O + C := by
    ext j
    simp [gradientX, O, C]
    ring
  rw [heq]
  change vecSq (O + C) + vecSq Z ≤ ell₀ ^ 2 * (vecSq (x - r) + vecSq (y - v))
  nlinarith

theorem exists_uniform_actual_joint_smoothness :
    ∃ L : ℝ, 0 < L ∧ ∀ (m n : ℕ) (hn : 10 ≤ n),
      NCPLVerification.IsJointlySmooth L
        (gradientX (m := m) (by omega : 0 < n)) (gradientY (by omega : 0 < n)) :=
  ⟨ell₀, ell₀_pos, fun _ _ hn => gradients_jointlySmooth hn⟩

/-- The current objective is strongly concave in the actual flattened dual
coordinates, with exactly the inner relay's `1/n²` modulus. -/
theorem objective_dual_strongly_concave {m n : ℕ} (hn : 0 < n)
    (x : Primal m) (u v : Dual m n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * objective hn x u + (1 - t) * objective hn x v +
      ((1 / (n : ℝ) ^ 2) / 2) * t * (1 - t) * vecSq (u - v) ≤
      objective hn x (t • u + (1 - t) • v) := by
  have hvec : (∑ i : Fin m, vecSq ((fun j : Fin n => u (finProdFinEquiv (i, j))) -
      (fun j : Fin n => v (finProdFinEquiv (i, j))))) = vecSq (u - v) := by
    unfold vecSq NCPLVerification.vecSq
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    rfl
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m))) (fun i _ =>
    Inner.H_strongly_concave hn (entrance x i) (exit x i)
      (fun j => u (finProdFinEquiv (i, j)))
      (fun j => v (finProdFinEquiv (i, j))) ht0 ht1)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hi :
      t * Inner.objective hn (pulse x) u + (1 - t) * Inner.objective hn (pulse x) v +
        ((1 / (n : ℝ) ^ 2) / 2) * t * (1 - t) * vecSq (u - v) ≤
        Inner.objective hn (pulse x) (t • u + (1 - t) • v) := by
    simp only [hvec] at hs
    simp only [Inner.objective, pulse, pulsePair_a, pulsePair_b]
    convert! hs using 1
  rw [objective_split, objective_split, objective_split]
  nlinarith

theorem objective_dual_concave {m n : ℕ} (hn : 0 < n) (x : Primal m) :
    ConcaveOn ℝ Set.univ (objective hn x) := by
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  have ha1 : a ≤ 1 := by linarith
  have h := objective_dual_strongly_concave hn x u v ha ha1
  have hb_eq : b = 1 - a := by linarith
  rw [hb_eq]
  change a * objective hn x u + (1 - a) * objective hn x v ≤
    objective hn x (a • u + (1 - a) • v)
  have hterm : 0 ≤ ((1 / (n : ℝ) ^ 2) / 2) * a * (1 - a) * vecSq (u - v) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (div_nonneg (div_nonneg zero_le_one (sq_nonneg _)) (by norm_num)) ha)
      (sub_nonneg.mpr ha1)) (vecSq_nonneg _)
  linarith

end

end NCC.Construction.Regularity
