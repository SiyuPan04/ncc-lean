import NCCLowerBoundVerification.Lower.RadialBudget
import NCPLVerification.InnerDifferentiability

/-!
# From a terminal value-gradient obstruction to OS failure

This module formalizes `lem:terminal-os`.  The key point is proved rather
than postulated: differentiability and unconstrained proximal minimality imply
the exact first-order equation
`grad phi u + 2 * ell * (u - x) = 0`.
-/

namespace NCCLowerBoundVerification

noncomputable section

def affineLine {d : Nat} (u h : EVec d) (t : ℝ) : EVec d :=
  t • h + u

theorem affineLine_zero {d : Nat} (u h : EVec d) :
    affineLine u h 0 = u := by
  simp [affineLine]

theorem hasDerivAt_along_affineLine {d : Nat}
    {phi : EVec d → ℝ} {g u : EVec d}
    (hphi : NCPLVerification.HasEVecFDerivAt phi
      (NCPLVerification.evecDot g) u) (h : EVec d) :
    HasDerivAt (fun t : ℝ ↦ phi (affineLine u h t))
      (radialDot g h) 0 := by
  letI : AddCommGroup (EVec d) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec d) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec d) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let L : ℝ →L[ℝ] EVec d := (1 : ℝ →L[ℝ] ℝ).smulRight h
  have hline : HasFDerivAt (affineLine u h) L 0 := by
    simpa [affineLine, L, ContinuousLinearMap.smulRight_apply,
      add_comm] using L.hasFDerivAt.add_const u
  have houter : HasFDerivAt phi (NCPLVerification.evecDot g) u := by
    simpa only [NCPLVerification.HasEVecFDerivAt] using hphi
  have houterAt : HasFDerivAt phi (NCPLVerification.evecDot g)
      (affineLine u h 0) := by
    simpa [affineLine] using houter
  have hcomp := houterAt.comp 0 hline
  have hderiv := hcomp.hasDerivAt
  apply hderiv.congr_deriv
  rw [ContinuousLinearMap.comp_apply]
  simp [L, ContinuousLinearMap.smulRight_apply,
    NCPLVerification.evecDot_apply, radialDot]

theorem hasDerivAt_vecSq_affineLine_sub {d : Nat}
    (u x h : EVec d) :
    HasDerivAt (fun t : ℝ ↦ vecSq (affineLine u h t - x))
      (2 * radialDot (u - x) h) 0 := by
  unfold vecSq NCPLVerification.vecSq
  have hsum : HasDerivAt
      (fun t : ℝ ↦ ∑ i : Fin d, (affineLine u h t i - x i) ^ 2)
      (∑ i : Fin d, 2 * (u i - x i) * h i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have hlin : HasDerivAt
        (fun t : ℝ ↦ affineLine u h t i - x i) (h i) 0 := by
      convert (((hasDerivAt_id (𝕜 := ℝ) 0).mul_const (h i)).add_const
        (u i - x i)) using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      · funext t
        simp [affineLine]
        ring
      · simp
    have hmul := hlin.mul hlin
    have hfun :
        (fun t : ℝ ↦ (affineLine u h t i - x i) ^ 2) =ᶠ[nhds 0]
          ((fun t : ℝ ↦ affineLine u h t i - x i) *
            fun t : ℝ ↦ affineLine u h t i - x i) := by
      apply Filter.Eventually.of_forall
      intro t
      simp [pow_two]
    apply (hmul.congr_of_eventuallyEq hfun).congr_deriv
    simp [affineLine]
    ring
  apply hsum.congr_deriv
  unfold radialDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

/-- Exact unconstrained proximal first-order condition. -/
theorem proxPoint_gradient_equation {d : Nat}
    {phi : EVec d → ℝ} {ell : ℝ} {x u g : EVec d}
    (hu : IsProxPoint Set.univ phi ell x u)
    (hphi : NCPLVerification.HasEVecFDerivAt phi
      (NCPLVerification.evecDot g) u) :
    g + (2 * ell) • (u - x) = 0 := by
  have hdirection : ∀ h : EVec d,
      radialDot g h + 2 * ell * radialDot (u - x) h = 0 := by
    intro h
    let objective : ℝ → ℝ := fun t ↦
      phi (affineLine u h t) +
        ell * vecSq (affineLine u h t - x)
    have hmin : IsLocalMin objective 0 := by
      apply Filter.Eventually.of_forall
      intro t
      have h := hu.2 (affineLine u h t) (Set.mem_univ _)
      simpa [objective, affineLine_zero] using h
    have hdphi := hasDerivAt_along_affineLine hphi h
    have hdsq := (hasDerivAt_vecSq_affineLine_sub u x h).const_mul ell
    have hd : HasDerivAt objective
        (radialDot g h + 2 * ell * radialDot (u - x) h) 0 := by
      change HasDerivAt
        (fun t ↦ phi (affineLine u h t) +
          ell * vecSq (affineLine u h t - x))
        (radialDot g h + 2 * ell * radialDot (u - x) h) 0
      have hadd := hdphi.add hdsq
      have hfun :
          (fun t ↦ phi (affineLine u h t) +
            ell * vecSq (affineLine u h t - x)) =ᶠ[nhds 0]
            ((fun t ↦ phi (affineLine u h t)) +
              fun t ↦ ell * vecSq (affineLine u h t - x)) := by
        apply Filter.Eventually.of_forall
        intro t
        rfl
      apply (hadd.congr_of_eventuallyEq hfun).congr_deriv
      ring
    exact hmin.hasDerivAt_eq_zero hd
  funext i
  have hi := hdirection (NCPLVerification.evecBasis i)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
  unfold radialDot at hi
  simp [NCPLVerification.evecBasis] at hi
  simpa only [Pi.sub_apply] using hi

theorem coordinate_sq_le_vecSq {d : Nat} (z : EVec d) (i : Fin d) :
    z i ^ 2 ≤ vecSq z := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (z j)) (Finset.mem_univ i)

theorem vecSq_smul' {d : Nat} (c : ℝ) (z : EVec d) :
    vecSq (c • z) = c ^ 2 * vecSq z := by
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/--
Abstract but exact form of `lem:terminal-os`.  `hterminalGradient` is the
separately proved terminal value-gradient certificate; every remaining step,
including proximal optimality and all constants, is discharged here.
-/
theorem not_optimizationStationary_of_terminal_gradient {d : Nat}
    {phi : EVec d → ℝ} {grad : EVec d → EVec d}
    {ell eps lambda : ℝ} (hell : 0 < ell) (heps : 0 < eps)
    (hlambda : 0 < lambda) (hmove : eps / (2 * ell) ≤ lambda)
    (hdiff : ∀ u, NCPLVerification.HasEVecFDerivAt phi
      (NCPLVerification.evecDot (grad u)) u)
    (terminal : Fin d) {x : EVec d} (hxterminal : x terminal = 0)
    (hterminalGradient : ∀ u, u terminal / lambda ≤ 1 →
      16 * eps ^ 2 ≤ vecSq (grad u)) :
    ¬ IsOptimizationStationary Set.univ phi ell eps x := by
  rintro ⟨u, hu, hres⟩
  have hcoord := coordinate_sq_le_vecSq (u - x) terminal
  have hcoordBound : (u terminal - x terminal) ^ 2 ≤
      (eps / (2 * ell)) ^ 2 := hcoord.trans hres
  rw [hxterminal, sub_zero] at hcoordBound
  have hmove0 : 0 ≤ eps / (2 * ell) := by positivity
  have hlambdaSq : (eps / (2 * ell)) ^ 2 ≤ lambda ^ 2 := by
    nlinarith
  have huterminal : u terminal ≤ lambda := by
    nlinarith [hcoordBound.trans hlambdaSq]
  have hscaledTerminal : u terminal / lambda ≤ 1 := by
    exact (div_le_iff₀ hlambda).2 (by simpa using huterminal)
  have hlower := hterminalGradient u hscaledTerminal
  have heq := proxPoint_gradient_equation hu (hdiff u)
  have hgrad : grad u = (-2 * ell) • (u - x) := by
    have := congrArg (fun z : EVec d ↦ z - (2 * ell) • (u - x)) heq
    simpa using this
  have hupper : vecSq (grad u) ≤ eps ^ 2 := by
    rw [hgrad, vecSq_smul']
    have hscale := mul_le_mul_of_nonneg_left hres (sq_nonneg (-2 * ell))
    calc
      (-2 * ell) ^ 2 * vecSq (u - x) ≤
          (-2 * ell) ^ 2 * (eps / (2 * ell)) ^ 2 := hscale
      _ = eps ^ 2 := by field_simp [ne_of_gt hell]
  nlinarith [sq_pos_of_pos heps]

end

end NCCLowerBoundVerification
