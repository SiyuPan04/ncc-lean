import NCPLVerification.PerspectiveDifferentiability
import NCPLVerification.InnerValue

/-!
# Primal-parameter differentiability of a perspective block

This module treats the scale and activation as differentiable functions of a
finite-dimensional primal variable.  The positive-scale result is ordinary
calculus; the flat zero-scale boundary is handled separately below.
-/

namespace NCPLVerification

noncomputable section

theorem differentiable_innerGamma {N : Nat} :
    Differentiable ℝ (innerGamma : EVec N → ℝ) := by
  intro z
  exact (hasEVecFDerivAt_innerGamma z).differentiableAt

theorem differentiable_innerH (N : Nat) (lambdaWall : ℝ) :
    Differentiable ℝ (innerH N lambdaWall) := by
  intro z
  exact (hasEVecFDerivAt_innerH N lambdaWall z).differentiableAt

theorem differentiable_innerWallEnergy (N : Nat) :
    Differentiable ℝ (innerWallEnergy N) := by
  intro z
  exact (hasEVecFDerivAt_innerWallEnergy N z).differentiableAt

/-- On the open set where the scale is positive, a perspective block is
genuinely differentiable in every primal parameter on which `rho` and `A`
depend. -/
theorem differentiableAt_perspectiveDelay_comp_pos {T N : Nat}
    (lambdaWall eta : ℝ) (u : EVec N)
    (rho A : EVec T → ℝ) (x : EVec T)
    (hrho : DifferentiableAt ℝ rho x) (hA : DifferentiableAt ℝ A x)
    (hpos : 0 < rho x) :
    DifferentiableAt ℝ
      (fun w ↦ perspectiveDelay N lambdaWall eta (rho w) (A w) u) x := by
  have hz : DifferentiableAt ℝ (fun w : EVec T ↦ rescaleEVec (rho w) u) x := by
    apply differentiableAt_pi.2
    intro j
    have hc : DifferentiableAt ℝ (fun _ : EVec T ↦ u j) x :=
      differentiableAt_const (𝕜 := ℝ) (c := u j)
    convert hc.mul (hrho.inv hpos.ne') using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { funext w; rfl }
  have hgamma : DifferentiableAt ℝ
      (fun w : EVec T ↦ innerGamma (rescaleEVec (rho w) u)) x :=
    (differentiable_innerGamma (N := N) _).comp x hz
  have hH : DifferentiableAt ℝ
      (fun w : EVec T ↦
        innerH N lambdaWall (rescaleEVec (rho w) u)) x :=
    (differentiable_innerH N lambdaWall _).comp x hz
  have hformula : DifferentiableAt ℝ
      (fun w : EVec T ↦
        A w * innerGamma (rescaleEVec (rho w) u) -
          eta * rho w ^ 2 * innerH N lambdaWall (rescaleEVec (rho w) u)) x := by
    exact (hA.mul hgamma).sub
      (((differentiableAt_const (c := eta)).mul (hrho.pow 2)).mul hH)
  have hopen : ∀ᶠ w in nhds x, 0 < rho w :=
    hrho.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hopen] with w hw
  simp [perspectiveDelay, hw]

/-- Positive-scale calculus when the dual argument also varies. -/
theorem differentiableAt_perspectiveDelay_comp_pos_variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : Nat}
    (lambdaWall eta : ℝ) (rho A : E → ℝ) (u : E → EVec N) (x : E)
    (hrho : DifferentiableAt ℝ rho x) (hA : DifferentiableAt ℝ A x)
    (hu : DifferentiableAt ℝ u x) (hpos : 0 < rho x) :
    DifferentiableAt ℝ
      (fun w ↦ perspectiveDelay N lambdaWall eta (rho w) (A w) (u w)) x := by
  have hz : DifferentiableAt ℝ
      (fun w : E ↦ rescaleEVec (rho w) (u w)) x := by
    apply differentiableAt_pi.2
    intro j
    have hcoord : DifferentiableAt ℝ (fun w : E ↦ u w j) x := by
      exact (differentiableAt_apply j (u x)).comp x hu
    convert hcoord.mul (hrho.inv hpos.ne') using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { funext w; rfl }
  have hgamma : DifferentiableAt ℝ
      (fun w : E ↦ innerGamma (rescaleEVec (rho w) (u w))) x :=
    (differentiable_innerGamma (N := N) _).comp x hz
  have hH : DifferentiableAt ℝ
      (fun w : E ↦ innerH N lambdaWall (rescaleEVec (rho w) (u w))) x :=
    (differentiable_innerH N lambdaWall _).comp x hz
  have hformula : DifferentiableAt ℝ
      (fun w : E ↦
        A w * innerGamma (rescaleEVec (rho w) (u w)) -
          eta * rho w ^ 2 *
            innerH N lambdaWall (rescaleEVec (rho w) (u w))) x := by
    exact (hA.mul hgamma).sub
      (((differentiableAt_const (c := eta)).mul (hrho.pow 2)).mul hH)
  have hopen : ∀ᶠ w in nhds x, 0 < rho w :=
    hrho.continuousAt.eventually (isOpen_Ioi.mem_nhds hpos)
  apply hformula.congr_of_eventuallyEq
  filter_upwards [hopen] with w hw
  simp [perspectiveDelay, hw]

theorem negPart_div_pos (u rho : ℝ) (hrho : 0 < rho) :
    negPart (u / rho) = negPart u / rho := by
  by_cases hu : 0 ≤ u
  · have hudiv : 0 ≤ u / rho := div_nonneg hu hrho.le
    simp [negPart_eq_zero hu, negPart_eq_zero hudiv]
  · have hu' : u < 0 := lt_of_not_ge hu
    have hudiv : u / rho < 0 := div_neg_of_neg_of_pos hu' hrho
    unfold negPart
    rw [max_eq_left (neg_pos.mpr hudiv).le, max_eq_left (neg_pos.mpr hu').le]
    ring

theorem innerWallEnergy_rescale {N : Nat} (u : EVec N) (rho : ℝ)
    (hrho : 0 < rho) :
    rho ^ 2 * innerWallEnergy N (rescaleEVec rho u) =
      innerWallEnergy N u := by
  unfold innerWallEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [rescaleEVec, negPart_div_pos _ _ hrho]
  field_simp [hrho.ne']

theorem perspectiveDelay_pos_decompose {N : Nat} (lambdaWall eta A : ℝ)
    (u : EVec N) {rho : ℝ} (hrho : 0 < rho) :
    perspectiveDelay N lambdaWall eta rho A u =
      A * innerGamma (rescaleEVec rho u) -
        eta * rho ^ 2 * innerResidualEnergy N (rescaleEVec rho u) -
        eta * lambdaWall * innerWallEnergy N u := by
  rw [perspectiveDelay, if_pos hrho]
  change A * innerGamma (rescaleEVec rho u) -
      eta * rho ^ 2 *
        (innerResidualEnergy N (rescaleEVec rho u) +
          lambdaWall * innerWallEnergy N (rescaleEVec rho u)) = _
  calc
    _ = A * innerGamma (rescaleEVec rho u) -
        eta * rho ^ 2 * innerResidualEnergy N (rescaleEVec rho u) -
        eta * lambdaWall *
          (rho ^ 2 * innerWallEnergy N (rescaleEVec rho u)) := by ring
    _ = _ := by rw [innerWallEnergy_rescale u rho hrho]

theorem innerResidualEnergy_nonneg {N : Nat} (hN : 0 < N)
    (z : EVec N) : 0 ≤ innerResidualEnergy N z := by
  unfold innerResidualEnergy
  exact Finset.sum_nonneg fun i _ ↦
    mul_nonneg (innerAlpha_pos hN i).le (sq_nonneg _)

/-- Uniform value estimate for the non-wall part of the perspective.  It is
the quantitative fact that makes the zero-scale extension differentiable. -/
theorem abs_perspectiveDelay_add_wall_le {N : Nat} (hN : 0 < N)
    (lambdaWall eta rho A Amax : ℝ) (u : EVec N)
    (hrho : 0 ≤ rho) (hA : 0 ≤ A) (hAmax0 : 0 ≤ Amax)
    (hAmax : A ≤ Amax * rho ^ 2) :
    |perspectiveDelay N lambdaWall eta rho A u +
        eta * lambdaWall * innerWallEnergy N u| ≤
      (Amax + 12 * |eta|) * rho ^ 2 := by
  rcases hrho.eq_or_lt with rfl | hrhopos
  · simp [perspectiveDelay]
  · rw [perspectiveDelay_pos_decompose lambdaWall eta A u hrhopos]
    ring_nf
    have hg0 := innerGamma_nonneg (rescaleEVec rho u)
    have hg1 := innerGamma_le_one (rescaleEVec rho u)
    have hE0 := innerResidualEnergy_nonneg hN (rescaleEVec rho u)
    have hE12 := innerResidualEnergy_le_twelve hN (rescaleEVec rho u)
    have hterm : |A * innerGamma (rescaleEVec rho u)| ≤ A := by
      rw [abs_of_nonneg (mul_nonneg hA hg0)]
      nlinarith
    have hres :
        |eta * rho ^ 2 * innerResidualEnergy N (rescaleEVec rho u)| ≤
          |eta| * rho ^ 2 * 12 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg rho),
        abs_of_nonneg hE0]
      exact mul_le_mul_of_nonneg_left hE12
        (mul_nonneg (abs_nonneg eta) (sq_nonneg rho))
    have htri := abs_sub
      (A * innerGamma (rescaleEVec rho u))
      (eta * rho ^ 2 * innerResidualEnergy N (rescaleEVec rho u))
    have hrhosq := sq_nonneg rho
    nlinarith

/-- Flat-boundary differentiability in primal parameters.  The assumptions
are exactly the article's `A = O(rho^2)` condition together with the fact that
`rho^2` has zero derivative at a closed gate. -/
theorem hasEVecFDerivAt_perspectiveDelay_comp_zero {T N : Nat}
    (hN : 0 < N) (lambdaWall eta Amax : ℝ) (u : EVec N)
    (rho rhoSq A : EVec T → ℝ) (x : EVec T)
    (hrho : ∀ w, 0 ≤ rho w) (hA : ∀ w, 0 ≤ A w)
    (hAmax0 : 0 ≤ Amax)
    (hAmax : ∀ w, A w ≤ Amax * rho w ^ 2)
    (hsq : ∀ w, rho w ^ 2 = rhoSq w)
    (hrho0 : rho x = 0)
    (hrhoSqDeriv : HasEVecFDerivAt rhoSq 0 x) :
    HasEVecFDerivAt
      (fun w ↦ perspectiveDelay N lambdaWall eta (rho w) (A w) u) 0 x := by
  let R : EVec T → ℝ := fun w ↦
    perspectiveDelay N lambdaWall eta (rho w) (A w) u +
      eta * lambdaWall * innerWallEnergy N u
  have hrhoSq0 : rhoSq x = 0 := by
    rw [← hsq x, hrho0]
    ring
  have hR0 : R x = 0 := by
    unfold R
    simp [perspectiveDelay, hrho0]
  have hC0 : 0 ≤ Amax + 12 * |eta| := by positivity
  have hRbound (w : EVec T) :
      |R w| ≤ (Amax + 12 * |eta|) * rhoSq w := by
    unfold R
    rw [← hsq w]
    exact abs_perspectiveDelay_add_wall_le hN lambdaWall eta
      (rho w) (A w) Amax u (hrho w) (hA w) hAmax0 (hAmax w)
  unfold HasEVecFDerivAt at hrhoSqDeriv ⊢
  have hrhoLittle :
      (fun w : EVec T ↦ rhoSq w) =o[nhds x]
        (fun w : EVec T ↦ w - x) := by
    simpa [hrhoSq0] using hrhoSqDeriv.isLittleO
  have hRbig : R =O[nhds x] rhoSq := by
    apply Asymptotics.IsBigO.of_bound (Amax + 12 * |eta|)
    filter_upwards [] with w
    have hr2nonneg : 0 ≤ rhoSq w := by
      rw [← hsq w]
      exact sq_nonneg (rho w)
    simpa [Real.norm_eq_abs, abs_of_nonneg hr2nonneg] using hRbound w
  have hRlittle : R =o[nhds x] (fun w : EVec T ↦ w - x) :=
    hRbig.trans_isLittleO hrhoLittle
  have hRderiv : HasFDerivAt R (0 : EVec T →L[ℝ] ℝ) x := by
    apply HasFDerivAt.of_isLittleO
    simpa [hR0] using hRlittle
  have hconst : HasFDerivAt
      (fun _ : EVec T ↦ -eta * lambdaWall * innerWallEnergy N u)
      (0 : EVec T →L[ℝ] ℝ) x :=
    hasFDerivAt_const (𝕜 := ℝ)
      (-eta * lambdaWall * innerWallEnergy N u) x
  convert hRderiv.add hconst using 1
  · funext w
    simp only [Pi.add_apply]
    unfold R
    ring
  · simp

/-- Joint-variable version of the flat-boundary argument.  The varying dual
argument contributes only through the explicit wall term at a closed gate. -/
theorem differentiableAt_perspectiveDelay_comp_zero_variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : Nat}
    (hN : 0 < N) (lambdaWall eta Amax : ℝ)
    (rho rhoSq A : E → ℝ) (u : E → EVec N) (x : E)
    (hrho : ∀ w, 0 ≤ rho w) (hA : ∀ w, 0 ≤ A w)
    (hAmax0 : 0 ≤ Amax)
    (hAmax : ∀ w, A w ≤ Amax * rho w ^ 2)
    (hsq : ∀ w, rho w ^ 2 = rhoSq w)
    (hrho0 : rho x = 0)
    (hrhoSqDeriv : HasFDerivAt rhoSq (0 : E →L[ℝ] ℝ) x)
    (hu : DifferentiableAt ℝ u x) :
    DifferentiableAt ℝ
      (fun w ↦ perspectiveDelay N lambdaWall eta (rho w) (A w) (u w)) x := by
  let R : E → ℝ := fun w ↦
    perspectiveDelay N lambdaWall eta (rho w) (A w) (u w) +
      eta * lambdaWall * innerWallEnergy N (u w)
  have hrhoSq0 : rhoSq x = 0 := by
    rw [← hsq x, hrho0]
    ring
  have hR0 : R x = 0 := by
    unfold R
    simp [perspectiveDelay, hrho0]
  have hRbound (w : E) :
      |R w| ≤ (Amax + 12 * |eta|) * rhoSq w := by
    unfold R
    rw [← hsq w]
    exact abs_perspectiveDelay_add_wall_le hN lambdaWall eta
      (rho w) (A w) Amax (u w) (hrho w) (hA w) hAmax0 (hAmax w)
  have hrhoLittle : rhoSq =o[nhds x] (fun w : E ↦ w - x) := by
    simpa [hrhoSq0] using hrhoSqDeriv.isLittleO
  have hRbig : R =O[nhds x] rhoSq := by
    apply Asymptotics.IsBigO.of_bound (Amax + 12 * |eta|)
    filter_upwards [] with w
    have hr2nonneg : 0 ≤ rhoSq w := by
      rw [← hsq w]
      exact sq_nonneg (rho w)
    simpa [Real.norm_eq_abs, abs_of_nonneg hr2nonneg] using hRbound w
  have hRlittle : R =o[nhds x] (fun w : E ↦ w - x) :=
    hRbig.trans_isLittleO hrhoLittle
  have hRderiv : HasFDerivAt R (0 : E →L[ℝ] ℝ) x := by
    apply HasFDerivAt.of_isLittleO
    simpa [hR0] using hRlittle
  have hwall : DifferentiableAt ℝ
      (fun w : E ↦ innerWallEnergy N (u w)) x :=
    (differentiable_innerWallEnergy N (u x)).comp x hu
  have hconst : DifferentiableAt ℝ
      (fun _ : E ↦ -eta * lambdaWall) x :=
    differentiableAt_const (𝕜 := ℝ) (c := -eta * lambdaWall)
  have hsum := hRderiv.differentiableAt.add (hconst.mul hwall)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [] with w
  simp only [Pi.add_apply, Pi.mul_apply]
  unfold R
  ring

end

end NCPLVerification
