import NCPLVerification.Perspective

/-!
# Frechet differentiability of the inner chain

The algebraic development uses `EVec N = Fin N -> Real`.  This file pins
the norm topology explicitly when stating analytic facts.  That avoids the
instance diamond between the finite product topology and the topology induced
by the sup norm; mathematically they are the same topology.
-/

namespace NCPLVerification

noncomputable section

/-- `HasFDerivAt` on `EVec`, with the norm-induced topology selected
explicitly.  This wrapper prevents an irrelevant topology instance diamond. -/
def HasEVecFDerivAt {N : Nat} (f : EVec N -> Real)
    (f' : EVec N →L[ℝ] ℝ) (z : EVec N) : Prop :=
  @HasFDerivAt ℝ _ (EVec N)
    Pi.normedAddCommGroup.toAddCommGroup Pi.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f f' z

/-- Differentiability with the same explicitly selected finite-dimensional
norm topology as `HasEVecFDerivAt`. -/
def EVecDifferentiableAt {N : Nat} (f : EVec N → Real)
    (z : EVec N) : Prop :=
  @DifferentiableAt ℝ _ (EVec N)
    Pi.normedAddCommGroup.toAddCommGroup Pi.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f z

/-- The Fréchet derivative with those same explicit instances. -/
def evecFderiv {N : Nat} (f : EVec N → Real) (z : EVec N) :
    EVec N →L[ℝ] ℝ :=
  @fderiv ℝ _ (EVec N)
    Pi.normedAddCommGroup.toAddCommGroup Pi.normedSpace.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace f z

theorem EVecDifferentiableAt.hasEVecFDerivAt {N : Nat}
    {f : EVec N → Real} {z : EVec N} (h : EVecDifferentiableAt f z) :
    HasEVecFDerivAt f (evecFderiv f z) z := by
  unfold EVecDifferentiableAt evecFderiv HasEVecFDerivAt at *
  exact h.hasFDerivAt

def evecBasis {N : Nat} (i : Fin N) : EVec N :=
  fun j ↦ if j = i then 1 else 0

def continuousLinearMapCoordinates {N : Nat}
    (f' : EVec N →L[ℝ] ℝ) : EVec N :=
  fun i ↦ f' (evecBasis i)

theorem continuousLinearMap_apply_eq_coordinates {N : Nat}
    (f' : EVec N →L[ℝ] ℝ) (h : EVec N) :
    f' h = ∑ i : Fin N, continuousLinearMapCoordinates f' i * h i := by
  have hdecomp : h = ∑ i : Fin N, h i • evecBasis i := by
    funext j
    simp [evecBasis]
  calc
    f' h = f' (∑ i : Fin N, h i • evecBasis i) := congrArg f' hdecomp
    _ = ∑ i : Fin N, f' (h i • evecBasis i) := by rw [map_sum]
    _ = ∑ i : Fin N, continuousLinearMapCoordinates f' i * h i := by
      apply Finset.sum_congr rfl
      intro i _
      simp [continuousLinearMapCoordinates, mul_comm]

/-- The continuous linear coordinate projection, using the norm topology. -/
def evecProj {N : Nat} (i : Fin N) :
    EVec N →L[ℝ] ℝ := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact LinearMap.toContinuousLinearMap
    ({ toFun := fun z : EVec N => z i
       map_add' := by intro x y; rfl
       map_smul' := by intro c x; rfl } : EVec N →ₗ[ℝ] ℝ)

@[simp] theorem evecProj_apply {N : Nat} (i : Fin N) (z : EVec N) :
    evecProj i z = z i := by
  unfold evecProj
  rfl

theorem hasEVecFDerivAt_apply {N : Nat} (z : EVec N) (i : Fin N) :
    HasEVecFDerivAt (fun w : EVec N => w i) (evecProj i) z := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasEVecFDerivAt evecProj
  exact (LinearMap.toContinuousLinearMap
    ({ toFun := fun w : EVec N => w i
       map_add' := by intro x y; rfl
       map_smul' := by intro c x; rfl } : EVec N →ₗ[ℝ] ℝ)).hasFDerivAt

/-- Derivative of the predecessor coordinate (the zeroth predecessor is the
constant one). -/
def innerPrevCLM {N : Nat} (i : Fin N) : EVec N →L[ℝ] ℝ :=
  if hi : i.1 = 0 then 0 else evecProj ⟨i.1 - 1, by omega⟩

theorem hasEVecFDerivAt_innerPrev {N : Nat} (z : EVec N) (i : Fin N) :
    HasEVecFDerivAt (fun w : EVec N => innerPrev w i)
      (innerPrevCLM i) z := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasEVecFDerivAt
  by_cases hi : i.1 = 0
  · have hconst : HasFDerivAt (fun _ : EVec N => (1 : ℝ)) 0 z :=
      hasFDerivAt_const (𝕜 := ℝ) 1 z
    simpa [innerPrev, innerPrevCLM, hi] using hconst
  · have happ : HasFDerivAt (fun w : EVec N => w ⟨i.1 - 1, by omega⟩)
        (evecProj ⟨i.1 - 1, by omega⟩) z :=
      by
        convert (evecProj (N := N) ⟨i.1 - 1, by omega⟩).hasFDerivAt using 1
        funext w
        exact evecProj_apply _ w
    simpa [innerPrev, innerPrevCLM, hi] using happ

/-- Actual derivative of the squared residual in link `i`. -/
def innerResidualSqFDeriv {N : Nat} (z : EVec N) (i : Fin N) :
    EVec N →L[ℝ] ℝ :=
  let prevMap := ContinuousLinearMap.toSpanSingleton ℝ
    (sigmaDeriv (innerPrev z i)) ∘L innerPrevCLM i
  let hereMap := ContinuousLinearMap.toSpanSingleton ℝ
    (betaDeriv (z i)) ∘L evecProj i
  let productMap := (sigma (innerPrev z i)) • hereMap +
    (beta (z i)) • prevMap
  ContinuousLinearMap.toSpanSingleton ℝ (2 * innerResidual z i) ∘L
    (-productMap)

theorem hasEVecFDerivAt_innerResidual_sq {N : Nat}
    (z : EVec N) (i : Fin N) :
    HasEVecFDerivAt (fun w : EVec N => innerResidual w i ^ 2)
      (innerResidualSqFDeriv z i) z := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasEVecFDerivAt
  have hprev : HasFDerivAt (fun w : EVec N => innerPrev w i)
      (innerPrevCLM i) z := by
    simpa only [HasEVecFDerivAt] using hasEVecFDerivAt_innerPrev z i
  have hsigma := (hasDerivAt_sigma (innerPrev z i)).hasFDerivAt.comp z hprev
  have hhere : HasFDerivAt (fun w : EVec N => w i) (evecProj i) z :=
    (evecProj (N := N) i).hasFDerivAt
  have hbeta := (hasDerivAt_beta (z i)).hasFDerivAt.comp z hhere
  have hproduct := hsigma.mul hbeta
  have hinside := (hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) z).sub hproduct
  have houter := (hasDerivAt_posPart_sq
    (1 - sigma (innerPrev z i) * beta (z i))).hasFDerivAt.comp z hinside
  simpa [innerResidualSqFDeriv, innerResidual, gateResidual,
    Function.comp_def] using houter

/-- Actual derivative of the squared negative-part wall at coordinate `i`. -/
def innerWallSqFDeriv {N : Nat} (z : EVec N) (i : Fin N) :
    EVec N →L[ℝ] ℝ :=
  ContinuousLinearMap.toSpanSingleton ℝ (-2 * negPart (z i)) ∘L evecProj i

theorem hasEVecFDerivAt_innerWall_sq {N : Nat}
    (z : EVec N) (i : Fin N) :
    HasEVecFDerivAt (fun w : EVec N => negPart (w i) ^ 2)
      (innerWallSqFDeriv z i) z := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasEVecFDerivAt
  have hhere : HasFDerivAt (fun w : EVec N => w i) (evecProj i) z :=
    (evecProj (N := N) i).hasFDerivAt
  have h := (hasDerivAt_negPart_sq (z i)).hasFDerivAt.comp z hhere
  simpa [innerWallSqFDeriv, Function.comp_def] using h

/-- The derivative assembled from all residual and wall terms. -/
def innerHFDeriv (N : Nat) (lambdaWall : ℝ) (z : EVec N) :
    EVec N →L[ℝ] ℝ :=
  (∑ i : Fin N, (innerAlpha N i) • innerResidualSqFDeriv z i) +
    lambdaWall • (∑ i : Fin N, (innerD N i) • innerWallSqFDeriv z i)

/-- The inner objective has a genuine Frechet derivative at every point,
including all splice points of both piecewise gates. -/
theorem hasEVecFDerivAt_innerH (N : Nat) (lambdaWall : ℝ) (z : EVec N) :
    HasEVecFDerivAt (innerH N lambdaWall) (innerHFDeriv N lambdaWall z) z := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasEVecFDerivAt
  have hres : HasFDerivAt
      (fun w : EVec N => ∑ i : Fin N,
        innerAlpha N i * innerResidual w i ^ 2)
      (∑ i : Fin N, (innerAlpha N i) • innerResidualSqFDeriv z i) z := by
    apply HasFDerivAt.fun_sum
    intro i _
    have hi : HasFDerivAt (fun w : EVec N => innerResidual w i ^ 2)
        (innerResidualSqFDeriv z i) z := by
      simpa [HasEVecFDerivAt] using hasEVecFDerivAt_innerResidual_sq z i
    simpa only using hi.const_mul (innerAlpha N i)
  have hwall : HasFDerivAt
      (fun w : EVec N => ∑ i : Fin N,
        innerD N i * negPart (w i) ^ 2)
      (∑ i : Fin N, (innerD N i) • innerWallSqFDeriv z i) z := by
    apply HasFDerivAt.fun_sum
    intro i _
    have hi : HasFDerivAt (fun w : EVec N => negPart (w i) ^ 2)
        (innerWallSqFDeriv z i) z := by
      simpa [HasEVecFDerivAt] using hasEVecFDerivAt_innerWall_sq z i
    simpa only using hi.const_mul (innerD N i)
  have htotal := hres.add (hwall.const_mul lambdaWall)
  unfold innerHFDeriv
  convert htotal using 1
  funext w
  rfl

@[simp] theorem innerPrevCLM_apply {N : Nat} (i : Fin N) (h : EVec N) :
    innerPrevCLM i h =
      if hi : i.1 = 0 then 0 else h ⟨i.1 - 1, by omega⟩ := by
  by_cases hi : i.1 = 0 <;> simp [innerPrevCLM, hi]

@[simp] theorem innerResidualSqFDeriv_apply {N : Nat}
    (z h : EVec N) (i : Fin N) :
    innerResidualSqFDeriv z i h =
      -2 * innerResidual z i *
        (sigma (innerPrev z i) * betaDeriv (z i) * h i +
          beta (z i) * sigmaDeriv (innerPrev z i) * innerPrevCLM i h) := by
  by_cases hi : i.1 = 0 <;>
    simp [innerResidualSqFDeriv, innerPrevCLM, hi] <;> ring

@[simp] theorem innerWallSqFDeriv_apply {N : Nat}
    (z h : EVec N) (i : Fin N) :
    innerWallSqFDeriv z i h = -2 * negPart (z i) * h i := by
  simp [innerWallSqFDeriv]
  ring

/-- Reindex a sum over nonzero coordinates by their predecessors. -/
theorem sum_predecessor_eq_sum_successor {N : Nat} (a h : EVec N) :
    (∑ i : Fin N,
      if hi : i.1 = 0 then 0 else a i * h ⟨i.1 - 1, by omega⟩) =
    ∑ j : Fin N,
      if hj : j.1 + 1 < N then a ⟨j.1 + 1, hj⟩ * h j else 0 := by
  cases N with
  | zero => simp
  | succ n =>
      rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
      simp
      apply Finset.sum_congr rfl
      intro x _
      rfl

theorem continuousLinearMap_sum_apply {ι E F : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace ℝ E]
    [NormedSpace ℝ F] (f : ι → E →L[ℝ] F) (x : E) :
    (∑ i, f i) x = ∑ i, f i x := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

/-- Coefficient with which residual `i` differentiates its predecessor. -/
def innerPredecessorContribution (N : Nat) (z : EVec N) (i : Fin N) : ℝ :=
  -2 * innerAlpha N i * innerResidual z i * beta (z i) *
    sigmaDeriv (innerPrev z i)

theorem sum_predecessorContribution_eq_forward (N : Nat) (z h : EVec N) :
    (∑ i : Fin N, innerPredecessorContribution N z i * innerPrevCLM i h) =
      ∑ j : Fin N, -2 * innerForward N z j * h j := by
  calc
    (∑ i : Fin N, innerPredecessorContribution N z i * innerPrevCLM i h) =
        ∑ i : Fin N, if hi : i.1 = 0 then 0 else
          innerPredecessorContribution N z i * h ⟨i.1 - 1, by omega⟩ := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i.1 = 0 <;> simp [hi]
    _ = ∑ j : Fin N, if hj : j.1 + 1 < N then
          innerPredecessorContribution N z ⟨j.1 + 1, hj⟩ * h j else 0 :=
      sum_predecessor_eq_sum_successor
        (fun i => innerPredecessorContribution N z i) h
    _ = ∑ j : Fin N, -2 * innerForward N z j * h j := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j.1 + 1 < N
      · simp only [innerForward, innerPredecessorContribution, hj, dite_true]
        rw [show innerPrev z ⟨j.1 + 1, hj⟩ = z j by
          simp [innerPrev]]
        ring
      · simp [innerForward, hj]

/-- The assembled Frechet derivative acts by Euclidean dot product with the
explicit coordinate field `innerGradient`. -/
theorem innerHFDeriv_apply_eq_gradient_dot (N : Nat) (lambdaWall : ℝ)
    (z h : EVec N) :
    innerHFDeriv N lambdaWall z h =
      ∑ i : Fin N, innerGradient N lambdaWall z i * h i := by
  have hres :
      (∑ i : Fin N, innerAlpha N i * innerResidualSqFDeriv z i h) =
        (∑ i : Fin N, -2 * innerIncoming N z i * h i) +
          ∑ i : Fin N,
            innerPredecessorContribution N z i * innerPrevCLM i h := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [innerResidualSqFDeriv_apply]
    simp only [innerIncoming, innerPredecessorContribution]
    ring
  have hwall :
      lambdaWall *
          (∑ i : Fin N, innerD N i * innerWallSqFDeriv z i h) =
        ∑ i : Fin N,
          (-2 * lambdaWall * innerD N i * negPart (z i)) * h i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [innerWallSqFDeriv_apply]
    ring
  rw [innerHFDeriv]
  rw [add_apply]
  rw [smul_apply]
  rw [continuousLinearMap_sum_apply, continuousLinearMap_sum_apply]
  simp only [smul_apply, smul_eq_mul]
  rw [hres, sum_predecessorContribution_eq_forward, hwall]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [innerGradient]
  ring

/-- Continuous linear functional represented by Euclidean dot product. -/
def evecDot {N : Nat} (g : EVec N) : EVec N →L[ℝ] ℝ := by
  letI : AddCommGroup (EVec N) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec N) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact LinearMap.toContinuousLinearMap
    ({ toFun := fun h : EVec N => ∑ i : Fin N, g i * h i
       map_add' := by
         intro x y
         rw [← Finset.sum_add_distrib]
         apply Finset.sum_congr rfl
         intro i _
         simp only [Pi.add_apply]
         ring
       map_smul' := by
         intro c x
         simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro i _
         ring } : EVec N →ₗ[ℝ] ℝ)

@[simp] theorem evecDot_apply {N : Nat} (g h : EVec N) :
    evecDot g h = ∑ i : Fin N, g i * h i := by
  unfold evecDot
  rfl

theorem innerHFDeriv_eq_gradientDot (N : Nat) (lambdaWall : ℝ)
    (z : EVec N) :
    innerHFDeriv N lambdaWall z = evecDot (innerGradient N lambdaWall z) := by
  apply ContinuousLinearMap.ext
  intro h
  simpa using innerHFDeriv_apply_eq_gradient_dot N lambdaWall z h

/-- Final analytic form of the inner-chain lemma: the derivative of `H_N`
is represented by exactly the coordinate gradient used by the PL and
zero-chain proofs. -/
theorem hasEVecFDerivAt_innerH_gradient (N : Nat) (lambdaWall : ℝ)
    (z : EVec N) :
    HasEVecFDerivAt (innerH N lambdaWall)
      (evecDot (innerGradient N lambdaWall z)) z := by
  rw [← innerHFDeriv_eq_gradientDot]
  exact hasEVecFDerivAt_innerH N lambdaWall z

end

end NCPLVerification
