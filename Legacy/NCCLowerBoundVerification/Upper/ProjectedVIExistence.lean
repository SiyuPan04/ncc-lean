import NCCLowerBoundVerification.Upper.ProjectionGeometry

/-!
# Existence of the projected variational-inequality solution

This file removes the explicit `uStar`/normal-cone premise from the projected
micro-solver.  The ambient type `EVec d = Fin d → ℝ` carries the sup norm in
Lean, whereas all analytic estimates in the paper use the Euclidean square
`vecSq`.  We therefore transfer the projected step to `EuclideanSpace`, put
the closed feasible set there, and apply the Banach fixed-point theorem to
the resulting complete subtype.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace ProjectedVIExistence

noncomputable section

open RelativeFOAM ProjectionGeometry

abbrev EuclideanVec (d : Nat) := EuclideanSpace ℝ (Fin d)

def toEuclidean {d : Nat} (x : EVec d) : EuclideanVec d :=
  WithLp.toLp 2 x

def fromEuclidean {d : Nat} (x : EuclideanVec d) : EVec d :=
  WithLp.ofLp x

@[simp] theorem fromEuclidean_toEuclidean {d : Nat} (x : EVec d) :
    fromEuclidean (toEuclidean x) = x := rfl

@[simp] theorem toEuclidean_fromEuclidean {d : Nat} (x : EuclideanVec d) :
    toEuclidean (fromEuclidean x) = x := rfl

@[simp] theorem fromEuclidean_sub {d : Nat} (x y : EuclideanVec d) :
    fromEuclidean (x - y) = fromEuclidean x - fromEuclidean y := rfl

@[simp] theorem toEuclidean_sub {d : Nat} (x y : EVec d) :
    toEuclidean (x - y) = toEuclidean x - toEuclidean y := rfl

def fromEuclideanLinear (d : Nat) : EuclideanVec d →ₗ[ℝ] EVec d where
  toFun := fromEuclidean
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

def euclideanSet {d : Nat} (C : Set (EVec d)) : Set (EuclideanVec d) :=
  fromEuclidean ⁻¹' C

theorem euclideanSet_isClosed {d : Nat} {C : Set (EVec d)}
    (hC : IsClosed C) : IsClosed (euclideanSet C) := by
  exact hC.preimage (fromEuclideanLinear d).continuous_of_finiteDimensional

theorem norm_toEuclidean {d : Nat} (x : EVec d) :
    ‖toEuclidean x‖ = Real.sqrt (vecSq x) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  unfold vecSq NCPLVerification.vecSq toEuclidean
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.norm_eq_abs, sq_abs]

theorem norm_euclidean {d : Nat} (x : EuclideanVec d) :
    ‖x‖ = Real.sqrt (vecSq (fromEuclidean x)) := by
  conv_lhs => rw [← toEuclidean_fromEuclidean x]
  exact norm_toEuclidean (fromEuclidean x)

def contractionSq (M : ℝ) : ℝ := 1 - (M ^ 2)⁻¹

def contractionNN (M : ℝ) : NNReal :=
  ⟨Real.sqrt (contractionSq M), Real.sqrt_nonneg _⟩

@[simp] theorem contractionNN_coe (M : ℝ) :
    (contractionNN M : ℝ) = Real.sqrt (contractionSq M) := rfl

theorem inverse_square_pos {M : ℝ} (hM : 1 ≤ M) : 0 < (M ^ 2)⁻¹ := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  positivity

theorem inverse_square_le_one {M : ℝ} (hM : 1 ≤ M) : (M ^ 2)⁻¹ ≤ 1 := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have hsq : 1 ≤ M ^ 2 := by nlinarith
  have hinv : 0 ≤ (M ^ 2)⁻¹ := by positivity
  have hmul : M ^ 2 * (M ^ 2)⁻¹ = 1 := by
    field_simp [hMpos.ne']
  nlinarith

theorem contractionSq_nonneg {M : ℝ} (hM : 1 ≤ M) :
    0 ≤ contractionSq M := by
  unfold contractionSq
  linarith [inverse_square_le_one hM]

theorem contractionSq_lt_one {M : ℝ} (hM : 1 ≤ M) :
    contractionSq M < 1 := by
  unfold contractionSq
  linarith [inverse_square_pos hM]

theorem contractionNN_lt_one {M : ℝ} (hM : 1 ≤ M) :
    contractionNN M < 1 := by
  change Real.sqrt (contractionSq M) < 1
  have hq := contractionSq_nonneg hM
  have hq1 := contractionSq_lt_one hM
  have hs := Real.sq_sqrt hq
  have hs0 := Real.sqrt_nonneg (contractionSq M)
  nlinarith

def liftedProjectedStep {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    (A : EVec d → EVec d) (M : ℝ) :
    euclideanSet C → euclideanSet C :=
  fun u => ⟨toEuclidean
      (projectedStep project A (M ^ 2)⁻¹ (fromEuclidean u.1)), hp.mem _⟩

theorem liftedProjectedStep_contracting {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotoneOn C A 1)
    (hlip : IsEuclideanLipschitzOn C A M) :
    ContractingWith (contractionNN M) (liftedProjectedStep hp A M) := by
  refine ⟨contractionNN_lt_one hM, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro u v
  have hsq := projectedStep_contraction_M_inv_sq_on hp hM hmono hlip
    u.property v.property
  have hout : 0 ≤ vecSq
      (projectedStep project A (M ^ 2)⁻¹ (fromEuclidean u.1) -
        projectedStep project A (M ^ 2)⁻¹ (fromEuclidean v.1)) :=
    vecSq_nonneg _
  have hin : 0 ≤ vecSq (fromEuclidean u.1 - fromEuclidean v.1) :=
    vecSq_nonneg _
  have hroot :
      Real.sqrt (vecSq
        (projectedStep project A (M ^ 2)⁻¹ (fromEuclidean u.1) -
          projectedStep project A (M ^ 2)⁻¹ (fromEuclidean v.1))) ≤
        Real.sqrt (contractionSq M) *
          Real.sqrt (vecSq (fromEuclidean u.1 - fromEuclidean v.1)) := by
    calc
      Real.sqrt (vecSq
          (projectedStep project A (M ^ 2)⁻¹ (fromEuclidean u.1) -
            projectedStep project A (M ^ 2)⁻¹ (fromEuclidean v.1))) ≤
          Real.sqrt (contractionSq M *
            vecSq (fromEuclidean u.1 - fromEuclidean v.1)) :=
        Real.sqrt_le_sqrt hsq
      _ = Real.sqrt (contractionSq M) *
          Real.sqrt (vecSq (fromEuclidean u.1 - fromEuclidean v.1)) :=
        Real.sqrt_mul (contractionSq_nonneg hM) _
  simpa only [Subtype.dist_eq, dist_eq_norm, liftedProjectedStep,
    norm_euclidean, fromEuclidean_toEuclidean, fromEuclidean_sub,
    contractionNN_coe] using hroot

/-- Banach existence for the concrete projected step on a nonempty closed
feasible set.  Convexity is not needed here because `hp` already contains
the full projection variational inequality; it is required when constructing
such a projection from a set. -/
theorem exists_projectedStep_fixedPoint {d : Nat} {C : Set (EVec d)}
    (hCne : C.Nonempty) (hCclosed : IsClosed C)
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotoneOn C A 1)
    (hlip : IsEuclideanLipschitzOn C A M) :
    ∃ uStar ∈ C,
      projectedStep project A (M ^ 2)⁻¹ uStar = uStar := by
  let CE := euclideanSet C
  have hCEclosed : IsClosed CE := euclideanSet_isClosed hCclosed
  letI : CompleteSpace CE := hCEclosed.completeSpace_coe
  let F : CE → CE := liftedProjectedStep hp A M
  have hcontract : ContractingWith (contractionNN M) F :=
    liftedProjectedStep_contracting hp hM hmono hlip
  obtain ⟨u0, hu0⟩ := hCne
  let z0 : CE := ⟨toEuclidean u0, hu0⟩
  obtain ⟨zStar, hzfixed, -, -⟩ :=
    hcontract.exists_fixedPoint z0 (by simp)
  refine ⟨fromEuclidean zStar.1, zStar.property, ?_⟩
  have h := congrArg (fun z : CE => fromEuclidean z.1) hzfixed
  simpa [F, liftedProjectedStep] using h

theorem projectedStep_fixedPoint_unique {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotoneOn C A 1)
    (hlip : IsEuclideanLipschitzOn C A M)
    {u v : EVec d} (hu : u ∈ C) (hv : v ∈ C)
    (hufixed : projectedStep project A (M ^ 2)⁻¹ u = u)
    (hvfixed : projectedStep project A (M ^ 2)⁻¹ v = v) : u = v := by
  have hsq := projectedStep_contraction_M_inv_sq_on hp hM hmono hlip hu hv
  rw [hufixed, hvfixed] at hsq
  have hnonneg := vecSq_nonneg (u - v)
  have hpos := inverse_square_pos hM
  have hzero : vecSq (u - v) = 0 := by
    nlinarith
  exact sub_eq_zero.mp ((vecSq_eq_zero_iff (u - v)).mp hzero)

theorem exists_unique_projectedStep_fixedPoint {d : Nat}
    {C : Set (EVec d)} (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (_hCconvex : Convex ℝ C)
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotoneOn C A 1)
    (hlip : IsEuclideanLipschitzOn C A M) :
    ∃! uStar : EVec d,
      uStar ∈ C ∧ projectedStep project A (M ^ 2)⁻¹ uStar = uStar := by
  obtain ⟨uStar, huStar, hfixed⟩ :=
    exists_projectedStep_fixedPoint hCne hCclosed hp hM hmono hlip
  refine ⟨uStar, ⟨huStar, hfixed⟩, ?_⟩
  intro v hv
  exact projectedStep_fixedPoint_unique hp hM hmono hlip
    hv.1 huStar hv.2 hfixed

theorem normal_of_projectedStep_fixed {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    {uStar : EVec d} (hfixed :
      projectedStep project A (M ^ 2)⁻¹ uStar = uStar) :
    IsEuclideanNormal C uStar (-A uStar) := by
  have heta : 0 < (M ^ 2)⁻¹ := inverse_square_pos hM
  have hn := hp.normal (uStar - (M ^ 2)⁻¹ • A uStar)
  rw [show project (uStar - (M ^ 2)⁻¹ • A uStar) = uStar by
    exact hfixed] at hn
  have hscaled := hn.nonneg_smul (inv_nonneg.mpr heta.le)
  have heq : ((M ^ 2)⁻¹)⁻¹ •
      (uStar - (M ^ 2)⁻¹ • A uStar - uStar) = -A uStar := by
    funext i
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]
    field_simp [heta.ne']
    ring
  rwa [heq] at hscaled

/-- The missing existence statement for the projected micro-solver: closed,
nonempty, convex feasibility plus the existing projection interface and the
paper's monotonicity/Lipschitz assumptions produce an actual VI solution. -/
theorem exists_projectedVI_solution {d : Nat} {C : Set (EVec d)}
    (hCne : C.Nonempty) (hCclosed : IsClosed C)
    (_hCconvex : Convex ℝ C)
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotoneOn C A 1)
    (hlip : IsEuclideanLipschitzOn C A M) :
    ∃ uStar ∈ C, IsEuclideanNormal C uStar (-A uStar) := by
  obtain ⟨uStar, huStar, hfixed⟩ :=
    exists_projectedStep_fixedPoint hCne hCclosed hp hM hmono hlip
  exact ⟨uStar, huStar, normal_of_projectedStep_fixed hp hM hfixed⟩

end

end ProjectedVIExistence
end Upper
end NCCLowerBoundVerification
