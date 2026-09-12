import NCCLowerBoundVerification.Upper.MoreauEnvelope
import NCCLowerBoundVerification.Upper.ClassAnalytic
import NCCLowerBoundVerification.Lower.TerminalOS
import NCCLowerBound.Simplified.CorrectedModel

/-!
# Moreau differentiability and optimization-stationarity bridge

This module isolates a type-correct consequence that is important for the
simplified manuscript.  Differentiability of the value function itself is not
part of the NC--C function class.  Once the value is weakly convex and its
proximal problem has a minimizer at every anchor, its Moreau envelope is
automatically continuously Fréchet differentiable (`C¹`).

The second part proves that the paper's existential proximal definition of
optimization stationarity is exactly the squared Euclidean residual-gradient
test.  For an unconstrained differentiable value function, that residual is
also exactly the gradient of the value at the selected proximal point.
-/

namespace NCCLowerBound
namespace Simplified

noncomputable section

open NCCLowerBoundVerification
open NCCLowerBoundVerification.Upper

/-! ## Differentiability is a theorem, not a class assumption -/

/--
Weak convexity, a positive proximal coefficient, and existence of proximal
minimizers imply the genuine Fréchet derivative formula for the Moreau
envelope at every anchor.
-/
theorem moreauEnvelope_hasFDerivAt_of_weakConvex
    {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ} {ell : ℝ}
    (hell : 0 < ell) (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z : EVec m) :
    HasFDerivAt (moreauEnvelope phi ell hexists)
      (residualCLM (residualGradient hexists z)) z := by
  exact hasFDerivAt_moreauEnvelope hell hweak hexists z

/-- The Moreau envelope is automatically Fréchet differentiable everywhere. -/
theorem moreauEnvelope_differentiable_of_weakConvex
    {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ} {ell : ℝ}
    (hell : 0 < ell) (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) :
    Differentiable ℝ (moreauEnvelope phi ell hexists) := by
  exact differentiable_moreauEnvelope hell hweak hexists

/-- Exact `fderiv` formula for the automatically differentiable envelope. -/
theorem moreauEnvelope_fderiv_eq_residual
    {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ} {ell : ℝ}
    (hell : 0 < ell) (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z : EVec m) :
    fderiv ℝ (moreauEnvelope phi ell hexists) z =
      residualCLM (residualGradient hexists z) := by
  exact fderiv_moreauEnvelope_eq hell hweak hexists z

/-! ## Continuity of the derivative and the `C¹` bridge -/

/-- The squared residual estimate from `Upper.MoreauEnvelope`, converted to
the ambient finite-product norm.  The harmless factor `m + 1` avoids a
separate zero-dimensional case while retaining a global Lipschitz bound. -/
theorem residualGradient_norm_sub_le
    {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ} {ell : ℝ}
    (hell : 0 < ell) (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z w : EVec m) :
    ‖residualGradient hexists z - residualGradient hexists w‖ ≤
      (2 * ell * ((m : ℝ) + 1)) * ‖z - w‖ := by
  let dg := residualGradient hexists z - residualGradient hexists w
  let dz := z - w
  have hnorm : ‖dg‖ ≤ Real.sqrt (vecSq dg) :=
    norm_le_sqrt_vecSq dg
  have hnormSq : ‖dg‖ ^ 2 ≤ vecSq dg := by
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg dg) (Real.sqrt_nonneg (vecSq dg))).2 hnorm
    simpa [Real.sq_sqrt (vecSq_nonneg dg)] using hsquare
  have hres : vecSq dg ≤ (2 * ell) ^ 2 * vecSq dz := by
    simpa [dg, dz] using residualGradient_lipschitz_sq hell hweak hexists z w
  have hinput : vecSq dz ≤ (m : ℝ) * ‖dz‖ ^ 2 :=
    vecSq_le_card_mul_norm_sq dz
  have hchain :
      ‖dg‖ ^ 2 ≤ (2 * ell) ^ 2 * (m : ℝ) * ‖dz‖ ^ 2 :=
    hnormSq.trans <| hres.trans <|
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left hinput (sq_nonneg (2 * ell)))
  have hm : (0 : ℝ) ≤ m := by positivity
  have hmGrow : (m : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (m : ℝ)]
  have htargetSq :
      ‖dg‖ ^ 2 ≤ ((2 * ell * ((m : ℝ) + 1)) * ‖dz‖) ^ 2 := by
    calc
      ‖dg‖ ^ 2 ≤ (2 * ell) ^ 2 * (m : ℝ) * ‖dz‖ ^ 2 := hchain
      _ ≤ (2 * ell) ^ 2 * ((m : ℝ) + 1) ^ 2 * ‖dz‖ ^ 2 := by
        gcongr
      _ = ((2 * ell * ((m : ℝ) + 1)) * ‖dz‖) ^ 2 := by ring
  have htargetNonneg :
      0 ≤ (2 * ell * ((m : ℝ) + 1)) * ‖dz‖ := by positivity
  exact (sq_le_sq₀ (norm_nonneg dg) htargetNonneg).1 htargetSq

/-- The Moreau residual-gradient field is globally Lipschitz in the ambient
norm, hence in particular continuous. -/
theorem residualGradient_lipschitzWith
    {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ} {ell : ℝ}
    (hell : 0 < ell) (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) :
    LipschitzWith ⟨2 * ell * ((m : ℝ) + 1), by positivity⟩
      (residualGradient hexists) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simp only [dist_eq_norm]
  change ‖residualGradient hexists z - residualGradient hexists w‖ ≤
    (2 * ell * ((m : ℝ) + 1)) * ‖z - w‖
  exact residualGradient_norm_sub_le hell hweak hexists z w

/-- Continuity of the residual-gradient field, obtained from its global
Lipschitz estimate. -/
theorem residualGradient_continuous
    {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ} {ell : ℝ}
    (hell : 0 < ell) (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) :
    Continuous (residualGradient hexists) :=
  (residualGradient_lipschitzWith hell hweak hexists).continuous

/-- The Riesz-style map used by the derivative formula is itself a continuous
linear map from residual vectors to continuous linear functionals. -/
def residualCLMMap (m : Nat) :
    EVec m →L[ℝ] (EVec m →L[ℝ] ℝ) := by
  exact LinearMap.toContinuousLinearMap
    ({ toFun := residualCLM
       map_add' := by
         intro g k
         ext h
         simp only [residualCLM_apply, add_apply]
         unfold eDot
         rw [← Finset.sum_add_distrib]
         apply Finset.sum_congr rfl
         intro i _
         simp only [Pi.add_apply]
         ring
       map_smul' := by
         intro c g
         ext h
         simp only [residualCLM_apply, smul_apply,
           RingHom.id_apply]
         unfold eDot
         simp only [Pi.smul_apply, smul_eq_mul]
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro i _
         ring } : EVec m →ₗ[ℝ] (EVec m →L[ℝ] ℝ))

@[simp] theorem residualCLMMap_apply {m : Nat} (g : EVec m) :
    residualCLMMap m g = residualCLM g :=
  rfl

/-- The actual Fréchet derivative field of the envelope is continuous. -/
theorem moreauEnvelope_continuous_fderiv_of_weakConvex
    {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ} {ell : ℝ}
    (hell : 0 < ell) (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) :
    Continuous (fderiv ℝ (moreauEnvelope phi ell hexists)) := by
  have hcontinuous :
      Continuous (fun z ↦ residualCLM (residualGradient hexists z)) := by
    change Continuous (fun z ↦
      residualCLMMap m (residualGradient hexists z))
    exact (residualCLMMap m).continuous.comp
      (residualGradient_continuous hell hweak hexists)
  convert hcontinuous using 1
  funext z
  exact moreauEnvelope_fderiv_eq_residual hell hweak hexists z

/-- Weak convexity and everywhere proximal attainment imply that the Moreau
envelope is continuously Fréchet differentiable, i.e. `C¹`. -/
theorem moreauEnvelope_contDiff_one_of_weakConvex
    {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ} {ell : ℝ}
    (hell : 0 < ell) (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) :
    ContDiff ℝ 1 (moreauEnvelope phi ell hexists) := by
  rw [contDiff_one_iff_fderiv]
  exact ⟨moreauEnvelope_differentiable_of_weakConvex hell hweak hexists,
    moreauEnvelope_continuous_fderiv_of_weakConvex hell hweak hexists⟩

/-! ## Direct consequence for the corrected function class -/

namespace CorrectedModel

/-- Every member of the corrected NC--C function class has a `C¹` Moreau
envelope of its value.  Both weak convexity and proximal attainment are
derived from `IsFunctionClass`; neither is an additional hypothesis. -/
theorem IsFunctionClass.value_moreauEnvelope_contDiff_one
    {ell D Delta : ℝ} {m n : Nat} {P : NCCInstance m n}
    (hP : IsFunctionClass ell D Delta P) :
    ContDiff ℝ 1
      (moreauEnvelope (ValueOn P.Y P.f) ell
        (NCCLowerBoundVerification.Upper.IsNCCClass.value_hasProxEverywhere
          hP.2.2.2)) := by
  let hclass : IsNCCClass ell D Delta P := hP.2.2.2
  have hweak : IsWeaklyConvexOn ell P.X (ValueOn P.Y P.f) := by
    simpa [IsWeaklyConvexOn, quadraticCorrection] using
      hclass.value_weakConvexity
  exact moreauEnvelope_contDiff_one_of_weakConvex hclass.ell_pos hweak
    (NCCLowerBoundVerification.Upper.IsNCCClass.value_hasProxEverywhere hclass)

end CorrectedModel

/-! ## Exact stationarity equivalences -/

/-- The Euclidean norm used in the paper, represented on `EVec` coordinates. -/
def euclideanNorm {m : Nat} (v : EVec m) : ℝ :=
  Real.sqrt (vecSq v)

theorem euclideanNorm_nonneg {m : Nat} (v : EVec m) :
    0 ≤ euclideanNorm v := by
  exact Real.sqrt_nonneg _

/-- Squared and unsquared Euclidean residual tests agree for nonnegative tolerances. -/
theorem euclideanNorm_le_iff_vecSq_le {m : Nat} {v : EVec m} {eps : ℝ}
    (heps : 0 ≤ eps) :
    euclideanNorm v ≤ eps ↔ vecSq v ≤ eps ^ 2 := by
  simp only [euclideanNorm, Real.sqrt_le_iff]
  exact and_iff_right heps

/--
A small residual gradient supplies the selected proximal point as an exact
optimization-stationarity witness.  This direction needs no weak-convexity
assumption because the selected point is already a global proximal minimizer.
-/
theorem optimizationStationary_of_residualGradient_vecSq_le
    {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ} {ell eps : ℝ}
    (hell : 0 < ell) (hexists : HasProxEverywhere X phi ell) (z : EVec m)
    (hres : vecSq (residualGradient hexists z) ≤ eps ^ 2) :
    IsOptimizationStationary X phi ell eps z := by
  refine ⟨selectedProx hexists z, selectedProx_spec hexists z, ?_⟩
  have hscale :
      vecSq (residualGradient hexists z) =
        (2 * ell) ^ 2 * vecSq (z - selectedProx hexists z) := by
    unfold residualGradient
    rw [NCCLowerBoundVerification.Upper.vecSq_smul]
  rw [hscale] at hres
  rw [vecSq_sub_comm]
  have hden : 0 < (2 * ell) ^ 2 := sq_pos_of_pos (by positivity)
  have hres' :
      vecSq (z - selectedProx hexists z) * (2 * ell) ^ 2 ≤ eps ^ 2 := by
    simpa only [mul_comm] using hres
  calc
    vecSq (z - selectedProx hexists z) ≤
        eps ^ 2 / (2 * ell) ^ 2 := (le_div_iff₀ hden).2 hres'
    _ = (eps / (2 * ell)) ^ 2 := by
      field_simp [ne_of_gt hell]

/--
Under weak convexity, any proximal witness is the selected proximal point;
therefore optimization stationarity forces the residual-gradient bound.
-/
theorem residualGradient_vecSq_le_of_optimizationStationary
    {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ} {ell eps : ℝ}
    (hell : 0 < ell) (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z : EVec m)
    (hos : IsOptimizationStationary X phi ell eps z) :
    vecSq (residualGradient hexists z) ≤ eps ^ 2 := by
  obtain ⟨u, hu, hmove⟩ := hos
  have hselected : selectedProx hexists z = u :=
    selectedProx_unique hell hweak hexists hu
  have hscale :
      vecSq (residualGradient hexists z) =
        (2 * ell) ^ 2 * vecSq (u - z) := by
    unfold residualGradient
    rw [hselected, NCCLowerBoundVerification.Upper.vecSq_smul,
      vecSq_sub_comm]
  rw [hscale]
  calc
    (2 * ell) ^ 2 * vecSq (u - z) ≤
        (2 * ell) ^ 2 * (eps / (2 * ell)) ^ 2 :=
      mul_le_mul_of_nonneg_left hmove (sq_nonneg (2 * ell))
    _ = eps ^ 2 := by
      field_simp [ne_of_gt hell]

/--
The manuscript's existential proximal stationarity predicate is exactly the
squared Euclidean Moreau-residual test.
-/
theorem optimizationStationary_iff_residualGradient_vecSq_le
    {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ} {ell eps : ℝ}
    (hell : 0 < ell) (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z : EVec m) :
    IsOptimizationStationary X phi ell eps z ↔
      vecSq (residualGradient hexists z) ≤ eps ^ 2 := by
  constructor
  · exact residualGradient_vecSq_le_of_optimizationStationary
      hell hweak hexists z
  · exact optimizationStationary_of_residualGradient_vecSq_le
      hell hexists z

/-- Unsquared Euclidean-norm form of the exact stationarity equivalence. -/
theorem optimizationStationary_iff_residualGradient_euclideanNorm_le
    {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ} {ell eps : ℝ}
    (hell : 0 < ell) (heps : 0 ≤ eps)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z : EVec m) :
    IsOptimizationStationary X phi ell eps z ↔
      euclideanNorm (residualGradient hexists z) ≤ eps := by
  rw [optimizationStationary_iff_residualGradient_vecSq_le
    hell hweak hexists z]
  exact (euclideanNorm_le_iff_vecSq_le heps).symm

/-! ## Unconstrained differentiable value functions -/

/--
For an unconstrained differentiable value function, proximal optimality says
that the Moreau residual is exactly the value gradient evaluated at the
selected proximal point.
-/
theorem residualGradient_eq_gradient_at_selectedProx
    {m : Nat} {phi : EVec m → ℝ} {ell : ℝ}
    (hexists : HasProxEverywhere (Set.univ : Set (EVec m)) phi ell)
    (z g : EVec m)
    (hphi : NCPLVerification.HasEVecFDerivAt phi
      (NCPLVerification.evecDot g) (selectedProx hexists z)) :
    residualGradient hexists z = g := by
  have heq := NCCLowerBoundVerification.proxPoint_gradient_equation
    (selectedProx_spec hexists z) hphi
  funext i
  have hi := congrFun heq i
  simp only [residualGradient, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    Pi.add_apply, Pi.zero_apply] at hi ⊢
  linarith

/-- Function-valued version of the proximal-gradient identity. -/
theorem residualGradient_eq_valueGradient_at_selectedProx
    {m : Nat} {phi : EVec m → ℝ} {grad : EVec m → EVec m} {ell : ℝ}
    (hexists : HasProxEverywhere (Set.univ : Set (EVec m)) phi ell)
    (hdiff : ∀ u, NCPLVerification.HasEVecFDerivAt phi
      (NCPLVerification.evecDot (grad u)) u) (z : EVec m) :
    residualGradient hexists z = grad (selectedProx hexists z) := by
  exact residualGradient_eq_gradient_at_selectedProx hexists z
    (grad (selectedProx hexists z)) (hdiff _)

/--
For an unconstrained differentiable value, optimization stationarity is also
exactly a bound on its gradient at the selected proximal point.
-/
theorem optimizationStationary_iff_valueGradientAtProx_vecSq_le
    {m : Nat} {phi : EVec m → ℝ} {grad : EVec m → EVec m}
    {ell eps : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell (Set.univ : Set (EVec m)) phi)
    (hexists : HasProxEverywhere (Set.univ : Set (EVec m)) phi ell)
    (hdiff : ∀ u, NCPLVerification.HasEVecFDerivAt phi
      (NCPLVerification.evecDot (grad u)) u) (z : EVec m) :
    IsOptimizationStationary Set.univ phi ell eps z ↔
      vecSq (grad (selectedProx hexists z)) ≤ eps ^ 2 := by
  rw [optimizationStationary_iff_residualGradient_vecSq_le
    hell hweak hexists z,
    residualGradient_eq_valueGradient_at_selectedProx hexists hdiff z]

end

end Simplified
end NCCLowerBound
