import NCCLowerBoundVerification.Upper.Proximal
import NCCLowerBoundVerification.Upper.PerturbationBias
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Moreau envelope and its residual gradient

This module formalizes the Moreau part of TeX 1522--1576.  The only
existence input is `HasProxEverywhere`, saying that the proximal problem has
an actual minimizer at every anchor.  Weak convexity and `ell > 0` then give
uniqueness through `Upper.Proximal`.
-/

namespace NCCLowerBoundVerification
namespace Upper

noncomputable section

open Asymptotics

/-- Existence of an actual proximal minimizer at every anchor. -/
def HasProxEverywhere {m : Nat} (X : Set (EVec m))
    (phi : EVec m → ℝ) (ell : ℝ) : Prop :=
  ∀ z, ∃ u, IsProxPoint X phi ell z u

/-- A selected proximal map; its specification below is independent of choice. -/
def selectedProx {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ}
    {ell : ℝ} (hexists : HasProxEverywhere X phi ell) (z : EVec m) : EVec m :=
  Classical.choose (hexists z)

theorem selectedProx_spec {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ}
    (hexists : HasProxEverywhere X phi ell) (z : EVec m) :
    IsProxPoint X phi ell z (selectedProx hexists z) :=
  Classical.choose_spec (hexists z)

/-- The Moreau envelope with parameter `1 / (2 * ell)`. -/
def moreauEnvelope {m : Nat} {X : Set (EVec m)} (phi : EVec m → ℝ)
    (ell : ℝ) (hexists : HasProxEverywhere X phi ell) (z : EVec m) : ℝ :=
  proxObjective phi ell z (selectedProx hexists z)

/-- The vector represented by the Moreau derivative. -/
def residualGradient {m : Nat} {X : Set (EVec m)} {phi : EVec m → ℝ}
    {ell : ℝ} (hexists : HasProxEverywhere X phi ell) (z : EVec m) : EVec m :=
  (2 * ell) • (z - selectedProx hexists z)

/-- Explicit Euclidean dot product. -/
def eDot {m : Nat} (x y : EVec m) : ℝ :=
  ∑ i : Fin m, x i * y i

theorem eDot_comm {m : Nat} (x y : EVec m) : eDot x y = eDot y x := by
  unfold eDot
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem eDot_sub_left {m : Nat} (x y h : EVec m) :
    eDot (x - y) h = eDot x h - eDot y h := by
  unfold eDot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

theorem vecSq_add_expand {m : Nat} (x y : EVec m) :
    vecSq (x + y) = vecSq x + 2 * eDot x y + vecSq y := by
  unfold vecSq NCPLVerification.vecSq eDot
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

theorem vecSq_sub_expand' {m : Nat} (x y : EVec m) :
    vecSq (x - y) = vecSq x - 2 * eDot x y + vecSq y := by
  unfold vecSq NCPLVerification.vecSq eDot
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

theorem vecSq_anchor_add {m : Nat} (u z h : EVec m) :
    vecSq (u - (z + h)) =
      vecSq (u - z) - 2 * eDot (u - z) h + vecSq h := by
  rw [show u - (z + h) = (u - z) - h by abel]
  exact vecSq_sub_expand' _ _

theorem vecSq_four_point {m : Nat} (u v z w : EVec m) :
    vecSq (v - z) + vecSq (u - w) - vecSq (u - z) - vecSq (v - w) =
      2 * eDot (z - w) (u - v) := by
  unfold vecSq NCPLVerification.vecSq eDot
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

private theorem vecSq_nonneg' {m : Nat} (x : EVec m) : 0 ≤ vecSq x := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i)

theorem vecSq_smul {m : Nat} (c : ℝ) (x : EVec m) :
    vecSq (c • x) = c ^ 2 * vecSq x := by
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Weak convexity makes the selected prox map single-valued. -/
theorem selectedProx_unique {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) {z u : EVec m}
    (hu : IsProxPoint X phi ell z u) : selectedProx hexists z = u := by
  exact proxPoint_unique_of_weaklyConvexOn hell hweak
    (selectedProx_spec hexists z) hu

/-- The key weak-monotonicity inequality between two proximal points. -/
theorem prox_displacement_inequality {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z w : EVec m) :
    vecSq (selectedProx hexists z - selectedProx hexists w) ≤
      2 * eDot (z - w) (selectedProx hexists z - selectedProx hexists w) := by
  let u := selectedProx hexists z
  let v := selectedProx hexists w
  have hu := selectedProx_spec hexists z
  have hv := selectedProx_spec hexists w
  have hzu := proxPoint_strongMinimizer hell hweak hu v hv.1
  have hwv := proxPoint_strongMinimizer hell hweak hv u hu.1
  have hfour := vecSq_four_point u v z w
  unfold proxObjective at hzu hwv
  dsimp [u, v] at hzu hwv hfour ⊢
  rw [vecSq_sub_comm (selectedProx hexists w) (selectedProx hexists z)] at hzu
  nlinarith

/-- The proximal residual `z - prox z` is nonexpansive in squared Euclidean norm. -/
theorem proxResidual_nonexpansive {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z w : EVec m) :
    vecSq ((z - selectedProx hexists z) -
        (w - selectedProx hexists w)) ≤ vecSq (z - w) := by
  have hmono := prox_displacement_inequality hell hweak hexists z w
  have hid :
      (z - selectedProx hexists z) - (w - selectedProx hexists w) =
        (z - w) - (selectedProx hexists z - selectedProx hexists w) := by abel
  rw [hid, vecSq_sub_expand']
  linarith [vecSq_nonneg' (selectedProx hexists z - selectedProx hexists w)]

/-- Consequently the residual-gradient field is `2 * ell`-Lipschitz. -/
theorem residualGradient_lipschitz_sq {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z w : EVec m) :
    vecSq (residualGradient hexists z - residualGradient hexists w) ≤
      (2 * ell) ^ 2 * vecSq (z - w) := by
  have h := proxResidual_nonexpansive hell hweak hexists z w
  have heq : residualGradient hexists z - residualGradient hexists w =
      (2 * ell) • ((z - selectedProx hexists z) -
        (w - selectedProx hexists w)) := by
    unfold residualGradient
    module
  rw [heq]
  rw [vecSq_smul]
  exact mul_le_mul_of_nonneg_left h (sq_nonneg (2 * ell))

/-! ## Actual derivative of the envelope -/

/-- Continuous linear functional represented by the residual gradient. -/
def residualCLM {m : Nat} (g : EVec m) : EVec m →L[ℝ] ℝ := by
  letI : AddCommGroup (EVec m) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec m) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec m) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  exact LinearMap.toContinuousLinearMap
    ({ toFun := fun h : EVec m ↦ eDot g h
       map_add' := by
         intro x y
         unfold eDot
         rw [← Finset.sum_add_distrib]
         apply Finset.sum_congr rfl
         intro i _
         simp only [Pi.add_apply]
         ring
       map_smul' := by
         intro c x
         unfold eDot
         simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
         rw [Finset.mul_sum]
         apply Finset.sum_congr rfl
         intro i _
         ring } : EVec m →ₗ[ℝ] ℝ)

@[simp] theorem residualCLM_apply {m : Nat} (g h : EVec m) :
    residualCLM g h = eDot g h := rfl

/-- The direct two-sided-minimality remainder estimate. -/
theorem moreauEnvelope_remainder_abs_le {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z h : EVec m) :
    |moreauEnvelope phi ell hexists (z + h) - moreauEnvelope phi ell hexists z -
        residualCLM (residualGradient hexists z) h| ≤ ell * vecSq h := by
  let u := selectedProx hexists z
  let v := selectedProx hexists (z + h)
  have hu := selectedProx_spec hexists z
  have hv := selectedProx_spec hexists (z + h)
  have hupper := hv.2 u hu.1
  have hlower := proxPoint_strongMinimizer hell hweak hu v hv.1
  have hanchorU := vecSq_anchor_add u z h
  have hanchorV := vecSq_anchor_add v z h
  have hsquare := vecSq_nonneg' ((v - u) - (2 : ℝ) • h)
  have hsquareId :
      vecSq ((v - u) - (2 : ℝ) • h) =
        vecSq (v - u) - 4 * eDot (v - u) h + 4 * vecSq h := by
    unfold vecSq NCPLVerification.vecSq eDot
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hsquareId] at hsquare
  change proxObjective phi ell (z + h) v ≤
    proxObjective phi ell (z + h) u at hupper
  unfold proxObjective at hupper hlower
  unfold moreauEnvelope proxObjective
  rw [residualCLM_apply]
  unfold residualGradient
  have hdot : eDot ((2 * ell) • (z - u)) h =
      2 * ell * eDot (z - u) h := by
    unfold eDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hsign : eDot (z - u) h = -eDot (u - z) h := by
    rw [eDot_sub_left, eDot_sub_left]
    ring
  have hdiff : eDot (v - u) h =
      eDot (v - z) h - eDot (u - z) h := by
    rw [eDot_sub_left, eDot_sub_left, eDot_sub_left]
    ring
  rw [hdot]
  dsimp [u, v] at hanchorU hanchorV hupper hlower hsquare hsign hdiff ⊢
  rw [hanchorU] at hupper
  rw [abs_le]
  constructor <;> nlinarith [hanchorV, hsign, hdiff, vecSq_nonneg' h]

/-- Coordinate squared norm is controlled by the ambient finite-product norm. -/
theorem vecSq_le_card_mul_norm_sq {m : Nat} (h : EVec m) :
    vecSq h ≤ (m : ℝ) * ‖h‖ ^ 2 := by
  unfold vecSq NCPLVerification.vecSq
  calc
    (∑ i : Fin m, h i ^ 2) ≤ ∑ _i : Fin m, ‖h‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi : |h i| ≤ ‖h‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm h i
      simpa [sq_abs] using
        (sq_le_sq₀ (abs_nonneg (h i)) (norm_nonneg h)).2 hi
    _ = (m : ℝ) * ‖h‖ ^ 2 := by simp

/--
The envelope has the actual Fréchet derivative represented by the residual.
This is proved from the quadratic remainder estimate, not assumed as a
Danskin or smoothness hypothesis.
-/
theorem hasFDerivAt_moreauEnvelope {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z : EVec m) :
    HasFDerivAt (moreauEnvelope phi ell hexists)
      (residualCLM (residualGradient hexists z)) z := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have hbigO :
      (fun h : EVec m ↦
        moreauEnvelope phi ell hexists (z + h) -
          moreauEnvelope phi ell hexists z -
          residualCLM (residualGradient hexists z) h) =O[nhds 0]
        (fun h : EVec m ↦ ‖h‖ ^ 2) := by
    rw [isBigO_iff]
    refine ⟨ell * (m : ℝ), ?_⟩
    filter_upwards [] with h
    have hrem := moreauEnvelope_remainder_abs_le hell hweak hexists z h
    have hsq := vecSq_le_card_mul_norm_sq h
    rw [Real.norm_eq_abs]
    calc
      |moreauEnvelope phi ell hexists (z + h) -
          moreauEnvelope phi ell hexists z -
          residualCLM (residualGradient hexists z) h| ≤
          ell * vecSq h := hrem
      _ ≤ ell * ((m : ℝ) * ‖h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hell.le
      _ = (ell * (m : ℝ)) * |‖h‖ ^ 2| := by
        rw [abs_of_nonneg (sq_nonneg ‖h‖)]
        ring
  exact hbigO.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)

theorem fderiv_moreauEnvelope_eq {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z : EVec m) :
    fderiv ℝ (moreauEnvelope phi ell hexists) z =
      residualCLM (residualGradient hexists z) :=
  (hasFDerivAt_moreauEnvelope hell hweak hexists z).fderiv

/-- In particular, the Moreau envelope is differentiable everywhere. -/
theorem differentiable_moreauEnvelope {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) :
    Differentiable ℝ (moreauEnvelope phi ell hexists) := by
  intro z
  exact (hasFDerivAt_moreauEnvelope hell hweak hexists z).differentiableAt

/-! ## Interface with the perturbation-bias module -/

/-- A uniform value bias transfers directly to the two residual gradients. -/
theorem residualGradient_perturbation_vecSq_le {m : Nat}
    {X : Set (EVec m)} {phi phiR : EVec m → ℝ}
    {ell delta : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hweakR : IsWeaklyConvexOn ell X phiR)
    (hexists : HasProxEverywhere X phi ell)
    (hexistsR : HasProxEverywhere X phiR ell)
    (hbias : ∀ w, 0 ≤ phi w - phiR w ∧ phi w - phiR w ≤ delta)
    (z : EVec m) :
    vecSq (residualGradient hexists z - residualGradient hexistsR z) ≤
      4 * ell * delta := by
  let u := selectedProx hexists z
  let v := selectedProx hexistsR z
  have hu := selectedProx_spec hexists z
  have hv := selectedProx_spec hexistsR z
  have hphi := proxPoint_strongMinimizer_expanded hell hweak hu hv.1
  have hphiR := proxPoint_strongMinimizer_expanded hell hweakR hv hu.1
  have h := strongMinimizers_residualDifference_vecSq_le hell.le
    hbias hphi hphiR
  simpa [residualGradient, u, v] using h

/-- Specialized square of the TeX bound `D * sqrt (2 * ell * r)`. -/
theorem residualGradient_regularization_vecSq_le {m : Nat}
    {X : Set (EVec m)} {phi phiR : EVec m → ℝ}
    {ell r D : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hweakR : IsWeaklyConvexOn ell X phiR)
    (hexists : HasProxEverywhere X phi ell)
    (hexistsR : HasProxEverywhere X phiR ell)
    (hbias : ∀ w, 0 ≤ phi w - phiR w ∧
      phi w - phiR w ≤ r / 2 * D ^ 2) (z : EVec m) :
    vecSq (residualGradient hexists z - residualGradient hexistsR z) ≤
      2 * ell * r * D ^ 2 := by
  have h := residualGradient_perturbation_vecSq_le hell hweak hweakR
    hexists hexistsR hbias z
  calc
    _ ≤ 4 * ell * (r / 2 * D ^ 2) := h
    _ = 2 * ell * r * D ^ 2 := by ring

end

end Upper
end NCCLowerBoundVerification
