import NCCLowerBound.Simplified.RestrictedBall
import NCCLowerBoundVerification.Lower.RestrictedDanskin

/-!
# The inner relay on a finite dual ball

This file proves item (iv) of the inner-interface lemma for the current
symmetrically normalised relay.  Both primal pulse blocks and all dual relay
blocks are serialised as genuine Euclidean vectors, and the value below is
the literal `ValueOn` over `diameterBall` (or over `Set.univ`).

For a finite ball, compactness gives existence of a maximiser.  The exact
Jensen gap of `correctedH` gives uniqueness.  We then prove continuity of the
unique maximiser by the compact maximum theorem and apply the same
finite-dimensional Danskin squeeze used by the dependency project.  No
regularity of the value function is assumed.
-/

namespace NCCLowerBound
namespace Simplified
namespace InnerFiniteBall

noncomputable section

open scoped BigOperators
open Set Filter Asymptotics
open NCCLowerBoundVerification
open InnerRelay
open RestrictedBall

/-! ## Serialised pulse and inner objective -/

/-- The two primal pulse blocks, stored as `(a_i,b_i)` for every `i`. -/
abbrev Pulse (M : Nat) := NCCLowerBoundVerification.EVec (M * 2)

/-- All `M` relay blocks, stored consecutively. -/
abbrev Dual (M N : Nat) := RestrictedBall.FlatDual M N

def pulseA {M : Nat} (p : Pulse M) : Fin M → ℝ :=
  fun i ↦ p (finProdFinEquiv (i, ⟨0, by omega⟩))

def pulseB {M : Nat} (p : Pulse M) : Fin M → ℝ :=
  fun i ↦ p (finProdFinEquiv (i, ⟨1, by omega⟩))

/-- The literal serialised `f_inn`. -/
def innerObjective {M N : Nat} (hN : 0 < N) :
    Pulse M → Dual M N → ℝ :=
  fun p y ↦ innerComponent hN (pulseA p) (pulseB p)
    (unflattenBlocks y)

/-- The actual restricted inner value on a diameter-`D` ball. -/
def finiteValue {M N : Nat} (hN : 0 < N) (D : ℝ) : Pulse M → ℝ :=
  ValueOn (diameterBall (M * N) D) (innerObjective hN)

/-- The actual unrestricted inner value. -/
def unboundedValue {M N : Nat} (hN : 0 < N) : Pulse M → ℝ :=
  ValueOn Set.univ (innerObjective hN)

/-- The exact polynomial obtained after eliminating every relay block. -/
def explicitValue {M : Nat} (p : Pulse M) : ℝ :=
  ∑ i : Fin M,
    ((pulseA p i) ^ 2 - pulseA p i * pulseB p i + (pulseB p i) ^ 2)

theorem vecSq_pulse {M : Nat} (p : Pulse M) :
    vecSq p =
      ∑ i : Fin M, ((pulseA p i) ^ 2 + (pulseB p i) ^ 2) := by
  unfold vecSq NCPLVerification.vecSq pulseA pulseB
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp [Fin.sum_univ_two]

@[simp] theorem unflattenBlocks_add {M N : Nat} (y z : Dual M N) :
    unflattenBlocks (y + z) = unflattenBlocks y + unflattenBlocks z := by
  rfl

@[simp] theorem unflattenBlocks_sub {M N : Nat} (y z : Dual M N) :
    unflattenBlocks (y - z) = unflattenBlocks y - unflattenBlocks z := by
  rfl

@[simp] theorem unflattenBlocks_smul {M N : Nat} (c : ℝ) (y : Dual M N) :
    unflattenBlocks (c • y) = c • unflattenBlocks y := by
  rfl

/-! ## Smoothness of the joint polynomial -/

private theorem vecSq_comp_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : Nat} {w : E → InnerRelay.EVec N}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ vecSq (w x)) := by
  unfold vecSq NCPLVerification.vecSq
  apply ContDiff.sum
  intro i _
  exact ((contDiff_apply ℝ ℝ i).comp hw).pow 2

private theorem pathEnergy_comp_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : Nat} {w : E → InnerRelay.EVec N}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ pathEnergy N (w x)) := by
  cases N with
  | zero => simpa [pathEnergy] using (contDiff_const :
      ContDiff ℝ (⊤ : ℕ∞) (fun _ : E ↦ (0 : ℝ)))
  | succ n =>
      simp only [pathEnergy]
      apply ContDiff.sum
      intro i _
      exact (((contDiff_apply ℝ ℝ i.castSucc).comp hw).sub
        ((contDiff_apply ℝ ℝ i.succ).comp hw)).pow 2

private theorem correctedH_comp_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : Nat} (hN : 0 < N)
    {a b : E → ℝ} {w : E → InnerRelay.EVec N}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ correctedH hN (a x) (b x) (w x)) := by
  have hwfirst : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ w x (first hN)) :=
    (contDiff_apply ℝ ℝ (first hN)).comp hw
  have hwlast : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ w x (last hN)) :=
    (contDiff_apply ℝ ℝ (last hN)).comp hw
  have hforcing : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ endpointForcing hN (a x) (b x) (w x)) := by
    unfold endpointForcing
    exact (ha.mul hwfirst).sub (hb.mul hwlast)
  have hquad : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ regularizedPathQuad N (w x)) := by
    unfold regularizedPathQuad
    exact (contDiff_const.mul (vecSq_comp_contDiff hw)).add
      (pathEnergy_comp_contDiff hw)
  have hrelay : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ relayH hN (a x) (b x) (w x)) := by
    unfold relayH
    exact (contDiff_const.mul hquad).add (contDiff_const.mul hforcing)
  unfold correctedH
  exact hrelay.add (contDiff_const.mul ((ha.pow 2).add (hb.pow 2)))

/-- `f_inn` is jointly `C∞` in its serialised primal and dual variables. -/
theorem innerObjective_uncurry_contDiff {M N : Nat} (hN : 0 < N) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (innerObjective (M := M) hN)) := by
  unfold Function.uncurry innerObjective innerComponent
  apply ContDiff.sum
  intro i _
  apply correctedH_comp_contDiff hN
  · unfold pulseA
    fun_prop
  · unfold pulseB
    fun_prop
  · unfold unflattenBlocks
    fun_prop

theorem innerObjective_dual_continuous {M N : Nat} (hN : 0 < N)
    (p : Pulse M) : Continuous (innerObjective hN p) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (innerObjective hN p) := by
    unfold innerObjective innerComponent
    apply ContDiff.sum
    intro i _
    apply correctedH_comp_contDiff hN contDiff_const contDiff_const
    unfold unflattenBlocks
    fun_prop
  exact hcd.continuous

theorem innerObjective_primal_contDiff {M N : Nat} (hN : 0 < N)
    (y : Dual M N) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Pulse M ↦ innerObjective hN p y) := by
  unfold innerObjective innerComponent
  apply ContDiff.sum
  intro i _
  apply correctedH_comp_contDiff hN
  · unfold pulseA
    fun_prop
  · unfold pulseB
    fun_prop
  · exact contDiff_const

/-! ## Strict concavity and finite-ball maximisers -/

private theorem dual_regularized_sum_pos {M N : Nat} (hN : 0 < N)
    {y z : Dual M N} (hyz : y ≠ z) :
    0 < ∑ i : Fin M,
      regularizedPathQuad N (unflattenBlocks y i - unflattenBlocks z i) := by
  have hsquares :
      vecSq (y - z) = ∑ i : Fin M,
        vecSq (unflattenBlocks y i - unflattenBlocks z i) := by
    calc
      vecSq (y - z) =
          vecSq (flattenBlocks (unflattenBlocks (y - z))) := by
            rw [flattenBlocks_unflattenBlocks]
      _ = ∑ i : Fin M, vecSq (unflattenBlocks (y - z) i) :=
        vecSq_flattenBlocks (unflattenBlocks (y - z))
      _ = ∑ i : Fin M,
          vecSq (unflattenBlocks y i - unflattenBlocks z i) := by rfl
  have hsq : 0 < vecSq (y - z) :=
    vecSq_pos_of_ne_zero (sub_ne_zero.mpr hyz)
  have hreg : 0 < pathRegularization N := pathRegularization_pos hN
  have hlower : pathRegularization N * vecSq (y - z) ≤
      ∑ i : Fin M,
        regularizedPathQuad N (unflattenBlocks y i - unflattenBlocks z i) := by
    rw [hsquares, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦
      regularizedPathQuad_lower N
        (unflattenBlocks y i - unflattenBlocks z i)
  exact lt_of_lt_of_le (mul_pos hreg hsq) hlower

private theorem innerObjective_dual_combo_gap {M N : Nat} (hN : 0 < N)
    (p : Pulse M) (y z : Dual M N) (t : ℝ) :
    innerObjective hN p (t • y + (1 - t) • z) =
      t * innerObjective hN p y + (1 - t) * innerObjective hN p z +
        (1 / 2 : ℝ) * t * (1 - t) *
          ∑ i : Fin M,
            regularizedPathQuad N
              (unflattenBlocks y i - unflattenBlocks z i) := by
  unfold innerObjective innerComponent
  simp_rw [unflattenBlocks_add, unflattenBlocks_smul, Pi.add_apply,
    Pi.smul_apply, correctedH_jensen_identity]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- For every primal pulse, the serialised inner objective is strictly
concave on every diameter ball. -/
theorem innerObjective_dual_strictConcaveOn {M N : Nat} (hN : 0 < N)
    (p : Pulse M) (D : ℝ) :
    StrictConcaveOn ℝ (diameterBall (M * N) D) (innerObjective hN p) := by
  refine ⟨diameterBall_convex _ _, ?_⟩
  intro y _ z _ hyz t s ht hs hts
  have hs_eq : s = 1 - t := by linarith
  subst s
  rw [innerObjective_dual_combo_gap]
  have hsum := dual_regularized_sum_pos hN hyz
  have hcoef : 0 < (1 / 2 : ℝ) * t * (1 - t) := by positivity
  have hgap : 0 < (1 / 2 : ℝ) * t * (1 - t) *
      ∑ i : Fin M,
        regularizedPathQuad N
          (unflattenBlocks y i - unflattenBlocks z i) :=
    mul_pos hcoef hsum
  exact lt_add_of_pos_right _ hgap

private theorem diameterBall_compact (d : Nat) (D : ℝ) :
    IsCompact (diameterBall d D) := by
  apply Metric.isCompact_of_isClosed_isBounded (diameterBall_closed d D)
  rw [Metric.isBounded_iff_subset_closedBall
    (0 : NCCLowerBoundVerification.EVec d)]
  refine ⟨|D / 2|, ?_⟩
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg (D / 2))).2
  intro i
  have hi : (y i) ^ 2 ≤ vecSq y := by
    unfold vecSq NCPLVerification.vecSq
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (y j))
      (Finset.mem_univ i)
  have habsSq : |y i| ^ 2 ≤ |D / 2| ^ 2 := by
    simpa only [sq_abs] using hi.trans hy
  simpa only [Real.norm_eq_abs] using
    (sq_le_sq₀ (abs_nonneg (y i)) (abs_nonneg (D / 2))).mp habsSq

/-- The finite-ball maximum is genuinely attained. -/
theorem finite_maximizer_exists {M N : Nat} (hN : 0 < N)
    {D : ℝ} (hD : 0 ≤ D) (p : Pulse M) :
    ∃ y, IsMaximizerOn (diameterBall (M * N) D)
      (innerObjective hN) p y := by
  obtain ⟨y, hy, hmax⟩ := (diameterBall_compact (M * N) D).exists_isMaxOn
    (diameterBall_nonempty _ _ hD)
    (innerObjective_dual_continuous hN p).continuousOn
  exact ⟨y, hy, fun z hz ↦ hmax hz⟩

/-- Two finite-ball maximisers coincide. -/
theorem finite_maximizer_unique {M N : Nat} (hN : 0 < N)
    (D : ℝ) (p : Pulse M) {y z : Dual M N}
    (hy : IsMaximizerOn (diameterBall (M * N) D)
      (innerObjective hN) p y)
    (hz : IsMaximizerOn (diameterBall (M * N) D)
      (innerObjective hN) p z) : y = z := by
  exact (innerObjective_dual_strictConcaveOn hN p D).eq_of_isMaxOn
    hy.2 hz.2 hy.1 hz.1

/-- The chosen finite-ball maximiser. -/
def finiteMaximizer {M N : Nat} (hN : 0 < N) (D : ℝ) (hD : 0 ≤ D)
    (p : Pulse M) : Dual M N :=
  Classical.choose (finite_maximizer_exists hN hD p)

theorem finiteMaximizer_spec {M N : Nat} (hN : 0 < N)
    (D : ℝ) (hD : 0 ≤ D) (p : Pulse M) :
    IsMaximizerOn (diameterBall (M * N) D) (innerObjective hN) p
      (finiteMaximizer hN D hD p) :=
  Classical.choose_spec (finite_maximizer_exists hN hD p)

/-- The unique finite-ball maximiser depends continuously on the pulse. -/
theorem finiteMaximizer_continuous {M N : Nat} (hN : 0 < N)
    (D : ℝ) (hD : 0 ≤ D) :
    Continuous (finiteMaximizer (M := M) hN D hD) := by
  rw [continuous_iff_continuousAt]
  intro p
  let arg : Pulse M → Dual M N := finiteMaximizer hN D hD
  let Y : Set (Dual M N) := diameterBall (M * N) D
  apply (diameterBall_compact (M * N) D).tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun q ↦
      (finiteMaximizer_spec (M := M) (N := N) hN D hD q).1)
  intro y hy hcluster
  have hpair : MapClusterPt (p, y) (nhds p) (fun q ↦ (q, arg q)) :=
    NCCLowerBoundVerification.MapClusterPt.pair_self hcluster
  have hymax : IsMaximizerOn Y (innerObjective hN) p y := by
    refine ⟨hy, ?_⟩
    intro v hv
    let H : (Pulse M × Dual M N) → ℝ := fun q ↦
      innerObjective hN q.1 q.2 - innerObjective hN q.1 v
    have hH : Continuous H := by
      unfold H
      exact (innerObjective_uncurry_contDiff (M := M) (N := N) hN).continuous.sub
        ((innerObjective_primal_contDiff hN v).continuous.comp continuous_fst)
    have hHcluster : MapClusterPt (H (p, y)) (nhds p)
        (H ∘ fun q ↦ (q, arg q)) :=
      hpair.continuousAt_comp hH.continuousAt
    have hnonneg : ∀ᶠ q in nhds p,
        (H ∘ fun z ↦ (z, arg z)) q ∈ Ici 0 := by
      apply Filter.Eventually.of_forall
      intro q
      change 0 ≤ innerObjective hN q (arg q) - innerObjective hN q v
      exact sub_nonneg.mpr
        ((finiteMaximizer_spec (M := M) (N := N) hN D hD q).2 v hv)
    have hlimnonneg : H (p, y) ∈ Ici (0 : ℝ) :=
      isClosed_Ici.mem_of_mapClusterPt hHcluster hnonneg
    exact sub_nonneg.mp hlimnonneg
  exact finite_maximizer_unique hN D p hymax
    (finiteMaximizer_spec (M := M) (N := N) hN D hD p)

/-! ## A genuine Danskin derivative -/

/-- The derivative of the joint polynomial. -/
def jointDerivative {M N : Nat} (hN : 0 < N)
    (q : Pulse M × Dual M N) :
    (Pulse M × Dual M N) →L[ℝ] ℝ :=
  fderiv ℝ (Function.uncurry (innerObjective hN)) q

theorem innerObjective_hasStrictFDerivAt {M N : Nat} (hN : 0 < N)
    (q : Pulse M × Dual M N) :
    HasStrictFDerivAt (Function.uncurry (innerObjective hN))
      (jointDerivative hN q) q := by
  exact (innerObjective_uncurry_contDiff (M := M) (N := N) hN).hasStrictFDerivAt
    (by simp)

def primalInclusion (M N : Nat) :
    Pulse M →L[ℝ] (Pulse M × Dual M N) :=
  (ContinuousLinearMap.id ℝ (Pulse M)).prod 0

/-- The primal derivative predicted by Danskin: restrict the joint derivative
at the unique maximiser to primal directions. -/
def finiteValueDerivative {M N : Nat} (hN : 0 < N)
    (D : ℝ) (hD : 0 ≤ D) (p : Pulse M) : Pulse M →L[ℝ] ℝ :=
  (jointDerivative hN (p, finiteMaximizer hN D hD p)).comp
    (primalInclusion M N)

/-- Danskin's theorem for the actual finite-ball `ValueOn`. -/
theorem finiteValue_hasFDerivAt {M N : Nat} (hN : 0 < N)
    {D : ℝ} (hD : 0 ≤ D) (p : Pulse M) :
    HasFDerivAt (finiteValue hN D) (finiteValueDerivative hN D hD p) p := by
  let arg : Pulse M → Dual M N := finiteMaximizer hN D hD
  let f : Pulse M → Dual M N → ℝ := innerObjective hN
  let Y : Set (Dual M N) := diameterBall (M * N) D
  let L : Pulse M →L[ℝ] ℝ := finiteValueDerivative hN D hD p
  have harg : Continuous arg := finiteMaximizer_continuous hN D hD
  have hspec (q : Pulse M) : IsMaximizerOn Y f q (arg q) := by
    exact finiteMaximizer_spec hN D hD q
  have hvalue (q : Pulse M) : ValueOn Y f q = f q (arg q) :=
    value_eq_of_isMaximizerOn (hspec q)
  have hfixedMap : HasFDerivAt (fun q : Pulse M ↦ (q, arg p))
      (primalInclusion M N) p := by
    exact (hasFDerivAt_id (𝕜 := ℝ) p).prodMk
      (hasFDerivAt_const (x := p) (arg p))
  have hfixed : HasFDerivAt (fun q : Pulse M ↦ f q (arg p)) L p := by
    change HasFDerivAt
      (Function.uncurry (innerObjective hN) ∘ fun q : Pulse M ↦ (q, arg p))
      L p
    simpa [L, finiteValueDerivative, arg] using
      (innerObjective_hasStrictFDerivAt hN (p, arg p)).hasFDerivAt.comp p
        hfixedMap
  have hlo :
      (fun q : Pulse M ↦ f q (arg p) - f p (arg p) - L (q - p))
        =o[nhds p] (fun q : Pulse M ↦ q - p) :=
    hfixed.isLittleO
  have hgraph : Continuous (fun q : Pulse M ↦ (q, arg q)) :=
    continuous_id.prodMk harg
  have hanchor : Continuous (fun q : Pulse M ↦ (p, arg q)) :=
    continuous_const.prodMk harg
  have hpairs : Continuous (fun q : Pulse M ↦
      ((q, arg q), (p, arg q))) := hgraph.prodMk hanchor
  have hstrict :=
    (innerObjective_hasStrictFDerivAt hN (p, arg p)).isLittleO
  have hcomposed := hstrict.comp_tendsto hpairs.continuousAt
  have hpairBigO :
      (fun q : Pulse M ↦ (q, arg q) - (p, arg q)) =O[nhds p]
        (fun q : Pulse M ↦ q - p) := by
    apply IsBigO.of_bound 1
    apply Filter.Eventually.of_forall
    intro q
    simp [Prod.norm_def]
  have hupperRaw := hcomposed.trans_isBigO hpairBigO
  have hhi :
      (fun q : Pulse M ↦ f q (arg q) - f p (arg q) - L (q - p))
        =o[nhds p] (fun q : Pulse M ↦ q - p) := by
    refine hupperRaw.congr_left ?_
    intro q
    change f q (arg q) - f p (arg q) -
        jointDerivative hN (p, arg p)
          ((q, arg q) - (p, arg q)) =
      f q (arg q) - f p (arg q) - L (q - p)
    have hsub : (q, arg q) - (p, arg q) =
        (q - p, (0 : Dual M N)) := by
      ext <;> simp
    rw [hsub]
    rfl
  unfold finiteValue
  apply HasFDerivAt.of_isLittleO
  apply NCCLowerBoundVerification.isLittleO_squeeze_real hlo hhi
  apply Filter.Eventually.of_forall
  intro q
  rw [show ValueOn (diameterBall (M * N) D) (innerObjective hN) q =
      f q (arg q) by exact hvalue q]
  rw [show ValueOn (diameterBall (M * N) D) (innerObjective hN) p =
      f p (arg p) by exact hvalue p]
  change f q (arg p) - f p (arg p) - L (q - p) ≤
      f q (arg q) - f p (arg p) - L (q - p) ∧
    f q (arg q) - f p (arg p) - L (q - p) ≤
      f q (arg q) - f p (arg q) - L (q - p)
  have hqmax : f q (arg p) ≤ f q (arg q) :=
    (hspec q).2 (arg p) (hspec p).1
  have hpmax : f p (arg q) ≤ f p (arg p) :=
    (hspec p).2 (arg q) (hspec q).1
  constructor <;> linarith

theorem finiteValue_differentiable {M N : Nat} (hN : 0 < N)
    {D : ℝ} (hD : 0 ≤ D) : Differentiable ℝ (finiteValue (M := M) hN D) := by
  intro p
  exact (finiteValue_hasFDerivAt hN hD p).differentiableAt

theorem finiteValue_fderiv {M N : Nat} (hN : 0 < N)
    {D : ℝ} (hD : 0 ≤ D) (p : Pulse M) :
    fderiv ℝ (finiteValue hN D) p = finiteValueDerivative hN D hD p :=
  (finiteValue_hasFDerivAt hN hD p).fderiv

/-! ## Radial derivative -/

/-- The part of the inner objective which is linear in the primal pulse. -/
def radialLinear {M N : Nat} (hN : 0 < N)
    (p : Pulse M) (y : Dual M N) : ℝ :=
  ∑ i : Fin M, relayScale hN *
    endpointForcing hN (pulseA p i) (pulseB p i) (unflattenBlocks y i)

def dualEnergy {M N : Nat} (y : Dual M N) : ℝ :=
  ∑ i : Fin M, regularizedPathQuad N (unflattenBlocks y i)

theorem innerObjective_decomposition {M N : Nat} (hN : 0 < N)
    (p : Pulse M) (y : Dual M N) :
    innerObjective hN p y =
      -(1 / 2 : ℝ) * dualEnergy y + radialLinear hN p y +
        (2 - rho hN) / 2 * vecSq p := by
  unfold innerObjective innerComponent correctedH
  rw [Finset.sum_add_distrib]
  have hcorr :
      (∑ i : Fin M,
        (2 - rho hN) / 2 * ((pulseA p i) ^ 2 + (pulseB p i) ^ 2)) =
        (2 - rho hN) / 2 *
          ∑ i : Fin M, ((pulseA p i) ^ 2 + (pulseB p i) ^ 2) := by
    rw [Finset.mul_sum]
  rw [hcorr, ← vecSq_pulse]
  unfold relayH radialLinear dualEnergy
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

@[simp] theorem radialLinear_zero {M N : Nat} (hN : 0 < N)
    (p : Pulse M) : radialLinear hN p (0 : Dual M N) = 0 := by
  unfold radialLinear endpointForcing unflattenBlocks
  simp

@[simp] theorem dualEnergy_zero (M N : Nat) :
    dualEnergy (0 : Dual M N) = 0 := by
  cases N with
  | zero => simp [dualEnergy, unflattenBlocks, regularizedPathQuad,
      vecSq, NCPLVerification.vecSq, pathEnergy]
  | succ n => simp [dualEnergy, unflattenBlocks, regularizedPathQuad,
      vecSq, NCPLVerification.vecSq, pathEnergy]

theorem dualEnergy_nonneg {M N : Nat} (y : Dual M N) :
    0 ≤ dualEnergy y := by
  unfold dualEnergy
  exact Finset.sum_nonneg fun i _ ↦ regularizedPathQuad_nonneg N _

theorem radialLinear_smul {M N : Nat} (hN : 0 < N)
    (c : ℝ) (p : Pulse M) (y : Dual M N) :
    radialLinear hN (c • p) y = c * radialLinear hN p y := by
  unfold radialLinear endpointForcing pulseA pulseB
  simp_rw [Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem vecSq_smul (d : Nat) (c : ℝ)
    (p : NCCLowerBoundVerification.EVec d) :
    vecSq (c • p) = c ^ 2 * vecSq p := by
  unfold vecSq NCPLVerification.vecSq
  change (∑ i : Fin d, (c * p i) ^ 2) = c ^ 2 * ∑ i : Fin d, p i ^ 2
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem innerObjective_smul_pulse {M N : Nat} (hN : 0 < N)
    (c : ℝ) (p : Pulse M) (y : Dual M N) :
    innerObjective hN (c • p) y =
      -(1 / 2 : ℝ) * dualEnergy y + c * radialLinear hN p y +
        (2 - rho hN) / 2 * c ^ 2 * vecSq p := by
  rw [innerObjective_decomposition, radialLinear_smul, vecSq_smul]
  ring

/-- Evaluation of the Danskin derivative in the radial direction. -/
theorem finiteValueDerivative_apply_self {M N : Nat} (hN : 0 < N)
    {D : ℝ} (hD : 0 ≤ D) (p : Pulse M) :
    finiteValueDerivative hN D hD p p =
      radialLinear hN p (finiteMaximizer hN D hD p) +
        (2 - rho hN) * vecSq p := by
  let y : Dual M N := finiteMaximizer hN D hD p
  let L : Pulse M →L[ℝ] ℝ := finiteValueDerivative hN D hD p
  have hfixedMap : HasFDerivAt (fun q : Pulse M ↦ (q, y))
      (primalInclusion M N) p := by
    exact (hasFDerivAt_id (𝕜 := ℝ) p).prodMk
      (hasFDerivAt_const (x := p) y)
  have hsection : HasFDerivAt (fun q : Pulse M ↦ innerObjective hN q y) L p := by
    change HasFDerivAt
      (Function.uncurry (innerObjective hN) ∘ fun q : Pulse M ↦ (q, y)) L p
    simpa [L, y, finiteValueDerivative] using
      (innerObjective_hasStrictFDerivAt hN (p, y)).hasFDerivAt.comp p hfixedMap
  have hcurve : HasDerivAt
      (fun t : ℝ ↦ innerObjective hN (t • p) y) (L p) 1 := by
    simpa [Function.comp_def] using hsection.comp_hasDerivAt_of_eq
      1 ((hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).smul_const p) (by simp)
  have hrhs : HasDerivAt
      (fun t : ℝ ↦
        -(1 / 2 : ℝ) * dualEnergy y + t * radialLinear hN p y +
          (2 - rho hN) / 2 * t ^ 2 * vecSq p)
      (radialLinear hN p y + (2 - rho hN) * vecSq p) 1 := by
    have hc : HasDerivAt (fun _ : ℝ ↦ -(1 / 2 : ℝ) * dualEnergy y) 0 1 :=
      hasDerivAt_const (x := (1 : ℝ)) _
    have hl : HasDerivAt (fun t : ℝ ↦ t * radialLinear hN p y)
        (radialLinear hN p y) 1 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).mul_const
        (radialLinear hN p y)
    have hq : HasDerivAt
        (fun t : ℝ ↦ (2 - rho hN) / 2 * t ^ 2 * vecSq p)
        ((2 - rho hN) * vecSq p) 1 := by
      have hraw :=
        (((hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).pow 2).mul_const (vecSq p)).const_mul
          ((2 - rho hN) / 2)
      refine hraw.congr_of_eventuallyEq ?_ |>.congr_deriv ?_
      · apply Filter.Eventually.of_forall
        intro t
        dsimp
        ring
      · norm_num
        ring
    refine (hc.add hl |>.add hq).congr_of_eventuallyEq ?_ |>.congr_deriv ?_
    · apply Filter.Eventually.of_forall
      intro t
      dsimp
    · simp
  have hpoly : HasDerivAt
      (fun t : ℝ ↦ innerObjective hN (t • p) y)
      (radialLinear hN p y + (2 - rho hN) * vecSq p) 1 := by
    exact hrhs.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t ↦ innerObjective_smul_pulse hN t p y)
  exact hcurve.unique hpoly

/-- The affine part of the objective is nonnegative at the constrained
maximiser, because the dual origin is feasible. -/
theorem radialLinear_finiteMaximizer_nonneg {M N : Nat} (hN : 0 < N)
    {D : ℝ} (hD : 0 ≤ D) (p : Pulse M) :
    0 ≤ radialLinear hN p (finiteMaximizer hN D hD p) := by
  let y : Dual M N := finiteMaximizer hN D hD p
  have hmax : innerObjective hN p (0 : Dual M N) ≤ innerObjective hN p y :=
    (finiteMaximizer_spec hN D hD p).2 0
      (zero_mem_diameterBall (M * N) D hD)
  rw [innerObjective_decomposition hN p (0 : Dual M N),
    innerObjective_decomposition hN p y] at hmax
  simp only [dualEnergy_zero, radialLinear_zero, neg_mul] at hmax
  have henergy : 0 ≤ dualEnergy y := dualEnergy_nonneg y
  nlinarith

/-- Item (iv), finite-radius case, stated with the actual Fréchet derivative
of the actual restricted `ValueOn`. -/
theorem finiteValue_radial {M N : Nat} (hN10 : 10 ≤ N)
    {D : ℝ} (hD : 0 ≤ D) (p : Pulse M) :
    (2 / 5 : ℝ) * vecSq p ≤
      (fderiv ℝ (finiteValue (M := M) (by omega : 0 < N) D) p) p := by
  let hN : 0 < N := by omega
  rw [finiteValue_fderiv hN hD,
    finiteValueDerivative_apply_self hN hD]
  have hlin := radialLinear_finiteMaximizer_nonneg hN hD p
  have hcorr := (correction_bounds_unconditional hN10).1
  have hsq : 0 ≤ vecSq p := by
    unfold vecSq NCPLVerification.vecSq
    positivity
  nlinarith [mul_le_mul_of_nonneg_right hcorr hsq]

/-! ## The unbounded case -/

/-- The exact Green-kernel maximiser, serialised in the same coordinates as
the literal unbounded `ValueOn`. -/
def unboundedMaximizer {M N : Nat} (hN : 0 < N)
    (p : Pulse M) : Dual M N :=
  flattenBlocks (blockWStar hN (pulseA p) (pulseB p))

theorem innerObjective_at_unboundedMaximizer {M N : Nat} (hN10 : 10 ≤ N)
    (p : Pulse M) :
    innerObjective (by omega : 0 < N) p
        (unboundedMaximizer (by omega : 0 < N) p) = explicitValue p := by
  simpa [innerObjective, unboundedMaximizer, explicitValue] using
    innerComponent_blockWStar_value hN10 (pulseA p) (pulseB p)

theorem innerObjective_le_unboundedMaximizer {M N : Nat} (hN : 0 < N)
    (p : Pulse M) (y : Dual M N) :
    innerObjective hN p y ≤ innerObjective hN p (unboundedMaximizer hN p) := by
  simpa [innerObjective, unboundedMaximizer] using
    innerComponent_le_at_blockWStar hN (pulseA p) (pulseB p)
      (unflattenBlocks y)

theorem unboundedMaximizer_spec {M N : Nat} (hN : 0 < N)
    (p : Pulse M) :
    IsMaximizerOn Set.univ (innerObjective hN) p
      (unboundedMaximizer hN p) := by
  exact ⟨Set.mem_univ _, fun y _ ↦ innerObjective_le_unboundedMaximizer hN p y⟩

theorem unbounded_maximizer_exists {M N : Nat} (hN : 0 < N)
    (p : Pulse M) :
    ∃ y, IsMaximizerOn Set.univ (innerObjective hN) p y :=
  ⟨unboundedMaximizer hN p, unboundedMaximizer_spec hN p⟩

theorem innerObjective_dual_strictConcave {M N : Nat} (hN : 0 < N)
    (p : Pulse M) :
    StrictConcaveOn ℝ Set.univ (innerObjective hN p) := by
  refine ⟨convex_univ, ?_⟩
  intro y _ z _ hyz t s ht hs hts
  have hs_eq : s = 1 - t := by linarith
  subst s
  rw [innerObjective_dual_combo_gap]
  have hsum := dual_regularized_sum_pos hN hyz
  have hcoef : 0 < (1 / 2 : ℝ) * t * (1 - t) := by positivity
  exact lt_add_of_pos_right _ (mul_pos hcoef hsum)

theorem unbounded_maximizer_unique {M N : Nat} (hN : 0 < N)
    (p : Pulse M) {y z : Dual M N}
    (hy : IsMaximizerOn Set.univ (innerObjective hN) p y)
    (hz : IsMaximizerOn Set.univ (innerObjective hN) p z) : y = z := by
  exact (innerObjective_dual_strictConcave hN p).eq_of_isMaxOn
    hy.2 hz.2 hy.1 hz.1

/-- Exact contraction of the actual unbounded `ValueOn`. -/
theorem unboundedValue_eq_explicitValue {M N : Nat} (hN10 : 10 ≤ N)
    (p : Pulse M) :
    unboundedValue (M := M) (by omega : 0 < N) p = explicitValue p := by
  rw [show unboundedValue (M := M) (by omega : 0 < N) p =
      innerObjective (by omega : 0 < N) p
        (unboundedMaximizer (by omega : 0 < N) p) by
    exact value_eq_of_isMaximizerOn
      (unboundedMaximizer_spec (M := M) (by omega : 0 < N) p)]
  exact innerObjective_at_unboundedMaximizer hN10 p

theorem explicitValue_contDiff {M : Nat} :
    ContDiff ℝ (⊤ : ℕ∞) (explicitValue : Pulse M → ℝ) := by
  unfold explicitValue
  apply ContDiff.sum
  intro i _
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun p : Pulse M ↦ pulseA p i) := by
    unfold pulseA
    fun_prop
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun p : Pulse M ↦ pulseB p i) := by
    unfold pulseB
    fun_prop
  exact ((ha.pow 2).sub (ha.mul hb)).add (hb.pow 2)

theorem unboundedValue_differentiable {M N : Nat} (hN10 : 10 ≤ N) :
    Differentiable ℝ (unboundedValue (M := M) (by omega : 0 < N)) := by
  have heq : unboundedValue (M := M) (by omega : 0 < N) = explicitValue := by
    funext p
    exact unboundedValue_eq_explicitValue hN10 p
  rw [heq]
  exact explicitValue_contDiff.differentiable (by simp)

theorem explicitValue_smul {M : Nat} (c : ℝ) (p : Pulse M) :
    explicitValue (c • p) = c ^ 2 * explicitValue p := by
  unfold explicitValue pulseA pulseB
  simp_rw [Pi.smul_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem explicitValue_fderiv_apply_self {M : Nat} (p : Pulse M) :
    (fderiv ℝ explicitValue p) p = 2 * explicitValue p := by
  have hsection : HasFDerivAt explicitValue (fderiv ℝ explicitValue p) p :=
    (explicitValue_contDiff.differentiable (by simp) p).hasFDerivAt
  have hcurve : HasDerivAt (fun t : ℝ ↦ explicitValue (t • p))
      ((fderiv ℝ explicitValue p) p) 1 := by
    simpa [Function.comp_def] using hsection.comp_hasDerivAt_of_eq
      1 ((hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).smul_const p) (by simp)
  have hraw : HasDerivAt (fun t : ℝ ↦ t ^ 2 * explicitValue p)
      (2 * explicitValue p) 1 := by
    have h := ((hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).pow 2).mul_const
      (explicitValue p)
    refine h.congr_deriv ?_
    norm_num
  have hpoly : HasDerivAt (fun t : ℝ ↦ explicitValue (t • p))
      (2 * explicitValue p) 1 :=
    hraw.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t ↦ explicitValue_smul t p)
  exact hcurve.unique hpoly

theorem explicitValue_radial_lower {M : Nat} (p : Pulse M) :
    (2 / 5 : ℝ) * vecSq p ≤ 2 * explicitValue p := by
  rw [vecSq_pulse]
  unfold explicitValue
  have hsum0 : 0 ≤ ∑ i : Fin M,
      ((pulseA p i) ^ 2 + (pulseB p i) ^ 2) := by positivity
  have hlink : ∑ i : Fin M,
      ((pulseA p i) ^ 2 + (pulseB p i) ^ 2) ≤
      2 * ∑ i : Fin M,
        ((pulseA p i) ^ 2 - pulseA p i * pulseB p i + (pulseB p i) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ ↦ by
      nlinarith [sq_nonneg (pulseA p i - pulseB p i)]
  nlinarith

/-- Item (iv), `D = ∞`: the same radial inequality for the actual
unrestricted `ValueOn Set.univ`. -/
theorem unboundedValue_radial {M N : Nat} (hN10 : 10 ≤ N)
    (p : Pulse M) :
    (2 / 5 : ℝ) * vecSq p ≤
      (fderiv ℝ (unboundedValue (M := M) (by omega : 0 < N)) p) p := by
  have heq : unboundedValue (M := M) (by omega : 0 < N) = explicitValue := by
    funext q
    exact unboundedValue_eq_explicitValue hN10 q
  rw [heq, explicitValue_fderiv_apply_self]
  exact explicitValue_radial_lower p

end

end InnerFiniteBall
end Simplified
end NCCLowerBound
