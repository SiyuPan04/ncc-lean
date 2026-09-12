import NCCLowerBoundVerification.Lower.TerminalConcrete
import NCCLowerBoundVerification.WeakConvexity

/-!
# A genuine Danskin theorem for the restricted lower-bound value

This file removes the externally supplied value-gradient field from the
terminal lower bound.  The maximizer over the compact dual ball is unique,
and its dependence on the primal point is continuous.  A finite-dimensional
Danskin argument then identifies the Fréchet derivative of the actual
`ValueOn` function.
-/

namespace NCCLowerBoundVerification

noncomputable section

open Set Filter Asymptotics

set_option maxHeartbeats 0

@[fun_prop] theorem continuous_Psi2 : Continuous Psi2 :=
  differentiable_Psi2.continuous

@[fun_prop] theorem continuous_Psi1Deriv : Continuous Psi1Deriv := by
  exact NCPLVerification.carmonPsiDeriv_lipschitz.continuous

@[fun_prop] theorem continuous_Psi2Deriv : Continuous Psi2Deriv := by
  unfold Psi2Deriv
  fun_prop

@[fun_prop] theorem continuous_pi2Deriv (P0 : ℝ) : Continuous (pi2Deriv P0) := by
  unfold pi2Deriv
  exact clipIntegrand_continuous _ _

@[fun_prop] theorem continuous_pi1Deriv (delta P0 : ℝ) :
    Continuous (pi1Deriv delta P0) := by
  unfold pi1Deriv
  exact (continuous_pi2Deriv P0).comp <| by fun_prop

@[fun_prop] theorem continuous_Sigma1Deriv (theta : ℝ) :
    Continuous (Sigma1Deriv theta) := by
  unfold Sigma1Deriv
  exact (leftHingeDeriv_contDiff 1 (1 + theta) (k := (0 : ℕ∞))).continuous

@[fun_prop] theorem continuous_Sigma2Deriv (tau : ℝ) :
    Continuous (Sigma2Deriv tau) := by
  unfold Sigma2Deriv
  exact (leftHingeDeriv_contDiff (-tau) 0 (k := (0 : ℕ∞))).continuous

@[fun_prop] theorem continuous_Sigma3Deriv (P0 P1 K : ℝ) :
    Continuous (Sigma3Deriv P0 P1 K) := by
  unfold Sigma3Deriv
  exact continuous_const.mul
    (rightHingeDeriv_contDiff (P0 ^ 2) (P1 ^ 2) (k := (0 : ℕ∞))).continuous

@[fun_prop] theorem continuous_deriv_Lambda2 (theta : ℝ) :
    Continuous (deriv (Lambda2 theta)) := by
  exact (Lambda2_contDiff (theta := theta) (k := (2 : ℕ∞))).continuous_deriv
    (by norm_num)

@[fun_prop] theorem continuous_Sigma1 (theta : ℝ) : Continuous (Sigma1 theta) :=
  (Sigma1_contDiff_one theta).continuous

@[fun_prop] theorem continuous_exitRelay (theta : ℝ) :
    Continuous (exitRelay theta) := by
  unfold exitRelay
  exact continuous_id.mul (Lambda2_continuous theta)

@[fun_prop] theorem continuous_exitRelayDeriv (theta : ℝ) :
    Continuous (exitRelayDeriv theta) := by
  unfold exitRelayDeriv
  exact (Lambda2_continuous theta).add
    (continuous_id.mul (continuous_deriv_Lambda2 theta))

@[fun_prop] theorem continuous_Lambda2 (theta : ℝ) :
    Continuous (Lambda2 theta) := Lambda2_continuous theta

@[fun_prop] theorem continuous_pi2 (P0 : ℝ) : Continuous (pi2 P0) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_pi2 P0 t).continuousAt

theorem continuous_serializeUnscaled {T n : Nat} :
    Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      serializeUnscaled p.1 p.2) := by
  have heq : (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      serializeUnscaled p.1 p.2) =
      (serializeUnscaledCLM (T := T) (n := n) :
        (UnscaledPrimal T × UnscaledDual T n) → SerializedSpace T n) := by
    funext p
    rfl
  rw [heq]
  exact (serializeUnscaledCLM (T := T) (n := n)).continuous

@[fun_prop] theorem continuous_serializedA_serialize {T n : Nat}
    (i : Fin (T - 1)) : Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      serializedA (serializeUnscaled p.1 p.2) i) := by
  exact (continuous_apply _).comp continuous_serializeUnscaled

@[fun_prop] theorem continuous_serializedB_serialize {T n : Nat}
    (i : Fin (T - 1)) : Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      serializedB (serializeUnscaled p.1 p.2) i) := by
  exact (continuous_apply _).comp continuous_serializeUnscaled

@[fun_prop] theorem continuous_serializedState_serialize {T n : Nat}
    (i : Fin (T - 1)) : Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      serializedState (serializeUnscaled p.1 p.2) i) := by
  exact (continuous_apply _).comp continuous_serializeUnscaled

@[fun_prop] theorem continuous_serializedDualBlock_serialize_apply {T n : Nat}
    (i : Fin (T - 1)) (k : Fin n) :
    Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      serializedDualBlock (serializeUnscaled p.1 p.2) i k) := by
  simp_rw [serializedDualBlock_serializeUnscaled]
  unfold dualBlock
  fun_prop

@[fun_prop] theorem continuous_serializedPulseSq_serialize {T n : Nat} :
    Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      serializedPulseSq (serializeUnscaled p.1 p.2)) := by
  unfold serializedPulseSq
  fun_prop

@[fun_prop] theorem continuous_serializedClippedNext_serialize {T n : Nat}
    (P : UnscaledParameters) (i : Fin (T - 1)) :
    Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      serializedClippedNext P (serializeUnscaled p.1 p.2) i) := by
  unfold serializedClippedNext
  exact (pi1_contDiff P.delta_pos P.P0_gt_one).continuous.comp
    (continuous_serializedState_serialize i)

@[fun_prop] theorem continuous_serializedClippedCurrent_serialize {T n : Nat}
    (P : UnscaledParameters) (i : Fin (T - 1)) :
    Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      serializedClippedCurrent P (serializeUnscaled p.1 p.2) i) := by
  unfold serializedClippedCurrent serializedCurrentState
  split
  · fun_prop
  · exact (pi1_contDiff P.delta_pos P.P0_gt_one).continuous.comp
      (continuous_serializedState_serialize _)

theorem continuous_unscaledObjective_uncurry {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) :
    Continuous (Function.uncurry (unscaledObjective (T := T) hn P)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x, y⟩
  exact (unscaledObjective_hasFDerivAt hn P x y).continuousAt

-- A first diagnostic: the displayed primal gradient is a continuous field.
theorem continuous_unscaledTrueGradX {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) :
    Continuous (Function.uncurry (unscaledTrueGradX (T := T) hn P)) := by
  apply continuous_pi
  intro j
  let i : Fin (T - 1) := ⟨j.val / 3, by omega⟩
  have hjmod : j.val % 3 < 3 := Nat.mod_lt _ (by omega)
  have hjdecomp : j.val = 3 * (j.val / 3) + j.val % 3 := by omega
  interval_cases hmod : j.val % 3
  · have hj : j = primalAIndex i := by
      apply Fin.ext
      simp [primalAIndex, i]
      omega
    rw [hj]
    change Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      primalA (unscaledTrueGradX hn P p.1 p.2) i)
    simp_rw [primalA_unscaledTrueGradX hn P]
    unfold serializedGradA entrancePulseDerivA innerGradA
    fun_prop
  · have hj : j = primalBIndex i := by
      apply Fin.ext
      simp [primalBIndex, i]
      omega
    rw [hj]
    change Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      primalB (unscaledTrueGradX hn P p.1 p.2) i)
    simp_rw [primalB_unscaledTrueGradX hn P]
    unfold serializedGradB innerGradB exitPulseDerivB
    fun_prop
  · have hj : j = primalStateIndex i := by
      apply Fin.ext
      simp [primalStateIndex, i]
      omega
    rw [hj]
    change Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      primalState (unscaledTrueGradX hn P p.1 p.2) i)
    simp_rw [primalState_unscaledTrueGradX hn P]
    unfold serializedGradState serializedNextStateContribution
      exitPulseDerivNext exitRelayDeriv
    split <;> dsimp only <;> fun_prop

/-! ## Strict dual concavity and the unique restricted maximizer -/

theorem innerChain_combo_gap {n : Nat} (hn : 0 < n) (C q r : ℝ)
    (u v : EVec n) (a b : ℝ) (hab : a + b = 1) :
    innerChain hn C q r (a • u + b • v) =
      a * innerChain hn C q r u + b * innerChain hn C q r v +
        (1 / 2 : ℝ) * a * b * regularizedPathQuad n (u - v) := by
  rw [innerChain, innerChain, innerChain,
    regularizedPathQuad_add_expansion,
    regularizedPathQuad_smul, regularizedPathQuad_smul,
    regularizedPathBilinear_smul_left,
    regularizedPathBilinear_smul_right,
    regularizedPathQuad_sub_expansion]
  unfold innerForcing
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hb : b = 1 - a := by linarith
  rw [hb]
  ring

def restrictedDualQuadratic {T n : Nat} (y : UnscaledDual T n) : ℝ :=
  ∑ i : Fin (T - 1), regularizedPathQuad n (dualBlock y i)

theorem restrictedDualQuadratic_lower {T n : Nat} (y : UnscaledDual T n) :
    pathRegularization n * vecSq y ≤ restrictedDualQuadratic y := by
  unfold restrictedDualQuadratic
  rw [vecSq_eq_sum_dualBlock, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ regularizedPathQuad_lower n (dualBlock y i)

theorem restrictedDualQuadratic_pos {T n : Nat} (hn : 0 < n)
    {y : UnscaledDual T n} (hy : y ≠ 0) :
    0 < restrictedDualQuadratic y := by
  have hreg : 0 < pathRegularization n := pathRegularization_pos hn
  have hsq : 0 < vecSq y := by
    exact vecSq_pos_of_ne_zero hy
  exact lt_of_lt_of_le (mul_pos hreg hsq) (restrictedDualQuadratic_lower y)

theorem unscaledObjective_dual_combo_gap {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T)
    (y z : UnscaledDual T n) (a b : ℝ) (hab : a + b = 1) :
    unscaledObjective hn P x (a • y + b • z) =
      a * unscaledObjective hn P x y + b * unscaledObjective hn P x z +
        (1 / 2 : ℝ) * a * b * restrictedDualQuadratic (y - z) := by
  rw [unscaledObjective_eq_outer_add_inner,
    unscaledObjective_eq_outer_add_inner,
    unscaledObjective_eq_outer_add_inner]
  have hblock : ∀ i : Fin (T - 1),
      dualBlock (a • y + b • z) i =
        a • dualBlock y i + b • dualBlock z i := by
    intro i
    funext k
    simp [dualBlock]
  simp_rw [hblock]
  simp_rw [innerChain_combo_gap hn (innerC hn)
    (primalA x _) (primalB x _) _ _ a b hab]
  unfold restrictedDualQuadratic
  have hsub : ∀ i : Fin (T - 1), dualBlock (y - z) i =
      dualBlock y i - dualBlock z i := by
    intro i
    funext k
    simp [dualBlock]
  simp_rw [hsub, Finset.sum_add_distrib, ← Finset.mul_sum]
  have houter :
      a * unscaledOuterValue hn P x + b * unscaledOuterValue hn P x =
        unscaledOuterValue hn P x := by
    rw [← add_mul, hab, one_mul]
  ring_nf at *
  nlinarith

theorem unscaledObjective_dual_strictConcaveOn {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) (D : ℝ) :
    StrictConcaveOn ℝ (diameterBall (n * (T - 1)) D)
      (unscaledObjective hn P x) := by
  refine ⟨unscaledDualDomain_convex T n D, ?_⟩
  intro y hy z hz hyz a b ha hb hab
  rw [unscaledObjective_dual_combo_gap hn P x y z a b hab]
  have hquad : 0 < restrictedDualQuadratic (y - z) :=
    restrictedDualQuadratic_pos hn (sub_ne_zero.mpr hyz)
  have hcoef : 0 < (1 / 2 : ℝ) * a * b := by positivity
  have hgap : 0 < (1 / 2 : ℝ) * a * b *
      restrictedDualQuadratic (y - z) := mul_pos hcoef hquad
  simpa only [smul_eq_mul] using lt_add_of_pos_right
    (a * unscaledObjective hn P x y + b * unscaledObjective hn P x z) hgap

def restrictedDualMaximizer {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (D : ℝ) (hD : 0 ≤ D)
    (x : UnscaledPrimal T) : UnscaledDual T n :=
  Classical.choose (unscaledObjective_maximum_attained hn P hD x)

theorem restrictedDualMaximizer_spec {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (D : ℝ) (hD : 0 ≤ D)
    (x : UnscaledPrimal T) :
    IsMaximizerOn (diameterBall (n * (T - 1)) D)
      (unscaledObjective hn P) x (restrictedDualMaximizer hn P D hD x) :=
  Classical.choose_spec (unscaledObjective_maximum_attained hn P hD x)

theorem restrictedDualMaximizer_unique {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (D : ℝ) (x : UnscaledPrimal T)
    {y z : UnscaledDual T n}
    (hy : IsMaximizerOn (diameterBall (n * (T - 1)) D)
      (unscaledObjective hn P) x y)
    (hz : IsMaximizerOn (diameterBall (n * (T - 1)) D)
      (unscaledObjective hn P) x z) : y = z := by
  exact (unscaledObjective_dual_strictConcaveOn hn P x D).eq_of_isMaxOn
    hy.2 hz.2 hy.1 hz.1

theorem MapClusterPt.pair_self {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {x : X} {y : Y} {u : X → Y}
    (h : MapClusterPt y (nhds x) u) :
    MapClusterPt (x, y) (nhds x) (fun z ↦ (z, u z)) := by
  rw [mapClusterPt_iff_frequently]
  intro s hs
  obtain ⟨sx, hsx, sy, hsy, hsub⟩ := mem_nhds_prod_iff.mp hs
  have hfreq : ∃ᶠ z in nhds x, u z ∈ sy := h.frequently hsy
  exact (hfreq.and_eventually hsx).mono fun z hz ↦ hsub ⟨hz.2, hz.1⟩

theorem continuous_restrictedDualMaximizer {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (D : ℝ) (hD : 0 ≤ D) :
    Continuous (restrictedDualMaximizer (T := T) hn P D hD) := by
  rw [continuous_iff_continuousAt]
  intro x
  let arg : UnscaledPrimal T → UnscaledDual T n :=
    restrictedDualMaximizer hn P D hD
  let Y : Set (UnscaledDual T n) := diameterBall (n * (T - 1)) D
  apply (unscaledDualDomain_compact T n D).tendsto_nhds_of_unique_mapClusterPt
    (Filter.Eventually.of_forall fun z ↦
      (restrictedDualMaximizer_spec hn P D hD z).1)
  intro y hy hcluster
  have hpair : MapClusterPt (x, y) (nhds x) (fun z ↦ (z, arg z)) :=
    MapClusterPt.pair_self hcluster
  have hymax : IsMaximizerOn Y (unscaledObjective hn P) x y := by
    refine ⟨hy, ?_⟩
    intro v hv
    let H : (UnscaledPrimal T × UnscaledDual T n) → ℝ := fun p ↦
      unscaledObjective hn P p.1 p.2 - unscaledObjective hn P p.1 v
    have hH : Continuous H := by
      unfold H
      exact continuous_unscaledObjective_uncurry hn P |>.sub
        (continuous_unscaledObjective_uncurry hn P |>.comp
          (continuous_fst.prodMk continuous_const))
    have hHcluster : MapClusterPt (H (x, y)) (nhds x)
        (H ∘ fun z ↦ (z, arg z)) :=
      hpair.continuousAt_comp hH.continuousAt
    have hnonneg : ∀ᶠ z in nhds x, (H ∘ fun w ↦ (w, arg w)) z ∈ Ici 0 := by
      apply Filter.Eventually.of_forall
      intro z
      change 0 ≤ unscaledObjective hn P z (arg z) -
        unscaledObjective hn P z v
      exact sub_nonneg.mpr
        ((restrictedDualMaximizer_spec hn P D hD z).2 v hv)
    have hlimnonneg : H (x, y) ∈ Ici (0 : ℝ) :=
      isClosed_Ici.mem_of_mapClusterPt hHcluster hnonneg
    exact sub_nonneg.mp hlimnonneg
  exact restrictedDualMaximizer_unique hn P D x hymax
    (restrictedDualMaximizer_spec hn P D hD x)

/-! ## Strict differentiability of the concrete joint objective -/

def evecDotL (d : Nat) : EVec d →L[ℝ] (EVec d →L[ℝ] ℝ) := by
  let L : EVec d →ₗ[ℝ] (EVec d →L[ℝ] ℝ) :=
    { toFun := NCPLVerification.evecDot
      map_add' := by
        intro g h
        apply ContinuousLinearMap.ext
        intro z
        change (∑ i : Fin d, (g i + h i) * z i) =
          (∑ i : Fin d, g i * z i) + ∑ i : Fin d, h i * z i
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      map_smul' := by
        intro c g
        apply ContinuousLinearMap.ext
        intro z
        change (∑ i : Fin d, (c * g i) * z i) =
          c * ∑ i : Fin d, g i * z i
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring }
  exact LinearMap.toContinuousLinearMap L

@[simp] theorem evecDotL_apply {d : Nat} (g : EVec d) :
    evecDotL d g = NCPLVerification.evecDot g := rfl

def concreteJointDerivative {T n : Nat} (hn : 0 < n)
    (p : UnscaledPrimal T × UnscaledDual T n) :
    (UnscaledPrimal T × UnscaledDual T n) →L[ℝ] ℝ :=
  (NCPLVerification.evecDot
      (serializedTrueGradient hn concreteUnscaledParameters
        (serializeUnscaled p.1 p.2))).comp
    (serializeUnscaledCLM (T := T) (n := n))

theorem continuous_concreteJointDerivative {T n : Nat} (hn : 0 < n) :
    Continuous (concreteJointDerivative (T := T) hn) := by
  let S := serializeUnscaledCLM (T := T) (n := n)
  have hgrad : Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      serializedTrueGradient hn concreteUnscaledParameters (S p)) :=
    (concreteSerializedTrueGradient_lipschitz (T := T) hn).continuous.comp
      S.continuous
  have hdot : Continuous (fun p : UnscaledPrimal T × UnscaledDual T n ↦
      NCPLVerification.evecDot
        (serializedTrueGradient hn concreteUnscaledParameters (S p))) :=
    (evecDotL ((T - 1) * (n + 3))).continuous.comp hgrad
  have hcomp : Continuous (fun L : SerializedSpace T n →L[ℝ] ℝ ↦
      L.comp S) := by
    exact ((ContinuousLinearMap.compL ℝ
      (UnscaledPrimal T × UnscaledDual T n) (SerializedSpace T n) ℝ).flip S).continuous
  exact hcomp.comp hdot

theorem concreteJointDerivative_hasFDerivAt {T n : Nat} (hn : 0 < n)
    (p : UnscaledPrimal T × UnscaledDual T n) :
    HasFDerivAt
      (Function.uncurry (unscaledObjective (T := T) hn
        concreteUnscaledParameters))
      (concreteJointDerivative hn p) p := by
  rcases p with ⟨x, y⟩
  exact unscaledObjective_hasFDerivAt hn concreteUnscaledParameters x y

theorem concreteJointObjective_hasStrictFDerivAt {T n : Nat} (hn : 0 < n)
    (p : UnscaledPrimal T × UnscaledDual T n) :
    HasStrictFDerivAt
      (Function.uncurry (unscaledObjective (T := T) hn
        concreteUnscaledParameters))
      (concreteJointDerivative hn p) p := by
  apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
  · exact Filter.Eventually.of_forall (concreteJointDerivative_hasFDerivAt hn)
  · exact (continuous_concreteJointDerivative hn).continuousAt

theorem concreteJointDerivative_apply_primal {T n : Nat} (hn : 0 < n)
    (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (h : UnscaledPrimal T) :
    concreteJointDerivative hn (x, y) (h, 0) =
      NCPLVerification.evecDot
        (unscaledTrueGradX hn concreteUnscaledParameters x y) h := by
  have hrep := (unscaledTrueGradient_representsJointGradient
    (T := T) hn concreteUnscaledParameters).2 x y h
      (0 : UnscaledDual T n)
  rw [(concreteJointDerivative_hasFDerivAt hn (x, y)).fderiv] at hrep
  simpa [NCPLVerification.evecDot_apply] using hrep

theorem isLittleO_squeeze_real {α E : Type*} [NormedAddCommGroup E]
    {l : Filter α} {lo mid hi : α → ℝ} {scale : α → E}
    (hlo : lo =o[l] scale) (hhi : hi =o[l] scale)
    (hsqueeze : ∀ᶠ z in l, lo z ≤ mid z ∧ mid z ≤ hi z) :
    mid =o[l] scale := by
  apply IsLittleO.of_bound
  intro c hc
  have hc2 : 0 < c / 2 := by positivity
  filter_upwards [hlo.bound hc2, hhi.bound hc2, hsqueeze] with z hloz hhiz hz
  rw [Real.norm_eq_abs] at hloz hhiz ⊢
  have habs : |mid z| ≤ |lo z| + |hi z| := by
    rw [abs_le]
    constructor
    · calc
        -(|lo z| + |hi z|) ≤ -|lo z| := by
          linarith [abs_nonneg (hi z)]
        _ ≤ lo z := neg_abs_le (lo z)
        _ ≤ mid z := hz.1
    · calc
        mid z ≤ hi z := hz.2
        _ ≤ |hi z| := le_abs_self (hi z)
        _ ≤ |lo z| + |hi z| := by
          linarith [abs_nonneg (lo z)]
  calc
    |mid z| ≤ |lo z| + |hi z| := habs
    _ ≤ (c / 2) * ‖scale z‖ + (c / 2) * ‖scale z‖ :=
      add_le_add hloz hhiz
    _ = c * ‖scale z‖ := by ring

/-! ## Restricted Danskin theorem for the concrete objective -/

def concreteRestrictedValueGradient {T n : Nat} (hn : 0 < n)
    (D : ℝ) (hD : 0 ≤ D) (x : UnscaledPrimal T) : UnscaledPrimal T :=
  unscaledTrueGradX hn concreteUnscaledParameters x
    (restrictedDualMaximizer hn concreteUnscaledParameters D hD x)

theorem hasEVecFDerivAt_concreteRestrictedValue {T n : Nat}
    (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D) (x : UnscaledPrimal T) :
    NCPLVerification.HasEVecFDerivAt
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) hn concreteUnscaledParameters))
      (NCPLVerification.evecDot
        (concreteRestrictedValueGradient hn D hD x)) x := by
  let arg : UnscaledPrimal T → UnscaledDual T n :=
    restrictedDualMaximizer hn concreteUnscaledParameters D hD
  let f : UnscaledPrimal T → UnscaledDual T n → ℝ :=
    unscaledObjective hn concreteUnscaledParameters
  let Y : Set (UnscaledDual T n) := diameterBall (n * (T - 1)) D
  let g : UnscaledPrimal T := unscaledTrueGradX hn
    concreteUnscaledParameters x (arg x)
  have harg : Continuous arg :=
    continuous_restrictedDualMaximizer hn concreteUnscaledParameters D hD
  have hspec (z : UnscaledPrimal T) : IsMaximizerOn Y f z (arg z) := by
    exact restrictedDualMaximizer_spec hn concreteUnscaledParameters D hD z
  have hvalue (z : UnscaledPrimal T) : ValueOn Y f z = f z (arg z) :=
    value_eq_of_isMaximizerOn (hspec z)
  have hlo :
      (fun z : UnscaledPrimal T ↦
        f z (arg x) - f x (arg x) -
          NCPLVerification.evecDot g (z - x)) =o[nhds x]
        (fun z : UnscaledPrimal T ↦ z - x) := by
    simpa [f, g] using
      (hasEVecFDerivAt_unscaledObjective_fixedDual hn
        concreteUnscaledParameters x (arg x)).isLittleO
  have hgraph : Continuous (fun z : UnscaledPrimal T ↦ (z, arg z)) :=
    continuous_id.prodMk harg
  have hanchor : Continuous (fun z : UnscaledPrimal T ↦ (x, arg z)) :=
    continuous_const.prodMk harg
  have hpairs : Continuous (fun z : UnscaledPrimal T ↦
      ((z, arg z), (x, arg z))) := hgraph.prodMk hanchor
  have hstrict :=
    (concreteJointObjective_hasStrictFDerivAt hn (x, arg x)).isLittleO
  have hcomposed := hstrict.comp_tendsto hpairs.continuousAt
  have hpairBigO :
      (fun z : UnscaledPrimal T ↦ (z, arg z) - (x, arg z)) =O[nhds x]
        (fun z : UnscaledPrimal T ↦ z - x) := by
    apply IsBigO.of_bound 1
    apply Filter.Eventually.of_forall
    intro z
    simp [Prod.norm_def]
  have hupperRaw := hcomposed.trans_isBigO hpairBigO
  have hhi :
      (fun z : UnscaledPrimal T ↦
        f z (arg z) - f x (arg z) -
          NCPLVerification.evecDot g (z - x)) =o[nhds x]
        (fun z : UnscaledPrimal T ↦ z - x) := by
    refine hupperRaw.congr_left ?_
    intro z
    change f z (arg z) - f x (arg z) -
        concreteJointDerivative hn (x, arg x)
          ((z, arg z) - (x, arg z)) =
      f z (arg z) - f x (arg z) -
        NCPLVerification.evecDot g (z - x)
    have hsub : (z, arg z) - (x, arg z) =
        (z - x, (0 : UnscaledDual T n)) := by
      ext <;> simp
    rw [hsub, concreteJointDerivative_apply_primal]
  unfold NCPLVerification.HasEVecFDerivAt
  apply HasFDerivAt.of_isLittleO
  apply isLittleO_squeeze_real hlo hhi
  apply Filter.Eventually.of_forall
  intro z
  rw [show ValueOn (diameterBall (n * (T - 1)) D)
      (unscaledObjective hn concreteUnscaledParameters) z = f z (arg z) by
        exact hvalue z]
  rw [show ValueOn (diameterBall (n * (T - 1)) D)
      (unscaledObjective hn concreteUnscaledParameters) x = f x (arg x) by
        exact hvalue x]
  change f z (arg x) - f x (arg x) -
      NCPLVerification.evecDot g (z - x) ≤
        f z (arg z) - f x (arg x) -
          NCPLVerification.evecDot
            (concreteRestrictedValueGradient hn D hD x) (z - x) ∧
      f z (arg z) - f x (arg x) -
          NCPLVerification.evecDot
            (concreteRestrictedValueGradient hn D hD x) (z - x) ≤
        f z (arg z) - f x (arg z) -
          NCPLVerification.evecDot g (z - x)
  have hzmax : f z (arg x) ≤ f z (arg z) :=
    (hspec z).2 (arg x) (hspec x).1
  have hxmax : f x (arg z) ≤ f x (arg x) :=
    (hspec x).2 (arg z) (hspec z).1
  have hgrad : concreteRestrictedValueGradient hn D hD x = g := rfl
  rw [hgrad]
  constructor <;> linarith

theorem concreteRestrictedValueGradient_spec {T n : Nat} (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) :
    ∀ u : UnscaledPrimal T,
      NCPLVerification.HasEVecFDerivAt
        (ValueOn (diameterBall (n * (T - 1)) D)
          (unscaledObjective (T := T) hn concreteUnscaledParameters))
        (NCPLVerification.evecDot
          (concreteRestrictedValueGradient hn D hD u)) u := by
  intro u
  exact hasEVecFDerivAt_concreteRestrictedValue hn hD u

/-! ## Terminal consequences with no differentiability hypothesis -/

theorem concrete_restrictedValue_not_OS_at_terminalC0_quarter_no_assumption
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (hsizeHierarchy :
      96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 ≤
        (D / 2) ^ 2)
    {ell0 : ℝ} (hell0 : 0 < ell0) {x : UnscaledPrimal T}
    (hxterminal : x (terminalPrimalIndex hT) = 0) :
    ¬ IsOptimizationStationary Set.univ
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters))
      ell0 (concreteTerminalC0 ell0 / 4) x := by
  exact concrete_restrictedValue_not_OS_at_terminalC0_quarter
    hT hn hD hsizeHierarchy
      (concreteRestrictedValueGradient (by omega : 0 < n) D hD)
      (concreteRestrictedValueGradient_spec (T := T)
        (by omega : 0 < n) hD)
      hell0 hxterminal

theorem concrete_paperScaledValue_not_optimizationStationary_no_assumption
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (hsizeHierarchy :
      96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 ≤
        (D / 2) ^ 2)
    {ell ell0 eps : ℝ} (hell : 0 < ell) (hell0 : 0 < ell0)
    (heps : 0 < eps) {x : UnscaledPrimal T}
    (hxterminal : x (terminalPrimalIndex hT) = 0) :
    let c0 := concreteTerminalC0 ell0
    let lambda := lowerScale ell ell0 eps c0
    let amp := lowerAmplitude ell ell0 lambda
    ¬ IsOptimizationStationary (scaledDomain lambda Set.univ)
      (ValueOn
        (scaledDomain lambda (diameterBall (n * (T - 1)) D))
        (scaledObjective lambda amp
          (unscaledObjective (T := T) (by omega : 0 < n)
            concreteUnscaledParameters))) ell eps x := by
  exact concrete_paperScaledValue_not_optimizationStationary
    hT hn hD hsizeHierarchy
      (concreteRestrictedValueGradient (by omega : 0 < n) D hD)
      (concreteRestrictedValueGradient_spec (T := T)
        (by omega : 0 < n) hD)
      hell hell0 heps hxterminal

end

end NCCLowerBoundVerification
