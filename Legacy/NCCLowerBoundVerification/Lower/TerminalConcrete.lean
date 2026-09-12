import NCCLowerBoundVerification.Lower.UnscaledMaximizer
import NCCLowerBoundVerification.Lower.TerminalGradientAlgebra
import NCCLowerBoundVerification.Lower.TerminalOS
import NCCLowerBoundVerification.Lower.UnscaledRegularity

/-!
# Concrete terminal certificate for the unscaled hard instance

This file connects the literal dual maximizer and the actual Frechet
derivative of `unscaledObjective` to the terminal pulse algebra.  In
particular, the value-gradient used here is obtained from the genuine
`ValueOn` objective; it is not an independently postulated vector field.
-/

namespace NCCLowerBoundVerification

noncomputable section

open Set

/-! ## The explicit unconstrained value and its envelope derivative -/

/-- The literal objective evaluated at its verified blockwise maximizer. -/
def unscaledExplicitValue {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) : ℝ :=
  unscaledObjective hn P x (unscaledInnerMaximizer hn x)

theorem unscaledValue_univ_eq_explicit {T n : Nat} (hn : 10 ≤ n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) :
    ValueOn Set.univ (unscaledObjective (by omega : 0 < n) P) x =
      unscaledExplicitValue (by omega : 0 < n) P x := by
  exact unscaledValue_univ_eq_at_innerMaximizer hn P x

/-- The blockwise Green-matrix maximizer is a genuine linear map of the
outer pulse vector. -/
def unscaledInnerMaximizerLinear {T n : Nat} (hn : 0 < n) :
    UnscaledPrimal T →ₗ[ℝ] UnscaledDual T n where
  toFun := unscaledInnerMaximizer hn
  map_add' := by
    intro x z
    funext j
    unfold unscaledInnerMaximizer innerMaximizer primalA primalB
    simp only [Pi.add_apply]
    ring
  map_smul' := by
    intro c x
    funext j
    unfold unscaledInnerMaximizer innerMaximizer primalA primalB
    simp only [Pi.smul_apply, smul_eq_mul]
    simp only [RingHom.id_apply]
    ring

def unscaledInnerMaximizerCLM {T n : Nat} (hn : 0 < n) :
    UnscaledPrimal T →L[ℝ] UnscaledDual T n :=
  LinearMap.toContinuousLinearMap (unscaledInnerMaximizerLinear hn)

@[simp] theorem unscaledInnerMaximizerCLM_apply {T n : Nat} (hn : 0 < n)
    (x : UnscaledPrimal T) :
    unscaledInnerMaximizerCLM hn x = unscaledInnerMaximizer hn x := by
  rfl

/-- The graph `x ↦ (x,y⋆(x))` as a continuous linear map. -/
def unscaledMaximizerGraphCLM {T n : Nat} (hn : 0 < n) :
    UnscaledPrimal T →L[ℝ] (UnscaledPrimal T × UnscaledDual T n) :=
  (ContinuousLinearMap.id ℝ (UnscaledPrimal T)).prod
    (unscaledInnerMaximizerCLM hn)

@[simp] theorem unscaledMaximizerGraphCLM_apply {T n : Nat} (hn : 0 < n)
    (x : UnscaledPrimal T) :
    unscaledMaximizerGraphCLM hn x = (x, unscaledInnerMaximizer hn x) := by
  simp [unscaledMaximizerGraphCLM]

/-- At the literal maximizer the derivative in every dual direction is
zero.  This is Fermat's theorem applied to the verified global maximum. -/
theorem unscaledObjective_dual_fderiv_zero_at_maximizer {T n : Nat}
    (hn : 10 ≤ n) (P : UnscaledParameters) (x : UnscaledPrimal T) :
    ((NCPLVerification.evecDot
        (serializedTrueGradient (by omega : 0 < n) P
          (serializeUnscaled x
            (unscaledInnerMaximizer (by omega : 0 < n) x)))).comp
      ((serializeUnscaledCLM (T := T) (n := n)).comp
        (ContinuousLinearMap.inr ℝ (UnscaledPrimal T)
          (UnscaledDual T n)))) = 0 := by
  let ystar := unscaledInnerMaximizer (by omega : 0 < n) x
  have hjoint := unscaledObjective_hasFDerivAt
    (T := T) (by omega : 0 < n) P x ystar
  have hp : HasFDerivAt (𝕜 := ℝ)
      (fun y : UnscaledDual T n ↦ (x, y))
      (ContinuousLinearMap.inr ℝ (UnscaledPrimal T) (UnscaledDual T n))
      ystar :=
    (hasFDerivAt_const (𝕜 := ℝ) (x := ystar) x).prodMk
      (hasFDerivAt_id (𝕜 := ℝ) ystar)
  have hderiv := hjoint.comp ystar hp
  have hmax : IsMaxOn (fun y : UnscaledDual T n ↦
      unscaledObjective (by omega : 0 < n) P x y) Set.univ ystar := by
    have hm := unscaledInnerMaximizer_isMaximizer_univ hn P x
    intro y hy
    exact hm.2 y hy
  have hlocal : IsLocalMax (fun y : UnscaledDual T n ↦
      unscaledObjective (by omega : 0 < n) P x y) ystar :=
    hmax.isLocalMax (isOpen_univ.mem_nhds (Set.mem_univ ystar))
  have hzero := hlocal.hasFDerivAt_eq_zero hderiv
  simpa [ystar, ContinuousLinearMap.comp_assoc] using hzero

/-- Envelope theorem for this concrete problem: differentiating through the
linear Green-matrix maximizer leaves precisely the true primal partial
gradient, because the true dual derivative vanishes at the maximizer. -/
theorem hasEVecFDerivAt_unscaledExplicitValue {T n : Nat} (hn : 10 ≤ n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) :
    NCPLVerification.HasEVecFDerivAt
      (unscaledExplicitValue (T := T) (by omega : 0 < n) P)
      (NCPLVerification.evecDot
        (unscaledTrueGradX (T := T) (by omega : 0 < n) P x
          (unscaledInnerMaximizer (by omega : 0 < n) x))) x := by
  let hnpos : 0 < n := by omega
  let ystar := unscaledInnerMaximizer hnpos x
  let g := serializedTrueGradient hnpos P (serializeUnscaled x ystar)
  let L := (NCPLVerification.evecDot g).comp
    (serializeUnscaledCLM (T := T) (n := n))
  let Lin := ContinuousLinearMap.inl ℝ (UnscaledPrimal T) (UnscaledDual T n)
  let M := unscaledInnerMaximizerCLM (T := T) hnpos
  let graph := unscaledMaximizerGraphCLM (T := T) hnpos
  have hjoint : HasFDerivAt
      (Function.uncurry (unscaledObjective (T := T) hnpos P)) L (x, ystar) := by
    simpa [L, g, ystar] using
      unscaledObjective_hasFDerivAt (T := T) hnpos P x ystar
  have hgraph : HasFDerivAt (fun z : UnscaledPrimal T ↦ (z,
      unscaledInnerMaximizer hnpos z)) graph x := by
    have hg : HasFDerivAt (fun z : UnscaledPrimal T ↦
        (z, unscaledInnerMaximizerCLM (T := T) hnpos z))
        ((ContinuousLinearMap.id ℝ (UnscaledPrimal T)).prod
          (unscaledInnerMaximizerCLM (T := T) hnpos)) x :=
      (hasFDerivAt_id x).prodMk
        (unscaledInnerMaximizerCLM (T := T) hnpos).hasFDerivAt
    simpa [graph, unscaledMaximizerGraphCLM] using hg
  have hcomp := hjoint.comp x hgraph
  have hfun : (Function.uncurry (unscaledObjective (T := T) hnpos P)) ∘
        (fun z : UnscaledPrimal T ↦ (z, unscaledInnerMaximizer hnpos z)) =
      unscaledExplicitValue hnpos P := by
    rfl
  rw [hfun] at hcomp
  have hdual : L.comp
      (ContinuousLinearMap.inr ℝ (UnscaledPrimal T) (UnscaledDual T n)) = 0 := by
    simpa [L, g, ystar, ContinuousLinearMap.comp_assoc] using
      unscaledObjective_dual_fderiv_zero_at_maximizer hn P x
  have hderivEq : L.comp graph = L.comp Lin := by
    ext h
    simp only [ContinuousLinearMap.comp_apply]
    rw [show graph h = (h, M h) by
      simp [graph, M, unscaledMaximizerGraphCLM],
      show Lin h = (h, 0) by simp [Lin]]
    have hsplit : (h, M h) = (h, 0) + (0, M h) := by ext <;> simp
    rw [hsplit, map_add]
    have hz : L (0, M h) = 0 := by
      have := congrArg (fun A => A (M h)) hdual
      simpa using this
    rw [hz, add_zero]
  rw [hderivEq] at hcomp
  let Lx := L.comp Lin
  change HasFDerivAt (unscaledExplicitValue hnpos P) Lx x at hcomp
  have hcoord : Lx = NCPLVerification.evecDot
      (NCPLVerification.continuousLinearMapCoordinates Lx) := by
    ext h
    rw [NCPLVerification.continuousLinearMap_apply_eq_coordinates]
    rfl
  have hgrad : unscaledTrueGradX (T := T) hnpos P x ystar =
      NCPLVerification.continuousLinearMapCoordinates Lx := by
    rfl
  rw [hcoord, ← hgrad] at hcomp
  simpa [NCPLVerification.HasEVecFDerivAt, hnpos, ystar, L, Lin, Lx,
    graph, M, g] using hcomp

/-! ## Literal primal coordinates of the true envelope gradient -/

private theorem primalAIndex_injective {T : Nat} :
    Function.Injective (primalAIndex (T := T)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val = 3 * j.val at hv
  omega

private theorem primalBIndex_injective {T : Nat} :
    Function.Injective (primalBIndex (T := T)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val + 1 = 3 * j.val + 1 at hv
  omega

private theorem primalStateIndex_injective {T : Nat} :
    Function.Injective (primalStateIndex (T := T)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val + 2 = 3 * j.val + 2 at hv
  omega

private theorem primalAIndex_ne_BIndex {T : Nat}
    (i j : Fin (T - 1)) : primalAIndex i ≠ primalBIndex j := by
  intro h
  have hv := congrArg Fin.val h
  change 3 * i.val = 3 * j.val + 1 at hv
  omega

private theorem primalAIndex_ne_stateIndex {T : Nat}
    (i j : Fin (T - 1)) : primalAIndex i ≠ primalStateIndex j := by
  intro h
  have hv := congrArg Fin.val h
  change 3 * i.val = 3 * j.val + 2 at hv
  omega

private theorem primalBIndex_ne_stateIndex {T : Nat}
    (i j : Fin (T - 1)) : primalBIndex i ≠ primalStateIndex j := by
  intro h
  have hv := congrArg Fin.val h
  change 3 * i.val + 1 = 3 * j.val + 2 at hv
  omega

@[simp] private theorem primalA_evecBasis_A {T : Nat}
    (i j : Fin (T - 1)) :
    primalA (NCPLVerification.evecBasis (primalAIndex i) : UnscaledPrimal T) j =
      if j = i then 1 else 0 := by
  unfold primalA NCPLVerification.evecBasis
  by_cases hji : j = i
  · subst j
    simp
  · have hidx : primalAIndex j ≠ primalAIndex i :=
      fun h ↦ hji (primalAIndex_injective h)
    simp [hji, hidx]

@[simp] private theorem primalB_evecBasis_A {T : Nat}
    (i j : Fin (T - 1)) :
    primalB (NCPLVerification.evecBasis (primalAIndex i) : UnscaledPrimal T) j = 0 := by
  simp [primalB, NCPLVerification.evecBasis,
    (primalAIndex_ne_BIndex i j).symm]

@[simp] private theorem primalState_evecBasis_A {T : Nat}
    (i j : Fin (T - 1)) :
    primalState (NCPLVerification.evecBasis (primalAIndex i) : UnscaledPrimal T) j = 0 := by
  simp [primalState, NCPLVerification.evecBasis,
    (primalAIndex_ne_stateIndex i j).symm]

@[simp] private theorem primalA_evecBasis_B {T : Nat}
    (i j : Fin (T - 1)) :
    primalA (NCPLVerification.evecBasis (primalBIndex i) : UnscaledPrimal T) j = 0 := by
  simp [primalA, NCPLVerification.evecBasis, primalAIndex_ne_BIndex]

@[simp] private theorem primalB_evecBasis_B {T : Nat}
    (i j : Fin (T - 1)) :
    primalB (NCPLVerification.evecBasis (primalBIndex i) : UnscaledPrimal T) j =
      if j = i then 1 else 0 := by
  unfold primalB NCPLVerification.evecBasis
  by_cases hji : j = i
  · subst j
    simp
  · have hidx : primalBIndex j ≠ primalBIndex i :=
      fun h ↦ hji (primalBIndex_injective h)
    simp [hji, hidx]

@[simp] private theorem primalState_evecBasis_B {T : Nat}
    (i j : Fin (T - 1)) :
    primalState (NCPLVerification.evecBasis (primalBIndex i) : UnscaledPrimal T) j = 0 := by
  simp [primalState, NCPLVerification.evecBasis,
    (primalBIndex_ne_stateIndex i j).symm]

@[simp] private theorem primalA_evecBasis_state {T : Nat}
    (i j : Fin (T - 1)) :
    primalA (NCPLVerification.evecBasis (primalStateIndex i) :
      UnscaledPrimal T) j = 0 := by
  simp [primalA, NCPLVerification.evecBasis, primalAIndex_ne_stateIndex]

@[simp] private theorem primalB_evecBasis_state {T : Nat}
    (i j : Fin (T - 1)) :
    primalB (NCPLVerification.evecBasis (primalStateIndex i) :
      UnscaledPrimal T) j = 0 := by
  simp [primalB, NCPLVerification.evecBasis, primalBIndex_ne_stateIndex]

@[simp] private theorem primalState_evecBasis_state {T : Nat}
    (i j : Fin (T - 1)) :
    primalState (NCPLVerification.evecBasis (primalStateIndex i) :
      UnscaledPrimal T) j = if j = i then 1 else 0 := by
  unfold primalState NCPLVerification.evecBasis
  by_cases hji : j = i
  · subst j
    simp
  · have hidx : primalStateIndex j ≠ primalStateIndex i :=
      fun h ↦ hji (primalStateIndex_injective h)
    simp [hji, hidx]

private theorem serializeUnscaled_evecBasis_A {T n : Nat}
    (i : Fin (T - 1)) :
    serializeUnscaled
        (NCPLVerification.evecBasis (primalAIndex i) : UnscaledPrimal T)
        (0 : UnscaledDual T n) =
      (NCPLVerification.evecBasis (serializedAIndex (n := n) i) :
        SerializedSpace T n) := by
  apply SerializedSpace.ext_blocks
  · intro j
    rw [serializedA_serializeUnscaled]
    simp [serializedA, NCPLVerification.evecBasis]
  · intro j k
    rw [serializedY_serializeUnscaled]
    simp [dualBlock, serializedY, NCPLVerification.evecBasis,
      (serializedAIndex_ne_dualIndex i j k).symm]
  · intro j
    rw [serializedB_serializeUnscaled]
    simp [serializedB, NCPLVerification.evecBasis,
      (serializedAIndex_ne_BIndex i j).symm]
  · intro j
    rw [serializedState_serializeUnscaled]
    simp [serializedState, NCPLVerification.evecBasis,
      (serializedAIndex_ne_stateIndex i j).symm]

private theorem serializeUnscaled_evecBasis_B {T n : Nat}
    (i : Fin (T - 1)) :
    serializeUnscaled
        (NCPLVerification.evecBasis (primalBIndex i) : UnscaledPrimal T)
        (0 : UnscaledDual T n) =
      (NCPLVerification.evecBasis (serializedBIndex (n := n) i) :
        SerializedSpace T n) := by
  apply SerializedSpace.ext_blocks
  · intro j
    rw [serializedA_serializeUnscaled]
    simp [serializedA, NCPLVerification.evecBasis,
      serializedAIndex_ne_BIndex]
  · intro j k
    rw [serializedY_serializeUnscaled]
    simp [dualBlock, serializedY, NCPLVerification.evecBasis,
      (serializedBIndex_ne_dualIndex i j k).symm]
  · intro j
    rw [serializedB_serializeUnscaled]
    by_cases hji : j = i
    · subst j
      simp [serializedB, NCPLVerification.evecBasis]
    · have hidx : serializedBIndex (n := n) j ≠ serializedBIndex i :=
        fun h ↦ hji (serializedBIndex_injective h)
      simp [serializedB, NCPLVerification.evecBasis, hji, hidx]
  · intro j
    rw [serializedState_serializeUnscaled]
    simp [serializedState, NCPLVerification.evecBasis,
      (serializedBIndex_ne_stateIndex i j).symm]

private theorem serializeUnscaled_evecBasis_state {T n : Nat}
    (i : Fin (T - 1)) :
    serializeUnscaled
        (NCPLVerification.evecBasis (primalStateIndex i) : UnscaledPrimal T)
        (0 : UnscaledDual T n) =
      (NCPLVerification.evecBasis (serializedStateIndex (n := n) i) :
        SerializedSpace T n) := by
  apply SerializedSpace.ext_blocks
  · intro j
    rw [serializedA_serializeUnscaled]
    simp [serializedA, NCPLVerification.evecBasis,
      serializedAIndex_ne_stateIndex]
  · intro j k
    rw [serializedY_serializeUnscaled]
    simp [dualBlock, serializedY, NCPLVerification.evecBasis,
      (serializedStateIndex_ne_dualIndex i j k).symm]
  · intro j
    rw [serializedB_serializeUnscaled]
    simp [serializedB, NCPLVerification.evecBasis,
      serializedBIndex_ne_stateIndex]
  · intro j
    rw [serializedState_serializeUnscaled]
    by_cases hji : j = i
    · subst j
      simp [serializedState, NCPLVerification.evecBasis]
    · have hidx : serializedStateIndex (n := n) j ≠ serializedStateIndex i :=
        fun h ↦ hji (serializedStateIndex_injective h)
      simp [serializedState, NCPLVerification.evecBasis, hji, hidx]

/-- The `a_i` entry of the genuine separated primal gradient is exactly the
already verified `a_i` entry of the literal serialized Fréchet gradient. -/
theorem primalA_unscaledTrueGradX {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (i : Fin (T - 1)) :
    primalA (unscaledTrueGradX hn P x y) i =
      serializedGradA hn P (serializeUnscaled x y) i := by
  let h : UnscaledPrimal T := NCPLVerification.evecBasis (primalAIndex i)
  have hrep := (unscaledTrueGradient_representsJointGradient
    (T := T) hn P).2 x y h (0 : UnscaledDual T n)
  rw [(unscaledObjective_hasFDerivAt (T := T) hn P x y).fderiv] at hrep
  simp only [ContinuousLinearMap.comp_apply, serializeUnscaledCLM_apply,
    Prod.fst, Prod.snd] at hrep
  rw [show serializeUnscaled h (0 : UnscaledDual T n) =
      (NCPLVerification.evecBasis (serializedAIndex (n := n) i) :
        SerializedSpace T n) by exact serializeUnscaled_evecBasis_A i] at hrep
  simp [h, NCPLVerification.evecDot_apply, NCPLVerification.evecBasis,
    primalA, serializedTrueGradient_A] at hrep
  exact hrep.symm

/-- The analogous literal identity for the `b_i` entry. -/
theorem primalB_unscaledTrueGradX {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (i : Fin (T - 1)) :
    primalB (unscaledTrueGradX hn P x y) i =
      serializedGradB hn P (serializeUnscaled x y) i := by
  let h : UnscaledPrimal T := NCPLVerification.evecBasis (primalBIndex i)
  have hrep := (unscaledTrueGradient_representsJointGradient
    (T := T) hn P).2 x y h (0 : UnscaledDual T n)
  rw [(unscaledObjective_hasFDerivAt (T := T) hn P x y).fderiv] at hrep
  simp only [ContinuousLinearMap.comp_apply, serializeUnscaledCLM_apply,
    Prod.fst, Prod.snd] at hrep
  rw [show serializeUnscaled h (0 : UnscaledDual T n) =
      (NCPLVerification.evecBasis (serializedBIndex (n := n) i) :
        SerializedSpace T n) by exact serializeUnscaled_evecBasis_B i] at hrep
  simp [h, NCPLVerification.evecDot_apply, NCPLVerification.evecBasis,
    primalB, serializedTrueGradient_B] at hrep
  exact hrep.symm

/-- Literal identity for the memory/state coordinate of the separated true
primal gradient. -/
theorem primalState_unscaledTrueGradX {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (i : Fin (T - 1)) :
    primalState (unscaledTrueGradX hn P x y) i =
      serializedGradState P (serializeUnscaled x y) i := by
  let h : UnscaledPrimal T := NCPLVerification.evecBasis (primalStateIndex i)
  have hrep := (unscaledTrueGradient_representsJointGradient
    (T := T) hn P).2 x y h (0 : UnscaledDual T n)
  rw [(unscaledObjective_hasFDerivAt (T := T) hn P x y).fderiv] at hrep
  simp only [ContinuousLinearMap.comp_apply, serializeUnscaledCLM_apply] at hrep
  rw [show serializeUnscaled h (0 : UnscaledDual T n) =
      (NCPLVerification.evecBasis (serializedStateIndex (n := n) i) :
        SerializedSpace T n) by exact serializeUnscaled_evecBasis_state i] at hrep
  simp [h, NCPLVerification.evecDot_apply, NCPLVerification.evecBasis,
    serializedTrueGradient_state] at hrep
  exact hrep.symm

/-- Once the current clipped state is low, every possible successor-block
term in its memory derivative is nonpositive. -/
theorem serializedNextStateContribution_nonpos_of_low {T n : Nat}
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1))
    (hmu : 0 ≤ P.mu)
    (hlow : serializedClippedNext P q i ≤ 1) :
    serializedNextStateContribution P q i ≤ 0 := by
  unfold serializedNextStateContribution
  split
  · let j : Fin (T - 1) := ⟨i.val + 1, by assumption⟩
    have hpsiD : Psi2Deriv (serializedClippedNext P q i) = 0 :=
      Psi2Deriv_eq_zero_of_le_one hlow
    have hscale : 0 ≤
        P.mu * Psi2 (serializedClippedNext P q j) :=
      mul_nonneg hmu (Psi2_nonneg _)
    have hhinge : Sigma1Deriv P.theta (serializedClippedNext P q i) ≤ 0 :=
      Sigma1Deriv_nonpos _ _
    have hclip : 0 ≤ pi1Deriv P.delta P.P0 (serializedState q i) :=
      (pi1Deriv_mem_unitInterval _ _ _).1
    simp only [hpsiD, zero_mul, mul_zero, sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos hscale hhinge) hclip
  · exact le_rfl

theorem serializedNextStateContribution_eq_order_of_low {T n : Nat}
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1))
    (hi : i.val + 1 < T - 1)
    (hlow : serializedClippedNext P q i ≤ 1) :
    serializedNextStateContribution P q i =
      let j : Fin (T - 1) := ⟨i.val + 1, hi⟩
      P.mu * Psi2 (serializedClippedNext P q j) *
        Sigma1Deriv P.theta (serializedClippedNext P q i) *
          pi1Deriv P.delta P.P0 (serializedState q i) := by
  unfold serializedNextStateContribution
  rw [dif_pos hi]
  have hpsiD := Psi2Deriv_eq_zero_of_le_one hlow
  simp [hpsiD]

/-- A literal low-to-high state jump forces a true memory-gradient
coordinate below `-1`.  Thus such a jump is impossible at gradient norm
strictly below one. -/
theorem explicitValue_low_to_high_state_grad_le_neg_one {T n : Nat}
    (hn : 10 ≤ n) {theta : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (P : UnscaledParameters)
    (hPtheta : P.theta = theta) (hPtau : P.tauS = tauS P.delta)
    (hPmu : P.mu = C.mu) (heta : 0 ≤ P.eta) (hbeta : 0 ≤ P.beta)
    (x : UnscaledPrimal T) (i : Fin (T - 1))
    (hi : i.val + 1 < T - 1)
    (hlow : clippedNext P x i ≤ 1)
    (hhigh : 1 + theta ≤
      clippedNext P x ⟨i.val + 1, hi⟩) :
    primalState
        (unscaledTrueGradX (by omega : 0 < n) P x
          (unscaledInnerMaximizer (by omega : 0 < n) x)) i ≤ -1 := by
  let hnpos : 0 < n := by omega
  let ystar := unscaledInnerMaximizer hnpos x
  let q := serializeUnscaled x ystar
  let raw := primalState x i
  let cur := clippedCurrent P x i
  let nxt := clippedNext P x i
  let j : Fin (T - 1) := ⟨i.val + 1, hi⟩
  have htheta : 0 < theta := by simpa [hPtheta] using P.theta_pos
  have hclip : 0 ≤ pi1Deriv P.delta P.P0 raw :=
    (pi1Deriv_mem_unitInterval _ _ _).1
  have hmemory : -P.eta * Psi1Deriv nxt *
      pi1Deriv P.delta P.P0 raw ≤ 0 := by
    have hp : 0 ≤ P.eta * Psi1Deriv nxt *
        pi1Deriv P.delta P.P0 raw :=
      mul_nonneg (mul_nonneg heta (Psi1Deriv_nonneg nxt)) hclip
    nlinarith
  have hpsi2D : Psi2Deriv nxt = 0 := Psi2Deriv_eq_zero_of_le_one hlow
  have hlamD : deriv (Lambda2 P.theta) nxt = 0 :=
    Lambda2_deriv_eq_zero_of_le_one P.theta_pos hlow
  have hrelayD : exitRelayDeriv P.theta nxt = 1 :=
    exitRelayDeriv_eq_one_of_le_one P.theta_pos hlow
  have hexit : exitPulseDerivNext P.beta P.theta cur (primalB x i) nxt *
      pi1Deriv P.delta P.P0 raw ≤ 0 := by
    unfold exitPulseDerivNext
    rw [hrelayD]
    have hp := mul_nonneg
      (mul_nonneg (mul_nonneg hbeta (Psi2_nonneg cur))
        (Psi2_nonneg (primalB x i))) hclip
    nlinarith
  have hnextEq : serializedNextStateContribution P q i =
      P.mu * Psi2 (clippedNext P x j) * Sigma1Deriv P.theta nxt *
        pi1Deriv P.delta P.P0 raw := by
    have heq := serializedNextStateContribution_eq_order_of_low P q i hi
      (by simpa [q, nxt] using hlow)
    simpa [q, j, raw, nxt] using heq
  have hpsiHigh : xi0 theta ≤ Psi2 (clippedNext P x j) :=
    xi0_le_Psi2 hhigh
  have hhinge : Sigma1Deriv P.theta nxt ≤ 0 := Sigma1Deriv_nonpos _ _
  have hmu0 : 0 ≤ P.mu := by rw [hPmu]; exact C.mu_pos.le
  have hcoeff : P.mu * xi0 theta ≤
      P.mu * Psi2 (clippedNext P x j) :=
    mul_le_mul_of_nonneg_left hpsiHigh hmu0
  have horderCompare :
      P.mu * Psi2 (clippedNext P x j) * Sigma1Deriv P.theta nxt *
          pi1Deriv P.delta P.P0 raw ≤
        P.mu * xi0 theta * Sigma1Deriv P.theta nxt *
          pi1Deriv P.delta P.P0 raw := by
    have hneg := mul_le_mul_of_nonpos_right hcoeff hhinge
    exact mul_le_mul_of_nonneg_right hneg hclip
  have hwall := wall_order_margin P.theta_pos P.delta_pos P.P0_gt_one
    (by simpa [hPtheta, hPmu] using C.order_margin) hlow
  rw [← hPtau] at hwall
  rw [primalState_unscaledTrueGradX]
  unfold serializedGradState
  simp only [serializedState_serializeUnscaled,
    serializedClippedCurrent_serializeUnscaled,
    serializedClippedNext_serializeUnscaled,
    serializedA_serializeUnscaled, serializedB_serializeUnscaled]
  change
    -P.eta * Psi1Deriv nxt * pi1Deriv P.delta P.P0 raw +
        Sigma2Deriv P.tauS raw +
        P.mu * Psi2Deriv nxt * pi1Deriv P.delta P.P0 raw * Sigma1 P.theta cur -
        P.alpha * Psi2 cur * deriv (Lambda2 P.theta) nxt *
          pi1Deriv P.delta P.P0 raw * pi2 P.P0 (primalA x i) +
        exitPulseDerivNext P.beta P.theta cur (primalB x i) nxt *
          pi1Deriv P.delta P.P0 raw +
        serializedNextStateContribution P q i ≤ -1
  rw [hpsi2D, hlamD, hnextEq]
  simp only [zero_mul, mul_zero, sub_zero, add_zero]
  have hcombined : Sigma2Deriv P.tauS raw +
      P.mu * Psi2 (clippedNext P x j) * Sigma1Deriv P.theta nxt *
        pi1Deriv P.delta P.P0 raw ≤ -1 := by
    calc
      _ ≤ Sigma2Deriv P.tauS raw +
          P.mu * xi0 theta * Sigma1Deriv P.theta nxt *
            pi1Deriv P.delta P.P0 raw := by linarith
      _ ≤ -1 := by
        simpa [raw, nxt, clippedNext, hPtheta, hPmu] using hwall
  linarith

theorem no_low_to_high_of_explicitValue_gradient_sq_lt_one {T n : Nat}
    (hn : 10 ≤ n) {theta : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (P : UnscaledParameters)
    (hPtheta : P.theta = theta) (hPtau : P.tauS = tauS P.delta)
    (hPmu : P.mu = C.mu) (heta : 0 ≤ P.eta) (hbeta : 0 ≤ P.beta)
    (x : UnscaledPrimal T)
    (hgrad : vecSq (unscaledTrueGradX (by omega : 0 < n) P x
      (unscaledInnerMaximizer (by omega : 0 < n) x)) < 1) :
    ∀ (i : Fin (T - 1)) (hi : i.val + 1 < T - 1),
      clippedNext P x i ≤ 1 →
      ¬ 1 + theta ≤ clippedNext P x ⟨i.val + 1, hi⟩ := by
  intro i hi hlow hhigh
  let grad := unscaledTrueGradX (by omega : 0 < n) P x
    (unscaledInnerMaximizer (by omega : 0 < n) x)
  have hs := explicitValue_low_to_high_state_grad_le_neg_one hn C P
    hPtheta hPtau hPmu heta hbeta x i hi hlow hhigh
  have hcoord := coordinate_sq_le_vecSq grad (primalStateIndex i)
  have hs' : grad (primalStateIndex i) ≤ -1 := by
    simpa [grad, primalState] using hs
  have hone : (1 : ℝ) ≤ (grad (primalStateIndex i)) ^ 2 := by
    nlinarith [sq_nonneg (grad (primalStateIndex i) + 1)]
  have : (1 : ℝ) ≤ vecSq grad := hone.trans hcoord
  exact (not_lt_of_ge this) (by simpa [grad] using hgrad)

/-! ## The concrete transition-band obstruction -/

/-- If the output of the state clip lies in the transition band, then its
raw input is still in the identity core of the clip. -/
theorem pi1Deriv_eq_one_of_output_mem_transition
    {delta P0 theta raw : ℝ}
    (hdelta : 0 < delta) (hP0 : 1 < P0)
    (htheta_pos : 0 < theta) (htheta_small : theta < 1 / 10)
    (hlow : 1 ≤ pi1 delta P0 raw)
    (hhigh : pi1 delta P0 raw ≤ 1 + theta) :
    pi1Deriv delta P0 raw = 1 := by
  have hrawLow : stateLower delta ≤ raw := by
    by_contra h
    have hraw : raw ≤ stateLower delta := le_of_not_ge h
    have hmono := (pi1_monotone hdelta hP0) hraw
    have hend : pi1 delta P0 (stateLower delta) = stateLower delta := by
      apply pi1_eq_self hdelta hP0 le_rfl
      unfold stateLower stateUpper
      linarith
    rw [hend] at hmono
    unfold stateLower at hmono
    linarith
  have hrawHigh : raw ≤ stateUpper := by
    by_contra h
    have hraw : stateUpper ≤ raw := le_of_not_ge h
    have hmono := (pi1_monotone hdelta hP0) hraw
    have hend : pi1 delta P0 stateUpper = stateUpper := by
      apply pi1_eq_self hdelta hP0
      · unfold stateLower stateUpper
        linarith
      · exact le_rfl
    rw [hend] at hmono
    unfold stateUpper at hmono
    linarith
  exact pi1Deriv_eq_one hdelta hP0 hrawLow hrawHigh

/-- With the actual concrete memory remainder, a clipped state in the
transition band forces the corresponding literal serialized gradient
coordinate below `-1`. -/
theorem concrete_serialized_transition_state_grad_le_neg_one {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1))
    (hlow : 1 ≤ serializedClippedNext concreteUnscaledParameters q i)
    (hhigh : serializedClippedNext concreteUnscaledParameters q i ≤
      1 + concreteTheta) :
    serializedGradState concreteUnscaledParameters q i ≤ -1 := by
  let P := concreteUnscaledParameters
  let nxt := serializedClippedNext P q i
  let raw := serializedState q i
  have hclip : pi1Deriv P.delta P.P0 raw = 1 := by
    apply pi1Deriv_eq_one_of_output_mem_transition P.delta_pos P.P0_gt_one
      concreteTheta_pos concreteTheta_lt_tenth
    · simpa [P, nxt, raw, serializedClippedNext] using hlow
    · simpa [P, nxt, raw, serializedClippedNext] using hhigh
  have hpsi : 2 ≤ Psi1Deriv nxt := by
    apply two_le_Psi1Deriv_on concreteTheta_pos concreteTheta_lt_tenth
    · simpa [P, nxt] using hlow
    · simpa [P, nxt] using hhigh
  have hremAbs := concreteCs_dominates_final_memory_remainder q i
  have hrem : serializedMemoryRemainder P q i ≤ concreteCs := by
    exact (le_abs_self _).trans (by simpa [P] using hremAbs)
  have heta : 0 ≤ P.eta := by
    change 0 ≤ concreteRadialTransition.eta
    exact concreteRadialTransition.eta_pos.le
  have hpsiEta : P.eta * 2 ≤ P.eta * Psi1Deriv nxt :=
    mul_le_mul_of_nonneg_left hpsi heta
  have hmargin : concreteCs + 1 ≤ P.eta * 2 := by
    simpa [P, concreteUnscaledParameters, concreteRadialTransition,
      assembleRadialTransition] using concreteTransitionEta.transition_margin
  rw [serializedGradState_eq_eta_term_add_memory]
  change -P.eta * Psi1Deriv nxt * pi1Deriv P.delta P.P0 raw +
      serializedMemoryRemainder P q i ≤ -1
  rw [hclip, mul_one]
  linarith

/-- The transition-band estimate is an estimate for an actual coordinate of
the true gradient of the explicit value function. -/
theorem explicitValue_transition_state_grad_le_neg_one {T n : Nat}
    (hn : 10 ≤ n) (x : UnscaledPrimal T) (i : Fin (T - 1))
    (hlow : 1 ≤ clippedNext concreteUnscaledParameters x i)
    (hhigh : clippedNext concreteUnscaledParameters x i ≤
      1 + concreteTheta) :
    primalState
        (unscaledTrueGradX (by omega : 0 < n) concreteUnscaledParameters x
          (unscaledInnerMaximizer (by omega : 0 < n) x)) i ≤ -1 := by
  rw [primalState_unscaledTrueGradX]
  apply concrete_serialized_transition_state_grad_le_neg_one
  · simpa using hlow
  · simpa using hhigh

/-- At squared gradient norm below one, every concrete clipped state is
already either low or high; the open transition band is empty. -/
theorem no_transition_of_explicitValue_gradient_sq_lt_one {T n : Nat}
    (hn : 10 ≤ n) (x : UnscaledPrimal T)
    (hgrad : vecSq
      (unscaledTrueGradX (by omega : 0 < n) concreteUnscaledParameters x
        (unscaledInnerMaximizer (by omega : 0 < n) x)) < 1) :
    ∀ i : Fin (T - 1),
      clippedNext concreteUnscaledParameters x i ≤ 1 ∨
        1 + concreteTheta ≤ clippedNext concreteUnscaledParameters x i := by
  intro i
  by_cases hlow : clippedNext concreteUnscaledParameters x i ≤ 1
  · exact Or.inl hlow
  · right
    by_contra hhigh
    let grad := unscaledTrueGradX (by omega : 0 < n)
      concreteUnscaledParameters x
      (unscaledInnerMaximizer (by omega : 0 < n) x)
    have hs := explicitValue_transition_state_grad_le_neg_one hn x i
      (le_of_lt (lt_of_not_ge hlow)) (le_of_not_ge hhigh)
    have hcoord := coordinate_sq_le_vecSq grad (primalStateIndex i)
    have hs' : grad (primalStateIndex i) ≤ -1 := by
      simpa [grad, primalState] using hs
    have hone : (1 : ℝ) ≤ (grad (primalStateIndex i)) ^ 2 := by
      nlinarith [sq_nonneg (grad (primalStateIndex i) + 1)]
    have : (1 : ℝ) ≤ vecSq grad := hone.trans hcoord
    exact (not_lt_of_ge this) (by simpa [grad] using hgrad)

/-- A low clipped state together with the transition dichotomy determines
an actual frontier block.  The proof selects the first low state, so its
predecessor is high (with the fixed initial state `s₁ = 2` handling index
zero). -/
theorem exists_concrete_frontier_of_low_and_no_transition {T : Nat}
    (x : UnscaledPrimal T)
    (htransition : ∀ i : Fin (T - 1),
      clippedNext concreteUnscaledParameters x i ≤ 1 ∨
        1 + concreteTheta ≤ clippedNext concreteUnscaledParameters x i)
    (ilow : Fin (T - 1))
    (hlow : clippedNext concreteUnscaledParameters x ilow ≤ 1) :
    ∃ i : Fin (T - 1),
      1 + concreteTheta ≤ clippedCurrent concreteUnscaledParameters x i ∧
        clippedNext concreteUnscaledParameters x i ≤ 1 := by
  classical
  let lowAt : Nat → Prop := fun k ↦
    ∃ hk : k < T - 1,
      clippedNext concreteUnscaledParameters x ⟨k, hk⟩ ≤ 1
  have hex : ∃ k, lowAt k := by
    exact ⟨ilow.val, ilow.isLt, hlow⟩
  let k := Nat.find hex
  have hkspec : lowAt k := Nat.find_spec hex
  rcases hkspec with ⟨hklt, hklow⟩
  let i : Fin (T - 1) := ⟨k, hklt⟩
  refine ⟨i, ?_, by simpa [i] using hklow⟩
  by_cases hk0 : k = 0
  · have hclipTwo : pi1 concreteUnscaledParameters.delta
        concreteUnscaledParameters.P0 2 = 2 := by
      apply pi1_eq_self concreteUnscaledParameters.delta_pos
        concreteUnscaledParameters.P0_gt_one
      · unfold stateLower
        linarith [concreteUnscaledParameters.delta_pos]
      · norm_num [stateUpper]
    simp [clippedCurrent, currentState, i, hk0, hclipTwo, concreteTheta]
    norm_num
  · let j : Fin (T - 1) := ⟨k - 1, by omega⟩
    have hjk : k - 1 < k := by omega
    have hjNotLow : ¬ clippedNext concreteUnscaledParameters x j ≤ 1 := by
      intro hjlow
      exact (Nat.find_min hex hjk) ⟨j.isLt, hjlow⟩
    have hjHigh := (htransition j).resolve_left hjNotLow
    simpa [clippedCurrent, clippedNext, currentState, i, j, hk0] using hjHigh

/-- The first-low construction plus the no-low-to-high estimate gives the
complete paper frontier: all earlier clipped memories are high and every
memory from the frontier onward is low. -/
theorem exists_concrete_full_frontier_of_low {T : Nat}
    (x : UnscaledPrimal T)
    (htransition : ∀ i : Fin (T - 1),
      clippedNext concreteUnscaledParameters x i ≤ 1 ∨
        1 + concreteTheta ≤ clippedNext concreteUnscaledParameters x i)
    (hnoLowHigh : ∀ (i : Fin (T - 1))
      (hi : i.val + 1 < T - 1),
      clippedNext concreteUnscaledParameters x i ≤ 1 →
      ¬ 1 + concreteTheta ≤
        clippedNext concreteUnscaledParameters x ⟨i.val + 1, hi⟩)
    (ilow : Fin (T - 1))
    (hlow : clippedNext concreteUnscaledParameters x ilow ≤ 1) :
    ∃ i : Fin (T - 1),
      1 + concreteTheta ≤ clippedCurrent concreteUnscaledParameters x i ∧
      clippedNext concreteUnscaledParameters x i ≤ 1 ∧
      (∀ l : Fin (T - 1), l.val < i.val →
        1 + concreteTheta ≤ clippedNext concreteUnscaledParameters x l) ∧
      (∀ l : Fin (T - 1), i.val ≤ l.val →
        clippedNext concreteUnscaledParameters x l ≤ 1) := by
  classical
  let lowAt : Nat → Prop := fun k ↦
    ∃ hk : k < T - 1,
      clippedNext concreteUnscaledParameters x ⟨k, hk⟩ ≤ 1
  have hex : ∃ k, lowAt k := ⟨ilow.val, ilow.isLt, hlow⟩
  let k := Nat.find hex
  have hkspec : lowAt k := Nat.find_spec hex
  rcases hkspec with ⟨hklt, hklow⟩
  let i : Fin (T - 1) := ⟨k, hklt⟩
  have hbefore : ∀ l : Fin (T - 1), l.val < k →
      1 + concreteTheta ≤ clippedNext concreteUnscaledParameters x l := by
    intro l hl
    have hlNotLow : ¬ clippedNext concreteUnscaledParameters x l ≤ 1 := by
      intro hllow
      exact (Nat.find_min hex hl) ⟨l.isLt, hllow⟩
    exact (htransition l).resolve_left hlNotLow
  have hafterNat : ∀ (m : Nat) (hm : m < T - 1), k ≤ m →
      clippedNext concreteUnscaledParameters x ⟨m, hm⟩ ≤ 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro hm hkm
        by_cases hmk : m = k
        · subst m
          simpa using hklow
        · have hkmStrict : k < m := lt_of_le_of_ne hkm (Ne.symm hmk)
          let p : Fin (T - 1) := ⟨m - 1, by omega⟩
          have hpLow : clippedNext concreteUnscaledParameters x p ≤ 1 := by
            apply ih (m - 1) (by omega) (by omega) (by omega)
          have hnotHigh : ¬ 1 + concreteTheta ≤
              clippedNext concreteUnscaledParameters x ⟨m, hm⟩ := by
            intro hmHigh
            have hpSucc : p.val + 1 < T - 1 := by
              dsimp [p]
              omega
            have hforbid := hnoLowHigh p hpSucc hpLow
            have hindex :
                (⟨p.val + 1, hpSucc⟩ : Fin (T - 1)) = ⟨m, hm⟩ := by
              apply Fin.ext
              dsimp [p]
              omega
            rw [hindex] at hforbid
            exact hforbid hmHigh
          exact (htransition ⟨m, hm⟩).resolve_right hnotHigh
  have hafter : ∀ l : Fin (T - 1), k ≤ l.val →
      clippedNext concreteUnscaledParameters x l ≤ 1 := by
    intro l hl
    simpa using hafterNat l.val l.isLt hl
  have hcurrent : 1 + concreteTheta ≤
      clippedCurrent concreteUnscaledParameters x i := by
    by_cases hk0 : k = 0
    · have hclipTwo : pi1 concreteUnscaledParameters.delta
          concreteUnscaledParameters.P0 2 = 2 := by
        apply pi1_eq_self concreteUnscaledParameters.delta_pos
          concreteUnscaledParameters.P0_gt_one
        · unfold stateLower
          linarith [concreteUnscaledParameters.delta_pos]
        · norm_num [stateUpper]
      simp [clippedCurrent, currentState, i, hk0, hclipTwo, concreteTheta]
      norm_num
    · let j : Fin (T - 1) := ⟨k - 1, by omega⟩
      have hjHigh := hbefore j (by dsimp [j]; omega)
      simpa [clippedCurrent, clippedNext, currentState, i, j, hk0] using hjHigh
  refine ⟨i, hcurrent, by simpa [i] using hklow, ?_, ?_⟩
  · intro l hl
    exact hbefore l (by simpa [i] using hl)
  · intro l hl
    exact hafter l (by simpa [i] using hl)

/-- The high-`b` terminal branch is also a statement about the literal
memory coordinate of the true value gradient. -/
theorem explicitValue_exit_frontier_state_grad_le_neg_one {T n : Nat}
    (hn : 10 ≤ n) {theta : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (P : UnscaledParameters)
    (hPtheta : P.theta = theta) (hPtau : P.tauS = tauS P.delta)
    (hPbeta : P.beta = C.beta) (heta : 0 ≤ P.eta) (hmu : 0 ≤ P.mu)
    (x : UnscaledPrimal T) (i : Fin (T - 1))
    (hcurrent : 1 + theta ≤ clippedCurrent P x i)
    (hnext : clippedNext P x i ≤ 1)
    (hb : 1 + theta ≤ primalB x i) :
    primalState
        (unscaledTrueGradX (by omega : 0 < n) P x
          (unscaledInnerMaximizer (by omega : 0 < n) x)) i ≤ -1 := by
  let hnpos : 0 < n := by omega
  let ystar := unscaledInnerMaximizer hnpos x
  let q := serializeUnscaled x ystar
  let raw := primalState x i
  let cur := clippedCurrent P x i
  let nxt := clippedNext P x i
  have htheta : 0 < theta := by simpa [hPtheta] using P.theta_pos
  have hclip : 0 ≤ pi1Deriv P.delta P.P0 raw :=
    (pi1Deriv_mem_unitInterval _ _ _).1
  have hpsi1 : 0 ≤ Psi1Deriv nxt := Psi1Deriv_nonneg _
  have hmemory : -P.eta * Psi1Deriv nxt *
      pi1Deriv P.delta P.P0 raw ≤ 0 := by
    have := mul_nonneg (mul_nonneg heta hpsi1) hclip
    nlinarith
  have hpsi2D : Psi2Deriv nxt = 0 := Psi2Deriv_eq_zero_of_le_one hnext
  have hlamD : deriv (Lambda2 P.theta) nxt = 0 :=
    Lambda2_deriv_eq_zero_of_le_one P.theta_pos hnext
  have hrelayD : exitRelayDeriv P.theta nxt = 1 :=
    exitRelayDeriv_eq_one_of_le_one P.theta_pos hnext
  have hnextTerm : serializedNextStateContribution P q i ≤ 0 := by
    apply serializedNextStateContribution_nonpos_of_low P q i hmu
    simpa [q, nxt] using hnext
  have hcurPsi : xi0 theta ≤ Psi2 cur := xi0_le_Psi2 hcurrent
  have hbPsi : xi0 theta ≤ Psi2 (primalB x i) := xi0_le_Psi2 hb
  have hxi : 0 ≤ xi0 theta := (xi0_pos htheta).le
  have hprod : (xi0 theta) ^ 2 ≤ Psi2 cur * Psi2 (primalB x i) := by
    calc
      (xi0 theta) ^ 2 = xi0 theta * xi0 theta := by ring
      _ ≤ Psi2 cur * xi0 theta := mul_le_mul_of_nonneg_right hcurPsi hxi
      _ ≤ Psi2 cur * Psi2 (primalB x i) :=
        mul_le_mul_of_nonneg_left hbPsi (Psi2_nonneg cur)
  have hactualExit :
      -P.beta * Psi2 cur * Psi2 (primalB x i) *
          pi1Deriv P.delta P.P0 raw ≤
        -C.beta * (xi0 theta) ^ 2 *
          pi1Deriv P.delta P.P0 raw := by
    rw [hPbeta]
    have hs := mul_le_mul_of_nonneg_left hprod C.beta_pos.le
    have hs' := mul_le_mul_of_nonneg_right hs hclip
    nlinarith
  have hwall := wall_exit_margin P.theta_pos P.delta_pos P.P0_gt_one
    (by simpa [hPtheta] using C.exit_margin) hnext
  rw [← hPtau] at hwall
  have hlamTheta :
      Lambda2 theta (pi1 P.delta P.P0 (primalState x i)) = 1 := by
    apply Lambda2_eq_one_of_le_one htheta
    simpa [clippedNext, raw, nxt] using hnext
  rw [hPtheta, hlamTheta, mul_one] at hwall
  rw [primalState_unscaledTrueGradX]
  unfold serializedGradState
  simp only [serializedState_serializeUnscaled,
    serializedClippedCurrent_serializeUnscaled,
    serializedClippedNext_serializeUnscaled,
    serializedA_serializeUnscaled, serializedB_serializeUnscaled]
  change
    -P.eta * Psi1Deriv nxt * pi1Deriv P.delta P.P0 raw +
        Sigma2Deriv P.tauS raw +
        P.mu * Psi2Deriv nxt * pi1Deriv P.delta P.P0 raw * Sigma1 P.theta cur -
        P.alpha * Psi2 cur * deriv (Lambda2 P.theta) nxt *
          pi1Deriv P.delta P.P0 raw * pi2 P.P0 (primalA x i) +
        exitPulseDerivNext P.beta P.theta cur (primalB x i) nxt *
          pi1Deriv P.delta P.P0 raw +
        serializedNextStateContribution P q i ≤ -1
  rw [hpsi2D, hlamD]
  simp only [zero_mul, mul_zero, sub_zero, add_zero]
  unfold exitPulseDerivNext
  rw [hrelayD]
  have hcombined : Sigma2Deriv P.tauS raw +
      (-P.beta * Psi2 cur * Psi2 (primalB x i) *
        pi1Deriv P.delta P.P0 raw) ≤ -1 := by
    calc
      _ ≤ Sigma2Deriv P.tauS raw - C.beta * (xi0 theta) ^ 2 *
          pi1Deriv P.delta P.P0 raw := by linarith
      _ ≤ -1 := by
        simpa [raw] using hwall
  linarith

/-! ## The current block after substituting the actual Green maximizer -/

/-- The endpoint Green identities imply the exact `a` derivative of the
Li-link after the literal dual maximizer is substituted. -/
theorem innerGradA_at_innerMaximizer_transfer {n : Nat} (hn : 10 ≤ n)
    (a b : ℝ) :
    innerGradA (by omega : 0 < n) (innerC (by omega : 0 < n))
        (innerMaximizer (by omega : 0 < n) a b) +
      2 * innerC1 (by omega : 0 < n) * a =
        12 * (a - b / 2) := by
  let hnpos : 0 < n := by omega
  change innerGradA hnpos (innerC hnpos) (innerMaximizer hnpos a b) +
      2 * innerC1 hnpos * a = 12 * (a - b / 2)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hC : 0 ≤ innerC hnpos := by
    exact (innerC_pos hn).le
  have hs : innerScale n (innerC hnpos) ^ 2 = innerC hnpos / (n : ℝ) := by
    unfold innerScale
    rw [Real.sq_sqrt]
    exact div_nonneg hC hnreal.le
  have hX : innerB n (innerLast hnpos) (innerFirst hnpos) ≠ 0 := by
    exact ne_of_gt (innerB_cross_pos hn)
  unfold innerGradA innerMaximizer innerC1
  rw [innerB_apply_comm n (innerFirst hnpos) (innerLast hnpos)]
  ring_nf
  rw [hs]
  unfold innerC
  field_simp [hX, ne_of_gt hnreal]
  ring

/-- The exact companion identity for the `b` derivative. -/
theorem innerGradB_at_innerMaximizer_transfer {n : Nat} (hn : 10 ≤ n)
    (a b : ℝ) :
    innerGradB (by omega : 0 < n) (innerC (by omega : 0 < n))
        (innerMaximizer (by omega : 0 < n) a b) +
      2 * innerC2 (by omega : 0 < n) * b =
        -6 * (a - b / 2) := by
  let hnpos : 0 < n := by omega
  change innerGradB hnpos (innerC hnpos) (innerMaximizer hnpos a b) +
      2 * innerC2 hnpos * b = -6 * (a - b / 2)
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hC : 0 ≤ innerC hnpos := (innerC_pos hn).le
  have hs : innerScale n (innerC hnpos) ^ 2 = innerC hnpos / (n : ℝ) := by
    unfold innerScale
    rw [Real.sq_sqrt]
    exact div_nonneg hC hnreal.le
  have hX : innerB n (innerLast hnpos) (innerFirst hnpos) ≠ 0 :=
    ne_of_gt (innerB_cross_pos hn)
  have hdiag := innerB_endpoint_diagonal_eq hnpos
  unfold innerGradB innerMaximizer innerC2
  rw [show innerB n (innerLast hnpos) (innerLast hnpos) =
      innerB n (innerFirst hnpos) (innerFirst hnpos) by exact hdiag]
  ring_nf
  rw [hs]
  unfold innerC
  field_simp [hX, ne_of_gt hnreal]
  ring

theorem primalA_sq_le_pulseSq {T : Nat} (x : UnscaledPrimal T)
    (i : Fin (T - 1)) : (primalA x i) ^ 2 ≤ pulseSq x := by
  unfold pulseSq
  have hi : i ∈ (Finset.univ : Finset (Fin (T - 1))) := Finset.mem_univ i
  calc
    (primalA x i) ^ 2 ≤ (primalA x i) ^ 2 + (primalB x i) ^ 2 := by
      exact le_add_of_nonneg_right (sq_nonneg _)
    _ ≤ Finset.univ.sum (fun j : Fin (T - 1) ↦
        (primalA x j) ^ 2 + (primalB x j) ^ 2) := by
      exact Finset.single_le_sum
        (fun j _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)) hi

theorem primalB_sq_le_pulseSq {T : Nat} (x : UnscaledPrimal T)
    (i : Fin (T - 1)) : (primalB x i) ^ 2 ≤ pulseSq x := by
  unfold pulseSq
  have hi : i ∈ (Finset.univ : Finset (Fin (T - 1))) := Finset.mem_univ i
  calc
    (primalB x i) ^ 2 ≤ (primalA x i) ^ 2 + (primalB x i) ^ 2 := by
      exact le_add_of_nonneg_left (sq_nonneg _)
    _ ≤ Finset.univ.sum (fun j : Fin (T - 1) ↦
        (primalA x j) ^ 2 + (primalB x j) ^ 2) := by
      exact Finset.single_le_sum
        (fun j _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)) hi

private theorem abs_primalA_le_of_pulseSq {T : Nat} (P : UnscaledParameters)
    (x : UnscaledPrimal T) (i : Fin (T - 1))
    (hpulse : pulseSq x ≤ P.P0 ^ 2) :
    |primalA x i| ≤ P.P0 := by
  have hs : (primalA x i) ^ 2 ≤ P.P0 ^ 2 :=
    (primalA_sq_le_pulseSq x i).trans hpulse
  have hp0 : 0 ≤ P.P0 := P.P0_gt_one.le.trans' (by norm_num)
  exact (sq_le_sq₀ (abs_nonneg _) hp0).1 (by simpa [sq_abs] using hs)

/-- On a frontier block and inside the radial core, the actual envelope
gradient in the entrance coordinate is exactly the paper's `g_a`. -/
theorem explicitValue_current_gradA_eq_terminalGa {T n : Nat}
    (hn : 10 ≤ n) {theta : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (P : UnscaledParameters)
    (hPalpha : P.alpha = C.alpha) (hPgamma : P.gamma = C.gamma)
    (hP01 : P.P0 ^ 2 < P.P1 ^ 2)
    (x : UnscaledPrimal T) (i : Fin (T - 1))
    (hpulse : pulseSq x ≤ P.P0 ^ 2)
    (hnext : clippedNext P x i ≤ 1) :
    primalA
        (unscaledTrueGradX (by omega : 0 < n) P x
          (unscaledInnerMaximizer (by omega : 0 < n) x)) i =
      terminalGa C (clippedCurrent P x i) (primalA x i) (primalB x i) := by
  let hnpos : 0 < n := by omega
  have haAbs := abs_primalA_le_of_pulseSq P x i hpulse
  have haCore : |primalA x i| ≤ P.P0 + 2 := by linarith
  have hpi : pi2Deriv P.P0 (primalA x i) = 1 :=
    pi2Deriv_eq_one haCore
  have hlam : Lambda2 P.theta (clippedNext P x i) = 1 :=
    Lambda2_eq_one_of_le_one P.theta_pos hnext
  have hrad : Sigma3Deriv P.P0 P.P1 P.K (pulseSq x) = 0 :=
    Sigma3Deriv_eq_zero hP01 hpulse
  have hinner := innerGradA_at_innerMaximizer_transfer hn
    (primalA x i) (primalB x i)
  rw [primalA_unscaledTrueGradX]
  unfold serializedGradA
  simp only [serializedClippedCurrent_serializeUnscaled,
    serializedClippedNext_serializeUnscaled, serializedA_serializeUnscaled,
    serializedB_serializeUnscaled, serializedDualBlock_serializeUnscaled,
    serializedPulseSq_serializeUnscaled]
  rw [dualBlock_unscaledInnerMaximizer, hrad]
  unfold entrancePulseDerivA terminalGa
  rw [hpi, hlam, hPalpha, hPgamma]
  ring_nf at hinner ⊢
  linarith

/-- The analogous exact identity for the exit coordinate. -/
theorem explicitValue_current_gradB_eq_terminalGb {T n : Nat}
    (hn : 10 ≤ n) {theta : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (P : UnscaledParameters)
    (hPbeta : P.beta = C.beta) (hPgamma : P.gamma = C.gamma)
    (hP01 : P.P0 ^ 2 < P.P1 ^ 2)
    (x : UnscaledPrimal T) (i : Fin (T - 1))
    (hpulse : pulseSq x ≤ P.P0 ^ 2)
    (hnext : clippedNext P x i ≤ 1) :
    primalB
        (unscaledTrueGradX (by omega : 0 < n) P x
          (unscaledInnerMaximizer (by omega : 0 < n) x)) i =
      terminalGb C (clippedCurrent P x i) (clippedNext P x i)
        (primalA x i) (primalB x i) := by
  let hnpos : 0 < n := by omega
  have hrelay : exitRelay P.theta (clippedNext P x i) = clippedNext P x i :=
    exitRelay_eq_self_of_le_one P.theta_pos hnext
  have hrad : Sigma3Deriv P.P0 P.P1 P.K (pulseSq x) = 0 :=
    Sigma3Deriv_eq_zero hP01 hpulse
  have hinner := innerGradB_at_innerMaximizer_transfer hn
    (primalA x i) (primalB x i)
  rw [primalB_unscaledTrueGradX]
  unfold serializedGradB
  simp only [serializedClippedCurrent_serializeUnscaled,
    serializedClippedNext_serializeUnscaled, serializedA_serializeUnscaled,
    serializedB_serializeUnscaled, serializedDualBlock_serializeUnscaled,
    serializedPulseSq_serializeUnscaled]
  rw [dualBlock_unscaledInnerMaximizer, hrad]
  unfold exitPulseDerivB terminalGb
  rw [hrelay, hPbeta, hPgamma]
  ring_nf at hinner ⊢
  linarith

theorem primalAB_sq_le_vecSq {T : Nat} (z : UnscaledPrimal T)
    (i : Fin (T - 1)) :
    (primalA z i) ^ 2 + (primalB z i) ^ 2 ≤ vecSq z := by
  let ia := primalAIndex i
  let ib := primalBIndex i
  have hne : ia ≠ ib := by
    exact primalAIndex_ne_BIndex i i
  have hsub : ({ia, ib} : Finset (Fin (3 * (T - 1)))) ⊆ Finset.univ := by
    intro j _
    exact Finset.mem_univ j
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun j _ _ ↦ sq_nonneg (z j))
  simpa [vecSq, NCPLVerification.vecSq, primalA, primalB, ia, ib, hne] using hsum

/-- The literal current pulse coordinates of the actual unconstrained value
gradient already carry the full numerical obstruction. -/
theorem explicitValue_current_gradient_sq_lower {T n : Nat}
    (hn : 10 ≤ n) {theta : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (P : UnscaledParameters)
    (hPalpha : P.alpha = C.alpha) (hPbeta : P.beta = C.beta)
    (hPgamma : P.gamma = C.gamma) (hP01 : P.P0 ^ 2 < P.P1 ^ 2)
    (x : UnscaledPrimal T) (i : Fin (T - 1))
    (hpulse : pulseSq x ≤ P.P0 ^ 2)
    (htheta : 0 < theta)
    (hcurrent : 1 + theta ≤ clippedCurrent P x i)
    (hnextLow : clippedNext P x i ≤ 1)
    (hnextLower : -C.deltaS ≤ clippedNext P x i)
    (hb : primalB x i < 1 + theta) :
    (1 / 20 : ℝ) ≤
      vecSq (unscaledTrueGradX (by omega : 0 < n) P x
        (unscaledInnerMaximizer (by omega : 0 < n) x)) := by
  let grad := unscaledTrueGradX (by omega : 0 < n) P x
    (unscaledInnerMaximizer (by omega : 0 < n) x)
  have hga := explicitValue_current_gradA_eq_terminalGa hn C P
    hPalpha hPgamma hP01 x i hpulse hnextLow
  have hgb := explicitValue_current_gradB_eq_terminalGb hn C P
    hPbeta hPgamma hP01 x i hpulse hnextLow
  have hpulseLower := terminal_pulse_gradient_sq_lower
    (a := primalA x i) C htheta hcurrent hnextLower hb
  have hcoords := primalAB_sq_le_vecSq grad i
  change primalA grad i = _ at hga
  change primalB grad i = _ at hgb
  rw [hga, hgb] at hcoords
  exact hpulseLower.trans hcoords

/-- The two small-pulse terminal branches (`b` high, or the three-range
`a,b` argument) combine into a lower bound for the actual value gradient. -/
theorem explicitValue_frontier_gradient_sq_lower {T n : Nat}
    (hn : 10 ≤ n) {theta : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (P : UnscaledParameters)
    (hPtheta : P.theta = theta) (hPtau : P.tauS = tauS P.delta)
    (hPalpha : P.alpha = C.alpha) (hPbeta : P.beta = C.beta)
    (hPgamma : P.gamma = C.gamma) (hP01 : P.P0 ^ 2 < P.P1 ^ 2)
    (heta : 0 ≤ P.eta) (hmu : 0 ≤ P.mu)
    (x : UnscaledPrimal T) (i : Fin (T - 1))
    (hpulse : pulseSq x ≤ P.P0 ^ 2)
    (hcurrent : 1 + theta ≤ clippedCurrent P x i)
    (hnextLow : clippedNext P x i ≤ 1)
    (hnextLower : -C.deltaS ≤ clippedNext P x i) :
    (1 / 20 : ℝ) ≤
      vecSq (unscaledTrueGradX (by omega : 0 < n) P x
        (unscaledInnerMaximizer (by omega : 0 < n) x)) := by
  have htheta : 0 < theta := by simpa [hPtheta] using P.theta_pos
  by_cases hbHigh : 1 + theta ≤ primalB x i
  · have hs := explicitValue_exit_frontier_state_grad_le_neg_one hn C P
      hPtheta hPtau hPbeta heta hmu x i hcurrent hnextLow hbHigh
    let grad := unscaledTrueGradX (by omega : 0 < n) P x
      (unscaledInnerMaximizer (by omega : 0 < n) x)
    have hcoord := coordinate_sq_le_vecSq grad (primalStateIndex i)
    have hs' : grad (primalStateIndex i) ≤ -1 := by
      simpa [grad, primalState] using hs
    have hone : (1 : ℝ) ≤ (grad (primalStateIndex i)) ^ 2 := by
      nlinarith [sq_nonneg (grad (primalStateIndex i) + 1)]
    exact (by norm_num : (1 / 20 : ℝ) ≤ 1) |>.trans <|
      hone.trans hcoord
  · exact explicitValue_current_gradient_sq_lower hn C P hPalpha hPbeta
      hPgamma hP01 x i hpulse htheta hcurrent hnextLow hnextLower
      (lt_of_not_ge hbHigh)

/-! ## The literal low-terminal, small-pulse certificate -/

/-- The coordinate occupied by the paper's last raw memory variable `s_T`. -/
def terminalMemoryIndex {T : Nat} (hT : 2 ≤ T) : Fin (T - 1) :=
  ⟨T - 2, by omega⟩

/-- The paper's raw terminal assumption `s_T ≤ 1` implies the corresponding
clipped terminal state is low. -/
theorem concrete_clipped_terminal_le_one_of_raw_le_one {T : Nat}
    (hT : 2 ≤ T) (x : UnscaledPrimal T)
    (hterminal : primalState x (terminalMemoryIndex hT) ≤ 1) :
    clippedNext concreteUnscaledParameters x (terminalMemoryIndex hT) ≤ 1 := by
  have hone : pi1 concreteUnscaledParameters.delta
      concreteUnscaledParameters.P0 1 = 1 := by
    apply pi1_eq_self concreteUnscaledParameters.delta_pos
      concreteUnscaledParameters.P0_gt_one
    · unfold stateLower
      linarith [concreteUnscaledParameters.delta_pos]
    · norm_num [stateUpper]
  unfold clippedNext
  calc
    pi1 concreteUnscaledParameters.delta concreteUnscaledParameters.P0
        (primalState x (terminalMemoryIndex hT)) ≤
      pi1 concreteUnscaledParameters.delta concreteUnscaledParameters.P0 1 :=
        (pi1_monotone concreteUnscaledParameters.delta_pos
          concreteUnscaledParameters.P0_gt_one) hterminal
    _ = 1 := hone

/-- In the radial core, the literal terminal condition already forces the
actual gradient of the concrete explicit value to have squared norm at
least `1/20`.  All constants and every gradient coordinate in this theorem
are those of the assembled hard instance. -/
theorem concrete_explicitValue_terminal_small_pulse_gradient_sq_lower
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n)
    (x : UnscaledPrimal T)
    (hpulse : pulseSq x ≤ concreteUnscaledParameters.P0 ^ 2)
    (hterminal : primalState x (terminalMemoryIndex hT) ≤ 1) :
    (1 / 20 : ℝ) ≤
      vecSq (unscaledTrueGradX (by omega : 0 < n)
        concreteUnscaledParameters x
        (unscaledInnerMaximizer (by omega : 0 < n) x)) := by
  let grad := unscaledTrueGradX (by omega : 0 < n)
    concreteUnscaledParameters x
    (unscaledInnerMaximizer (by omega : 0 < n) x)
  change (1 / 20 : ℝ) ≤ vecSq grad
  by_contra hsmall
  have hgradSmall : vecSq grad < (1 / 20 : ℝ) := lt_of_not_ge hsmall
  have hgradOne : vecSq grad < 1 := hgradSmall.trans (by norm_num)
  have htransition := no_transition_of_explicitValue_gradient_sq_lt_one
    hn x (by simpa [grad] using hgradOne)
  have hterminalClipped := concrete_clipped_terminal_le_one_of_raw_le_one
    hT x hterminal
  obtain ⟨i, hcurrent, hnext⟩ :=
    exists_concrete_frontier_of_low_and_no_transition x htransition
      (terminalMemoryIndex hT) hterminalClipped
  have hnextLower : -concreteGateThreshold.deltaS ≤
      clippedNext concreteUnscaledParameters x i := by
    simpa [clippedNext, concreteUnscaledParameters, concreteRadialTransition,
      assembleRadialTransition] using
        (concretePi1_mem (primalState x i)).1
  have hP0ltP1 : concreteUnscaledParameters.P0 <
      concreteUnscaledParameters.P1 := by
    change concreteRadialTransition.P0 < concreteRadialTransition.P1
    exact concreteRadialTransition.P0_lt_P1
  have hP0pos : 0 < concreteUnscaledParameters.P0 :=
    lt_trans (by norm_num) concreteUnscaledParameters.P0_gt_one
  have hP1pos : 0 < concreteUnscaledParameters.P1 :=
    hP0pos.trans hP0ltP1
  have hP01 : concreteUnscaledParameters.P0 ^ 2 <
      concreteUnscaledParameters.P1 ^ 2 := by
    nlinarith
  have hlower := explicitValue_frontier_gradient_sq_lower hn
    concreteGateThreshold concreteUnscaledParameters
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) hP01
    (by
      change 0 ≤ concreteRadialTransition.eta
      exact concreteRadialTransition.eta_pos.le)
    concreteGateThreshold.mu_pos.le x i hpulse hcurrent hnext hnextLower
  exact (not_lt_of_ge (by simpa [grad] using hlower)) hgradSmall

/-! ## Pulse projection and radial pairing -/

/-- The block-coordinate equivalence `(i,a/b/s) ↔ 3 i + a/b/s` for the
separated primal space. -/
def unscaledPrimalBlockEquiv (T : Nat) :
    (Fin (T - 1) × Fin 3) ≃ Fin (3 * (T - 1)) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm (T - 1) 3))

@[simp] theorem unscaledPrimalBlockEquiv_a {T : Nat}
    (i : Fin (T - 1)) :
    unscaledPrimalBlockEquiv T (i, ⟨0, by omega⟩) = primalAIndex i := by
  apply Fin.ext
  simp [unscaledPrimalBlockEquiv, finProdFinEquiv, primalAIndex]

@[simp] theorem unscaledPrimalBlockEquiv_b {T : Nat}
    (i : Fin (T - 1)) :
    unscaledPrimalBlockEquiv T (i, ⟨1, by omega⟩) = primalBIndex i := by
  apply Fin.ext
  simp [unscaledPrimalBlockEquiv, finProdFinEquiv, primalBIndex]
  omega

@[simp] theorem unscaledPrimalBlockEquiv_state {T : Nat}
    (i : Fin (T - 1)) :
    unscaledPrimalBlockEquiv T (i, ⟨2, by omega⟩) = primalStateIndex i := by
  apply Fin.ext
  simp [unscaledPrimalBlockEquiv, finProdFinEquiv, primalStateIndex]
  omega

/-- Orthogonal projection of a primal vector onto its pulse coordinates;
all memory coordinates are set to zero. -/
def pulseOnly {T : Nat} (x : UnscaledPrimal T) : UnscaledPrimal T :=
  fun j ↦
    let ik := (unscaledPrimalBlockEquiv T).symm j
    if ik.2.val = 0 then primalA x ik.1
    else if ik.2.val = 1 then primalB x ik.1
    else 0

@[simp] theorem pulseOnly_primalA {T : Nat} (x : UnscaledPrimal T)
    (i : Fin (T - 1)) : primalA (pulseOnly x) i = primalA x i := by
  change pulseOnly x (primalAIndex i) = x (primalAIndex i)
  conv_lhs => rw [← unscaledPrimalBlockEquiv_a i]
  simp [pulseOnly, primalA]

@[simp] theorem pulseOnly_primalB {T : Nat} (x : UnscaledPrimal T)
    (i : Fin (T - 1)) : primalB (pulseOnly x) i = primalB x i := by
  change pulseOnly x (primalBIndex i) = x (primalBIndex i)
  conv_lhs => rw [← unscaledPrimalBlockEquiv_b i]
  simp [pulseOnly, primalB]

@[simp] theorem pulseOnly_primalState {T : Nat} (x : UnscaledPrimal T)
    (i : Fin (T - 1)) : primalState (pulseOnly x) i = 0 := by
  change pulseOnly x (primalStateIndex i) = 0
  conv_lhs => rw [← unscaledPrimalBlockEquiv_state i]
  simp [pulseOnly]

/-- The squared norm of the pulse projection is exactly the paper's
`pulseSq`; no memory coordinate is included. -/
theorem vecSq_pulseOnly {T : Nat} (x : UnscaledPrimal T) :
    vecSq (pulseOnly x) = pulseSq x := by
  unfold vecSq NCPLVerification.vecSq pulseSq
  calc
    (∑ j : Fin (3 * (T - 1)), pulseOnly x j ^ 2) =
        ∑ ik : Fin (T - 1) × Fin 3,
          pulseOnly x (unscaledPrimalBlockEquiv T ik) ^ 2 := by
      symm
      exact Equiv.sum_comp (unscaledPrimalBlockEquiv T)
        (fun j : Fin (3 * (T - 1)) ↦ pulseOnly x j ^ 2)
    _ = ∑ i : Fin (T - 1),
        ∑ k : Fin 3, pulseOnly x (unscaledPrimalBlockEquiv T (i, k)) ^ 2 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ i : Fin (T - 1),
        ((primalA x i) ^ 2 + (primalB x i) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.sum_univ_three]
      simp [pulseOnly, primalA, primalB]

/-- The radial pairing with the pulse projection is the blockwise pulse
pairing used in the paper. -/
theorem radialDot_pulseOnly {T : Nat} (x z : UnscaledPrimal T) :
    radialDot (pulseOnly x) z =
      ∑ i : Fin (T - 1),
        (primalA x i * primalA z i + primalB x i * primalB z i) := by
  unfold radialDot
  calc
    (∑ j : Fin (3 * (T - 1)), pulseOnly x j * z j) =
        ∑ ik : Fin (T - 1) × Fin 3,
          pulseOnly x (unscaledPrimalBlockEquiv T ik) *
            z (unscaledPrimalBlockEquiv T ik) := by
      symm
      exact Equiv.sum_comp (unscaledPrimalBlockEquiv T)
        (fun j : Fin (3 * (T - 1)) ↦ pulseOnly x j * z j)
    _ = ∑ i : Fin (T - 1), ∑ k : Fin 3,
        pulseOnly x (unscaledPrimalBlockEquiv T (i, k)) *
          z (unscaledPrimalBlockEquiv T (i, k)) := by
      rw [Fintype.sum_prod_type]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Fin.sum_univ_three]
      simp [pulseOnly, primalA, primalB]
      have ha : unscaledPrimalBlockEquiv T (i, (0 : Fin 3)) =
          primalAIndex i := by
        apply Fin.ext
        simp [unscaledPrimalBlockEquiv, finProdFinEquiv, primalAIndex]
      have hb : unscaledPrimalBlockEquiv T (i, (1 : Fin 3)) =
          primalBIndex i := by
        apply Fin.ext
        simp [unscaledPrimalBlockEquiv, finProdFinEquiv, primalBIndex]
        omega
      have hs : unscaledPrimalBlockEquiv T (i, (2 : Fin 3)) =
          primalStateIndex i := by
        apply Fin.ext
        simp [unscaledPrimalBlockEquiv, finProdFinEquiv, primalStateIndex]
        omega
      rw [ha, hb]

/-- Radial pairing contributed by the entrance/exit pulses in one block. -/
def outerPulseRadialTerm {T : Nat} (P : UnscaledParameters)
    (x : UnscaledPrimal T) (i : Fin (T - 1)) : ℝ :=
  primalA x i * entrancePulseDerivA P.alpha P.theta P.P0
      (clippedCurrent P x i) (clippedNext P x i) (primalA x i) +
    primalB x i * exitPulseDerivB P.beta P.theta
      (clippedCurrent P x i) (primalB x i) (clippedNext P x i)

/-- After substituting the literal Green maximizer, the radial pairing in
one pulse block splits exactly into the outer remainder, the positive
effective link, and the radial-budget derivative. -/
theorem explicitValue_pulse_radial_block_eq {T n : Nat}
    (hn : 10 ≤ n) (P : UnscaledParameters) (x : UnscaledPrimal T)
    (i : Fin (T - 1)) :
    let grad := unscaledTrueGradX (by omega : 0 < n) P x
      (unscaledInnerMaximizer (by omega : 0 < n) x)
    primalA x i * primalA grad i + primalB x i * primalB grad i =
      outerPulseRadialTerm P x i +
      12 * (primalA x i - primalB x i / 2) ^ 2 +
      2 * P.gamma * ((primalA x i) ^ 2 + (primalB x i) ^ 2) +
      2 * Sigma3Deriv P.P0 P.P1 P.K (pulseSq x) *
        ((primalA x i) ^ 2 + (primalB x i) ^ 2) := by
  dsimp only
  have hA := innerGradA_at_innerMaximizer_transfer hn
    (primalA x i) (primalB x i)
  have hB := innerGradB_at_innerMaximizer_transfer hn
    (primalA x i) (primalB x i)
  rw [primalA_unscaledTrueGradX, primalB_unscaledTrueGradX]
  unfold serializedGradA serializedGradB outerPulseRadialTerm
  simp only [serializedClippedCurrent_serializeUnscaled,
    serializedClippedNext_serializeUnscaled, serializedA_serializeUnscaled,
    serializedB_serializeUnscaled, serializedDualBlock_serializeUnscaled,
    serializedPulseSq_serializeUnscaled]
  rw [dualBlock_unscaledInnerMaximizer]
  ring_nf at hA hB ⊢
  linear_combination (primalA x i) * hA + (primalB x i) * hB

/-- Summing the block identity gives the exact radial pairing of the true
explicit-value gradient. -/
theorem explicitValue_pulse_radial_pairing_eq {T n : Nat}
    (hn : 10 ≤ n) (P : UnscaledParameters) (x : UnscaledPrimal T) :
    let grad := unscaledTrueGradX (by omega : 0 < n) P x
      (unscaledInnerMaximizer (by omega : 0 < n) x)
    radialDot (pulseOnly x) grad =
      (∑ i : Fin (T - 1), outerPulseRadialTerm P x i) +
      (∑ i : Fin (T - 1),
        12 * (primalA x i - primalB x i / 2) ^ 2) +
      2 * P.gamma * pulseSq x +
      2 * Sigma3Deriv P.P0 P.P1 P.K (pulseSq x) * pulseSq x := by
  dsimp only
  rw [radialDot_pulseOnly]
  calc
    (∑ i : Fin (T - 1),
        (primalA x i *
          primalA
            (unscaledTrueGradX (by omega : 0 < n) P x
              (unscaledInnerMaximizer (by omega : 0 < n) x)) i +
        primalB x i *
          primalB
            (unscaledTrueGradX (by omega : 0 < n) P x
              (unscaledInnerMaximizer (by omega : 0 < n) x)) i)) =
      ∑ i : Fin (T - 1),
        (outerPulseRadialTerm P x i +
          12 * (primalA x i - primalB x i / 2) ^ 2 +
          2 * P.gamma * ((primalA x i) ^ 2 + (primalB x i) ^ 2) +
          2 * Sigma3Deriv P.P0 P.P1 P.K (pulseSq x) *
            ((primalA x i) ^ 2 + (primalB x i) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact explicitValue_pulse_radial_block_eq hn P x i
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      unfold pulseSq
      rw [Finset.mul_sum, Finset.mul_sum]

theorem primalAB_sq_le_pulseSq {T : Nat} (x : UnscaledPrimal T)
    (i : Fin (T - 1)) :
    (primalA x i) ^ 2 + (primalB x i) ^ 2 ≤ pulseSq x := by
  unfold pulseSq
  exact Finset.single_le_sum
    (fun j _ ↦ add_nonneg (sq_nonneg (primalA x j))
      (sq_nonneg (primalB x j))) (Finset.mem_univ i)

theorem outerPulseRadialTerm_eq_zero_of_next_high {T : Nat}
    (P : UnscaledParameters) (x : UnscaledPrimal T) (i : Fin (T - 1))
    (hnext : 1 + P.theta ≤ clippedNext P x i) :
    outerPulseRadialTerm P x i = 0 := by
  unfold outerPulseRadialTerm entrancePulseDerivA exitPulseDerivB
  rw [Lambda2_eq_zero_of_one_add_le P.theta_pos hnext,
    exitRelay_eq_zero_of_high P.theta_pos hnext]
  ring

theorem outerPulseRadialTerm_eq_zero_of_current_low {T : Nat}
    (P : UnscaledParameters) (x : UnscaledPrimal T) (i : Fin (T - 1))
    (hcurrent : clippedCurrent P x i ≤ 1) :
    outerPulseRadialTerm P x i = 0 := by
  unfold outerPulseRadialTerm entrancePulseDerivA exitPulseDerivB
  rw [Psi2_eq_zero_of_le_one hcurrent]
  ring

/-- Under a full concrete frontier, all outer pulse radial terms except the
current block vanish exactly. -/
theorem concrete_sum_outerPulseRadialTerm_eq_frontier {T : Nat}
    (x : UnscaledPrimal T) (i : Fin (T - 1))
    (hbefore : ∀ l : Fin (T - 1), l.val < i.val →
      1 + concreteTheta ≤ clippedNext concreteUnscaledParameters x l)
    (hafter : ∀ l : Fin (T - 1), i.val ≤ l.val →
      clippedNext concreteUnscaledParameters x l ≤ 1) :
    (∑ l : Fin (T - 1),
      outerPulseRadialTerm concreteUnscaledParameters x l) =
        outerPulseRadialTerm concreteUnscaledParameters x i := by
  apply Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
  intro l _ hli
  have hval : l.val ≠ i.val := by
    intro h
    apply hli
    exact Fin.ext h
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · apply outerPulseRadialTerm_eq_zero_of_next_high
    simpa [concreteUnscaledParameters] using hbefore l hlt
  · apply outerPulseRadialTerm_eq_zero_of_current_low
    have hl0 : l.val ≠ 0 := by omega
    let p : Fin (T - 1) := ⟨l.val - 1, by omega⟩
    have hpLow := hafter p (by dsimp [p]; omega)
    simpa [clippedCurrent, clippedNext, currentState, p, hl0] using hpLow

/-- A low raw terminal coordinate and an actual explicit-value gradient
below one yield the complete concrete frontier used in both radial
arguments. -/
theorem concrete_full_frontier_of_terminal_gradient_sq_lt_one
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n) (x : UnscaledPrimal T)
    (hgrad : vecSq
      (unscaledTrueGradX (by omega : 0 < n) concreteUnscaledParameters x
        (unscaledInnerMaximizer (by omega : 0 < n) x)) < 1)
    (hterminal : primalState x (terminalMemoryIndex hT) ≤ 1) :
    ∃ i : Fin (T - 1),
      1 + concreteTheta ≤ clippedCurrent concreteUnscaledParameters x i ∧
      clippedNext concreteUnscaledParameters x i ≤ 1 ∧
      (∀ l : Fin (T - 1), l.val < i.val →
        1 + concreteTheta ≤ clippedNext concreteUnscaledParameters x l) ∧
      (∀ l : Fin (T - 1), i.val ≤ l.val →
        clippedNext concreteUnscaledParameters x l ≤ 1) := by
  have htransition := no_transition_of_explicitValue_gradient_sq_lt_one
    hn x hgrad
  have hnoLowHigh := no_low_to_high_of_explicitValue_gradient_sq_lt_one
    hn concreteGateThreshold concreteUnscaledParameters
    (by rfl) (by rfl) (by rfl)
    (by
      change 0 ≤ concreteRadialTransition.eta
      exact concreteRadialTransition.eta_pos.le)
    concreteGateThreshold.beta_pos.le x hgrad
  have hterminalClipped := concrete_clipped_terminal_le_one_of_raw_le_one
    hT x hterminal
  exact exists_concrete_full_frontier_of_low x htransition hnoLowHigh
    (terminalMemoryIndex hT) hterminalClipped

/-! ## The large-pulse branch -/

/-- On a complete concrete frontier, once the pulse radius has reached
`P0`, the radial pairing forces the actual explicit-value gradient to grow
at least linearly in the pulse radius.  This is the Cauchy--Schwarz step of
the large-pulse argument, stated directly as a squared-norm inequality. -/
theorem concrete_explicitValue_large_pulse_gradient_sq_ge_gamma_sq_mul_pulse
    {T n : Nat} (hn : 10 ≤ n) (x : UnscaledPrimal T)
    (i : Fin (T - 1))
    (hpulse : concreteUnscaledParameters.P0 ^ 2 ≤ pulseSq x)
    (hnext : clippedNext concreteUnscaledParameters x i ≤ 1)
    (hbefore : ∀ l : Fin (T - 1), l.val < i.val →
      1 + concreteTheta ≤ clippedNext concreteUnscaledParameters x l)
    (hafter : ∀ l : Fin (T - 1), i.val ≤ l.val →
      clippedNext concreteUnscaledParameters x l ≤ 1) :
    concreteGateThreshold.gamma ^ 2 * pulseSq x ≤
      vecSq (unscaledTrueGradX (by omega : 0 < n)
        concreteUnscaledParameters x
        (unscaledInnerMaximizer (by omega : 0 < n) x)) := by
  let grad := unscaledTrueGradX (by omega : 0 < n)
    concreteUnscaledParameters x
    (unscaledInnerMaximizer (by omega : 0 < n) x)
  let dot := radialDot (pulseOnly x) grad
  let blockSq := (primalA x i) ^ 2 + (primalB x i) ^ 2
  let r := Real.sqrt (pulseSq x)
  have hpulseNonneg : 0 ≤ pulseSq x := by
    rw [← vecSq_pulseOnly]
    exact vecSq_nonneg (pulseOnly x)
  have hrNonneg : 0 ≤ r := by
    exact Real.sqrt_nonneg _
  have hrSq : r ^ 2 = pulseSq x := by
    exact Real.sq_sqrt hpulseNonneg
  have hP0pos : 0 < concreteUnscaledParameters.P0 :=
    lt_trans (by norm_num) concreteUnscaledParameters.P0_gt_one
  have hrP0 : concreteUnscaledParameters.P0 ≤ r := by
    nlinarith
  have hnextLower : -concreteGateThreshold.deltaS ≤
      clippedNext concreteUnscaledParameters x i := by
    simpa [clippedNext, concreteUnscaledParameters, concreteRadialTransition,
      assembleRadialTransition] using
        (concretePi1_mem (primalState x i)).1
  have houterAbs :
      |outerPulseRadialTerm concreteUnscaledParameters x i| ≤
        concreteCp * Real.sqrt blockSq := by
    simpa [outerPulseRadialTerm, concreteUnscaledParameters] using
      (concreteCp_dominates_pulse_remainder
        (current := clippedCurrent concreteUnscaledParameters x i)
        (next := clippedNext concreteUnscaledParameters x i)
        (a := primalA x i) (b := primalB x i)
        concreteUnscaledParameters.P0 hnextLower hnext)
  have hblock : blockSq ≤ pulseSq x := by
    exact primalAB_sq_le_pulseSq x i
  have hsqrtBlock : Real.sqrt blockSq ≤ r := by
    exact Real.sqrt_le_sqrt hblock
  have houter : -concreteCp * r ≤
      outerPulseRadialTerm concreteUnscaledParameters x i := by
    calc
      -concreteCp * r ≤ -concreteCp * Real.sqrt blockSq := by
        have hmul := mul_le_mul_of_nonneg_left hsqrtBlock concreteCp_pos.le
        nlinarith
      _ ≤ outerPulseRadialTerm concreteUnscaledParameters x i :=
        by simpa only [neg_mul] using (abs_le.mp houterAbs).1
  have houterSum := concrete_sum_outerPulseRadialTerm_eq_frontier
    x i hbefore hafter
  have hlink : 0 ≤ ∑ l : Fin (T - 1),
      12 * (primalA x l - primalB x l / 2) ^ 2 := by
    exact Finset.sum_nonneg (fun l _ ↦
      mul_nonneg (by norm_num) (sq_nonneg _))
  have hK : 0 ≤ concreteUnscaledParameters.K := by
    change 0 ≤ concreteRadialTransition.K
    linarith [concreteRadialTransition.K_gt, concreteCq_pos]
  have hsigma : 0 ≤ Sigma3Deriv concreteUnscaledParameters.P0
      concreteUnscaledParameters.P1 concreteUnscaledParameters.K
      (pulseSq x) :=
    (Sigma3Deriv_mem hK).1
  have hradial : 0 ≤
      2 * Sigma3Deriv concreteUnscaledParameters.P0
          concreteUnscaledParameters.P1 concreteUnscaledParameters.K
          (pulseSq x) * pulseSq x :=
    mul_nonneg (mul_nonneg (by norm_num) hsigma) hpulseNonneg
  have hpair :
      dot =
        (∑ l : Fin (T - 1),
          outerPulseRadialTerm concreteUnscaledParameters x l) +
        (∑ l : Fin (T - 1),
          12 * (primalA x l - primalB x l / 2) ^ 2) +
        2 * concreteGateThreshold.gamma * pulseSq x +
        2 * Sigma3Deriv concreteUnscaledParameters.P0
          concreteUnscaledParameters.P1 concreteUnscaledParameters.K
          (pulseSq x) * pulseSq x := by
    simpa [dot, grad, concreteUnscaledParameters] using
      (explicitValue_pulse_radial_pairing_eq hn
        concreteUnscaledParameters x)
  have hdotLower :
      2 * concreteGateThreshold.gamma * pulseSq x - concreteCp * r ≤ dot := by
    rw [houterSum] at hpair
    linarith
  have hmargin := concreteRadialTransition.P0_margin r hrP0
  have hdotGamma :
      concreteGateThreshold.gamma * pulseSq x ≤ dot := by
    rw [hrSq] at hmargin
    exact hmargin.trans hdotLower
  have hcauchy : dot ^ 2 ≤ pulseSq x * vecSq grad := by
    have h := radialDot_sq_le (pulseOnly x) grad
    rw [vecSq_pulseOnly] at h
    simpa [dot] using h
  have hgammaPulseNonneg :
      0 ≤ concreteGateThreshold.gamma * pulseSq x :=
    mul_nonneg concreteGateThreshold.gamma_pos.le hpulseNonneg
  have hdotNonneg : 0 ≤ dot := hgammaPulseNonneg.trans hdotGamma
  have hfactor : 0 ≤
      (dot - concreteGateThreshold.gamma * pulseSq x) *
        (dot + concreteGateThreshold.gamma * pulseSq x) :=
    mul_nonneg (sub_nonneg.mpr hdotGamma)
      (add_nonneg hdotNonneg hgammaPulseNonneg)
  have hsqLower :
      (concreteGateThreshold.gamma * pulseSq x) ^ 2 ≤ dot ^ 2 := by
    nlinarith
  have hscaled :
      pulseSq x * (concreteGateThreshold.gamma ^ 2 * pulseSq x) ≤
        pulseSq x * vecSq grad := by
    calc
      pulseSq x * (concreteGateThreshold.gamma ^ 2 * pulseSq x) =
          (concreteGateThreshold.gamma * pulseSq x) ^ 2 := by ring
      _ ≤ dot ^ 2 := hsqLower
      _ ≤ pulseSq x * vecSq grad := hcauchy
  have hP0sqPos : 0 < concreteUnscaledParameters.P0 ^ 2 := by
    simpa [pow_two] using mul_pos hP0pos hP0pos
  have hpulsePos : 0 < pulseSq x := hP0sqPos.trans_le hpulse
  exact le_of_mul_le_mul_left hscaled hpulsePos

/-- A radius-independent consequence of the large-pulse estimate. -/
theorem concrete_explicitValue_large_pulse_gradient_sq_lower_of_frontier
    {T n : Nat} (hn : 10 ≤ n) (x : UnscaledPrimal T)
    (i : Fin (T - 1))
    (hpulse : concreteUnscaledParameters.P0 ^ 2 ≤ pulseSq x)
    (hnext : clippedNext concreteUnscaledParameters x i ≤ 1)
    (hbefore : ∀ l : Fin (T - 1), l.val < i.val →
      1 + concreteTheta ≤ clippedNext concreteUnscaledParameters x l)
    (hafter : ∀ l : Fin (T - 1), i.val ≤ l.val →
      clippedNext concreteUnscaledParameters x l ≤ 1) :
    (concreteGateThreshold.gamma * concreteUnscaledParameters.P0) ^ 2 ≤
      vecSq (unscaledTrueGradX (by omega : 0 < n)
        concreteUnscaledParameters x
        (unscaledInnerMaximizer (by omega : 0 < n) x)) := by
  have hlarge :=
    concrete_explicitValue_large_pulse_gradient_sq_ge_gamma_sq_mul_pulse
      hn x i hpulse hnext hbefore hafter
  calc
    (concreteGateThreshold.gamma * concreteUnscaledParameters.P0) ^ 2 =
        concreteGateThreshold.gamma ^ 2 *
          concreteUnscaledParameters.P0 ^ 2 := by ring
    _ ≤ concreteGateThreshold.gamma ^ 2 * pulseSq x :=
      mul_le_mul_of_nonneg_left hpulse (sq_nonneg _)
    _ ≤ _ := hlarge

/-- A completely explicit positive lower-bound constant that works in all
three branches: the radial core, an already-large gradient, and the
large-pulse radial regime. -/
def concreteTerminalGradientSqLower : ℝ :=
  min (1 / 20) (min 1
    ((concreteGateThreshold.gamma * concreteUnscaledParameters.P0) ^ 2))

theorem concreteTerminalGradientSqLower_pos :
    0 < concreteTerminalGradientSqLower := by
  unfold concreteTerminalGradientSqLower
  exact lt_min (by norm_num) <| lt_min (by norm_num) <|
    sq_pos_of_pos <| mul_pos concreteGateThreshold.gamma_pos <|
      lt_trans (by norm_num) concreteUnscaledParameters.P0_gt_one

/-- The literal raw terminal condition forces a positive squared-norm
lower bound for the actual gradient of the concrete explicit value, with
no pulse-radius hypothesis.  The proof exhausts the small-pulse,
already-large-gradient, and large-pulse frontier cases. -/
theorem concrete_explicitValue_terminal_gradient_sq_lower
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n)
    (x : UnscaledPrimal T)
    (hterminal : primalState x (terminalMemoryIndex hT) ≤ 1) :
    concreteTerminalGradientSqLower ≤
      vecSq (unscaledTrueGradX (by omega : 0 < n)
        concreteUnscaledParameters x
        (unscaledInnerMaximizer (by omega : 0 < n) x)) := by
  let grad := unscaledTrueGradX (by omega : 0 < n)
    concreteUnscaledParameters x
    (unscaledInnerMaximizer (by omega : 0 < n) x)
  by_cases hpulse :
      pulseSq x ≤ concreteUnscaledParameters.P0 ^ 2
  · have hsmall :=
      concrete_explicitValue_terminal_small_pulse_gradient_sq_lower
        hT hn x hpulse hterminal
    calc
      concreteTerminalGradientSqLower ≤ (1 / 20 : ℝ) := by
        exact min_le_left _ _
      _ ≤ vecSq grad := by simpa [grad] using hsmall
  · have hpulseLarge : concreteUnscaledParameters.P0 ^ 2 ≤ pulseSq x :=
      le_of_not_ge hpulse
    by_cases hgradOne : 1 ≤ vecSq grad
    · calc
        concreteTerminalGradientSqLower ≤ 1 := by
          exact (min_le_right _ _).trans (min_le_left _ _)
        _ ≤ vecSq grad := hgradOne
    · have hgradLt : vecSq grad < 1 := lt_of_not_ge hgradOne
      obtain ⟨i, _hcurrent, hnext, hbefore, hafter⟩ :=
        concrete_full_frontier_of_terminal_gradient_sq_lt_one
          hT hn x (by simpa [grad] using hgradLt) hterminal
      have hlarge :=
        concrete_explicitValue_large_pulse_gradient_sq_lower_of_frontier
          hn x i hpulseLarge hnext hbefore hafter
      calc
        concreteTerminalGradientSqLower ≤
            (concreteGateThreshold.gamma *
              concreteUnscaledParameters.P0) ^ 2 := by
          exact (min_le_right _ _).trans (min_le_right _ _)
        _ ≤ vecSq grad := by simpa [grad] using hlarge

/-- The corresponding derivative certificate for the genuine explicit
value, now free of any pulse-size restriction. -/
theorem concrete_explicitValue_terminal_gradient_certificate
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n)
    (x : UnscaledPrimal T)
    (hterminal : primalState x (terminalMemoryIndex hT) ≤ 1) :
    let grad := unscaledTrueGradX (by omega : 0 < n)
      concreteUnscaledParameters x
      (unscaledInnerMaximizer (by omega : 0 < n) x)
    NCPLVerification.HasEVecFDerivAt
        (unscaledExplicitValue (T := T) (by omega : 0 < n)
          concreteUnscaledParameters)
        (NCPLVerification.evecDot grad) x ∧
      concreteTerminalGradientSqLower ≤ vecSq grad := by
  dsimp only
  exact ⟨hasEVecFDerivAt_unscaledExplicitValue hn
      concreteUnscaledParameters x,
    concrete_explicitValue_terminal_gradient_sq_lower
      hT hn x hterminal⟩

/-! ## Envelope identification for the restricted value -/

/-- The true primal partial gradient is the actual Fréchet derivative when
the dual argument is held fixed. -/
theorem hasEVecFDerivAt_unscaledObjective_fixedDual
    {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (x : UnscaledPrimal T) (y : UnscaledDual T n) :
    NCPLVerification.HasEVecFDerivAt
      (fun z : UnscaledPrimal T ↦ unscaledObjective hn P z y)
      (NCPLVerification.evecDot (unscaledTrueGradX hn P x y)) x := by
  letI : AddCommGroup (UnscaledPrimal T) :=
    Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (UnscaledPrimal T) := Pi.normedSpace.toModule
  letI : TopologicalSpace (UnscaledPrimal T) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let g := serializedTrueGradient hn P (serializeUnscaled x y)
  let L := (NCPLVerification.evecDot g).comp
    (serializeUnscaledCLM (T := T) (n := n))
  let Lin := ContinuousLinearMap.inl ℝ (UnscaledPrimal T) (UnscaledDual T n)
  let Lx := L.comp Lin
  have hjoint : HasFDerivAt
      (Function.uncurry (unscaledObjective (T := T) hn P)) L (x, y) := by
    simpa [L, g] using unscaledObjective_hasFDerivAt
      (T := T) hn P x y
  have hgraph : HasFDerivAt (fun z : UnscaledPrimal T ↦ (z, y)) Lin x := by
    have h : HasFDerivAt (fun z : UnscaledPrimal T ↦ Lin z + (0, y))
        Lin x := Lin.hasFDerivAt.add_const (0, y)
    convert h using 1
    funext z
    simp [Lin]
  have hcomp := hjoint.comp x hgraph
  have hcoord : Lx = NCPLVerification.evecDot
      (NCPLVerification.continuousLinearMapCoordinates Lx) := by
    ext h
    rw [NCPLVerification.continuousLinearMap_apply_eq_coordinates]
    rfl
  have hgrad : unscaledTrueGradX (T := T) hn P x y =
      NCPLVerification.continuousLinearMapCoordinates Lx := by
    rfl
  change HasFDerivAt (fun z : UnscaledPrimal T ↦
    unscaledObjective hn P z y) Lx x at hcomp
  rw [hcoord, ← hgrad] at hcomp
  exact hcomp

/-- A differentiable pointwise maximum has the same gradient as every
active smooth section.  Here this elementary envelope statement is proved
from the global-maximizer inequality and Fermat's theorem, rather than
postulated as a Danskin rule. -/
theorem restrictedValue_gradient_eq_at_maximizer
    {T n : Nat} (hn : 0 < n) (P : UnscaledParameters) {D : ℝ}
    (hD : 0 ≤ D) (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (hy : IsMaximizerOn (diameterBall (n * (T - 1)) D)
      (unscaledObjective hn P) x y)
    (g : UnscaledPrimal T)
    (hvalue : NCPLVerification.HasEVecFDerivAt
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) hn P))
      (NCPLVerification.evecDot g) x) :
    g = unscaledTrueGradX hn P x y := by
  let phi := ValueOn (diameterBall (n * (T - 1)) D)
    (unscaledObjective (T := T) hn P)
  let secFun := fun z : UnscaledPrimal T ↦ unscaledObjective hn P z y
  have hsection : NCPLVerification.HasEVecFDerivAt secFun
      (NCPLVerification.evecDot (unscaledTrueGradX hn P x y)) x := by
    simpa [secFun] using hasEVecFDerivAt_unscaledObjective_fixedDual
      hn P x y
  have hdiff : HasFDerivAt (fun z ↦ phi z - secFun z)
      (NCPLVerification.evecDot g -
        NCPLVerification.evecDot (unscaledTrueGradX hn P x y)) x := by
    exact hvalue.sub hsection
  have hattain : ∀ z : UnscaledPrimal T, ∃ w,
      IsMaximizerOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective hn P) z w := by
    intro z
    exact unscaledObjective_maximum_attained hn P hD z
  have hmin : IsLocalMin (fun z ↦ phi z - secFun z) x := by
    apply Filter.Eventually.of_forall
    intro z
    have hzle : secFun z ≤ phi z := by
      obtain ⟨w, hw⟩ := hattain z
      rw [show phi z = unscaledObjective hn P z w by
        exact value_eq_of_isMaximizerOn hw]
      exact hw.2 y hy.1
    have hxeq : phi x = secFun x := by
      exact value_eq_of_isMaximizerOn hy
    change phi x - secFun x ≤ phi z - secFun z
    rw [hxeq]
    simpa only [sub_self] using sub_nonneg.mpr hzle
  have hzero := hmin.hasFDerivAt_eq_zero hdiff
  have hmaps : NCPLVerification.evecDot g =
      NCPLVerification.evecDot (unscaledTrueGradX hn P x y) :=
    sub_eq_zero.mp hzero
  funext j
  have hj := congrArg
    (fun L : UnscaledPrimal T →L[ℝ] ℝ ↦
      L (NCPLVerification.evecBasis j)) hmaps
  simpa [NCPLVerification.evecDot_apply, NCPLVerification.evecBasis] using hj

/-- Memory partials do not contain any dual coordinate. -/
theorem primalState_unscaledTrueGradX_independent_dual
    {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (x : UnscaledPrimal T) (y z : UnscaledDual T n)
    (i : Fin (T - 1)) :
    primalState (unscaledTrueGradX hn P x y) i =
      primalState (unscaledTrueGradX hn P x z) i := by
  rw [primalState_unscaledTrueGradX, primalState_unscaledTrueGradX]
  unfold serializedGradState serializedNextStateContribution
  split_ifs <;>
    simp only [serializedState_serializeUnscaled,
      serializedClippedCurrent_serializeUnscaled,
      serializedClippedNext_serializeUnscaled,
      serializedA_serializeUnscaled, serializedB_serializeUnscaled]

/-- The transition exclusion therefore holds for the primal partial at an
arbitrary restricted maximizer, not only at the Green maximizer. -/
theorem no_transition_of_section_gradient_sq_lt_one
    {T n : Nat} (hn : 10 ≤ n) (x : UnscaledPrimal T)
    (y : UnscaledDual T n)
    (hgrad : vecSq (unscaledTrueGradX (by omega : 0 < n)
      concreteUnscaledParameters x y) < 1) :
    ∀ i : Fin (T - 1),
      clippedNext concreteUnscaledParameters x i ≤ 1 ∨
        1 + concreteTheta ≤ clippedNext concreteUnscaledParameters x i := by
  intro i
  let g := unscaledTrueGradX (by omega : 0 < n)
    concreteUnscaledParameters x y
  let ge := unscaledTrueGradX (by omega : 0 < n)
    concreteUnscaledParameters x
    (unscaledInnerMaximizer (by omega : 0 < n) x)
  by_cases hlow : clippedNext concreteUnscaledParameters x i ≤ 1
  · exact Or.inl hlow
  · right
    by_contra hhigh
    have hs0 := explicitValue_transition_state_grad_le_neg_one hn x i
      (le_of_lt (lt_of_not_ge hlow)) (le_of_not_ge hhigh)
    have hs : primalState g i ≤ -1 := by
      rw [primalState_unscaledTrueGradX_independent_dual
        (by omega : 0 < n) concreteUnscaledParameters x y
        (unscaledInnerMaximizer (by omega : 0 < n) x) i]
      simpa [ge] using hs0
    have hcoord := coordinate_sq_le_vecSq g (primalStateIndex i)
    have hs' : g (primalStateIndex i) ≤ -1 := by
      simpa [g, primalState] using hs
    have hone : (1 : ℝ) ≤ (g (primalStateIndex i)) ^ 2 := by
      nlinarith [sq_nonneg (g (primalStateIndex i) + 1)]
    exact (not_lt_of_ge (hone.trans hcoord)) (by simpa [g] using hgrad)

/-- The low-to-high exclusion likewise transfers to an arbitrary active
dual maximizer. -/
theorem no_low_to_high_of_section_gradient_sq_lt_one
    {T n : Nat} (hn : 10 ≤ n) (x : UnscaledPrimal T)
    (y : UnscaledDual T n)
    (hgrad : vecSq (unscaledTrueGradX (by omega : 0 < n)
      concreteUnscaledParameters x y) < 1) :
    ∀ (i : Fin (T - 1)) (hi : i.val + 1 < T - 1),
      clippedNext concreteUnscaledParameters x i ≤ 1 →
      ¬ 1 + concreteTheta ≤
        clippedNext concreteUnscaledParameters x ⟨i.val + 1, hi⟩ := by
  intro i hi hlow hhigh
  let g := unscaledTrueGradX (by omega : 0 < n)
    concreteUnscaledParameters x y
  have hs0 := explicitValue_low_to_high_state_grad_le_neg_one hn
    concreteGateThreshold concreteUnscaledParameters
    (by rfl) (by rfl) (by rfl)
    (by
      change 0 ≤ concreteRadialTransition.eta
      exact concreteRadialTransition.eta_pos.le)
    concreteGateThreshold.beta_pos.le x i hi hlow hhigh
  have hs : primalState g i ≤ -1 := by
    rw [primalState_unscaledTrueGradX_independent_dual
      (by omega : 0 < n) concreteUnscaledParameters x y
      (unscaledInnerMaximizer (by omega : 0 < n) x) i]
    simpa [g] using hs0
  have hcoord := coordinate_sq_le_vecSq g (primalStateIndex i)
  have hs' : g (primalStateIndex i) ≤ -1 := by
    simpa [g, primalState] using hs
  have hone : (1 : ℝ) ≤ (g (primalStateIndex i)) ^ 2 := by
    nlinarith [sq_nonneg (g (primalStateIndex i) + 1)]
  exact (not_lt_of_ge (hone.trans hcoord)) (by simpa [g] using hgrad)

/-- The complete frontier for an arbitrary active restricted maximizer. -/
theorem concrete_full_frontier_of_terminal_section_gradient_sq_lt_one
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n) (x : UnscaledPrimal T)
    (y : UnscaledDual T n)
    (hgrad : vecSq (unscaledTrueGradX (by omega : 0 < n)
      concreteUnscaledParameters x y) < 1)
    (hterminal : primalState x (terminalMemoryIndex hT) ≤ 1) :
    ∃ i : Fin (T - 1),
      1 + concreteTheta ≤ clippedCurrent concreteUnscaledParameters x i ∧
      clippedNext concreteUnscaledParameters x i ≤ 1 ∧
      (∀ l : Fin (T - 1), l.val < i.val →
        1 + concreteTheta ≤ clippedNext concreteUnscaledParameters x l) ∧
      (∀ l : Fin (T - 1), i.val ≤ l.val →
        clippedNext concreteUnscaledParameters x l ≤ 1) := by
  have htransition := no_transition_of_section_gradient_sq_lt_one
    hn x y hgrad
  have hnoLowHigh := no_low_to_high_of_section_gradient_sq_lt_one
    hn x y hgrad
  have hterminalClipped := concrete_clipped_terminal_le_one_of_raw_le_one
    hT x hterminal
  exact exists_concrete_full_frontier_of_low x htransition hnoLowHigh
    (terminalMemoryIndex hT) hterminalClipped

/-! ## Radial identity at a restricted maximizer -/

/-- Radial contribution of the constrained inner-chain value in one
block, evaluated at an active dual point. -/
def innerPulseRadialTerm {T n : Nat} (hn : 0 < n)
    (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (i : Fin (T - 1)) : ℝ :=
  primalA x i * innerGradA hn (innerC hn) (dualBlock y i) +
    primalB x i * innerGradB hn (innerC hn) (dualBlock y i)

/-- Radial contribution of the correction quadratics in one block. -/
def quadraticPulseRadialTerm {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T)
    (i : Fin (T - 1)) : ℝ :=
  2 * (innerC1 hn + P.gamma) * (primalA x i) ^ 2 +
    2 * (innerC2 hn + P.gamma) * (primalB x i) ^ 2

/-- Exact blockwise radial identity before substituting the unconstrained
Green maximizer. -/
theorem section_pulse_radial_block_eq {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters)
    (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (i : Fin (T - 1)) :
    let grad := unscaledTrueGradX hn P x y
    primalA x i * primalA grad i + primalB x i * primalB grad i =
      outerPulseRadialTerm P x i + innerPulseRadialTerm hn x y i +
      quadraticPulseRadialTerm hn P x i +
      2 * Sigma3Deriv P.P0 P.P1 P.K (pulseSq x) *
        ((primalA x i) ^ 2 + (primalB x i) ^ 2) := by
  dsimp only
  rw [primalA_unscaledTrueGradX, primalB_unscaledTrueGradX]
  unfold serializedGradA serializedGradB outerPulseRadialTerm
    innerPulseRadialTerm quadraticPulseRadialTerm
  simp only [serializedClippedCurrent_serializeUnscaled,
    serializedClippedNext_serializeUnscaled, serializedA_serializeUnscaled,
    serializedB_serializeUnscaled, serializedDualBlock_serializeUnscaled,
    serializedPulseSq_serializeUnscaled]
  ring

/-- Summed radial identity at an arbitrary dual point. -/
theorem section_pulse_radial_pairing_eq {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters)
    (x : UnscaledPrimal T) (y : UnscaledDual T n) :
    let grad := unscaledTrueGradX hn P x y
    radialDot (pulseOnly x) grad =
      (∑ i : Fin (T - 1), outerPulseRadialTerm P x i) +
      (∑ i : Fin (T - 1), innerPulseRadialTerm hn x y i) +
      (∑ i : Fin (T - 1), quadraticPulseRadialTerm hn P x i) +
      2 * Sigma3Deriv P.P0 P.P1 P.K (pulseSq x) * pulseSq x := by
  dsimp only
  rw [radialDot_pulseOnly]
  calc
    (∑ i : Fin (T - 1),
        (primalA x i * primalA (unscaledTrueGradX hn P x y) i +
          primalB x i * primalB (unscaledTrueGradX hn P x y) i)) =
      ∑ i : Fin (T - 1),
        (outerPulseRadialTerm P x i + innerPulseRadialTerm hn x y i +
          quadraticPulseRadialTerm hn P x i +
          2 * Sigma3Deriv P.P0 P.P1 P.K (pulseSq x) *
            ((primalA x i) ^ 2 + (primalB x i) ^ 2)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact section_pulse_radial_block_eq hn P x y i
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      unfold pulseSq
      rw [Finset.mul_sum]

/-- At a maximizer over a ball containing zero, the constrained inner-chain
radial contribution is nonnegative.  This proves item (v) of the paper's
inner interface at the exact active maximizer needed below. -/
theorem sum_innerPulseRadialTerm_nonneg_of_maximizer
    {T n : Nat} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (hy : IsMaximizerOn (diameterBall (n * (T - 1)) D)
      (unscaledObjective hn concreteUnscaledParameters) x y) :
    0 ≤ ∑ i : Fin (T - 1), innerPulseRadialTerm hn x y i := by
  have hcompare := hy.2 0 (zero_mem_diameterBall _ _ hD)
  rw [unscaledObjective_eq_outer_add_inner hn
      concreteUnscaledParameters x 0,
    unscaledObjective_eq_outer_add_inner hn
      concreteUnscaledParameters x y] at hcompare
  have hzero : (∑ i : Fin (T - 1),
      innerChain hn (innerC hn) (primalA x i) (primalB x i)
        (dualBlock (0 : UnscaledDual T n) i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [show dualBlock (0 : UnscaledDual T n) i = 0 by
      funext k
      simp [dualBlock]]
    exact innerChain_zero_dual hn (innerC hn)
      (primalA x i) (primalB x i)
  rw [hzero, add_zero] at hcompare
  have hinner : 0 ≤ ∑ i : Fin (T - 1),
      innerChain hn (innerC hn) (primalA x i) (primalB x i)
        (dualBlock y i) := by
    linarith
  apply hinner.trans
  apply Finset.sum_le_sum
  intro i _
  have hq := regularizedPathQuad_nonneg n (dualBlock y i)
  unfold innerPulseRadialTerm innerGradA innerGradB innerChain innerForcing
  nlinarith

/-- The correction quadratics have radial contribution at least
`-2 c_q ‖p‖²`. -/
theorem concrete_sum_quadraticPulseRadialTerm_lower
    {T n : Nat} (hn : 10 ≤ n) (x : UnscaledPrimal T) :
    -2 * concreteCq * pulseSq x ≤
      ∑ i : Fin (T - 1),
        quadraticPulseRadialTerm (by omega : 0 < n)
          concreteUnscaledParameters x i := by
  unfold pulseSq
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa [quadraticPulseRadialTerm, concreteUnscaledParameters] using
    concreteCq_dominates_quadratic_correction hn
      (primalA x i) (primalB x i)

/-- Restricted-value analogue of the paper's radial tail estimate.  It
uses only an active maximizer in the dual ball: the inner contribution is
nonnegative, the correction costs at most `2 c_q`, and the radial budget
supplies `2 K`. -/
theorem concrete_restricted_section_large_pulse_radial_lower
    {T n : Nat} (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (hy : IsMaximizerOn (diameterBall (n * (T - 1)) D)
      (unscaledObjective (by omega : 0 < n)
        concreteUnscaledParameters) x y)
    (i : Fin (T - 1))
    (hpulse : concreteUnscaledParameters.P1 ^ 2 ≤ pulseSq x)
    (hnext : clippedNext concreteUnscaledParameters x i ≤ 1)
    (hbefore : ∀ l : Fin (T - 1), l.val < i.val →
      1 + concreteTheta ≤ clippedNext concreteUnscaledParameters x l)
    (hafter : ∀ l : Fin (T - 1), i.val ≤ l.val →
      clippedNext concreteUnscaledParameters x l ≤ 1) :
    (1 / 2 : ℝ) * pulseSq x ≤
      radialDot (pulseOnly x)
        (unscaledTrueGradX (by omega : 0 < n)
          concreteUnscaledParameters x y) := by
  let grad := unscaledTrueGradX (by omega : 0 < n)
    concreteUnscaledParameters x y
  let dot := radialDot (pulseOnly x) grad
  let blockSq := (primalA x i) ^ 2 + (primalB x i) ^ 2
  let r := Real.sqrt (pulseSq x)
  have hpulseNonneg : 0 ≤ pulseSq x := by
    rw [← vecSq_pulseOnly]
    exact vecSq_nonneg (pulseOnly x)
  have hrNonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hrSq : r ^ 2 = pulseSq x := Real.sq_sqrt hpulseNonneg
  have hP0pos : 0 < concreteUnscaledParameters.P0 :=
    lt_trans (by norm_num) concreteUnscaledParameters.P0_gt_one
  have hP0ltP1 : concreteUnscaledParameters.P0 <
      concreteUnscaledParameters.P1 := by
    change concreteRadialTransition.P0 < concreteRadialTransition.P1
    exact concreteRadialTransition.P0_lt_P1
  have hP1pos : 0 < concreteUnscaledParameters.P1 :=
    hP0pos.trans hP0ltP1
  have hrP1 : concreteUnscaledParameters.P1 ≤ r := by
    nlinarith
  have hnextLower : -concreteGateThreshold.deltaS ≤
      clippedNext concreteUnscaledParameters x i := by
    simpa [clippedNext, concreteUnscaledParameters, concreteRadialTransition,
      assembleRadialTransition] using
        (concretePi1_mem (primalState x i)).1
  have houterAbs :
      |outerPulseRadialTerm concreteUnscaledParameters x i| ≤
        concreteCp * Real.sqrt blockSq := by
    simpa [outerPulseRadialTerm, concreteUnscaledParameters] using
      (concreteCp_dominates_pulse_remainder
        (current := clippedCurrent concreteUnscaledParameters x i)
        (next := clippedNext concreteUnscaledParameters x i)
        (a := primalA x i) (b := primalB x i)
        concreteUnscaledParameters.P0 hnextLower hnext)
  have hblock : blockSq ≤ pulseSq x := primalAB_sq_le_pulseSq x i
  have hsqrtBlock : Real.sqrt blockSq ≤ r := Real.sqrt_le_sqrt hblock
  have houter : -concreteCp * r ≤
      outerPulseRadialTerm concreteUnscaledParameters x i := by
    calc
      -concreteCp * r ≤ -concreteCp * Real.sqrt blockSq := by
        have hmul := mul_le_mul_of_nonneg_left hsqrtBlock concreteCp_pos.le
        nlinarith
      _ ≤ outerPulseRadialTerm concreteUnscaledParameters x i := by
        simpa only [neg_mul] using (abs_le.mp houterAbs).1
  have houterSum := concrete_sum_outerPulseRadialTerm_eq_frontier
    x i hbefore hafter
  have hinner := sum_innerPulseRadialTerm_nonneg_of_maximizer
    (by omega : 0 < n) hD x y hy
  have hcorrection := concrete_sum_quadraticPulseRadialTerm_lower hn x
  have hP01 : concreteUnscaledParameters.P0 ^ 2 <
      concreteUnscaledParameters.P1 ^ 2 := by
    nlinarith [hP0ltP1]
  have hsigma : Sigma3Deriv concreteUnscaledParameters.P0
      concreteUnscaledParameters.P1 concreteUnscaledParameters.K
      (pulseSq x) = concreteUnscaledParameters.K :=
    Sigma3Deriv_eq_K hP01 hpulse
  have hpair :
      dot =
        (∑ l : Fin (T - 1),
          outerPulseRadialTerm concreteUnscaledParameters x l) +
        (∑ l : Fin (T - 1),
          innerPulseRadialTerm (by omega : 0 < n) x y l) +
        (∑ l : Fin (T - 1),
          quadraticPulseRadialTerm (by omega : 0 < n)
            concreteUnscaledParameters x l) +
        2 * Sigma3Deriv concreteUnscaledParameters.P0
          concreteUnscaledParameters.P1 concreteUnscaledParameters.K
          (pulseSq x) * pulseSq x := by
    simpa [dot, grad] using section_pulse_radial_pairing_eq
      (by omega : 0 < n) concreteUnscaledParameters x y
  rw [houterSum, hsigma] at hpair
  have hdotBase :
      2 * (concreteUnscaledParameters.K - concreteCq) * pulseSq x -
          concreteCp * r ≤ dot := by
    linarith
  have hmargin := concreteRadialTransition.P1_margin r hrP1
  rw [hrSq] at hmargin
  exact hmargin.trans hdotBase

/-- Squared version of the paper's numerical `τ₀`: it is strictly below
both one and `(P1/2)²`. -/
def concreteRestrictedGradientSqThreshold : ℝ :=
  min (1 / 2) (concreteUnscaledParameters.P1 ^ 2 / 8)

theorem concreteRestrictedGradientSqThreshold_pos :
    0 < concreteRestrictedGradientSqThreshold := by
  have hP0pos : 0 < concreteUnscaledParameters.P0 :=
    lt_trans (by norm_num) concreteUnscaledParameters.P0_gt_one
  have hP1pos : 0 < concreteUnscaledParameters.P1 := by
    change 0 < concreteRadialTransition.P1
    exact hP0pos.trans concreteRadialTransition.P0_lt_P1
  unfold concreteRestrictedGradientSqThreshold
  exact lt_min (by norm_num) (div_pos (sq_pos_of_pos hP1pos) (by norm_num))

theorem concreteRestrictedGradientSqThreshold_lt_one :
    concreteRestrictedGradientSqThreshold < 1 :=
  (min_le_left _ _).trans_lt (by norm_num)

/-- The literal bounded-pulse certificate for the constrained value.
Whenever `g` is the actual Fréchet gradient of `ValueOn`, a low terminal
memory and a gradient below the numerical threshold force
`pulseSq < P1²`. -/
theorem concrete_bounded_pulse_of_restricted_gradient_sq_le_threshold
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (x g : UnscaledPrimal T)
    (hvalue : NCPLVerification.HasEVecFDerivAt
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters))
      (NCPLVerification.evecDot g) x)
    (hterminal : primalState x (terminalMemoryIndex hT) ≤ 1)
    (hsmall : vecSq g ≤ concreteRestrictedGradientSqThreshold) :
    pulseSq x < concreteUnscaledParameters.P1 ^ 2 := by
  obtain ⟨y, hy⟩ := unscaledObjective_maximum_attained
    (T := T) (by omega : 0 < n) concreteUnscaledParameters hD x
  have hgeq := restrictedValue_gradient_eq_at_maximizer
    (by omega : 0 < n) concreteUnscaledParameters hD x y hy g hvalue
  let grad := unscaledTrueGradX (by omega : 0 < n)
    concreteUnscaledParameters x y
  have hgradSmall : vecSq grad ≤ concreteRestrictedGradientSqThreshold := by
    simpa [grad, hgeq] using hsmall
  have hgradLt : vecSq grad < 1 :=
    hgradSmall.trans_lt concreteRestrictedGradientSqThreshold_lt_one
  obtain ⟨i, _hcurrent, hnext, hbefore, hafter⟩ :=
    concrete_full_frontier_of_terminal_section_gradient_sq_lt_one
      hT hn x y (by simpa [grad] using hgradLt) hterminal
  by_contra hpulseLt
  have hpulse : concreteUnscaledParameters.P1 ^ 2 ≤ pulseSq x :=
    le_of_not_gt hpulseLt
  have hradial := concrete_restricted_section_large_pulse_radial_lower
    hn hD x y hy i hpulse hnext hbefore hafter
  let dot := radialDot (pulseOnly x) grad
  have hdot : (1 / 2 : ℝ) * pulseSq x ≤ dot := by
    simpa [dot, grad] using hradial
  have hcauchy : dot ^ 2 ≤ pulseSq x * vecSq grad := by
    have h := radialDot_sq_le (pulseOnly x) grad
    rw [vecSq_pulseOnly] at h
    simpa [dot] using h
  have hP0pos : 0 < concreteUnscaledParameters.P0 :=
    lt_trans (by norm_num) concreteUnscaledParameters.P0_gt_one
  have hP1pos : 0 < concreteUnscaledParameters.P1 := by
    change 0 < concreteRadialTransition.P1
    exact hP0pos.trans concreteRadialTransition.P0_lt_P1
  have hP1sqPos : 0 < concreteUnscaledParameters.P1 ^ 2 :=
    sq_pos_of_pos hP1pos
  have hpulsePos : 0 < pulseSq x := hP1sqPos.trans_le hpulse
  have hhalfNonneg : 0 ≤ (1 / 2 : ℝ) * pulseSq x := by positivity
  have hdotNonneg : 0 ≤ dot := hhalfNonneg.trans hdot
  have hfactor : 0 ≤
      (dot - (1 / 2 : ℝ) * pulseSq x) *
        (dot + (1 / 2 : ℝ) * pulseSq x) :=
    mul_nonneg (sub_nonneg.mpr hdot) (add_nonneg hdotNonneg hhalfNonneg)
  have hsq : ((1 / 2 : ℝ) * pulseSq x) ^ 2 ≤ dot ^ 2 := by
    nlinarith
  have hscaled :
      pulseSq x * ((1 / 4 : ℝ) * pulseSq x) ≤
        pulseSq x * vecSq grad := by
    calc
      pulseSq x * ((1 / 4 : ℝ) * pulseSq x) =
          ((1 / 2 : ℝ) * pulseSq x) ^ 2 := by ring
      _ ≤ dot ^ 2 := hsq
      _ ≤ pulseSq x * vecSq grad := hcauchy
  have hquarter : (1 / 4 : ℝ) * pulseSq x ≤ vecSq grad :=
    le_of_mul_le_mul_left hscaled hpulsePos
  have hquarterP1 : (1 / 4 : ℝ) *
      concreteUnscaledParameters.P1 ^ 2 ≤ vecSq grad := by
    exact (mul_le_mul_of_nonneg_left hpulse (by norm_num)).trans hquarter
  have hthresholdP1 : concreteRestrictedGradientSqThreshold ≤
      concreteUnscaledParameters.P1 ^ 2 / 8 := by
    exact min_le_right _ _
  nlinarith

/-! ## Restricted-ball inactivity at the derivative level -/

theorem continuous_pulseSq {T : Nat} :
    Continuous (pulseSq : UnscaledPrimal T → ℝ) := by
  unfold pulseSq
  apply continuous_finsetSum
  intro i _hi
  exact ((continuous_apply (primalAIndex i)).pow 2).add
    ((continuous_apply (primalBIndex i)).pow 2)

/-- Strict feasibility of the explicit dual maximizer is stable on a
neighborhood.  Consequently the restricted value has exactly the same true
Fréchet derivative as the explicit unconstrained value. -/
theorem hasEVecFDerivAt_unscaledRestrictedValue_of_strict_size
    {T n : Nat} (hn : 10 ≤ n) (P : UnscaledParameters) {D : ℝ}
    (x : UnscaledPrimal T)
    (hsize : 96000 * (n : ℝ) ^ 2 * pulseSq x < (D / 2) ^ 2) :
    NCPLVerification.HasEVecFDerivAt
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n) P))
      (NCPLVerification.evecDot
        (unscaledTrueGradX (T := T) (by omega : 0 < n) P x
          (unscaledInnerMaximizer (by omega : 0 < n) x))) x := by
  let c : ℝ := 96000 * (n : ℝ) ^ 2
  let R : ℝ := (D / 2) ^ 2
  have hc : Continuous (fun z : UnscaledPrimal T ↦ c * pulseSq z) :=
    continuous_const.mul continuous_pulseSq
  have hev : ∀ᶠ z in nhds x, c * pulseSq z < R :=
    hc.continuousAt.eventually_lt continuousAt_const (by simpa [c, R] using hsize)
  have heq :
      (fun z : UnscaledPrimal T ↦
        ValueOn (diameterBall (n * (T - 1)) D)
          (unscaledObjective (T := T) (by omega : 0 < n) P) z) =ᶠ[nhds x]
      unscaledExplicitValue (T := T) (by omega : 0 < n) P := by
    filter_upwards [hev] with z hz
    have hle : 96000 * (n : ℝ) ^ 2 * pulseSq z ≤ (D / 2) ^ 2 := by
      simpa [c, R] using hz.le
    calc
      ValueOn (diameterBall (n * (T - 1)) D)
          (unscaledObjective (by omega : 0 < n) P) z =
        ValueOn Set.univ (unscaledObjective (by omega : 0 < n) P) z :=
          unscaledValue_diameterBall_eq_univ_of_size hn P z hle
      _ = unscaledExplicitValue (by omega : 0 < n) P z :=
        unscaledValue_univ_eq_explicit hn P z
  exact (hasEVecFDerivAt_unscaledExplicitValue hn P x).congr_of_eventuallyEq heq

/-- The paper's restricted-ball inactivity lemma, including the derived
pulse bound, value identity, and equality of the actual restricted gradient
with the explicit Green-maximizer gradient. -/
theorem concrete_restrictedValue_inactive_of_small_gradient
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (hsizeHierarchy :
      96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 ≤
        (D / 2) ^ 2)
    (x g : UnscaledPrimal T)
    (hvalue : NCPLVerification.HasEVecFDerivAt
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters))
      (NCPLVerification.evecDot g) x)
    (hterminal : primalState x (terminalMemoryIndex hT) ≤ 1)
    (hsmall : vecSq g ≤ concreteRestrictedGradientSqThreshold) :
    pulseSq x < concreteUnscaledParameters.P1 ^ 2 ∧
      ValueOn (diameterBall (n * (T - 1)) D)
          (unscaledObjective (T := T) (by omega : 0 < n)
            concreteUnscaledParameters) x =
        unscaledExplicitValue (by omega : 0 < n)
          concreteUnscaledParameters x ∧
      g = unscaledTrueGradX (by omega : 0 < n)
        concreteUnscaledParameters x
        (unscaledInnerMaximizer (by omega : 0 < n) x) := by
  have hpulse :=
    concrete_bounded_pulse_of_restricted_gradient_sq_le_threshold
      hT hn hD x g hvalue hterminal hsmall
  have hcoef : 0 < 96000 * (n : ℝ) ^ 2 := by positivity
  have hsize : 96000 * (n : ℝ) ^ 2 * pulseSq x < (D / 2) ^ 2 := by
    calc
      96000 * (n : ℝ) ^ 2 * pulseSq x <
          96000 * (n : ℝ) ^ 2 *
            concreteUnscaledParameters.P1 ^ 2 :=
        mul_lt_mul_of_pos_left hpulse hcoef
      _ ≤ (D / 2) ^ 2 := hsizeHierarchy
  let grad := unscaledTrueGradX (by omega : 0 < n)
    concreteUnscaledParameters x
    (unscaledInnerMaximizer (by omega : 0 < n) x)
  have hexplicit : NCPLVerification.HasEVecFDerivAt
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters))
      (NCPLVerification.evecDot grad) x := by
    simpa [grad] using
      hasEVecFDerivAt_unscaledRestrictedValue_of_strict_size
        hn concreteUnscaledParameters x hsize
  have hmaps : NCPLVerification.evecDot g =
      NCPLVerification.evecDot grad := hvalue.unique hexplicit
  have hgeq : g = grad := by
    funext j
    have hj := congrArg
      (fun L : UnscaledPrimal T →L[ℝ] ℝ ↦
        L (NCPLVerification.evecBasis j)) hmaps
    simpa [NCPLVerification.evecDot_apply,
      NCPLVerification.evecBasis] using hj
  refine ⟨hpulse, ?_, by simpa [grad] using hgeq⟩
  calc
    ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (by omega : 0 < n)
          concreteUnscaledParameters) x =
      ValueOn Set.univ
        (unscaledObjective (by omega : 0 < n)
          concreteUnscaledParameters) x :=
        unscaledValue_diameterBall_eq_univ_of_size hn
          concreteUnscaledParameters x hsize.le
    _ = unscaledExplicitValue (by omega : 0 < n)
          concreteUnscaledParameters x :=
      unscaledValue_univ_eq_explicit hn concreteUnscaledParameters x

/-- Final squared gradient constant for the genuinely restricted value. -/
def concreteRestrictedTerminalGradientSqLower : ℝ :=
  min concreteTerminalGradientSqLower
    concreteRestrictedGradientSqThreshold

theorem concreteRestrictedTerminalGradientSqLower_pos :
    0 < concreteRestrictedTerminalGradientSqLower := by
  unfold concreteRestrictedTerminalGradientSqLower
  exact lt_min concreteTerminalGradientSqLower_pos
    concreteRestrictedGradientSqThreshold_pos

/-- Complete terminal gradient certificate for the actual bounded-dual
value function.  No pulse-size assumption remains: bounded pulse is proved
first for the constrained maximum, then dual-ball inactivity transfers the
explicit terminal estimate. -/
theorem concrete_restrictedValue_terminal_gradient_sq_lower
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (hsizeHierarchy :
      96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 ≤
        (D / 2) ^ 2)
    (x g : UnscaledPrimal T)
    (hvalue : NCPLVerification.HasEVecFDerivAt
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters))
      (NCPLVerification.evecDot g) x)
    (hterminal : primalState x (terminalMemoryIndex hT) ≤ 1) :
    concreteRestrictedTerminalGradientSqLower ≤ vecSq g := by
  by_cases hsmall : vecSq g ≤ concreteRestrictedGradientSqThreshold
  · obtain ⟨_hpulse, _hvalueEq, hgeq⟩ :=
      concrete_restrictedValue_inactive_of_small_gradient
        hT hn hD hsizeHierarchy x g hvalue hterminal hsmall
    have hexplicit := concrete_explicitValue_terminal_gradient_sq_lower
      hT hn x hterminal
    calc
      concreteRestrictedTerminalGradientSqLower ≤
          concreteTerminalGradientSqLower := min_le_left _ _
      _ ≤ vecSq (unscaledTrueGradX (by omega : 0 < n)
          concreteUnscaledParameters x
          (unscaledInnerMaximizer (by omega : 0 < n) x)) := hexplicit
      _ = vecSq g := by rw [hgeq]
  · have hlarge : concreteRestrictedGradientSqThreshold < vecSq g :=
      lt_of_not_ge hsmall
    exact (min_le_right _ _).trans hlarge.le

/-- Derivative plus norm lower bound, packaged at the actual `ValueOn`. -/
theorem concrete_restrictedValue_terminal_gradient_certificate
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (hsizeHierarchy :
      96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 ≤
        (D / 2) ^ 2)
    (x g : UnscaledPrimal T)
    (hvalue : NCPLVerification.HasEVecFDerivAt
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters))
      (NCPLVerification.evecDot g) x)
    (hterminal : primalState x (terminalMemoryIndex hT) ≤ 1) :
    NCPLVerification.HasEVecFDerivAt
        (ValueOn (diameterBall (n * (T - 1)) D)
          (unscaledObjective (T := T) (by omega : 0 < n)
            concreteUnscaledParameters))
        (NCPLVerification.evecDot g) x ∧
      concreteRestrictedTerminalGradientSqLower ≤ vecSq g :=
  ⟨hvalue, concrete_restrictedValue_terminal_gradient_sq_lower
    hT hn hD hsizeHierarchy x g hvalue hterminal⟩

/-! ## Actual restricted-value OS failure and scaling interface -/

/-- Serialized coordinate occupied by the last raw memory variable. -/
def terminalPrimalIndex {T : Nat} (hT : 2 ≤ T) : Fin (3 * (T - 1)) :=
  primalStateIndex (terminalMemoryIndex hT)

/-- Direct OS-failure interface for the genuine bounded-dual value.  The
only analytic input is a globally chosen actual gradient representation of
that very `ValueOn`; the terminal lower bound itself is fully discharged by
the preceding concrete theorem. -/
theorem concrete_restrictedValue_not_optimizationStationary
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (hsizeHierarchy :
      96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 ≤
        (D / 2) ^ 2)
    (grad : UnscaledPrimal T → UnscaledPrimal T)
    (hdiff : ∀ u, NCPLVerification.HasEVecFDerivAt
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters))
      (NCPLVerification.evecDot (grad u)) u)
    {ell0 eps0 : ℝ} (hell0 : 0 < ell0) (heps0 : 0 < eps0)
    (hmove : eps0 / (2 * ell0) ≤ 1)
    (hthreshold : 16 * eps0 ^ 2 ≤
      concreteRestrictedTerminalGradientSqLower)
    {x : UnscaledPrimal T}
    (hxterminal : x (terminalPrimalIndex hT) = 0) :
    ¬ IsOptimizationStationary Set.univ
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters)) ell0 eps0 x := by
  apply not_optimizationStationary_of_terminal_gradient
    hell0 heps0 (by norm_num : (0 : ℝ) < 1) hmove hdiff
    (terminalPrimalIndex hT) hxterminal
  intro u hu
  have hterminal : primalState u (terminalMemoryIndex hT) ≤ 1 := by
    simpa [terminalPrimalIndex, primalState] using hu
  exact hthreshold.trans
    (concrete_restrictedValue_terminal_gradient_sq_lower
      hT hn hD hsizeHierarchy u (grad u) (hdiff u) hterminal)

/-- The same failure after an arbitrary positive coordinate/amplitude
scaling, stated directly for the scaled `ValueOn` saddle objective. -/
theorem concrete_scaledRestrictedValue_not_optimizationStationary
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (hsizeHierarchy :
      96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 ≤
        (D / 2) ^ 2)
    (grad : UnscaledPrimal T → UnscaledPrimal T)
    (hdiff : ∀ u, NCPLVerification.HasEVecFDerivAt
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters))
      (NCPLVerification.evecDot (grad u)) u)
    {ell0 eps0 lambda amp : ℝ}
    (hell0 : 0 < ell0) (heps0 : 0 < eps0)
    (hlambda : 0 < lambda) (hamp : 0 < amp)
    (hmove : eps0 / (2 * ell0) ≤ 1)
    (hthreshold : 16 * eps0 ^ 2 ≤
      concreteRestrictedTerminalGradientSqLower)
    {x : UnscaledPrimal T}
    (hxterminal : x (terminalPrimalIndex hT) = 0) :
    ¬ IsOptimizationStationary (scaledDomain lambda Set.univ)
      (ValueOn
        (scaledDomain lambda (diameterBall (n * (T - 1)) D))
        (scaledObjective lambda amp
          (unscaledObjective (T := T) (by omega : 0 < n)
            concreteUnscaledParameters)))
      (amp * ell0 / lambda ^ 2) (amp / lambda * eps0) x := by
  have hxunscaled : unscaleCoords lambda x (terminalPrimalIndex hT) = 0 := by
    simp [unscaleCoords, hxterminal]
  have hsource : ¬ IsOptimizationStationary Set.univ
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters)) ell0 eps0
      (unscaleCoords lambda x) :=
    concrete_restrictedValue_not_optimizationStationary
      hT hn hD hsizeHierarchy grad hdiff hell0 heps0 hmove hthreshold
        hxunscaled
  have hscaled := not_scaledOS_of_not_sourceOS
    hlambda hamp hell0 hsource
  have hmax : ∀ z : UnscaledPrimal T, ∃ y,
      IsMaximizerOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (by omega : 0 < n)
          concreteUnscaledParameters) z y := by
    intro z
    exact unscaledObjective_maximum_attained
      (by omega : 0 < n) concreteUnscaledParameters hD z
  have hvalueEq := scaledValue_eq_scaledScalar
    hlambda.ne' hamp.le hmax
  rw [hvalueEq]
  exact hscaled

/-- The paper decreases the terminal constant, if necessary, so it is at
most the source smoothness constant `ell0`. -/
def concreteTerminalC0 (ell0 : ℝ) : ℝ :=
  min (Real.sqrt concreteRestrictedTerminalGradientSqLower) ell0

theorem concreteTerminalC0_pos {ell0 : ℝ} (hell0 : 0 < ell0) :
    0 < concreteTerminalC0 ell0 := by
  unfold concreteTerminalC0
  exact lt_min
    (Real.sqrt_pos.2 concreteRestrictedTerminalGradientSqLower_pos)
    hell0

theorem concreteTerminalC0_le_ell0 (ell0 : ℝ) :
    concreteTerminalC0 ell0 ≤ ell0 := by
  exact min_le_right _ _

theorem concreteTerminalC0_sq_le {ell0 : ℝ} (hell0 : 0 < ell0) :
    concreteTerminalC0 ell0 ^ 2 ≤
      concreteRestrictedTerminalGradientSqLower := by
  have hc0 : 0 ≤ concreteTerminalC0 ell0 :=
    (concreteTerminalC0_pos hell0).le
  have hsqrt : 0 ≤ Real.sqrt concreteRestrictedTerminalGradientSqLower :=
    Real.sqrt_nonneg _
  have hle : concreteTerminalC0 ell0 ≤
      Real.sqrt concreteRestrictedTerminalGradientSqLower := by
    exact min_le_left _ _
  have hfactor : 0 ≤
      (Real.sqrt concreteRestrictedTerminalGradientSqLower -
          concreteTerminalC0 ell0) *
        (Real.sqrt concreteRestrictedTerminalGradientSqLower +
          concreteTerminalC0 ell0) :=
    mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hsqrt hc0)
  have hsqrtSq :
      (Real.sqrt concreteRestrictedTerminalGradientSqLower) ^ 2 =
        concreteRestrictedTerminalGradientSqLower :=
    Real.sq_sqrt concreteRestrictedTerminalGradientSqLower_pos.le
  nlinarith

/-- Source OS failure at the paper's canonical threshold `c0/4`. -/
theorem concrete_restrictedValue_not_OS_at_terminalC0_quarter
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (hsizeHierarchy :
      96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 ≤
        (D / 2) ^ 2)
    (grad : UnscaledPrimal T → UnscaledPrimal T)
    (hdiff : ∀ u, NCPLVerification.HasEVecFDerivAt
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters))
      (NCPLVerification.evecDot (grad u)) u)
    {ell0 : ℝ} (hell0 : 0 < ell0) {x : UnscaledPrimal T}
    (hxterminal : x (terminalPrimalIndex hT) = 0) :
    ¬ IsOptimizationStationary Set.univ
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters))
      ell0 (concreteTerminalC0 ell0 / 4) x := by
  have hc0pos := concreteTerminalC0_pos hell0
  have hmove : (concreteTerminalC0 ell0 / 4) / (2 * ell0) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * ell0)).2
    have hc0le := concreteTerminalC0_le_ell0 ell0
    nlinarith
  have hthreshold : 16 * (concreteTerminalC0 ell0 / 4) ^ 2 ≤
      concreteRestrictedTerminalGradientSqLower := by
    have := concreteTerminalC0_sq_le hell0
    convert this using 1 <;> ring
  exact concrete_restrictedValue_not_optimizationStationary
    hT hn hD hsizeHierarchy grad hdiff hell0 (by positivity)
      hmove hthreshold hxterminal

/-- Direct paper-scaling specialization: with
`lambda = 4 ell0 eps / (c0 ell)` and
`amp = ell lambda² / ell0`, a zero scaled terminal coordinate is not
`eps`-OS for the actual scaled bounded-dual value. -/
theorem concrete_paperScaledValue_not_optimizationStationary
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (hsizeHierarchy :
      96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 ≤
        (D / 2) ^ 2)
    (grad : UnscaledPrimal T → UnscaledPrimal T)
    (hdiff : ∀ u, NCPLVerification.HasEVecFDerivAt
      (ValueOn (diameterBall (n * (T - 1)) D)
        (unscaledObjective (T := T) (by omega : 0 < n)
          concreteUnscaledParameters))
      (NCPLVerification.evecDot (grad u)) u)
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
  dsimp only
  let c0 := concreteTerminalC0 ell0
  let lambda := lowerScale ell ell0 eps c0
  let amp := lowerAmplitude ell ell0 lambda
  have hc0 : 0 < c0 := by
    exact concreteTerminalC0_pos hell0
  have hlambda : 0 < lambda := by
    dsimp [lambda, c0, lowerScale]
    positivity
  have hamp : 0 < amp := by
    dsimp [amp, lowerAmplitude]
    positivity
  have hmove : (c0 / 4) / (2 * ell0) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 2 * ell0)).2
    have hc0le : c0 ≤ ell0 := by
      exact concreteTerminalC0_le_ell0 ell0
    nlinarith
  have hthreshold : 16 * (c0 / 4) ^ 2 ≤
      concreteRestrictedTerminalGradientSqLower := by
    have hs := concreteTerminalC0_sq_le hell0
    change c0 ^ 2 ≤ concreteRestrictedTerminalGradientSqLower at hs
    convert hs using 1 <;> ring
  have hscaled := concrete_scaledRestrictedValue_not_optimizationStationary
    hT hn hD hsizeHierarchy grad hdiff hell0 (by positivity : 0 < c0 / 4)
      hlambda hamp hmove hthreshold hxterminal
  have hsmooth : amp * ell0 / lambda ^ 2 = ell := by
    dsimp [amp]
    exact lowerAmplitude_smooth_constant hell0.ne' hlambda.ne'
  have hfactor : amp / lambda = 4 * eps / c0 := by
    dsimp [amp, lambda]
    exact paper_lambda_gradient_factor hell.ne' hell0.ne' hc0.ne'
  have hepsScaled : amp / lambda * (c0 / 4) = eps := by
    rw [hfactor]
    field_simp [hc0.ne']
  rw [hsmooth, hepsScaled] at hscaled
  exact hscaled

/-- A fully literal restricted-ball terminal certificate at one verified
frontier point: the displayed vector is simultaneously the true Fréchet
gradient of `ValueOn` and has the numerical lower bound. -/
theorem restrictedValue_frontier_gradient_certificate {T n : Nat}
    (hn : 10 ≤ n) {theta : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (P : UnscaledParameters) {D : ℝ}
    (hPtheta : P.theta = theta) (hPtau : P.tauS = tauS P.delta)
    (hPalpha : P.alpha = C.alpha) (hPbeta : P.beta = C.beta)
    (hPgamma : P.gamma = C.gamma) (hP01 : P.P0 ^ 2 < P.P1 ^ 2)
    (heta : 0 ≤ P.eta) (hmu : 0 ≤ P.mu)
    (x : UnscaledPrimal T) (i : Fin (T - 1))
    (hsize : 96000 * (n : ℝ) ^ 2 * pulseSq x < (D / 2) ^ 2)
    (hpulse : pulseSq x ≤ P.P0 ^ 2)
    (hcurrent : 1 + theta ≤ clippedCurrent P x i)
    (hnextLow : clippedNext P x i ≤ 1)
    (hnextLower : -C.deltaS ≤ clippedNext P x i) :
    let grad := unscaledTrueGradX (by omega : 0 < n) P x
      (unscaledInnerMaximizer (by omega : 0 < n) x)
    NCPLVerification.HasEVecFDerivAt
        (ValueOn (diameterBall (n * (T - 1)) D)
          (unscaledObjective (T := T) (by omega : 0 < n) P))
        (NCPLVerification.evecDot grad) x ∧
      (1 / 20 : ℝ) ≤ vecSq grad := by
  dsimp only
  constructor
  · exact hasEVecFDerivAt_unscaledRestrictedValue_of_strict_size
      hn P x hsize
  · exact explicitValue_frontier_gradient_sq_lower hn C P hPtheta hPtau
      hPalpha hPbeta hPgamma hP01 heta hmu x i hpulse hcurrent
      hnextLow hnextLower

end

end NCCLowerBoundVerification
