import NCCLowerBoundVerification.Lower.AccuracyRegime
import NCCLowerBoundVerification.Lower.PaperRegularity
import NCCLowerBoundVerification.Lower.RotationClosure
import NCCLowerBoundVerification.Lower.RestrictedDanskin
import NCCLowerBoundVerification.Lower.TaggedResisting
import NCCLowerBoundVerification.Lower.TerminalConcrete
import NCCLowerBoundVerification.Lower.UnscaledRegularity

/-!
# Assembly of the deterministic lower bound

This file connects the genuine separated gradients to the tagged resisting
construction, transports the zero-chain through the paper scaling, and
packages the finite-horizon rotated hard instance used in the main theorem.
-/

namespace NCCLowerBoundVerification

noncomputable section

open NCPLVerification

/-! ## The genuine separated gradients are the packed gradients -/

private theorem main_dualBlockIndex_pair {T n : Nat}
    (i : Fin (T - 1)) (k : Fin n) :
    dualBlockIndexPair (dualBlockIndex i k) = (i, k) := by
  unfold dualBlockIndexPair
  have hcast : Fin.cast (Nat.mul_comm n (T - 1)) (dualBlockIndex i k) =
      finProdFinEquiv (i, k) := by
    apply Fin.ext
    simp [dualBlockIndex, finProdFinEquiv]
    omega
  rw [hcast, Equiv.symm_apply_apply]

private theorem serializeUnscaled_evecBasis_Y {T n : Nat}
    (i : Fin (T - 1)) (k : Fin n) :
    serializeUnscaled (0 : UnscaledPrimal T)
        (evecBasis (dualBlockIndex i k) : UnscaledDual T n) =
      (evecBasis (serializedDualIndex i k) : SerializedSpace T n) := by
  apply SerializedSpace.ext_blocks
  · intro j
    rw [serializedA_serializeUnscaled]
    simp [primalA, serializedA, evecBasis,
      serializedAIndex_ne_dualIndex]
  · intro j l
    rw [serializedY_serializeUnscaled]
    unfold dualBlock serializedY evecBasis
    by_cases hji : j = i
    · subst j
      by_cases hlk : l = k
      · subst l
        simp
      · have hdual : dualBlockIndex i l ≠ dualBlockIndex i k := by
          intro h
          have hp := congrArg dualBlockIndexPair h
          rw [main_dualBlockIndex_pair, main_dualBlockIndex_pair] at hp
          exact hlk (congrArg Prod.snd hp)
        have hserial : serializedDualIndex i l ≠ serializedDualIndex i k := by
          intro h
          have hp : (i, l) = (i, k) := serializedDualIndex_injective h
          exact hlk (congrArg Prod.snd hp)
        simp [hdual, hserial]
    · have hdual : dualBlockIndex j l ≠ dualBlockIndex i k := by
        intro h
        have hp := congrArg dualBlockIndexPair h
        rw [main_dualBlockIndex_pair, main_dualBlockIndex_pair] at hp
        exact hji (congrArg Prod.fst hp)
      have hserial : serializedDualIndex j l ≠ serializedDualIndex i k := by
        intro h
        have hp : (j, l) = (i, k) := serializedDualIndex_injective h
        exact hji (congrArg Prod.fst hp)
      simp [hdual, hserial]
  · intro j
    rw [serializedB_serializeUnscaled]
    simp [primalB, serializedB, evecBasis,
      serializedBIndex_ne_dualIndex]
  · intro j
    rw [serializedState_serializeUnscaled]
    simp [primalState, serializedState, evecBasis,
      serializedStateIndex_ne_dualIndex]

private theorem dualBlock_unscaledTrueGradY {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (i : Fin (T - 1)) (k : Fin n) :
    dualBlock (unscaledTrueGradY hn P x y) i k =
      -serializedSaddleGradY hn P (serializeUnscaled x y) i k := by
  let h : UnscaledDual T n := evecBasis (dualBlockIndex i k)
  have hrep := (unscaledTrueGradient_representsJointGradient
    (T := T) hn P).2 x y (0 : UnscaledPrimal T) h
  rw [(unscaledObjective_hasFDerivAt (T := T) hn P x y).fderiv] at hrep
  simp only [ContinuousLinearMap.comp_apply, serializeUnscaledCLM_apply] at hrep
  rw [show serializeUnscaled (0 : UnscaledPrimal T) h =
      (evecBasis (serializedDualIndex i k) : SerializedSpace T n) by
        exact serializeUnscaled_evecBasis_Y i k] at hrep
  simp [h, evecDot_apply, evecBasis, serializedTrueGradient_Y] at hrep
  exact hrep.symm

/-- The packed primal field used by `TaggedResisting` is literally the
genuine Fréchet-gradient field stored in the hard `NCCInstance`. -/
theorem packedTrueGradX_eq_unscaledTrueGradX {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) :
    (packedTrueGradX hn P :
      UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T) =
      unscaledTrueGradX hn P := by
  funext x y j
  obtain ⟨c, hc⟩ := UnscaledTag.primalIndex_surjective (T := T) (n := n) j
  cases c with
  | a i =>
      simp [UnscaledTag.primalIndex] at hc
      subst j
      change primalA (packedTrueGradX hn P x y) i =
        primalA (unscaledTrueGradX hn P x y) i
      rw [primalA_unscaledTrueGradX]
      simp only [packedTrueGradX, primalA_unserializePrimal]
      rw [serializedA, serializedTrueGradient_A]
  | y i k => simp [UnscaledTag.primalIndex] at hc
  | b i =>
      simp [UnscaledTag.primalIndex] at hc
      subst j
      change primalB (packedTrueGradX hn P x y) i =
        primalB (unscaledTrueGradX hn P x y) i
      rw [primalB_unscaledTrueGradX]
      simp only [packedTrueGradX, primalB_unserializePrimal]
      rw [serializedB, serializedTrueGradient_B]
  | state i =>
      simp [UnscaledTag.primalIndex] at hc
      subst j
      change primalState (packedTrueGradX hn P x y) i =
        primalState (unscaledTrueGradX hn P x y) i
      rw [primalState_unscaledTrueGradX]
      simp only [packedTrueGradX, primalState_unserializePrimal]
      rw [serializedState, serializedTrueGradient_state]

/-- The analogous identity for the genuine dual gradient. -/
theorem packedTrueGradY_eq_unscaledTrueGradY {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) :
    (packedTrueGradY hn P :
      UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n) =
      unscaledTrueGradY hn P := by
  funext x y j
  obtain ⟨c, hc⟩ := UnscaledTag.dualIndex_surjective (T := T) (n := n) j
  cases c with
  | a i => simp [UnscaledTag.dualIndex] at hc
  | y i k =>
      simp [UnscaledTag.dualIndex] at hc
      subst j
      change dualBlock (packedTrueGradY hn P x y) i k =
        dualBlock (unscaledTrueGradY hn P x y) i k
      rw [dualBlock_unscaledTrueGradY]
      simp only [packedTrueGradY, dualBlock_unserializeDual]
      rw [serializedDualBlock, serializedY, serializedTrueGradient_Y]
  | b i => simp [UnscaledTag.dualIndex] at hc
  | state i => simp [UnscaledTag.dualIndex] at hc

/-! ## Scaling preserves the genuine tagged field -/

private theorem scaleCoords_eq_smul {d : Nat} (c : ℝ) (z : EVec d) :
    scaleCoords c z = c • z := rfl

private theorem unscaleCoords_eq_scaleCoords_inv {d : Nat} (lambda : ℝ)
    (z : EVec d) :
    unscaleCoords lambda z = scaleCoords (1 / lambda) z := by
  funext i
  simp [unscaleCoords, scaleCoords, div_eq_mul_inv, mul_comm]

theorem serializeUnscaled_scaleCoords {T n : Nat} (c : ℝ)
    (x : UnscaledPrimal T) (y : UnscaledDual T n) :
    serializeUnscaled (scaleCoords c x) (scaleCoords c y) =
      scaleCoords c (serializeUnscaled x y) := by
  rw [scaleCoords_eq_smul, scaleCoords_eq_smul, scaleCoords_eq_smul]
  exact (serializeUnscaledLinear (T := T) (n := n)).map_smul c (x, y)

theorem unserializePrimal_scaleCoords {T n : Nat} (c : ℝ)
    (z : SerializedSpace T n) :
    unserializePrimal (scaleCoords c z) =
      scaleCoords c (unserializePrimal z) := by
  calc
    unserializePrimal (scaleCoords c z) =
        unserializePrimal (scaleCoords c
          (serializeUnscaled (unserializePrimal z) (unserializeDual z))) := by
            rw [serializeUnscaled_unserialize]
    _ = unserializePrimal
        (serializeUnscaled (scaleCoords c (unserializePrimal z))
          (scaleCoords c (unserializeDual z))) := by
            rw [serializeUnscaled_scaleCoords]
    _ = scaleCoords c (unserializePrimal z) := by simp

theorem unserializeDual_scaleCoords {T n : Nat} (c : ℝ)
    (z : SerializedSpace T n) :
    unserializeDual (scaleCoords c z) =
      scaleCoords c (unserializeDual z) := by
  calc
    unserializeDual (scaleCoords c z) =
        unserializeDual (scaleCoords c
          (serializeUnscaled (unserializePrimal z) (unserializeDual z))) := by
            rw [serializeUnscaled_unserialize]
    _ = unserializeDual
        (serializeUnscaled (scaleCoords c (unserializePrimal z))
          (scaleCoords c (unserializeDual z))) := by
            rw [serializeUnscaled_scaleCoords]
    _ = scaleCoords c (unserializeDual z) := by simp

theorem unserializePrimal_unscaleCoords {T n : Nat} (lambda : ℝ)
    (z : SerializedSpace T n) :
    unserializePrimal (unscaleCoords lambda z) =
      unscaleCoords lambda (unserializePrimal z) := by
  rw [unscaleCoords_eq_scaleCoords_inv,
    unserializePrimal_scaleCoords, unscaleCoords_eq_scaleCoords_inv]

theorem unserializeDual_unscaleCoords {T n : Nat} (lambda : ℝ)
    (z : SerializedSpace T n) :
    unserializeDual (unscaleCoords lambda z) =
      unscaleCoords lambda (unserializeDual z) := by
  rw [unscaleCoords_eq_scaleCoords_inv,
    unserializeDual_scaleCoords, unscaleCoords_eq_scaleCoords_inv]

theorem taggedSerializedSaddleFieldOf_scaled {T n : Nat} (lambda amp : ℝ)
    (gx : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gy : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n) :
    taggedSerializedSaddleFieldOf
        (scaledGradX lambda amp gx) (scaledGradY lambda amp gy) =
      scaledVectorField lambda amp
        (taggedSerializedSaddleFieldOf gx gy) := by
  funext z
  unfold taggedSerializedSaddleFieldOf scaledGradX scaledGradY
    scaledVectorField
  change serializeUnscaled
      (scaleCoords (amp / lambda)
        (gx (unscaleCoords lambda (unserializePrimal z))
          (unscaleCoords lambda (unserializeDual z))))
      (-scaleCoords (amp / lambda)
        (gy (unscaleCoords lambda (unserializePrimal z))
          (unscaleCoords lambda (unserializeDual z)))) =
    scaleCoords (amp / lambda)
      (serializeUnscaled
        (gx (unserializePrimal (unscaleCoords lambda z))
          (unserializeDual (unscaleCoords lambda z)))
        (-gy (unserializePrimal (unscaleCoords lambda z))
          (unserializeDual (unscaleCoords lambda z))))
  rw [unserializePrimal_unscaleCoords, unserializeDual_unscaleCoords]
  rw [show -scaleCoords (amp / lambda)
      (gy (unscaleCoords lambda (unserializePrimal z))
        (unscaleCoords lambda (unserializeDual z))) =
      scaleCoords (amp / lambda)
        (-gy (unscaleCoords lambda (unserializePrimal z))
          (unscaleCoords lambda (unserializeDual z))) by
        funext i
        simp [scaleCoords]]
  exact serializeUnscaled_scaleCoords _ _ _

/-- The actual chain-rule gradients of the scaled hard objective satisfy the
same ordered first-order zero-chain used by the resisting construction. -/
theorem concrete_scaledTrueGradient_tagged_zeroChain {T n : Nat}
    (hn : 0 < n) (lambda amp : ℝ) :
    IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf
        (scaledGradX lambda amp
          (unscaledTrueGradX (T := T) hn concreteUnscaledParameters))
        (scaledGradY lambda amp
          (unscaledTrueGradY (T := T) hn concreteUnscaledParameters))) := by
  have hbase := packedTrueGradient_tagged_zeroChain
    (T := T) hn concreteUnscaledParameters
  rw [packedTrueGradX_eq_unscaledTrueGradX,
    packedTrueGradY_eq_unscaledTrueGradY] at hbase
  rw [taggedSerializedSaddleFieldOf_scaled]
  exact scaledVectorField_isFirstOrderZeroChain hbase

/-! ## Exact scaled domains and the terminal serialized coordinate -/

@[simp] theorem scaledDomain_univ {d : Nat} (lambda : ℝ) :
    scaledDomain lambda (Set.univ : Set (EVec d)) = Set.univ := by
  ext z
  simp [scaledDomain]

theorem scaledDomain_diameterBall_div {d : Nat} {lambda D : ℝ}
    (hlambda : 0 < lambda) :
    scaledDomain lambda (diameterBall d (D / lambda)) =
      diameterBall d D := by
  ext z
  change vecSq (unscaleCoords lambda z) ≤ ((D / lambda) / 2) ^ 2 ↔
    vecSq z ≤ (D / 2) ^ 2
  rw [vecSq_unscaleCoords]
  have hleft : (1 / lambda) ^ 2 * vecSq z = vecSq z / lambda ^ 2 := by
    field_simp [hlambda.ne']
  have hright : (D / lambda / 2) ^ 2 = (D / 2) ^ 2 / lambda ^ 2 := by
    field_simp [hlambda.ne']
  rw [hleft, hright]
  exact div_le_div_iff_of_pos_right (sq_pos_of_pos hlambda)

theorem terminal_serializedIndex_eq_last {T n : Nat} (hT : 2 ≤ T) :
    serializedStateIndex (n := n) (terminalMemoryIndex hT) =
      (⟨(T - 1) * (n + 3) - 1, by
          have : 0 < (T - 1) * (n + 3) :=
            Nat.mul_pos (by omega) (by omega)
          omega⟩ :
        Fin ((T - 1) * (n + 3))) := by
  apply Fin.ext
  simp only [serializedStateIndex, terminalMemoryIndex]
  have hstep : (T - 2 + 1) * (n + 3) =
      (T - 2) * (n + 3) + n + 3 := by ring
  have hTm : T - 1 = T - 2 + 1 := by omega
  rw [hTm, hstep]
  omega

theorem terminal_of_last_serialized_zero {T n : Nat} (hT : 2 ≤ T)
    (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (hzero : serializeUnscaled x y
      (⟨(T - 1) * (n + 3) - 1, by
          have : 0 < (T - 1) * (n + 3) :=
            Nat.mul_pos (by omega) (by omega)
          omega⟩ :
        Fin ((T - 1) * (n + 3))) = 0) :
    x (terminalPrimalIndex hT) = 0 := by
  rw [← terminal_serializedIndex_eq_last hT] at hzero
  change serializedState (serializeUnscaled x y) (terminalMemoryIndex hT) = 0 at hzero
  simpa [terminalPrimalIndex, primalState] using hzero

/-! ## Numerical dual-radius constant -/

/-- A concrete version of the paper's absolute maximizer-size constant. -/
def concreteCy : ℝ := Real.sqrt 96000

theorem concreteCy_pos : 0 < concreteCy := by
  unfold concreteCy
  exact Real.sqrt_pos.2 (by norm_num)

theorem concreteCy_sq : concreteCy ^ 2 = 96000 := by
  unfold concreteCy
  exact Real.sq_sqrt (by norm_num)

theorem concreteUnscaledP1_pos : 0 < concreteUnscaledParameters.P1 := by
  change 0 < concreteRadialTransition.P1
  exact lt_trans (by linarith [concreteRadialTransition.P0_gt_one])
    concreteRadialTransition.P0_lt_P1

/-- The floor choice of the inner-chain length guarantees exactly the ball
size hierarchy consumed by the restricted terminal certificate. -/
theorem concrete_sizeHierarchy_of_n_bound {n : Nat} {D0 : ℝ}
    (hD0 : 0 ≤ D0)
    (hn : (n : ℝ) ≤
      D0 / (2 * concreteCy * concreteUnscaledParameters.P1)) :
    96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 ≤
      (D0 / 2) ^ 2 := by
  have hden : 0 < 2 * concreteCy * concreteUnscaledParameters.P1 := by
    exact mul_pos (mul_pos (by norm_num) concreteCy_pos)
      concreteUnscaledP1_pos
  have hmul : (n : ℝ) *
      (2 * concreteCy * concreteUnscaledParameters.P1) ≤ D0 :=
    (le_div_iff₀ hden).mp hn
  have hlinear : concreteCy * (n : ℝ) *
      concreteUnscaledParameters.P1 ≤ D0 / 2 := by
    linarith
  have hsq := (sq_le_sq₀
    (mul_nonneg (mul_nonneg concreteCy_pos.le (Nat.cast_nonneg n))
      concreteUnscaledP1_pos.le)
    (div_nonneg hD0 (by norm_num))).2 hlinear
  calc
    96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 =
        (concreteCy * (n : ℝ) * concreteUnscaledParameters.P1) ^ 2 := by
      rw [mul_pow, mul_pow, concreteCy_sq]
    _ ≤ (D0 / 2) ^ 2 := hsq

/-! ## The one-query loss in the resisting lift only changes the constant -/

theorem lower_dimensions_of_regime
    {ell D Delta eps ell0 c0 Cy P1 cDelta : ℝ}
    (hell : 0 < ell) (_hD : 0 < D) (_hDelta : 0 < Delta) (heps : 0 < eps)
    (hell0 : 0 < ell0) (hc0 : 0 < c0) (hCy : 0 < Cy)
    (hP1 : 0 < P1) (hcDelta : 0 < cDelta)
    (hNregime : 20 ≤ c0 * ell * D / (8 * Cy * P1 * ell0 * eps))
    (hTregime : 4 ≤ c0 ^ 2 * ell * Delta /
      (32 * cDelta * ell0 * eps ^ 2)) :
    10 ≤ lowerN D Cy P1 ell ell0 eps c0 ∧
      2 ≤ lowerT Delta cDelta ell ell0 eps c0 := by
  have hNeq := lowerNArg_eq (D := D) (Cy := Cy) (P1 := P1)
    hCy.ne' hP1.ne' hell.ne' hell0.ne' heps.ne' hc0.ne'
  have hTeq := lowerTArg_eq (Delta := Delta) (cDelta := cDelta)
    hcDelta.ne' hell.ne' hell0.ne' heps.ne' hc0.ne'
  have hrawN : 20 ≤ lowerNArg D Cy P1 ell ell0 eps c0 := by
    rw [hNeq]
    exact hNregime
  have hrawT : 4 ≤ lowerTArg Delta cDelta ell ell0 eps c0 := by
    rw [hTeq]
    exact hTregime
  have hNfloor := half_le_natFloor (by linarith :
    2 ≤ lowerNArg D Cy P1 ell ell0 eps c0)
  have hTfloor := half_le_natFloor (by linarith :
    2 ≤ lowerTArg Delta cDelta ell ell0 eps c0)
  constructor
  · have hreal : (10 : ℝ) ≤ (lowerN D Cy P1 ell ell0 eps c0 : ℝ) := by
      change (10 : ℝ) ≤
        (⌊lowerNArg D Cy P1 ell ell0 eps c0⌋₊ : ℝ)
      linarith
    exact_mod_cast hreal
  · have hreal : (2 : ℝ) ≤
        (lowerT Delta cDelta ell ell0 eps c0 : ℝ) := by
      change (2 : ℝ) ≤
        (⌊lowerTArg Delta cDelta ell ell0 eps c0⌋₊ : ℝ)
      linarith
    exact_mod_cast hreal

theorem lowerN_cast_le_arg
    {ell D eps ell0 c0 Cy P1 : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps)
    (hell0 : 0 < ell0) (hc0 : 0 < c0) (hCy : 0 < Cy)
    (hP1 : 0 < P1) :
    (lowerN D Cy P1 ell ell0 eps c0 : ℝ) ≤
      lowerNArg D Cy P1 ell ell0 eps c0 := by
  unfold lowerN
  apply Nat.floor_le
  unfold lowerNArg lowerScale
  positivity

theorem lowerT_cast_le_arg
    {ell Delta eps ell0 c0 cDelta : ℝ}
    (hell : 0 < ell) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hell0 : 0 < ell0) (hc0 : 0 < c0) (hcDelta : 0 < cDelta) :
    (lowerT Delta cDelta ell ell0 eps c0 : ℝ) ≤
      lowerTArg Delta cDelta ell ell0 eps c0 := by
  unfold lowerT
  apply Nat.floor_le
  unfold lowerTArg lowerScale
  positivity

/-- The outer floor choice leaves a factor two of slack in the source gap,
which is enough to populate the `ScalingSource` gap field. -/
theorem concreteDelta0_lowerT_le_scaled_gap
    {ell Delta eps ell0 c0 : ℝ}
    (hell : 0 < ell) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hell0 : 0 < ell0) (hc0 : 0 < c0)
    (hTone : 1 ≤ lowerT Delta concreteCDelta ell ell0 eps c0) :
    concreteDelta0 (lowerT Delta concreteCDelta ell ell0 eps c0) ≤
      Delta / lowerAmplitude ell ell0
        (lowerScale ell ell0 eps c0) := by
  let T := lowerT Delta concreteCDelta ell ell0 eps c0
  let lambda := lowerScale ell ell0 eps c0
  let amp := lowerAmplitude ell ell0 lambda
  have hlambda : 0 < lambda := by
    dsimp [lambda, lowerScale]
    positivity
  have hamp : 0 < amp := by
    dsimp [amp, lowerAmplitude]
    positivity
  have hdelta := concreteDelta0_le_concreteCDelta_mul T hTone
  have hTarg := lowerT_cast_le_arg hell hDelta heps hell0 hc0
    concreteCDelta_pos
  have hmul : concreteCDelta * (T : ℝ) ≤
      concreteCDelta * lowerTArg Delta concreteCDelta ell ell0 eps c0 :=
    mul_le_mul_of_nonneg_left (by simpa [T] using hTarg)
      concreteCDelta_pos.le
  have heq : concreteCDelta *
      lowerTArg Delta concreteCDelta ell ell0 eps c0 =
        Delta / (2 * amp) := by
    dsimp [lowerTArg, amp, lambda, lowerAmplitude]
    field_simp [concreteCDelta_pos.ne', hell.ne', hell0.ne',
      heps.ne', hc0.ne']
  have hhalf : Delta / (2 * amp) ≤ Delta / amp := by
    have hq : 0 ≤ Delta / amp := div_nonneg hDelta.le hamp.le
    calc
      Delta / (2 * amp) = (Delta / amp) / 2 := by
        field_simp [hamp.ne']
      _ ≤ Delta / amp := by linarith
  change concreteDelta0 T ≤ Delta / amp
  calc
    concreteDelta0 T ≤ concreteCDelta * (T : ℝ) := hdelta
    _ ≤ concreteCDelta *
        lowerTArg Delta concreteCDelta ell ell0 eps c0 := hmul
    _ = Delta / (2 * amp) := heq
    _ ≤ Delta / amp := hhalf

/-- The inner floor choice implies the exact restricted-ball hierarchy at
the unscaled diameter `D / lambda`. -/
theorem concrete_lowerN_sizeHierarchy
    {ell D eps ell0 c0 : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (heps : 0 < eps)
    (hell0 : 0 < ell0) (hc0 : 0 < c0) :
    96000 *
        (lowerN D concreteCy concreteUnscaledParameters.P1
          ell ell0 eps c0 : ℝ) ^ 2 *
        concreteUnscaledParameters.P1 ^ 2 ≤
      (((D / lowerScale ell ell0 eps c0) / 2) ^ 2) := by
  let lambda := lowerScale ell ell0 eps c0
  let n := lowerN D concreteCy concreteUnscaledParameters.P1
    ell ell0 eps c0
  have hlambda : 0 < lambda := by
    dsimp [lambda, lowerScale]
    positivity
  have hnarg := lowerN_cast_le_arg hell hD heps hell0 hc0
    concreteCy_pos concreteUnscaledP1_pos
  have hargEq : lowerNArg D concreteCy concreteUnscaledParameters.P1
      ell ell0 eps c0 =
      (D / lambda) /
        (2 * concreteCy * concreteUnscaledParameters.P1) := by
    dsimp [lowerNArg, lambda]
    field_simp [hlambda.ne', concreteCy_pos.ne',
      concreteUnscaledP1_pos.ne']
  have hn : (n : ℝ) ≤
      (D / lambda) /
        (2 * concreteCy * concreteUnscaledParameters.P1) := by
    rw [← hargEq]
    simpa [n] using hnarg
  have hsize := concrete_sizeHierarchy_of_n_bound
    (n := n) (D0 := D / lambda) (by positivity) hn
  simpa [n, lambda] using hsize

/-- The online completion theorem needs a strict horizon inequality.  We use
`K = M - 1`, and this lemma absorbs that single lost query into an explicit
factor two in the headline constant. -/
theorem scaled_resisting_horizon_lower
    {ell D Delta eps ell0 c0 Cy P1 cDelta : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hell0 : 0 < ell0) (hc0 : 0 < c0) (hCy : 0 < Cy)
    (hP1 : 0 < P1) (hcDelta : 0 < cDelta)
    (hNregime : 20 ≤ c0 * ell * D / (8 * Cy * P1 * ell0 * eps))
    (hTregime : 4 ≤ c0 ^ 2 * ell * Delta /
      (32 * cDelta * ell0 * eps ^ 2)) :
    c0 ^ 3 / (2048 * Cy * P1 * cDelta * ell0 ^ 2) *
        (ell ^ 2 * D * Delta / eps ^ 3) ≤
      ((((lowerT Delta cDelta ell ell0 eps c0 - 1) *
        (lowerN D Cy P1 ell ell0 eps c0 + 3)) - 1 : Nat) : ℝ) := by
  let M : Nat := (lowerT Delta cDelta ell ell0 eps c0 - 1) *
    (lowerN D Cy P1 ell ell0 eps c0 + 3)
  have hbase :
      c0 ^ 3 / (1024 * Cy * P1 * cDelta * ell0 ^ 2) *
          (ell ^ 2 * D * Delta / eps ^ 3) ≤ (M : ℝ) := by
    simpa [M] using scaled_chain_length_lower hell hD hDelta heps hell0
      hc0 hCy hP1 hcDelta hNregime hTregime
  have hTeq := lowerTArg_eq (Delta := Delta) (cDelta := cDelta)
    hcDelta.ne' hell.ne' hell0.ne' heps.ne' hc0.ne'
  have hrawT : 4 ≤ lowerTArg Delta cDelta ell ell0 eps c0 := by
    rw [hTeq]
    exact hTregime
  have hTfloorReal : (2 : ℝ) ≤
      (lowerT Delta cDelta ell ell0 eps c0 : ℝ) := by
    have hhalfT := half_le_natFloor (by linarith :
      2 ≤ lowerTArg Delta cDelta ell ell0 eps c0)
    change (2 : ℝ) ≤
      (⌊lowerTArg Delta cDelta ell ell0 eps c0⌋₊ : ℝ)
    linarith
  have hTfloor : 2 ≤ lowerT Delta cDelta ell ell0 eps c0 := by
    exact_mod_cast hTfloorReal
  have houter : 1 ≤ lowerT Delta cDelta ell ell0 eps c0 - 1 := by omega
  have hinner : 3 ≤ lowerN D Cy P1 ell ell0 eps c0 + 3 := by omega
  have hMthree : 3 ≤ M := by
    have hmul := Nat.mul_le_mul houter hinner
    simpa [M] using hmul
  have hhalf : (M : ℝ) / 2 ≤ ((M - 1 : Nat) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ M)]
    have hMthreeReal : (3 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMthree
    linarith
  change _ ≤ ((M - 1 : Nat) : ℝ)
  calc
    c0 ^ 3 / (2048 * Cy * P1 * cDelta * ell0 ^ 2) *
        (ell ^ 2 * D * Delta / eps ^ 3) =
      (c0 ^ 3 / (1024 * Cy * P1 * cDelta * ell0 ^ 2) *
        (ell ^ 2 * D * Delta / eps ^ 3)) / 2 := by ring
    _ ≤ (M : ℝ) / 2 := div_le_div_of_nonneg_right hbase (by norm_num)
    _ ≤ ((M - 1 : Nat) : ℝ) := hhalf

/-! ## Assumption-free terminal failure on the visible scaled ball -/

theorem concrete_paperScaledValue_not_OS_visible_ball
    {T n : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n)
    {ell ell0 D eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hD : 0 < D) (heps : 0 < eps)
    (hsizeHierarchy :
      96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 ≤
        (((D / lowerScale ell ell0 eps (concreteTerminalC0 ell0)) / 2) ^ 2))
    {x : UnscaledPrimal T}
    (hxterminal : x (terminalPrimalIndex hT) = 0) :
    ¬ IsOptimizationStationary Set.univ
      (ValueOn (diameterBall (n * (T - 1)) D)
        (scaledObjective
          (lowerScale ell ell0 eps (concreteTerminalC0 ell0))
          (lowerAmplitude ell ell0
            (lowerScale ell ell0 eps (concreteTerminalC0 ell0)))
          (unscaledObjective (T := T) (by omega : 0 < n)
            concreteUnscaledParameters))) ell eps x := by
  let c0 := concreteTerminalC0 ell0
  let lambda := lowerScale ell ell0 eps c0
  have hc0 : 0 < c0 := concreteTerminalC0_pos hell0
  have hlambda : 0 < lambda := by
    dsimp [lambda, lowerScale]
    positivity
  have hraw :=
    concrete_paperScaledValue_not_optimizationStationary_no_assumption
      hT hn (D := D / lambda) (by positivity : 0 ≤ D / lambda)
      (by simpa [lambda, c0] using hsizeHierarchy)
      hell hell0 heps hxterminal
  dsimp only at hraw
  rw [scaledDomain_univ,
    scaledDomain_diameterBall_div (D := D) hlambda] at hraw
  simpa [lambda, c0] using hraw

/-! ## Terminal failure transported through the resisting rotation -/

/-- A reusable assembly lemma.  Once the base bounded-dual value fails the
OS test whenever its last memory coordinate is zero, every deterministic
ambient-domain component fails at all queries in the strict resisting
horizon.  The orthonormal frames are produced, not assumed. -/
theorem finite_horizon_rotated_OS_failure_of_terminal
    {T n DX DY K : Nat} (hT : 2 ≤ T) {D ell eps : ℝ}
    (A : Oracle.DeterministicFOComponent
      (Set.univ : Set (EVec DX)) (diameterBall DY D))
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (hchain : IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY)
    (hell : 0 ≤ ell)
    (hmax : ∀ x, ∃ y,
      IsMaximizerOn (diameterBall (n * (T - 1)) D) F x y)
    (hfailure : ∀ x : UnscaledPrimal T,
      x (terminalPrimalIndex hT) = 0 →
        ¬ IsOptimizationStationary Set.univ
          (ValueOn (diameterBall (n * (T - 1)) D) F) ell eps x) :
    ∃ U V, IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      Oracle.DeterministicFOComponent.FailsWithin A
        (productRotatedInstance (Set.univ : Set (EVec DX))
          (diameterBall DY D) U V F gradX gradY) ell eps K := by
  obtain ⟨U, V, hU, hV, hterminal⟩ :=
    finite_horizon_tagged_queried_terminal_orthonormal
      A F gradX gradY hchain hKM hcapX hcapY
  refine ⟨U, V, hU, hV, ?_⟩
  change ∀ t < K, ¬ IsOptimizationStationary Set.univ
    (ValueOn (diameterBall DY D) (rotatedF U V F)) ell eps
      (Oracle.DeterministicFOComponent.queriedAt A
        (productRotatedInstance (Set.univ : Set (EVec DX))
          (diameterBall DY D) U V F gradX gradY) t).1
  intro t ht hos
  let P := productRotatedInstance (Set.univ : Set (EVec DX))
    (diameterBall DY D) U V F gradX gradY
  let q := Oracle.DeterministicFOComponent.queriedAt A P t
  have hlast : serializeUnscaled (frameProject U q.1) (frameProject V q.2)
      (⟨(T - 1) * (n + 3) - 1, by
          have : 0 < (T - 1) * (n + 3) :=
            Nat.mul_pos (by omega) (by omega)
          omega⟩ : Fin ((T - 1) * (n + 3))) = 0 := by
    simpa [q, P] using hterminal t ht
  have hxterminal : frameProject U q.1 (terminalPrimalIndex hT) = 0 :=
    terminal_of_last_serialized_zero hT _ _ hlast
  apply hfailure (frameProject U q.1) hxterminal
  have hcov := liftedSaddle_optimizationStationarity_iff
    (eps := eps) hU hV hell hmax q.1
  apply hcov.mp
  change IsOptimizationStationary Set.univ
    (ValueOn (diameterBall DY D) (rotatedF U V F)) ell eps q.1
  simpa [q, P] using hos

/-- Class closure and terminal failure packaged into one hard ambient
instance for an arbitrary deterministic component. -/
theorem exists_rotated_hard_instance_of_terminal
    {T n DX DY K : Nat} (hT : 2 ≤ T) {ell D Delta eps : ℝ}
    (A : Oracle.DeterministicFOComponent
      (Set.univ : Set (EVec DX)) (diameterBall DY D))
    (P : NCCInstance (3 * (T - 1)) (n * (T - 1)))
    (hclass : IsNCCClass ell D Delta P)
    (hX : P.X = Set.univ)
    (hY : P.Y = diameterBall (n * (T - 1)) D)
    (hx0 : P.x0 = 0)
    (hchain : IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf P.gradX P.gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY)
    (hfailure : ∀ x : UnscaledPrimal T,
      x (terminalPrimalIndex hT) = 0 →
        ¬ IsOptimizationStationary Set.univ
          (ValueOn (diameterBall (n * (T - 1)) D) P.f) ell eps x) :
    ∃ Q : NCCInstance DX DY,
      IsNCCClass ell D Delta Q ∧
      Oracle.DeterministicFOComponent.FailsWithin A Q ell eps K ∧
      Q.X = Set.univ ∧
      Q.Y = diameterBall DY D ∧
      Q.x0 = 0 := by
  have hmax : ∀ x, ∃ y,
      IsMaximizerOn (diameterBall (n * (T - 1)) D) P.f x y := by
    intro x
    have hx : x ∈ P.X := by rw [hX]; simp
    simpa [hY] using hclass.maximum_attained x hx
  obtain ⟨U, V, hU, hV, hfail⟩ :=
    finite_horizon_rotated_OS_failure_of_terminal hT A P.f P.gradX P.gradY
      hchain hKM hcapX hcapY hclass.ell_pos.le hmax hfailure
  let Q := productRotatedInstance (Set.univ : Set (EVec DX))
    (diameterBall DY D) U V P.f P.gradX P.gradY
  refine ⟨Q, ?_, ?_, ?_, ?_, ?_⟩
  · have hrot := hclass.rotate_symmetric hX hY hx0 hU hV
    simpa [Q, productRotatedInstance, rotatedNCCInstance] using hrot
  · simpa [Q] using hfail
  · rfl
  · rfl
  · rfl

/-! ## Literal paper-class regularity -/

/-- The concrete unscaled objective is globally `C¹`.  Its Fréchet
derivative is the continuous serialized derivative already used by the
restricted Danskin theorem. -/
theorem concrete_unscaledObjective_contDiff_one {T n : Nat} (hn : 0 < n) :
    ContDiff ℝ 1 (Function.uncurry
      (unscaledObjective (T := T) hn concreteUnscaledParameters)) := by
  apply contDiff_one_iff_fderiv.2
  constructor
  · intro p
    exact (concreteJointDerivative_hasFDerivAt hn p).differentiableAt
  · have heq : fderiv ℝ (Function.uncurry
          (unscaledObjective (T := T) hn concreteUnscaledParameters)) =
        concreteJointDerivative hn := by
      funext p
      exact (concreteJointDerivative_hasFDerivAt hn p).fderiv
    rw [heq]
    exact continuous_concreteJointDerivative hn

/-- The terminal resisting construction preserves not only the analytic
class record but also the paper's literal neighborhood-`C¹` class. -/
theorem exists_paper_rotated_hard_instance_of_terminal
    {T n DX DY K : Nat} (hT : 2 ≤ T) {ell D Delta eps : ℝ}
    (A : Oracle.DeterministicFOComponent
      (Set.univ : Set (EVec DX)) (diameterBall DY D))
    (P : NCCInstance (3 * (T - 1)) (n * (T - 1)))
    (hclass : IsNCCClass ell D Delta P)
    (hC1 : ContDiff ℝ 1 (Function.uncurry P.f))
    (hX : P.X = Set.univ)
    (hY : P.Y = diameterBall (n * (T - 1)) D)
    (hx0 : P.x0 = 0)
    (hchain : IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf P.gradX P.gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY)
    (hfailure : ∀ x : UnscaledPrimal T,
      x (terminalPrimalIndex hT) = 0 →
        ¬ IsOptimizationStationary Set.univ
          (ValueOn (diameterBall (n * (T - 1)) D) P.f) ell eps x) :
    ∃ Q : NCCInstance DX DY,
      IsNCCClass ell D Delta Q ∧
      IsPaperNCCClass ell D Delta Q ∧
      Oracle.DeterministicFOComponent.FailsWithin A Q ell eps K ∧
      Q.X = Set.univ ∧
      Q.Y = diameterBall DY D ∧
      Q.x0 = 0 := by
  have hmax : ∀ x, ∃ y,
      IsMaximizerOn (diameterBall (n * (T - 1)) D) P.f x y := by
    intro x
    have hx : x ∈ P.X := by rw [hX]; simp
    simpa [hY] using hclass.maximum_attained x hx
  obtain ⟨U, V, hU, hV, hfail⟩ :=
    finite_horizon_rotated_OS_failure_of_terminal hT A P.f P.gradX P.gradY
      hchain hKM hcapX hcapY hclass.ell_pos.le hmax hfailure
  let Q := productRotatedInstance (Set.univ : Set (EVec DX))
    (diameterBall DY D) U V P.f P.gradX P.gradY
  have hrot : IsNCCClass ell D Delta Q := by
    have h := hclass.rotate_symmetric hX hY hx0 hU hV
    simpa [Q, productRotatedInstance, rotatedNCCInstance] using h
  have hQC1 : ContDiff ℝ 1 (Function.uncurry Q.f) := by
    simpa [Q, productRotatedInstance] using rotatedF_contDiff_one U V hC1
  refine ⟨Q, hrot, hrot.toPaper hQC1, ?_, ?_, ?_, ?_⟩
  · simpa [Q] using hfail
  · rfl
  · rfl
  · rfl

/-! ## The concrete scaled instance, conditional only on regularity data -/

/-- All information-theoretic and terminal parts of the lower bound are now
fully concrete.  The sole input left here is the analytic `ScalingSource`
record; the final theorem below instantiates it with the uniform regularity
certificate. -/
theorem exists_concrete_scaled_rotated_hard_instance
    {T n DX DY K : Nat} (hT : 2 ≤ T) (hn : 10 ≤ n)
    {ell ell0 D Delta eps : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (hsizeHierarchy :
      96000 * (n : ℝ) ^ 2 * concreteUnscaledParameters.P1 ^ 2 ≤
        (((D / lowerScale ell ell0 eps (concreteTerminalC0 ell0)) / 2) ^ 2))
    (hsrc : ScalingSource ell0
      (D / lowerScale ell ell0 eps (concreteTerminalC0 ell0))
      (Delta / lowerAmplitude ell ell0
        (lowerScale ell ell0 eps (concreteTerminalC0 ell0)))
      (unscaledNCCInstance (T := T) (by omega : 0 < n)
        concreteUnscaledParameters
        (D / lowerScale ell ell0 eps (concreteTerminalC0 ell0))))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY)
    (A : Oracle.DeterministicFOComponent
      (Set.univ : Set (EVec DX)) (diameterBall DY D)) :
    ∃ Q : NCCInstance DX DY,
      IsNCCClass ell D Delta Q ∧
      IsPaperNCCClass ell D Delta Q ∧
      Oracle.DeterministicFOComponent.FailsWithin A Q ell eps K ∧
      Q.X = Set.univ ∧
      Q.Y = diameterBall DY D ∧
      Q.x0 = 0 := by
  let c0 := concreteTerminalC0 ell0
  let lambda := lowerScale ell ell0 eps c0
  let amp := lowerAmplitude ell ell0 lambda
  let P0 := unscaledNCCInstance (T := T) (by omega : 0 < n)
    concreteUnscaledParameters (D / lambda)
  let P := scaleNCCInstance lambda amp P0
  have hc0 : 0 < c0 := concreteTerminalC0_pos hell0
  have hlambda : 0 < lambda := by
    dsimp [lambda, lowerScale]
    positivity
  have hclass : IsNCCClass ell D Delta P := by
    apply paper_scaleNCCInstance_isNCCClass hell hell0 hD hDelta hlambda
    simpa [P0, lambda, amp, c0] using hsrc
  have hX : P.X = Set.univ := by
    simp [P, P0, scaleNCCInstance, unscaledNCCInstance,
      unscaledPrimalDomain, scaledDomain_univ]
  have hY : P.Y = diameterBall (n * (T - 1)) D := by
    change scaledDomain lambda
      (diameterBall (n * (T - 1)) (D / lambda)) =
        diameterBall (n * (T - 1)) D
    exact scaledDomain_diameterBall_div hlambda
  have hx0 : P.x0 = 0 := by
    change scaleCoords lambda (0 : UnscaledPrimal T) = 0
    funext i
    simp [scaleCoords]
  have hchain : IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf P.gradX P.gradY) := by
    simpa [P, P0, scaleNCCInstance, unscaledNCCInstance] using
      (concrete_scaledTrueGradient_tagged_zeroChain
        (T := T) (n := n) (by omega : 0 < n) lambda amp)
  have hfailure : ∀ x : UnscaledPrimal T,
      x (terminalPrimalIndex hT) = 0 →
        ¬ IsOptimizationStationary Set.univ
          (ValueOn (diameterBall (n * (T - 1)) D) P.f) ell eps x := by
    intro x hx
    have hf := concrete_paperScaledValue_not_OS_visible_ball
      hT hn hell hell0 hD heps
      (by simpa [lambda, c0] using hsizeHierarchy) hx
    simpa [P, P0, scaleNCCInstance, lambda, amp, c0,
      unscaledNCCInstance] using hf
  have hC1 : ContDiff ℝ 1 (Function.uncurry P.f) := by
    have hbase := concrete_unscaledObjective_contDiff_one
      (T := T) (n := n) (by omega : 0 < n)
    have hscaled := scaledObjective_contDiff_one lambda amp hbase
    simpa [P, P0, scaleNCCInstance, unscaledNCCInstance] using hscaled
  exact exists_paper_rotated_hard_instance_of_terminal hT A P hclass hC1
    hX hY hx0 hchain hKM hcapX hcapY hfailure

/-! ## Canonical floor dimensions and the headline theorem -/

def concreteHardN (ell0 ell D eps : ℝ) : Nat :=
  lowerN D concreteCy concreteUnscaledParameters.P1 ell ell0 eps
    (concreteTerminalC0 ell0)

def concreteHardT (ell0 ell Delta eps : ℝ) : Nat :=
  lowerT Delta concreteCDelta ell ell0 eps (concreteTerminalC0 ell0)

def concreteHardM (ell0 ell D Delta eps : ℝ) : Nat :=
  (concreteHardT ell0 ell Delta eps - 1) *
    (concreteHardN ell0 ell D eps + 3)

/-- Strict resisting horizon used by the formal theorem. -/
def concreteHardK (ell0 ell D Delta eps : ℝ) : Nat :=
  concreteHardM ell0 ell D Delta eps - 1

def concreteHardDX (ell0 ell D Delta eps : ℝ) : Nat :=
  3 * (concreteHardT ell0 ell Delta eps - 1) +
    (concreteHardK ell0 ell D Delta eps + 2)

def concreteHardDY (ell0 ell D Delta eps : ℝ) : Nat :=
  concreteHardN ell0 ell D eps *
      (concreteHardT ell0 ell Delta eps - 1) +
    (concreteHardK ell0 ell D Delta eps + 2)

/-- Headline component-wise lower bound from any dimension-free source
regularity certificate.  This theorem already quantifies an arbitrary
deterministic component and has no value-gradient or differentiability
hypothesis. -/
theorem concrete_deterministic_lower_bound_of_uniform_source
    {ell0 ell D Delta eps : ℝ}
    (hell0 : 0 < ell0) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ lowerAccuracyConstant ell0
      (concreteTerminalC0 ell0) concreteCy
      concreteUnscaledParameters.P1 concreteCDelta *
        min (ell * D) (Real.sqrt (ell * Delta)))
    (hsource : ∀ {T n : Nat} (hT : 1 ≤ T) (hn : 10 ≤ n)
      {D0 Delta0 : ℝ},
      0 < D0 → concreteDelta0 T ≤ Delta0 →
        ScalingSource ell0 D0 Delta0
          (unscaledNCCInstance (T := T) (n := n) (by omega)
            concreteUnscaledParameters D0))
    (A : Oracle.DeterministicFOComponent
      (Set.univ : Set (EVec (concreteHardDX ell0 ell D Delta eps)))
      (diameterBall (concreteHardDY ell0 ell D Delta eps) D)) :
    ∃ Q : NCCInstance (concreteHardDX ell0 ell D Delta eps)
        (concreteHardDY ell0 ell D Delta eps),
      IsNCCClass ell D Delta Q ∧
      IsPaperNCCClass ell D Delta Q ∧
      Oracle.DeterministicFOComponent.FailsWithin A Q ell eps
        (concreteHardK ell0 ell D Delta eps) ∧
      Q.X = Set.univ ∧
      Q.Y = diameterBall (concreteHardDY ell0 ell D Delta eps) D ∧
      Q.x0 = 0 ∧
      concreteTerminalC0 ell0 ^ 3 /
          (2048 * concreteCy * concreteUnscaledParameters.P1 *
            concreteCDelta * ell0 ^ 2) *
          (ell ^ 2 * D * Delta / eps ^ 3) ≤
        (concreteHardK ell0 ell D Delta eps : ℝ) := by
  let c0 := concreteTerminalC0 ell0
  let n := concreteHardN ell0 ell D eps
  let T := concreteHardT ell0 ell Delta eps
  let M := concreteHardM ell0 ell D Delta eps
  let K := concreteHardK ell0 ell D Delta eps
  let DX := concreteHardDX ell0 ell D Delta eps
  let DY := concreteHardDY ell0 ell D Delta eps
  let lambda := lowerScale ell ell0 eps c0
  let amp := lowerAmplitude ell ell0 lambda
  have hc0 : 0 < c0 := concreteTerminalC0_pos hell0
  have hlambda : 0 < lambda := by
    dsimp [lambda, lowerScale]
    positivity
  have hregime := lower_size_regime_of_accuracy hell hD hDelta heps hell0
    hc0 concreteCy_pos concreteUnscaledP1_pos concreteCDelta_pos
    (by simpa [c0] using haccuracy)
  have hdims := lower_dimensions_of_regime hell hD hDelta heps hell0 hc0
    concreteCy_pos concreteUnscaledP1_pos concreteCDelta_pos
    hregime.1 hregime.2
  have hn : 10 ≤ n := by
    simpa [n, concreteHardN, c0] using hdims.1
  have hT : 2 ≤ T := by
    simpa [T, concreteHardT, c0] using hdims.2
  have hsize : 96000 * (n : ℝ) ^ 2 *
      concreteUnscaledParameters.P1 ^ 2 ≤ ((D / lambda) / 2) ^ 2 := by
    simpa [n, lambda, concreteHardN, c0] using
      (concrete_lowerN_sizeHierarchy hell hD heps hell0 hc0)
  have hgap : concreteDelta0 T ≤ Delta / amp := by
    have hTone : 1 ≤ lowerT Delta concreteCDelta ell ell0 eps c0 := by
      simpa [T, concreteHardT, c0] using (show 1 ≤ T by omega)
    simpa [T, amp, lambda, concreteHardT, c0] using
      (concreteDelta0_lowerT_le_scaled_gap hell hDelta heps hell0 hc0 hTone)
  have hsrc : ScalingSource ell0 (D / lambda) (Delta / amp)
      (unscaledNCCInstance (T := T) (by omega : 0 < n)
        concreteUnscaledParameters (D / lambda)) :=
    hsource (by omega) hn (by positivity) hgap
  have hMdef : M = (T - 1) * (n + 3) := by
    simp [M, T, n, concreteHardM]
  have hMpos : 0 < M := by
    rw [hMdef]
    exact Nat.mul_pos (by omega) (by omega)
  have hKdef : K = M - 1 := by rfl
  have hKM : K < (T - 1) * (n + 3) := by
    rw [hMdef] at hKdef hMpos
    rw [hKdef]
    omega
  have hcapX : 3 * (T - 1) + (K + 1) < DX := by
    dsimp [DX, concreteHardDX]
    simp [T, K]
  have hcapY : n * (T - 1) + (K + 1) < DY := by
    dsimp [DY, concreteHardDY]
    simp [T, n, K]
  have hhard := exists_concrete_scaled_rotated_hard_instance
    hT hn hell hell0 hD hDelta heps hsize hsrc hKM hcapX hcapY A
  have hrate := scaled_resisting_horizon_lower hell hD hDelta heps hell0
    hc0 concreteCy_pos concreteUnscaledP1_pos concreteCDelta_pos
    hregime.1 hregime.2
  obtain ⟨Q, hclass, hpaper, hfail, hQX, hQY, hQx0⟩ := hhard
  refine ⟨Q, hclass, hpaper, hfail, hQX, hQY, hQx0, ?_⟩
  simpa [K, M, T, n, concreteHardK, concreteHardM,
    concreteHardT, concreteHardN, c0] using hrate

end

end NCCLowerBoundVerification
