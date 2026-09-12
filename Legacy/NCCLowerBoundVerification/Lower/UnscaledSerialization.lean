import NCCLowerBoundVerification.Lower.UnscaledObjective

/-!
# The separated and serialized forms of the unscaled objective

The hard instance is stated on separate primal and dual spaces, while its
zero-chain is proved after interleaving the coordinates block by block.  This
file gives the actual coordinate permutation between those two views.
-/

namespace NCCLowerBoundVerification

noncomputable section

/-- Interleave `(a_i, y_{i,0}, ..., y_{i,n-1}, b_i, s_{i+1})` in every
outer block. -/
def serializeUnscaled {T n : Nat} (x : UnscaledPrimal T)
    (y : UnscaledDual T n) : SerializedSpace T n :=
  fun j =>
    let ik := finProdFinEquiv.symm j
    let i := ik.1
    let k := ik.2
    if hA : k.val = 0 then primalA x i
    else if hY : k.val ≤ n then
      dualBlock y i ⟨k.val - 1, by omega⟩
    else if hB : k.val = n + 1 then primalB x i
    else primalState x i

/-- Regard a primal coordinate as an outer block and one of `a,b,s`. -/
def primalBlockIndex {T : Nat} (j : Fin (3 * (T - 1))) :
    Fin (T - 1) × Fin 3 :=
  finProdFinEquiv.symm (Fin.cast (Nat.mul_comm 3 (T - 1)) j)

/-- Recover the primal vector from the interleaved coordinates. -/
def unserializePrimal {T n : Nat} (q : SerializedSpace T n) :
    UnscaledPrimal T :=
  fun j =>
    let ik := primalBlockIndex j
    if _hA : ik.2.val = 0 then serializedA q ik.1
    else if _hB : ik.2.val = 1 then serializedB q ik.1
    else serializedState q ik.1

/-- Regard a dual coordinate as an outer block and an inner-chain index. -/
def dualBlockIndexPair {T n : Nat} (j : Fin (n * (T - 1))) :
    Fin (T - 1) × Fin n :=
  finProdFinEquiv.symm (Fin.cast (Nat.mul_comm n (T - 1)) j)

/-- Recover the dual vector from the interleaved coordinates. -/
def unserializeDual {T n : Nat} (q : SerializedSpace T n) :
    UnscaledDual T n :=
  fun j =>
    let ik := dualBlockIndexPair j
    serializedY q ik.1 ik.2

/-- Unserialization is a fixed coordinate permutation, hence continuous. -/
theorem continuous_unserializePrimal {T n : Nat} :
    Continuous (unserializePrimal (T := T) (n := n)) := by
  apply continuous_pi
  intro j
  unfold unserializePrimal
  dsimp only
  split_ifs
  · unfold serializedA
    exact continuous_apply _
  · unfold serializedB
    exact continuous_apply _
  · unfold serializedState
    exact continuous_apply _

/-- Dual unserialization is likewise a fixed coordinate projection. -/
theorem continuous_unserializeDual {T n : Nat} :
    Continuous (unserializeDual (T := T) (n := n)) := by
  apply continuous_pi
  intro j
  unfold unserializeDual serializedY
  dsimp only
  exact continuous_apply _

private theorem serializedAIndex_prod {T n : Nat} (i : Fin (T - 1)) :
    serializedAIndex (n := n) i =
      finProdFinEquiv ((i, ⟨0, by omega⟩) :
        Fin (T - 1) × Fin (n + 3)) := by
  apply Fin.ext
  simp [serializedAIndex, finProdFinEquiv, Nat.mul_comm]

private theorem serializedDualIndex_prod {T n : Nat}
    (i : Fin (T - 1)) (k : Fin n) :
    serializedDualIndex i k =
      finProdFinEquiv ((i, ⟨k.val + 1, by omega⟩) :
        Fin (T - 1) × Fin (n + 3)) := by
  apply Fin.ext
  simp [serializedDualIndex, finProdFinEquiv, Nat.mul_comm]
  omega

private theorem serializedBIndex_prod {T n : Nat} (i : Fin (T - 1)) :
    serializedBIndex (n := n) i =
      finProdFinEquiv ((i, ⟨n + 1, by omega⟩) :
        Fin (T - 1) × Fin (n + 3)) := by
  apply Fin.ext
  simp [serializedBIndex, finProdFinEquiv, Nat.mul_comm]
  omega

private theorem serializedStateIndex_prod {T n : Nat} (i : Fin (T - 1)) :
    serializedStateIndex (n := n) i =
      finProdFinEquiv ((i, ⟨n + 2, by omega⟩) :
        Fin (T - 1) × Fin (n + 3)) := by
  apply Fin.ext
  simp [serializedStateIndex, finProdFinEquiv, Nat.mul_comm]
  omega

@[simp] theorem serializedA_serializeUnscaled {T n : Nat}
    (x : UnscaledPrimal T) (y : UnscaledDual T n) (i : Fin (T - 1)) :
    serializedA (serializeUnscaled x y) i = primalA x i := by
  unfold serializedA
  rw [serializedAIndex_prod]
  simp [serializeUnscaled]

@[simp] theorem serializedY_serializeUnscaled {T n : Nat}
    (x : UnscaledPrimal T) (y : UnscaledDual T n)
    (i : Fin (T - 1)) (k : Fin n) :
    serializedY (serializeUnscaled x y) i k = dualBlock y i k := by
  unfold serializedY
  rw [serializedDualIndex_prod]
  simp [serializeUnscaled]

@[simp] theorem serializedDualBlock_serializeUnscaled {T n : Nat}
    (x : UnscaledPrimal T) (y : UnscaledDual T n) (i : Fin (T - 1)) :
    serializedDualBlock (serializeUnscaled x y) i = dualBlock y i := by
  funext k
  simp [serializedDualBlock]

@[simp] theorem serializedB_serializeUnscaled {T n : Nat}
    (x : UnscaledPrimal T) (y : UnscaledDual T n) (i : Fin (T - 1)) :
    serializedB (serializeUnscaled x y) i = primalB x i := by
  unfold serializedB
  rw [serializedBIndex_prod]
  simp [serializeUnscaled]

@[simp] theorem serializedState_serializeUnscaled {T n : Nat}
    (x : UnscaledPrimal T) (y : UnscaledDual T n) (i : Fin (T - 1)) :
    serializedState (serializeUnscaled x y) i = primalState x i := by
  unfold serializedState
  rw [serializedStateIndex_prod]
  simp [serializeUnscaled]

private theorem primalAIndex_block {T : Nat} (i : Fin (T - 1)) :
    primalBlockIndex (primalAIndex i) =
      ((i, ⟨0, by omega⟩) : Fin (T - 1) × Fin 3) := by
  unfold primalBlockIndex
  have hcast : Fin.cast (Nat.mul_comm 3 (T - 1)) (primalAIndex i) =
      finProdFinEquiv ((i, ⟨0, by omega⟩) : Fin (T - 1) × Fin 3) := by
    apply Fin.ext
    simp [primalAIndex, finProdFinEquiv, Nat.mul_comm]
  rw [hcast, Equiv.symm_apply_apply]

private theorem primalBIndex_block {T : Nat} (i : Fin (T - 1)) :
    primalBlockIndex (primalBIndex i) =
      ((i, ⟨1, by omega⟩) : Fin (T - 1) × Fin 3) := by
  unfold primalBlockIndex
  have hcast : Fin.cast (Nat.mul_comm 3 (T - 1)) (primalBIndex i) =
      finProdFinEquiv ((i, ⟨1, by omega⟩) : Fin (T - 1) × Fin 3) := by
    apply Fin.ext
    simp [primalBIndex, finProdFinEquiv, Nat.mul_comm]
    omega
  rw [hcast, Equiv.symm_apply_apply]

private theorem primalStateIndex_block {T : Nat} (i : Fin (T - 1)) :
    primalBlockIndex (primalStateIndex i) =
      ((i, ⟨2, by omega⟩) : Fin (T - 1) × Fin 3) := by
  unfold primalBlockIndex
  have hcast : Fin.cast (Nat.mul_comm 3 (T - 1)) (primalStateIndex i) =
      finProdFinEquiv ((i, ⟨2, by omega⟩) : Fin (T - 1) × Fin 3) := by
    apply Fin.ext
    simp [primalStateIndex, finProdFinEquiv, Nat.mul_comm]
    omega
  rw [hcast, Equiv.symm_apply_apply]

private theorem dualBlockIndex_pair {T n : Nat}
    (i : Fin (T - 1)) (k : Fin n) :
    dualBlockIndexPair (dualBlockIndex i k) = (i, k) := by
  unfold dualBlockIndexPair
  have hcast : Fin.cast (Nat.mul_comm n (T - 1)) (dualBlockIndex i k) =
      finProdFinEquiv (i, k) := by
    apply Fin.ext
    simp [dualBlockIndex, finProdFinEquiv]
    omega
  rw [hcast, Equiv.symm_apply_apply]

@[simp] theorem primalA_unserializePrimal {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    primalA (unserializePrimal q) i = serializedA q i := by
  unfold primalA
  simp [unserializePrimal, primalAIndex_block]

@[simp] theorem primalB_unserializePrimal {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    primalB (unserializePrimal q) i = serializedB q i := by
  unfold primalB
  simp [unserializePrimal, primalBIndex_block]

@[simp] theorem primalState_unserializePrimal {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    primalState (unserializePrimal q) i = serializedState q i := by
  unfold primalState
  simp [unserializePrimal, primalStateIndex_block]

@[simp] theorem dualBlock_unserializeDual {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    dualBlock (unserializeDual q) i = serializedDualBlock q i := by
  funext k
  unfold dualBlock unserializeDual
  rw [dualBlockIndex_pair]
  rfl

/-- Extensionality by the four coordinate families in every serialized
block. -/
theorem SerializedSpace.ext_blocks {T n : Nat} {q r : SerializedSpace T n}
    (hA : ∀ i, serializedA q i = serializedA r i)
    (hY : ∀ i k, serializedY q i k = serializedY r i k)
    (hB : ∀ i, serializedB q i = serializedB r i)
    (hS : ∀ i, serializedState q i = serializedState r i) : q = r := by
  funext j
  let ik := finProdFinEquiv.symm j
  have hj : finProdFinEquiv ik = j := Equiv.apply_symm_apply _ j
  by_cases ha : ik.2.val = 0
  · have hk : ik.2 = (⟨0, by omega⟩ : Fin (n + 3)) := Fin.ext ha
    have hik : ik = (ik.1, (⟨0, by omega⟩ : Fin (n + 3))) :=
      Prod.ext rfl hk
    have hindex : j = serializedAIndex (n := n) ik.1 := by
      rw [← hj, hik, serializedAIndex_prod]
    rw [hindex]
    exact hA ik.1
  · by_cases hy : ik.2.val ≤ n
    · let k : Fin n := ⟨ik.2.val - 1, by omega⟩
      have hkval : k.val + 1 = ik.2.val := by dsimp [k]; omega
      have hk : ik.2 = (⟨k.val + 1, by omega⟩ : Fin (n + 3)) :=
        Fin.ext hkval.symm
      have hik : ik =
          (ik.1, (⟨k.val + 1, by omega⟩ : Fin (n + 3))) :=
        Prod.ext rfl hk
      have hindex : j = serializedDualIndex ik.1 k := by
        rw [← hj, hik, serializedDualIndex_prod]
      rw [hindex]
      exact hY ik.1 k
    · by_cases hb : ik.2.val = n + 1
      · have hk : ik.2 = (⟨n + 1, by omega⟩ : Fin (n + 3)) := Fin.ext hb
        have hik : ik =
            (ik.1, (⟨n + 1, by omega⟩ : Fin (n + 3))) :=
          Prod.ext rfl hk
        have hindex : j = serializedBIndex (n := n) ik.1 := by
          rw [← hj, hik, serializedBIndex_prod]
        rw [hindex]
        exact hB ik.1
      · have hsval : ik.2.val = n + 2 := by omega
        have hk : ik.2 = (⟨n + 2, by omega⟩ : Fin (n + 3)) := Fin.ext hsval
        have hik : ik =
            (ik.1, (⟨n + 2, by omega⟩ : Fin (n + 3))) :=
          Prod.ext rfl hk
        have hindex : j = serializedStateIndex (n := n) ik.1 := by
          rw [← hj, hik, serializedStateIndex_prod]
        rw [hindex]
        exact hS ik.1

@[simp] theorem serializeUnscaled_unserialize {T n : Nat}
    (q : SerializedSpace T n) :
    serializeUnscaled (unserializePrimal q) (unserializeDual q) = q := by
  apply SerializedSpace.ext_blocks
  · intro i; simp
  · intro i k; simp [serializedDualBlock]
  · intro i; simp
  · intro i; simp

@[simp] theorem serializedCurrentState_serializeUnscaled {T n : Nat}
    (x : UnscaledPrimal T) (y : UnscaledDual T n) (i : Fin (T - 1)) :
    serializedCurrentState (serializeUnscaled x y) i = currentState x i := by
  unfold serializedCurrentState currentState
  split <;> simp_all

@[simp] theorem serializedClippedCurrent_serializeUnscaled {T n : Nat}
    (P : UnscaledParameters) (x : UnscaledPrimal T)
    (y : UnscaledDual T n) (i : Fin (T - 1)) :
    serializedClippedCurrent P (serializeUnscaled x y) i =
      clippedCurrent P x i := by
  simp [serializedClippedCurrent, clippedCurrent]

@[simp] theorem serializedClippedNext_serializeUnscaled {T n : Nat}
    (P : UnscaledParameters) (x : UnscaledPrimal T)
    (y : UnscaledDual T n) (i : Fin (T - 1)) :
    serializedClippedNext P (serializeUnscaled x y) i =
      clippedNext P x i := by
  simp [serializedClippedNext, clippedNext]

@[simp] theorem serializedPulseSq_serializeUnscaled {T n : Nat}
    (x : UnscaledPrimal T) (y : UnscaledDual T n) :
    serializedPulseSq (serializeUnscaled x y) = pulseSq x := by
  simp [serializedPulseSq, pulseSq]

@[simp] theorem serializedBlock_serializeUnscaled {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters) (x : UnscaledPrimal T)
    (y : UnscaledDual T n) (i : Fin (T - 1)) :
    serializedBlock hn P (serializeUnscaled x y) i =
      unscaledBlock hn P x y i := by
  simp [serializedBlock, unscaledBlock]

/-- The serialized scalar objective is definitionally the same hard instance
after the genuine coordinate permutation. -/
theorem serializedObjective_serializeUnscaled {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters) (x : UnscaledPrimal T)
    (y : UnscaledDual T n) :
    serializedObjective hn P (serializeUnscaled x y) =
      unscaledObjective hn P x y := by
  simp [serializedObjective, unscaledObjective]

theorem serializedObjective_eq_unserialized {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters) (q : SerializedSpace T n) :
    serializedObjective hn P q =
      unscaledObjective hn P (unserializePrimal q) (unserializeDual q) := by
  conv_lhs => rw [← serializeUnscaled_unserialize q]
  exact serializedObjective_serializeUnscaled hn P
    (unserializePrimal q) (unserializeDual q)

/-! ## Pulling the true Fréchet gradient back to the separated variables -/

def serializeUnscaledLinear {T n : Nat} :
    (UnscaledPrimal T × UnscaledDual T n) →ₗ[ℝ] SerializedSpace T n where
  toFun p := serializeUnscaled p.1 p.2
  map_add' := by
    intro p q
    funext j
    change serializeUnscaled (p.1 + q.1) (p.2 + q.2) j =
      serializeUnscaled p.1 p.2 j + serializeUnscaled q.1 q.2 j
    unfold serializeUnscaled
    dsimp only
    split
    · simp [primalA]
    · split
      · simp [dualBlock]
      · split
        · simp [primalB]
        · simp [primalState]
  map_smul' := by
    intro a p
    funext j
    change serializeUnscaled (a • p.1) (a • p.2) j =
      a • serializeUnscaled p.1 p.2 j
    unfold serializeUnscaled
    dsimp only
    split
    · simp [primalA]
    · split
      · simp [dualBlock]
      · split
        · simp [primalB]
        · simp [primalState]

def serializeUnscaledCLM {T n : Nat} :
    (UnscaledPrimal T × UnscaledDual T n) →L[ℝ] SerializedSpace T n :=
  LinearMap.toContinuousLinearMap serializeUnscaledLinear

@[simp] theorem serializeUnscaledCLM_apply {T n : Nat}
    (p : UnscaledPrimal T × UnscaledDual T n) :
    serializeUnscaledCLM p = serializeUnscaled p.1 p.2 := rfl

/-- The true serialized gradient, pulled back along primal directions and
then written in primal coordinates. -/
def unscaledTrueGradX {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (x : UnscaledPrimal T) (y : UnscaledDual T n) : UnscaledPrimal T :=
  let g := serializedTrueGradient hn P (serializeUnscaled x y)
  NCPLVerification.continuousLinearMapCoordinates
    ((NCPLVerification.evecDot g).comp
      (serializeUnscaledCLM.comp
        (ContinuousLinearMap.inl ℝ (UnscaledPrimal T) (UnscaledDual T n))))

/-- The true serialized gradient, pulled back along dual directions and then
written in dual coordinates. -/
def unscaledTrueGradY {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (x : UnscaledPrimal T) (y : UnscaledDual T n) : UnscaledDual T n :=
  let g := serializedTrueGradient hn P (serializeUnscaled x y)
  NCPLVerification.continuousLinearMapCoordinates
    ((NCPLVerification.evecDot g).comp
      (serializeUnscaledCLM.comp
        (ContinuousLinearMap.inr ℝ (UnscaledPrimal T) (UnscaledDual T n))))

theorem unscaledObjective_hasFDerivAt {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T)
    (y : UnscaledDual T n) :
    HasFDerivAt (Function.uncurry (unscaledObjective (T := T) hn P))
      ((NCPLVerification.evecDot
        (serializedTrueGradient hn P (serializeUnscaled x y))).comp
          (serializeUnscaledCLM (T := T) (n := n))) (x, y) := by
  have hs := hasEVecFDerivAt_serializedObjective (T := T) hn P
    (serializeUnscaled x y)
  unfold NCPLVerification.HasEVecFDerivAt at hs
  have hc := hs.comp (x, y)
    (serializeUnscaledCLM (T := T) (n := n)).hasFDerivAt
  have heq : Function.uncurry (unscaledObjective (T := T) hn P) =
      serializedObjective (T := T) hn P ∘
        (serializeUnscaledCLM (T := T) (n := n)) := by
    funext p
    exact (serializedObjective_serializeUnscaled hn P p.1 p.2).symm
  rw [heq]
  exact hc

/-- The two separated fields are not symbolic formulas: they represent the
actual Fréchet derivative of the original two-variable objective. -/
theorem unscaledTrueGradient_representsJointGradient {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters) :
    NCPLVerification.RepresentsJointGradient
      (unscaledObjective (T := T) hn P)
      (unscaledTrueGradX (T := T) hn P)
      (unscaledTrueGradY (T := T) hn P) := by
  constructor
  · rintro ⟨x, y⟩
    exact (unscaledObjective_hasFDerivAt hn P x y).differentiableAt
  · intro x y hx hy
    let g := serializedTrueGradient hn P (serializeUnscaled x y)
    let L := (NCPLVerification.evecDot g).comp serializeUnscaledCLM
    have hf : fderiv ℝ (Function.uncurry (unscaledObjective hn P)) (x, y) =
        L := (unscaledObjective_hasFDerivAt hn P x y).fderiv
    rw [hf]
    have hdecomp : (hx, hy) = (hx, 0) + (0, hy) := by ext <;> simp
    rw [hdecomp, map_add]
    have hxcoord := NCPLVerification.continuousLinearMap_apply_eq_coordinates
      (L.comp (ContinuousLinearMap.inl ℝ (UnscaledPrimal T)
        (UnscaledDual T n))) hx
    have hycoord := NCPLVerification.continuousLinearMap_apply_eq_coordinates
      (L.comp (ContinuousLinearMap.inr ℝ (UnscaledPrimal T)
        (UnscaledDual T n))) hy
    change L (hx, 0) + L (0, hy) = _
    rw [show L (hx, 0) =
        (L.comp (ContinuousLinearMap.inl ℝ (UnscaledPrimal T)
          (UnscaledDual T n))) hx by rfl,
      show L (0, hy) =
        (L.comp (ContinuousLinearMap.inr ℝ (UnscaledPrimal T)
          (UnscaledDual T n))) hy by rfl,
      hxcoord, hycoord]
    rfl

/-! ## The joint saddle field through the literal pack/unpack -/

/-- The literal pack/unpack of the genuine serialized gradient, with the
dual sign required by a saddle oracle. -/
def packedUnserializedTrueSaddleField {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) :
    SerializedSpace T n :=
  let g := serializedTrueGradient hn P q
  serializeUnscaled (unserializePrimal g) (-unserializeDual g)

set_option linter.flexible false in
theorem packedUnserializedTrueSaddleField_eq_signed {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters) (q : SerializedSpace T n) :
    packedUnserializedTrueSaddleField hn P q =
      serializedSignedTrueSaddleField hn P q := by
  classical
  apply SerializedSpace.ext_blocks
  · intro i
    simp only [packedUnserializedTrueSaddleField]
    rw [serializedA_serializeUnscaled, primalA_unserializePrimal]
    unfold serializedSignedTrueSaddleField serializedA
    simp [
      serializedAIndex_ne_dualIndex, serializedAIndex_ne_BIndex,
      serializedAIndex_ne_stateIndex]
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hci
      have hne : serializedAIndex (n := n) c ≠ serializedAIndex i :=
        fun h => hci (serializedAIndex_injective h)
      simp [hne]
    · simp
  · intro i k
    simp only [packedUnserializedTrueSaddleField]
    rw [serializedY_serializeUnscaled]
    simp only [dualBlock, Pi.neg_apply]
    unfold unserializeDual
    rw [dualBlockIndex_pair]
    unfold serializedSignedTrueSaddleField serializedY
    simp [
      serializedAIndex_ne_dualIndex, serializedBIndex_ne_dualIndex,
      serializedStateIndex_ne_dualIndex]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single k]
      · simp
      · intro c _ hck
        have hne : serializedDualIndex i c ≠ serializedDualIndex i k := by
          intro h
          have hp : (i, c) = (i, k) := serializedDualIndex_injective h
          exact hck (congrArg Prod.snd hp)
        simp [hne]
      · simp
    · intro l _ hli
      apply Finset.sum_eq_zero
      intro c _
      have hne : serializedDualIndex l c ≠ serializedDualIndex i k := by
        intro h
        have hp : (l, c) = (i, k) := serializedDualIndex_injective h
        exact hli (congrArg Prod.fst hp)
      simp [hne]
    · simp
  · intro i
    simp only [packedUnserializedTrueSaddleField]
    rw [serializedB_serializeUnscaled, primalB_unserializePrimal]
    unfold serializedSignedTrueSaddleField serializedB
    simp [
      serializedAIndex_ne_BIndex, serializedBIndex_ne_dualIndex,
      serializedBIndex_ne_stateIndex]
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hci
      have hne : serializedBIndex (n := n) c ≠ serializedBIndex i :=
        fun h => hci (serializedBIndex_injective h)
      simp [hne]
    · simp
  · intro i
    simp only [packedUnserializedTrueSaddleField]
    rw [serializedState_serializeUnscaled, primalState_unserializePrimal]
    unfold serializedSignedTrueSaddleField serializedState
    simp [
      serializedAIndex_ne_stateIndex, serializedBIndex_ne_stateIndex,
      serializedStateIndex_ne_dualIndex]
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hci
      have hne : serializedStateIndex (n := n) c ≠
          serializedStateIndex i :=
        fun h => hci (serializedStateIndex_injective h)
      simp [hne]
    · simp

theorem packedUnserializedTrueSaddleField_eq_concrete {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters) :
    packedUnserializedTrueSaddleField (T := T) hn P =
      serializedSaddleField hn P := by
  funext q
  rw [packedUnserializedTrueSaddleField_eq_signed]
  exact (serializedSaddleField_eq_signedTrueGradient hn P q).symm

/-- Consequently the zero-chain proved from the concrete formulas is a
zero-chain of the actual Fréchet gradient after the genuine pack/unpack. -/
theorem packedUnserializedTrueSaddleField_isFirstOrderZeroChain
    {T n : Nat} (hn : 0 < n) (P : UnscaledParameters) :
    NCPLVerification.IsFirstOrderZeroChain
      (packedUnserializedTrueSaddleField (T := T) hn P) := by
  rw [packedUnserializedTrueSaddleField_eq_concrete hn P]
  exact serializedSaddleField_isFirstOrderZeroChain hn P

theorem packedUnserializedTrueSaddleField_isFirstOrderSaddleZeroChain
    {T n : Nat} (hn : 0 < n) (P : UnscaledParameters) :
    IsFirstOrderSaddleZeroChain
      (packedUnserializedTrueSaddleField (T := T) hn P) :=
  isFirstOrderSaddleZeroChain_of_global
    (packedUnserializedTrueSaddleField_isFirstOrderZeroChain hn P)

theorem packedUnserializedTrueSaddleField_zero_supported_a1
    {T n : Nat} (hn : 0 < n) (P : UnscaledParameters) :
    NCPLVerification.SupportedBelow 1
      (packedUnserializedTrueSaddleField (T := T) hn P 0) := by
  rw [packedUnserializedTrueSaddleField_eq_concrete hn P]
  exact serializedSaddleField_zero_supported_a1 hn P

end


end NCCLowerBoundVerification
