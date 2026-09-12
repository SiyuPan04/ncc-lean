import NCCLowerBoundVerification.Lower.UnscaledSerialization
import NCCLowerBoundVerification.Lower.RotationClosure
import NCCLowerBoundVerification.Oracle.Model
import NCCLowerBoundVerification.Oracle.ZeroChain
import NCPLVerification.ResistingOracle

/-!
# Product-preserving resisting frames in the paper's actual coordinate order

The generic development in `NCPLVerification.ResistingOracle` uses blocks of
the form `(dual..., primal)`.  The hard instance in this project instead uses

`a_i, y_{i,0}, ..., y_{i,n-1}, b_i, s_{i+1}`.

This file supplies the missing tagged construction.  In particular, an
`a`, `b`, or `s` tag always reveals a column of the primal frame `U`, while a
`y` tag always reveals a column of the dual frame `V`.
-/

namespace NCCLowerBoundVerification

noncomputable section

open NCPLVerification

set_option linter.unusedSimpArgs false
set_option linter.style.longLine false
set_option linter.unnecessarySimpa false

/-- The explicit interleaving is also a left inverse on the separated primal
space.  This direction is needed when a serialized zero-chain response is
turned back into the two gradients returned by the product oracle. -/
@[simp] theorem unserializePrimal_serializeUnscaled {T n : Nat}
    (x : UnscaledPrimal T) (y : UnscaledDual T n) :
    unserializePrimal (serializeUnscaled x y) = x := by
  funext j
  let ik := primalBlockIndex j
  have hj : finProdFinEquiv ik =
      Fin.cast (Nat.mul_comm 3 (T - 1)) j := by
    dsimp [ik, primalBlockIndex]
    exact Equiv.apply_symm_apply _ _
  have hv := congrArg Fin.val hj
  simp [finProdFinEquiv] at hv
  change (if hA : ik.2.val = 0 then
      serializedA (serializeUnscaled x y) ik.1
    else if hB : ik.2.val = 1 then
      serializedB (serializeUnscaled x y) ik.1
    else serializedState (serializeUnscaled x y) ik.1) = x j
  by_cases hA : ik.2.val = 0
  · rw [dif_pos hA, serializedA_serializeUnscaled]
    unfold primalA
    congr 1
    apply Fin.ext
    simp [primalAIndex]
    omega
  · rw [dif_neg hA]
    by_cases hB : ik.2.val = 1
    · rw [dif_pos hB, serializedB_serializeUnscaled]
      unfold primalB
      congr 1
      apply Fin.ext
      simp [primalBIndex]
      omega
    · have hS : ik.2.val = 2 := by omega
      rw [dif_neg hB, serializedState_serializeUnscaled]
      unfold primalState
      congr 1
      apply Fin.ext
      simp [primalStateIndex]
      omega

/-- The explicit interleaving is a left inverse on the separated dual space. -/
@[simp] theorem unserializeDual_serializeUnscaled {T n : Nat}
    (x : UnscaledPrimal T) (y : UnscaledDual T n) :
    unserializeDual (serializeUnscaled x y) = y := by
  funext j
  let ik := dualBlockIndexPair j
  have hj : finProdFinEquiv ik =
      Fin.cast (Nat.mul_comm n (T - 1)) j := by
    dsimp [ik, dualBlockIndexPair]
    exact Equiv.apply_symm_apply _ _
  have hv := congrArg Fin.val hj
  simp [finProdFinEquiv] at hv
  change serializedY (serializeUnscaled x y) ik.1 ik.2 = y j
  rw [serializedY_serializeUnscaled]
  unfold dualBlock
  congr 1
  apply Fin.ext
  simp [dualBlockIndex]
  omega

/-- A coordinate of the genuinely serialized unscaled hard instance. -/
inductive UnscaledTag (T n : Nat)
  | a (i : Fin (T - 1))
  | y (i : Fin (T - 1)) (k : Fin n)
  | b (i : Fin (T - 1))
  | state (i : Fin (T - 1))

namespace UnscaledTag

/-- Position of a tag in `a_i,y_{i,*},b_i,s_{i+1}` order. -/
def serializedIndex {T n : Nat} :
    UnscaledTag T n → Fin ((T - 1) * (n + 3))
  | a i => serializedAIndex (n := n) i
  | y i k => serializedDualIndex i k
  | b i => serializedBIndex (n := n) i
  | state i => serializedStateIndex (n := n) i

/-- The base primal column represented by a primal tag. -/
def primalIndex {T n : Nat} :
    UnscaledTag T n → Option (Fin (3 * (T - 1)))
  | a i => some (primalAIndex i)
  | y _ _ => none
  | b i => some (primalBIndex i)
  | state i => some (primalStateIndex i)

/-- The base dual column represented by a dual tag. -/
def dualIndex {T n : Nat} :
    UnscaledTag T n → Option (Fin (n * (T - 1)))
  | a _ => none
  | y i k => some (dualBlockIndex i k)
  | b _ => none
  | state _ => none

theorem serializedIndex_injective {T n : Nat} :
    Function.Injective (serializedIndex (T := T) (n := n)) := by
  intro c d h
  cases c with
  | a i =>
      cases d with
      | a j => exact congrArg a (serializedAIndex_injective h)
      | y j k => exact False.elim (serializedAIndex_ne_dualIndex i j k h)
      | b j => exact False.elim (serializedAIndex_ne_BIndex i j h)
      | state j => exact False.elim (serializedAIndex_ne_stateIndex i j h)
  | y i k =>
      cases d with
      | a j => exact False.elim (serializedAIndex_ne_dualIndex j i k h.symm)
      | y j u =>
          have hp : (i, k) = (j, u) := serializedDualIndex_injective h
          cases hp
          rfl
      | b j => exact False.elim (serializedBIndex_ne_dualIndex j i k h.symm)
      | state j => exact False.elim (serializedStateIndex_ne_dualIndex j i k h.symm)
  | b i =>
      cases d with
      | a j => exact False.elim (serializedAIndex_ne_BIndex j i h.symm)
      | y j k => exact False.elim (serializedBIndex_ne_dualIndex i j k h)
      | b j => exact congrArg b (serializedBIndex_injective h)
      | state j => exact False.elim (serializedBIndex_ne_stateIndex i j h)
  | state i =>
      cases d with
      | a j => exact False.elim (serializedAIndex_ne_stateIndex j i h.symm)
      | y j k => exact False.elim (serializedStateIndex_ne_dualIndex i j k h)
      | b j => exact False.elim (serializedBIndex_ne_stateIndex j i h.symm)
      | state j => exact congrArg state (serializedStateIndex_injective h)

/-- Every serialized coordinate has exactly one tag. -/
theorem serializedIndex_surjective {T n : Nat} :
    Function.Surjective (serializedIndex (T := T) (n := n)) := by
  intro j
  let ik := finProdFinEquiv.symm j
  have hj : finProdFinEquiv ik = j := Equiv.apply_symm_apply _ j
  by_cases ha : ik.2.val = 0
  · refine ⟨a ik.1, ?_⟩
    apply Fin.ext
    have hv := congrArg Fin.val hj
    simp [serializedIndex, serializedAIndex, finProdFinEquiv, ha,
      Nat.mul_comm] at hv ⊢
    omega
  · by_cases hy : ik.2.val ≤ n
    · let k : Fin n := ⟨ik.2.val - 1, by omega⟩
      refine ⟨y ik.1 k, ?_⟩
      apply Fin.ext
      have hv := congrArg Fin.val hj
      simp [serializedIndex, serializedDualIndex, finProdFinEquiv, k,
        Nat.mul_comm] at hv ⊢
      omega
    · by_cases hb : ik.2.val = n + 1
      · refine ⟨b ik.1, ?_⟩
        apply Fin.ext
        have hv := congrArg Fin.val hj
        simp [serializedIndex, serializedBIndex, finProdFinEquiv, hb,
          Nat.mul_comm] at hv ⊢
        omega
      · have hs : ik.2.val = n + 2 := by omega
        refine ⟨state ik.1, ?_⟩
        apply Fin.ext
        have hv := congrArg Fin.val hj
        simp [serializedIndex, serializedStateIndex, finProdFinEquiv, hs,
          Nat.mul_comm] at hv ⊢
        omega

/-- The unique tag at a serialized coordinate. -/
def tagAt {T n : Nat} (j : Fin ((T - 1) * (n + 3))) : UnscaledTag T n :=
  Classical.choose (serializedIndex_surjective j)

@[simp] theorem serializedIndex_tagAt {T n : Nat}
    (j : Fin ((T - 1) * (n + 3))) : serializedIndex (tagAt j) = j :=
  Classical.choose_spec (serializedIndex_surjective j)

@[simp] theorem tagAt_serializedIndex {T n : Nat} (c : UnscaledTag T n) :
    tagAt (serializedIndex c) = c := by
  apply serializedIndex_injective
  exact serializedIndex_tagAt _

theorem primalIndex_surjective {T n : Nat} :
    ∀ j : Fin (3 * (T - 1)), ∃ c : UnscaledTag T n, primalIndex c = some j := by
  intro j
  let ik := primalBlockIndex j
  have hj : finProdFinEquiv ik = Fin.cast (Nat.mul_comm 3 (T - 1)) j := by
    dsimp [ik, primalBlockIndex]
    exact Equiv.apply_symm_apply _ _
  have hv := congrArg Fin.val hj
  simp [finProdFinEquiv] at hv
  by_cases hA : ik.2.val = 0
  · refine ⟨.a ik.1, ?_⟩
    simp [primalIndex]
    apply Fin.ext
    simp [primalAIndex]
    omega
  · by_cases hB : ik.2.val = 1
    · refine ⟨.b ik.1, ?_⟩
      simp [primalIndex]
      apply Fin.ext
      simp [primalBIndex]
      omega
    · have hS : ik.2.val = 2 := by omega
      refine ⟨.state ik.1, ?_⟩
      simp [primalIndex]
      apply Fin.ext
      simp [primalStateIndex]
      omega

theorem dualIndex_surjective {T n : Nat} :
    ∀ j : Fin (n * (T - 1)), ∃ c : UnscaledTag T n, dualIndex c = some j := by
  intro j
  let ik := dualBlockIndexPair j
  have hj : finProdFinEquiv ik = Fin.cast (Nat.mul_comm n (T - 1)) j := by
    dsimp [ik, dualBlockIndexPair]
    exact Equiv.apply_symm_apply _ _
  have hv := congrArg Fin.val hj
  simp [finProdFinEquiv] at hv
  refine ⟨.y ik.1 ik.2, ?_⟩
  simp [dualIndex]
  apply Fin.ext
  simp [dualBlockIndex]
  omega

end UnscaledTag

/-- Zero-column predicate with the ambient space selected by the tag. -/
def TaggedColumnIsZero {T n DX DY : Nat}
    (U : Fin (3 * (T - 1)) → EVec DX)
    (V : Fin (n * (T - 1)) → EVec DY) : UnscaledTag T n → Prop
  | .a i => U (primalAIndex i) = 0
  | .y i k => V (dualBlockIndex i k) = 0
  | .b i => U (primalBIndex i) = 0
  | .state i => U (primalStateIndex i) = 0

/-- Unit-column predicate with the ambient space selected by the tag. -/
def TaggedColumnIsUnit {T n DX DY : Nat}
    (U : Fin (3 * (T - 1)) → EVec DX)
    (V : Fin (n * (T - 1)) → EVec DY) : UnscaledTag T n → Prop
  | .a i => evecDotValue (U (primalAIndex i)) (U (primalAIndex i)) = 1
  | .y i k => evecDotValue (V (dualBlockIndex i k)) (V (dualBlockIndex i k)) = 1
  | .b i => evecDotValue (U (primalBIndex i)) (U (primalBIndex i)) = 1
  | .state i => evecDotValue (U (primalStateIndex i)) (U (primalStateIndex i)) = 1

/-- A tagged column is still hidden at every serialized position `≥ t`. -/
def TaggedFramesZeroFrom {T n DX DY : Nat} (t : Nat)
    (U : Fin (3 * (T - 1)) → EVec DX)
    (V : Fin (n * (T - 1)) → EVec DY) : Prop :=
  ∀ c : UnscaledTag T n, t ≤ (UnscaledTag.serializedIndex c).val →
    TaggedColumnIsZero U V c

/-- Every already-revealed tagged column has unit norm. -/
def TaggedFramesUnitBelow {T n DX DY : Nat} (t : Nat)
    (U : Fin (3 * (T - 1)) → EVec DX)
    (V : Fin (n * (T - 1)) → EVec DY) : Prop :=
  ∀ c : UnscaledTag T n, (UnscaledTag.serializedIndex c).val < t →
    TaggedColumnIsUnit U V c

/-- One product-preserving reveal in the actual tagged order. -/
def TaggedFrameReveal {T n DX DY : Nat}
    (c : UnscaledTag T n) (qX : List (EVec DX)) (qY : List (EVec DY))
    (U U' : Fin (3 * (T - 1)) → EVec DX)
    (V V' : Fin (n * (T - 1)) → EVec DY) : Prop :=
  match c with
  | .a i => V' = V ∧ ∃ u : EVec DX,
      U' = Function.update U (primalAIndex i) u ∧
      evecDotValue u u = 1 ∧
      (∀ j, evecDotValue (U j) u = 0) ∧
      ∀ X ∈ qX, evecDotValue X u = 0
  | .y i k => U' = U ∧ ∃ u : EVec DY,
      V' = Function.update V (dualBlockIndex i k) u ∧
      evecDotValue u u = 1 ∧
      (∀ j, evecDotValue (V j) u = 0) ∧
      ∀ Y ∈ qY, evecDotValue Y u = 0
  | .b i => V' = V ∧ ∃ u : EVec DX,
      U' = Function.update U (primalBIndex i) u ∧
      evecDotValue u u = 1 ∧
      (∀ j, evecDotValue (U j) u = 0) ∧
      ∀ X ∈ qX, evecDotValue X u = 0
  | .state i => V' = V ∧ ∃ u : EVec DX,
      U' = Function.update U (primalStateIndex i) u ∧
      evecDotValue u u = 1 ∧
      (∀ j, evecDotValue (U j) u = 0) ∧
      ∀ X ∈ qX, evecDotValue X u = 0

private theorem tagged_primal_index_eq_of_serializedIndex_eq
    {T n : Nat} {c d : UnscaledTag T n}
    (h : UnscaledTag.serializedIndex c = UnscaledTag.serializedIndex d) : c = d :=
  UnscaledTag.serializedIndex_injective h

/-- A reveal leaves all old query projections unchanged. -/
theorem TaggedFrameReveal.project_eq {T n DX DY : Nat}
    {c : UnscaledTag T n} {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U U' : Fin (3 * (T - 1)) → EVec DX}
    {V V' : Fin (n * (T - 1)) → EVec DY}
    (hr : TaggedFrameReveal c qX qY U U' V V')
    (hz : TaggedFramesZeroFrom (UnscaledTag.serializedIndex c).val U V) :
    (∀ X ∈ qX, frameProject U' X = frameProject U X) ∧
    ∀ Y ∈ qY, frameProject V' Y = frameProject V Y := by
  cases c with
  | a i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      constructor
      · intro X hX
        apply frameProject_update_eq_of_dots
        · rw [hz (.a i) le_rfl]
          simp [evecDotValue]
        · rw [evecDotValue_comm]
          exact hq X hX
      · intro Y hY; rfl
  | y i k =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      constructor
      · intro X hX; rfl
      · intro Y hY
        apply frameProject_update_eq_of_dots
        · rw [hz (.y i k) le_rfl]
          simp [evecDotValue]
        · rw [evecDotValue_comm]
          exact hq Y hY
  | b i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      constructor
      · intro X hX
        apply frameProject_update_eq_of_dots
        · rw [hz (.b i) le_rfl]
          simp [evecDotValue]
        · rw [evecDotValue_comm]
          exact hq X hX
      · intro Y hY; rfl
  | state i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      constructor
      · intro X hX
        apply frameProject_update_eq_of_dots
        · rw [hz (.state i) le_rfl]
          simp [evecDotValue]
        · rw [evecDotValue_comm]
          exact hq X hX
      · intro Y hY; rfl

private theorem serializedIndex_eq_of_primalIndex_eq {T n : Nat}
    {c d : UnscaledTag T n} {i : Fin (3 * (T - 1))}
    (hc : c.primalIndex = some i) (hd : d.primalIndex = some i) :
    c.serializedIndex = d.serializedIndex := by
  cases c with
  | a u =>
      cases d with
      | a v =>
          simp [UnscaledTag.primalIndex] at hc hd
          subst i
          have huv : u = v := by
            apply Fin.ext
            have h := congrArg Fin.val hd
            simp [primalAIndex] at h
            omega
          subst v
          rfl
      | y v k => simp [UnscaledTag.primalIndex] at hd
      | b v =>
          simp [UnscaledTag.primalIndex] at hc hd
          subst i
          have h := congrArg Fin.val hd
          simp [primalAIndex, primalBIndex] at h
          omega
      | state v =>
          simp [UnscaledTag.primalIndex] at hc hd
          subst i
          have h := congrArg Fin.val hd
          simp [primalAIndex, primalStateIndex] at h
          omega
  | y u k => simp [UnscaledTag.primalIndex] at hc
  | b u =>
      cases d with
      | a v =>
          simp [UnscaledTag.primalIndex] at hc hd
          subst i
          have h := congrArg Fin.val hd
          simp [primalBIndex, primalAIndex] at h
          omega
      | y v k => simp [UnscaledTag.primalIndex] at hd
      | b v =>
          simp [UnscaledTag.primalIndex] at hc hd
          subst i
          have huv : u = v := by
            apply Fin.ext
            have h := congrArg Fin.val hd
            simp [primalBIndex] at h
            omega
          subst v
          rfl
      | state v =>
          simp [UnscaledTag.primalIndex] at hc hd
          subst i
          have h := congrArg Fin.val hd
          simp [primalBIndex, primalStateIndex] at h
          omega
  | state u =>
      cases d with
      | a v =>
          simp [UnscaledTag.primalIndex] at hc hd
          subst i
          have h := congrArg Fin.val hd
          simp [primalStateIndex, primalAIndex] at h
          omega
      | y v k => simp [UnscaledTag.primalIndex] at hd
      | b v =>
          simp [UnscaledTag.primalIndex] at hc hd
          subst i
          have h := congrArg Fin.val hd
          simp [primalStateIndex, primalBIndex] at h
          omega
      | state v =>
          simp [UnscaledTag.primalIndex] at hc hd
          subst i
          have huv : u = v := by
            apply Fin.ext
            have h := congrArg Fin.val hd
            simp [primalStateIndex] at h
            omega
          subst v
          rfl

private theorem serializedIndex_eq_of_dualIndex_eq {T n : Nat}
    {c d : UnscaledTag T n} {i : Fin (n * (T - 1))}
    (hc : c.dualIndex = some i) (hd : d.dualIndex = some i) :
    c.serializedIndex = d.serializedIndex := by
  cases c with
  | a u => simp [UnscaledTag.dualIndex] at hc
  | y u k =>
      cases d with
      | a v => simp [UnscaledTag.dualIndex] at hd
      | y v l =>
          simp [UnscaledTag.dualIndex] at hc hd
          subst i
          have hp : (u, k) = (v, l) := by
            apply finProdFinEquiv.injective
            apply Fin.ext
            have h := congrArg Fin.val hd
            simpa [dualBlockIndex, finProdFinEquiv, Nat.mul_comm,
              Nat.add_comm] using h.symm
          cases hp
          rfl
      | b v => simp [UnscaledTag.dualIndex] at hd
      | state v => simp [UnscaledTag.dualIndex] at hd
  | b u => simp [UnscaledTag.dualIndex] at hc
  | state u => simp [UnscaledTag.dualIndex] at hc

private theorem primal_update_unchanged_of_tag_ne {T n DX : Nat}
    {c d : UnscaledTag T n} {i j : Fin (3 * (T - 1))}
    (hc : c.primalIndex = some i) (hd : d.primalIndex = some j)
    (hne : c.serializedIndex ≠ d.serializedIndex)
    (U : Fin (3 * (T - 1)) → EVec DX) (u : EVec DX) :
    Function.update U i u j = U j := by
  have hij : j ≠ i := by
    intro h
    subst j
    exact hne (serializedIndex_eq_of_primalIndex_eq hc hd)
  simp [Function.update, hij]

private theorem dual_update_unchanged_of_tag_ne {T n DY : Nat}
    {c d : UnscaledTag T n} {i j : Fin (n * (T - 1))}
    (hc : c.dualIndex = some i) (hd : d.dualIndex = some j)
    (hne : c.serializedIndex ≠ d.serializedIndex)
    (V : Fin (n * (T - 1)) → EVec DY) (u : EVec DY) :
    Function.update V i u j = V j := by
  have hij : j ≠ i := by
    intro h
    subst j
    exact hne (serializedIndex_eq_of_dualIndex_eq hc hd)
  simp [Function.update, hij]

theorem TaggedFrameReveal.columnZero_iff_of_ne {T n DX DY : Nat}
    {c d : UnscaledTag T n} {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U U' : Fin (3 * (T - 1)) → EVec DX}
    {V V' : Fin (n * (T - 1)) → EVec DY}
    (hr : TaggedFrameReveal c qX qY U U' V V')
    (hne : c.serializedIndex ≠ d.serializedIndex) :
    TaggedColumnIsZero U' V' d ↔ TaggedColumnIsZero U V d := by
  unfold TaggedColumnIsZero
  cases c with
  | a i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      cases d with
      | a j =>
          simp only [TaggedColumnIsZero]
          rw [primal_update_unchanged_of_tag_ne (c := .a i) (d := .a j)
            (i := primalAIndex i) (j := primalAIndex j) rfl rfl hne]
      | y j k => rfl
      | b j =>
          simp only [TaggedColumnIsZero]
          rw [primal_update_unchanged_of_tag_ne (c := .a i) (d := .b j)
            (i := primalAIndex i) (j := primalBIndex j) rfl rfl hne]
      | state j =>
          simp only [TaggedColumnIsZero]
          rw [primal_update_unchanged_of_tag_ne (c := .a i) (d := .state j)
            (i := primalAIndex i) (j := primalStateIndex j) rfl rfl hne]
  | y i k =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      cases d with
      | a j => rfl
      | y j l =>
          simp only [TaggedColumnIsZero]
          rw [dual_update_unchanged_of_tag_ne (c := .y i k) (d := .y j l)
            (i := dualBlockIndex i k) (j := dualBlockIndex j l) rfl rfl hne]
      | b j => rfl
      | state j => rfl
  | b i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      cases d with
      | a j =>
          simp only [TaggedColumnIsZero]
          rw [primal_update_unchanged_of_tag_ne (c := .b i) (d := .a j)
            (i := primalBIndex i) (j := primalAIndex j) rfl rfl hne]
      | y j k => rfl
      | b j =>
          simp only [TaggedColumnIsZero]
          rw [primal_update_unchanged_of_tag_ne (c := .b i) (d := .b j)
            (i := primalBIndex i) (j := primalBIndex j) rfl rfl hne]
      | state j =>
          simp only [TaggedColumnIsZero]
          rw [primal_update_unchanged_of_tag_ne (c := .b i) (d := .state j)
            (i := primalBIndex i) (j := primalStateIndex j) rfl rfl hne]
  | state i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      cases d with
      | a j =>
          simp only [TaggedColumnIsZero]
          rw [primal_update_unchanged_of_tag_ne (c := .state i) (d := .a j)
            (i := primalStateIndex i) (j := primalAIndex j) rfl rfl hne]
      | y j k => rfl
      | b j =>
          simp only [TaggedColumnIsZero]
          rw [primal_update_unchanged_of_tag_ne (c := .state i) (d := .b j)
            (i := primalStateIndex i) (j := primalBIndex j) rfl rfl hne]
      | state j =>
          simp only [TaggedColumnIsZero]
          rw [primal_update_unchanged_of_tag_ne (c := .state i) (d := .state j)
            (i := primalStateIndex i) (j := primalStateIndex j) rfl rfl hne]

theorem TaggedFrameReveal.columnUnit_iff_of_ne {T n DX DY : Nat}
    {c d : UnscaledTag T n} {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U U' : Fin (3 * (T - 1)) → EVec DX}
    {V V' : Fin (n * (T - 1)) → EVec DY}
    (hr : TaggedFrameReveal c qX qY U U' V V')
    (hne : c.serializedIndex ≠ d.serializedIndex) :
    TaggedColumnIsUnit U' V' d ↔ TaggedColumnIsUnit U V d := by
  unfold TaggedColumnIsUnit
  cases c with
  | a i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      cases d with
      | a j => simp only [TaggedColumnIsUnit]; rw [primal_update_unchanged_of_tag_ne (c := .a i) (d := .a j)
          (i := primalAIndex i) (j := primalAIndex j) rfl rfl hne]
      | y j k => rfl
      | b j => simp only [TaggedColumnIsUnit]; rw [primal_update_unchanged_of_tag_ne (c := .a i) (d := .b j)
          (i := primalAIndex i) (j := primalBIndex j) rfl rfl hne]
      | state j => simp only [TaggedColumnIsUnit]; rw [primal_update_unchanged_of_tag_ne (c := .a i) (d := .state j)
          (i := primalAIndex i) (j := primalStateIndex j) rfl rfl hne]
  | y i k =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      cases d with
      | a j => rfl
      | y j l => simp only [TaggedColumnIsUnit]; rw [dual_update_unchanged_of_tag_ne (c := .y i k) (d := .y j l)
          (i := dualBlockIndex i k) (j := dualBlockIndex j l) rfl rfl hne]
      | b j => rfl
      | state j => rfl
  | b i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      cases d with
      | a j => simp only [TaggedColumnIsUnit]; rw [primal_update_unchanged_of_tag_ne (c := .b i) (d := .a j)
          (i := primalBIndex i) (j := primalAIndex j) rfl rfl hne]
      | y j k => rfl
      | b j => simp only [TaggedColumnIsUnit]; rw [primal_update_unchanged_of_tag_ne (c := .b i) (d := .b j)
          (i := primalBIndex i) (j := primalBIndex j) rfl rfl hne]
      | state j => simp only [TaggedColumnIsUnit]; rw [primal_update_unchanged_of_tag_ne (c := .b i) (d := .state j)
          (i := primalBIndex i) (j := primalStateIndex j) rfl rfl hne]
  | state i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      cases d with
      | a j => simp only [TaggedColumnIsUnit]; rw [primal_update_unchanged_of_tag_ne (c := .state i) (d := .a j)
          (i := primalStateIndex i) (j := primalAIndex j) rfl rfl hne]
      | y j k => rfl
      | b j => simp only [TaggedColumnIsUnit]; rw [primal_update_unchanged_of_tag_ne (c := .state i) (d := .b j)
          (i := primalStateIndex i) (j := primalBIndex j) rfl rfl hne]
      | state j => simp only [TaggedColumnIsUnit]; rw [primal_update_unchanged_of_tag_ne (c := .state i) (d := .state j)
          (i := primalStateIndex i) (j := primalStateIndex j) rfl rfl hne]

theorem TaggedFrameReveal.columnUnit_self {T n DX DY : Nat}
    {c : UnscaledTag T n} {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U U' : Fin (3 * (T - 1)) → EVec DX}
    {V V' : Fin (n * (T - 1)) → EVec DY}
    (hr : TaggedFrameReveal c qX qY U U' V V') :
    TaggedColumnIsUnit U' V' c := by
  cases c with
  | a i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      simpa [TaggedColumnIsUnit, Function.update] using hu
  | y i k =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      simpa [TaggedColumnIsUnit, Function.update] using hu
  | b i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      simpa [TaggedColumnIsUnit, Function.update] using hu
  | state i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      simpa [TaggedColumnIsUnit, Function.update] using hu

theorem TaggedFrameReveal.partial {T n DX DY : Nat}
    {c : UnscaledTag T n} {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U U' : Fin (3 * (T - 1)) → EVec DX}
    {V V' : Fin (n * (T - 1)) → EVec DY}
    (hr : TaggedFrameReveal c qX qY U U' V V')
    (hU : IsPartialOrthonormalFrame U) (hV : IsPartialOrthonormalFrame V)
    (hz : TaggedColumnIsZero U V c) :
    IsPartialOrthonormalFrame U' ∧ IsPartialOrthonormalFrame V' := by
  cases c with
  | a i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      exact ⟨hU.update_zero _ hz u hu horth, hV⟩
  | y i k =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      exact ⟨hU, hV.update_zero _ hz u hu horth⟩
  | b i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      exact ⟨hU.update_zero _ hz u hu horth, hV⟩
  | state i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      exact ⟨hU.update_zero _ hz u hu horth, hV⟩

/-- Reveal serialized coordinate `t`, choosing the new column orthogonal to
both its current product frame and every query made so far. -/
theorem exists_tagged_frame_reveal {T n DX DY t : Nat}
    {U : Fin (3 * (T - 1)) → EVec DX}
    {V : Fin (n * (T - 1)) → EVec DY}
    (qX : List (EVec DX)) (qY : List (EVec DY))
    (ht : t < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + qX.length < DX)
    (hcapY : n * (T - 1) + qY.length < DY)
    (hpartialU : IsPartialOrthonormalFrame U)
    (hpartialV : IsPartialOrthonormalFrame V)
    (hzero : TaggedFramesZeroFrom t U V)
    (hunit : TaggedFramesUnitBelow t U V) :
    ∃ U' V',
      TaggedFrameReveal (UnscaledTag.tagAt ⟨t, ht⟩) qX qY U U' V V' ∧
      IsPartialOrthonormalFrame U' ∧ IsPartialOrthonormalFrame V' ∧
      TaggedFramesZeroFrom (t + 1) U' V' ∧
      TaggedFramesUnitBelow (t + 1) U' V' := by
  let kt : Fin ((T - 1) * (n + 3)) := ⟨t, ht⟩
  let c : UnscaledTag T n := UnscaledTag.tagAt kt
  have hcidx : c.serializedIndex = kt := UnscaledTag.serializedIndex_tagAt kt
  have hcval : c.serializedIndex.val = t := by simpa [kt] using congrArg Fin.val hcidx
  have hczero : TaggedColumnIsZero U V c := hzero c (by omega)
  have build : ∃ U' V', TaggedFrameReveal c qX qY U U' V V' := by
    cases c with
    | a i =>
        obtain ⟨u, hu, horth, hq⟩ :=
          exists_unit_orthogonal_to_frame_constraints U qX hcapX
        exact ⟨Function.update U (primalAIndex i) u, V,
          rfl, u, rfl, hu, horth, hq⟩
    | y i k =>
        obtain ⟨u, hu, horth, hq⟩ :=
          exists_unit_orthogonal_to_frame_constraints V qY hcapY
        exact ⟨U, Function.update V (dualBlockIndex i k) u,
          rfl, u, rfl, hu, horth, hq⟩
    | b i =>
        obtain ⟨u, hu, horth, hq⟩ :=
          exists_unit_orthogonal_to_frame_constraints U qX hcapX
        exact ⟨Function.update U (primalBIndex i) u, V,
          rfl, u, rfl, hu, horth, hq⟩
    | state i =>
        obtain ⟨u, hu, horth, hq⟩ :=
          exists_unit_orthogonal_to_frame_constraints U qX hcapX
        exact ⟨Function.update U (primalStateIndex i) u, V,
          rfl, u, rfl, hu, horth, hq⟩
  obtain ⟨U', V', hr⟩ := build
  have hp := hr.partial hpartialU hpartialV hczero
  have hz' : TaggedFramesZeroFrom (t + 1) U' V' := by
    intro d hd
    have hne : c.serializedIndex ≠ d.serializedIndex := by
      intro heq
      have hv := congrArg Fin.val heq
      omega
    exact (hr.columnZero_iff_of_ne hne).2 (hzero d (by omega))
  have hu' : TaggedFramesUnitBelow (t + 1) U' V' := by
    intro d hd
    by_cases hdt : d.serializedIndex.val < t
    · have hne : c.serializedIndex ≠ d.serializedIndex := by
        intro heq
        have hv := congrArg Fin.val heq
        omega
      exact (hr.columnUnit_iff_of_ne hne).2 (hunit d hdt)
    · have heq : d.serializedIndex = c.serializedIndex := by
        apply Fin.ext
        omega
      have hdc : d = c := UnscaledTag.serializedIndex_injective heq
      subst d
      exact hr.columnUnit_self
  refine ⟨U', V', ?_, hp.1, hp.2, hz', hu'⟩
  simpa [c, kt] using hr

theorem taggedFrames_orthonormal_of_complete {T n DX DY : Nat}
    {U : Fin (3 * (T - 1)) → EVec DX}
    {V : Fin (n * (T - 1)) → EVec DY}
    (hpU : IsPartialOrthonormalFrame U) (hpV : IsPartialOrthonormalFrame V)
    (hu : TaggedFramesUnitBelow ((T - 1) * (n + 3)) U V) :
    IsOrthonormalFrame U ∧ IsOrthonormalFrame V := by
  constructor
  · apply isOrthonormalFrame_of_partial_complete hpU
    intro j
    obtain ⟨c, hc⟩ := UnscaledTag.primalIndex_surjective (n := n) j
    have hcu := hu c c.serializedIndex.isLt
    cases c with
    | a i =>
        simp [UnscaledTag.primalIndex] at hc
        subst j
        exact hcu
    | y i k => simp [UnscaledTag.primalIndex] at hc
    | b i =>
        simp [UnscaledTag.primalIndex] at hc
        subst j
        exact hcu
    | state i =>
        simp [UnscaledTag.primalIndex] at hc
        subst j
        exact hcu
  · apply isOrthonormalFrame_of_partial_complete hpV
    intro j
    obtain ⟨c, hc⟩ := UnscaledTag.dualIndex_surjective (T := T) j
    have hcu := hu c c.serializedIndex.isLt
    cases c with
    | a i => simp [UnscaledTag.dualIndex] at hc
    | y i k =>
        simp [UnscaledTag.dualIndex] at hc
        subst j
        exact hcu
    | b i => simp [UnscaledTag.dualIndex] at hc
    | state i => simp [UnscaledTag.dualIndex] at hc

/-- Hidden tagged columns force the projected joint query to be supported in
the already-revealed serialized prefix. -/
theorem supportedBelow_serializeProjection_of_taggedZero {T n DX DY t : Nat}
    {U : Fin (3 * (T - 1)) → EVec DX}
    {V : Fin (n * (T - 1)) → EVec DY}
    (hz : TaggedFramesZeroFrom t U V) (X : EVec DX) (Y : EVec DY) :
    SupportedBelow t
      (serializeUnscaled (frameProject U X) (frameProject V Y)) := by
  intro j hj
  let c : UnscaledTag T n := UnscaledTag.tagAt j
  have hc : c.serializedIndex = j := UnscaledTag.serializedIndex_tagAt j
  have hcol : TaggedColumnIsZero U V c := by
    apply hz c
    simpa [hc] using hj
  rw [← hc]
  cases hcCase : c with
  | a i =>
      have hcol' : U (primalAIndex i) = 0 := by
        apply hz (.a i)
        have hceq : (UnscaledTag.a i).serializedIndex = j := by
          simpa [hcCase] using hc
        simpa [hceq] using hj
      change serializedA (serializeUnscaled (frameProject U X) (frameProject V Y)) i = 0
      rw [serializedA_serializeUnscaled]
      change frameProject U X (primalAIndex i) = 0
      unfold frameProject
      rw [hcol']
      simp [evecDotValue]
  | y i k =>
      have hcol' : V (dualBlockIndex i k) = 0 := by
        apply hz (.y i k)
        have hceq : (UnscaledTag.y i k).serializedIndex = j := by
          simpa [hcCase] using hc
        simpa [hceq] using hj
      change serializedY (serializeUnscaled (frameProject U X) (frameProject V Y)) i k = 0
      rw [serializedY_serializeUnscaled]
      change frameProject V Y (dualBlockIndex i k) = 0
      unfold frameProject
      rw [hcol']
      simp [evecDotValue]
  | b i =>
      have hcol' : U (primalBIndex i) = 0 := by
        apply hz (.b i)
        have hceq : (UnscaledTag.b i).serializedIndex = j := by
          simpa [hcCase] using hc
        simpa [hceq] using hj
      change serializedB (serializeUnscaled (frameProject U X) (frameProject V Y)) i = 0
      rw [serializedB_serializeUnscaled]
      change frameProject U X (primalBIndex i) = 0
      unfold frameProject
      rw [hcol']
      simp [evecDotValue]
  | state i =>
      have hcol' : U (primalStateIndex i) = 0 := by
        apply hz (.state i)
        have hceq : (UnscaledTag.state i).serializedIndex = j := by
          simpa [hcCase] using hc
        simpa [hceq] using hj
      change serializedState (serializeUnscaled (frameProject U X) (frameProject V Y)) i = 0
      rw [serializedState_serializeUnscaled]
      change frameProject U X (primalStateIndex i) = 0
      unfold frameProject
      rw [hcol']
      simp [evecDotValue]

/-- A tagged reveal does not change the ambient embedding of any separated
response whose genuine serialization is supported before the revealed tag. -/
theorem TaggedFrameReveal.embed_eq_of_serialize_supported {T n DX DY : Nat}
    {c : UnscaledTag T n} {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U U' : Fin (3 * (T - 1)) → EVec DX}
    {V V' : Fin (n * (T - 1)) → EVec DY}
    (hr : TaggedFrameReveal c qX qY U U' V V')
    {x : UnscaledPrimal T} {y : UnscaledDual T n}
    (hs : SupportedBelow c.serializedIndex.val (serializeUnscaled x y)) :
    frameEmbed U' x = frameEmbed U x ∧
      frameEmbed V' y = frameEmbed V y := by
  have hcoord : serializeUnscaled x y c.serializedIndex = 0 :=
    hs c.serializedIndex le_rfl
  cases c with
  | a i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      constructor
      · apply frameEmbed_update_eq_of_coeff_zero
        change primalA x i = 0
        change serializeUnscaled x y (serializedAIndex (n := n) i) = 0 at hcoord
        change serializedA (serializeUnscaled x y) i = 0 at hcoord
        simpa using hcoord
      · rfl
  | y i k =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      constructor
      · rfl
      · apply frameEmbed_update_eq_of_coeff_zero
        change dualBlock y i k = 0
        change serializeUnscaled x y (serializedDualIndex i k) = 0 at hcoord
        change serializedY (serializeUnscaled x y) i k = 0 at hcoord
        simpa using hcoord
  | b i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      constructor
      · apply frameEmbed_update_eq_of_coeff_zero
        change primalB x i = 0
        change serializeUnscaled x y (serializedBIndex (n := n) i) = 0 at hcoord
        change serializedB (serializeUnscaled x y) i = 0 at hcoord
        simpa using hcoord
      · rfl
  | state i =>
      rcases hr with ⟨rfl, u, rfl, hu, horth, hq⟩
      constructor
      · apply frameEmbed_update_eq_of_coeff_zero
        change primalState x i = 0
        change serializeUnscaled x y (serializedStateIndex (n := n) i) = 0 at hcoord
        change serializedState (serializeUnscaled x y) i = 0 at hcoord
        simpa using hcoord
      · rfl

/-- Complete all still-hidden tagged columns while preserving the projections
of a fixed finite query list and the embeddings of responses supported in the
already-revealed prefix. -/
theorem exists_tagged_frame_completion_aux
    {T n DX DY t remaining : Nat}
    (qX : List (EVec DX)) (qY : List (EVec DY))
    {U : Fin (3 * (T - 1)) → EVec DX}
    {V : Fin (n * (T - 1)) → EVec DY}
    (hend : t + remaining = (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + qX.length < DX)
    (hcapY : n * (T - 1) + qY.length < DY)
    (hpU : IsPartialOrthonormalFrame U) (hpV : IsPartialOrthonormalFrame V)
    (hz : TaggedFramesZeroFrom t U V)
    (hu : TaggedFramesUnitBelow t U V) :
    ∃ U' V', IsOrthonormalFrame U' ∧ IsOrthonormalFrame V' ∧
      (∀ X ∈ qX, frameProject U' X = frameProject U X) ∧
      (∀ Y ∈ qY, frameProject V' Y = frameProject V Y) ∧
      ∀ x : UnscaledPrimal T, ∀ y : UnscaledDual T n,
        SupportedBelow t (serializeUnscaled x y) →
        frameEmbed U' x = frameEmbed U x ∧
          frameEmbed V' y = frameEmbed V y := by
  induction remaining generalizing t U V with
  | zero =>
      have ht : t = (T - 1) * (n + 3) := by omega
      have ho := taggedFrames_orthonormal_of_complete hpU hpV (by simpa [ht] using hu)
      refine ⟨U, V, ho.1, ho.2, ?_, ?_, ?_⟩
      · intro X hX; rfl
      · intro Y hY; rfl
      · intro x y hs; exact ⟨rfl, rfl⟩
  | succ remaining ih =>
      have ht : t < (T - 1) * (n + 3) := by omega
      obtain ⟨U1, V1, hr, hpU1, hpV1, hz1, hu1⟩ :=
        exists_tagged_frame_reveal qX qY ht hcapX hcapY hpU hpV hz hu
      have hend1 : (t + 1) + remaining = (T - 1) * (n + 3) := by omega
      obtain ⟨U2, V2, hU2, hV2, hprojX2, hprojY2, hembed2⟩ :=
        ih hend1 hpU1 hpV1 hz1 hu1
      let c : UnscaledTag T n := UnscaledTag.tagAt
        (⟨t, ht⟩ : Fin ((T - 1) * (n + 3)))
      have hcval : c.serializedIndex.val = t := by
        simpa [c] using congrArg Fin.val
          (UnscaledTag.serializedIndex_tagAt
            (⟨t, ht⟩ : Fin ((T - 1) * (n + 3))))
      have hr' : TaggedFrameReveal c qX qY U U1 V V1 := by simpa [c] using hr
      have hzC : TaggedFramesZeroFrom c.serializedIndex.val U V := by
        simpa [hcval] using hz
      have hp := hr'.project_eq hzC
      refine ⟨U2, V2, hU2, hV2, ?_, ?_, ?_⟩
      · intro X hX; rw [hprojX2 X hX, hp.1 X hX]
      · intro Y hY; rw [hprojY2 Y hY, hp.2 Y hY]
      · intro x y hs
        have hs1 : SupportedBelow (t + 1) (serializeUnscaled x y) :=
          hs.mono (by omega)
        have h2 := hembed2 x y hs1
        have h1 := hr'.embed_eq_of_serialize_supported (by simpa [hcval] using hs)
        exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem exists_tagged_frame_completion
    {T n DX DY t : Nat}
    (qX : List (EVec DX)) (qY : List (EVec DY))
    {U : Fin (3 * (T - 1)) → EVec DX}
    {V : Fin (n * (T - 1)) → EVec DY}
    (ht : t ≤ (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + qX.length < DX)
    (hcapY : n * (T - 1) + qY.length < DY)
    (hpU : IsPartialOrthonormalFrame U) (hpV : IsPartialOrthonormalFrame V)
    (hz : TaggedFramesZeroFrom t U V)
    (hu : TaggedFramesUnitBelow t U V) :
    ∃ U' V', IsOrthonormalFrame U' ∧ IsOrthonormalFrame V' ∧
      (∀ X ∈ qX, frameProject U' X = frameProject U X) ∧
      (∀ Y ∈ qY, frameProject V' Y = frameProject V Y) ∧
      ∀ x : UnscaledPrimal T, ∀ y : UnscaledDual T n,
        SupportedBelow t (serializeUnscaled x y) →
        frameEmbed U' x = frameEmbed U x ∧
          frameEmbed V' y = frameEmbed V y := by
  apply exists_tagged_frame_completion_aux qX qY
    (remaining := (T - 1) * (n + 3) - t)
  · omega
  · exact hcapX
  · exact hcapY
  · exact hpU
  · exact hpV
  · exact hz
  · exact hu

/-- The signed product gradient, viewed in the paper's serialized order. -/
def taggedSerializedSaddleFieldOf {T n : Nat}
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (z : SerializedSpace T n) : SerializedSpace T n :=
  serializeUnscaled
    (gradX (unserializePrimal z) (unserializeDual z))
    (-gradY (unserializePrimal z) (unserializeDual z))

/-- Separated coordinates of the genuine serialized gradient. -/
def packedTrueGradX {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (x : UnscaledPrimal T) (y : UnscaledDual T n) : UnscaledPrimal T :=
  unserializePrimal (serializedTrueGradient hn P (serializeUnscaled x y))

def packedTrueGradY {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (x : UnscaledPrimal T) (y : UnscaledDual T n) : UnscaledDual T n :=
  unserializeDual (serializedTrueGradient hn P (serializeUnscaled x y))

theorem taggedSerializedSaddleFieldOf_packedTrueGradient
    {T n : Nat} (hn : 0 < n) (P : UnscaledParameters) :
    taggedSerializedSaddleFieldOf
      (packedTrueGradX (T := T) hn P) (packedTrueGradY (T := T) hn P) =
      packedUnserializedTrueSaddleField hn P := by
  funext z
  simp [taggedSerializedSaddleFieldOf, packedTrueGradX, packedTrueGradY,
    packedUnserializedTrueSaddleField]

theorem packedTrueGradient_tagged_zeroChain
    {T n : Nat} (hn : 0 < n) (P : UnscaledParameters) :
    NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf
        (packedTrueGradX (T := T) hn P) (packedTrueGradY (T := T) hn P)) := by
  rw [taggedSerializedSaddleFieldOf_packedTrueGradient hn P]
  exact packedUnserializedTrueSaddleField_isFirstOrderZeroChain hn P

/-- Stability of a genuine rotated first-order reply under one online tagged
reveal.  No zero-respecting property of the algorithm is assumed. -/
theorem firstOrderRecord_rotated_eq_of_tagged_reveal
    {T n DX DY : Nat}
    {F : UnscaledPrimal T → UnscaledDual T n → ℝ}
    {gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T}
    {gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n}
    {c : UnscaledTag T n}
    {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U U' : Fin (3 * (T - 1)) → EVec DX}
    {V V' : Fin (n * (T - 1)) → EVec DY}
    (hr : TaggedFrameReveal c qX qY U U' V V')
    (hzero : TaggedFramesZeroFrom c.serializedIndex.val U V)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    {r : Nat} (hrc : r < c.serializedIndex.val)
    {X : EVec DX} {Y : EVec DY} (hX : X ∈ qX) (hY : Y ∈ qY)
    (hsupp : SupportedBelow r
      (serializeUnscaled (frameProject U X) (frameProject V Y))) :
    firstOrderRecord (rotatedF U' V' F)
        (rotatedGradX U' V' gradX) (rotatedGradY U' V' gradY) (X, Y) =
      firstOrderRecord (rotatedF U V F)
        (rotatedGradX U V gradX) (rotatedGradY U V gradY) (X, Y) := by
  have hp := hr.project_eq hzero
  have hpX := hp.1 X hX
  have hpY := hp.2 Y hY
  let x := frameProject U X
  let y := frameProject V Y
  let z := serializeUnscaled x y
  have hresponse : SupportedBelow (r + 1)
      (taggedSerializedSaddleFieldOf gradX gradY z) :=
    hchain r z hsupp
  have hresponse' : SupportedBelow c.serializedIndex.val
      (taggedSerializedSaddleFieldOf gradX gradY z) :=
    hresponse.mono (by omega)
  have hpack : taggedSerializedSaddleFieldOf gradX gradY z =
      serializeUnscaled (gradX x y) (-gradY x y) := by
    simp [taggedSerializedSaddleFieldOf, z, x, y]
  rw [hpack] at hresponse'
  have he := hr.embed_eq_of_serialize_supported hresponse'
  have heY : frameEmbed V' (gradY x y) = frameEmbed V (gradY x y) := by
    rw [frameEmbed_neg, frameEmbed_neg] at he
    exact neg_injective he.2
  simp [firstOrderRecord, rotatedF, rotatedGradX, rotatedGradY,
    hpX, hpY, x, y, he.1, heY]

/-- Stability of a genuine rotated first-order reply after all hidden tagged
columns have been completed.  The hypotheses state exactly what the
completion construction preserves: projections of earlier queries and
embeddings of responses supported in the revealed prefix. -/
theorem firstOrderRecord_rotated_eq_of_tagged_completion
    {T n DX DY K : Nat}
    {F : UnscaledPrimal T → UnscaledDual T n → ℝ}
    {gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T}
    {gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n}
    {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U U' : Fin (3 * (T - 1)) → EVec DX}
    {V V' : Fin (n * (T - 1)) → EVec DY}
    (hprojX : ∀ X ∈ qX, frameProject U' X = frameProject U X)
    (hprojY : ∀ Y ∈ qY, frameProject V' Y = frameProject V Y)
    (hembed : ∀ x : UnscaledPrimal T, ∀ y : UnscaledDual T n,
      SupportedBelow K (serializeUnscaled x y) →
      frameEmbed U' x = frameEmbed U x ∧
        frameEmbed V' y = frameEmbed V y)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    {r : Nat} (hrK : r < K)
    {X : EVec DX} {Y : EVec DY} (hX : X ∈ qX) (hY : Y ∈ qY)
    (hsupp : SupportedBelow r
      (serializeUnscaled (frameProject U X) (frameProject V Y))) :
    firstOrderRecord (rotatedF U' V' F)
        (rotatedGradX U' V' gradX) (rotatedGradY U' V' gradY) (X, Y) =
      firstOrderRecord (rotatedF U V F)
        (rotatedGradX U V gradX) (rotatedGradY U V gradY) (X, Y) := by
  have hpX := hprojX X hX
  have hpY := hprojY Y hY
  let x := frameProject U X
  let y := frameProject V Y
  let z := serializeUnscaled x y
  have hresponse : SupportedBelow (r + 1)
      (taggedSerializedSaddleFieldOf gradX gradY z) :=
    hchain r z hsupp
  have hresponse' : SupportedBelow K
      (taggedSerializedSaddleFieldOf gradX gradY z) :=
    hresponse.mono (by omega)
  have hpack : taggedSerializedSaddleFieldOf gradX gradY z =
      serializeUnscaled (gradX x y) (-gradY x y) := by
    simp [taggedSerializedSaddleFieldOf, z, x, y]
  rw [hpack] at hresponse'
  have he := hembed (gradX x y) (-gradY x y) hresponse'
  have heY : frameEmbed V' (gradY x y) = frameEmbed V (gradY x y) := by
    rw [frameEmbed_neg, frameEmbed_neg] at he
    exact neg_injective he.2
  simp [firstOrderRecord, rotatedF, rotatedGradX, rotatedGradY,
    hpX, hpY, x, y, he.1, heY]

/-- Exact transcript invariant for the tagged online construction. -/
def TaggedResistingFits {T n DX DY : Nat}
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (U : Fin (3 * (T - 1)) → EVec DX)
    (V : Fin (n * (T - 1)) → EVec DY) :
    Nat → List (FirstOrderRecord DX DY) → Prop
  | _, [] => True
  | s, r :: rs =>
      r = firstOrderRecord (rotatedF U V F)
        (rotatedGradX U V gradX) (rotatedGradY U V gradY)
        (r.queryX, r.queryY) ∧
      SupportedBelow s
        (serializeUnscaled (frameProject U r.queryX) (frameProject V r.queryY)) ∧
      TaggedResistingFits F gradX gradY U V (s + 1) rs

theorem TaggedResistingFits.snoc {T n DX DY : Nat}
    {F : UnscaledPrimal T → UnscaledDual T n → ℝ}
    {gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T}
    {gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n}
    {U : Fin (3 * (T - 1)) → EVec DX}
    {V : Fin (n * (T - 1)) → EVec DY}
    {s : Nat} {hist : List (FirstOrderRecord DX DY)}
    (hfits : TaggedResistingFits F gradX gradY U V s hist)
    (r : FirstOrderRecord DX DY)
    (hrecord : r = firstOrderRecord (rotatedF U V F)
      (rotatedGradX U V gradX) (rotatedGradY U V gradY)
      (r.queryX, r.queryY))
    (hsupp : SupportedBelow (s + hist.length)
      (serializeUnscaled (frameProject U r.queryX) (frameProject V r.queryY))) :
    TaggedResistingFits F gradX gradY U V s (hist ++ [r]) := by
  induction hist generalizing s with
  | nil =>
      change r = firstOrderRecord (rotatedF U V F)
          (rotatedGradX U V gradX) (rotatedGradY U V gradY)
          (r.queryX, r.queryY) ∧
        SupportedBelow s
          (serializeUnscaled (frameProject U r.queryX) (frameProject V r.queryY)) ∧
        True
      refine ⟨hrecord, ?_, True.intro⟩
      simpa using hsupp
  | cons a hist ih =>
      simp only [TaggedResistingFits] at hfits ⊢
      refine ⟨hfits.1, hfits.2.1, ?_⟩
      apply ih hfits.2.2
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsupp

theorem TaggedResistingFits.of_reveal {T n DX DY : Nat}
    {F : UnscaledPrimal T → UnscaledDual T n → ℝ}
    {gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T}
    {gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n}
    {c : UnscaledTag T n}
    {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U U' : Fin (3 * (T - 1)) → EVec DX}
    {V V' : Fin (n * (T - 1)) → EVec DY}
    (hr : TaggedFrameReveal c qX qY U U' V V')
    (hzero : TaggedFramesZeroFrom c.serializedIndex.val U V)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    {s : Nat} {hist : List (FirstOrderRecord DX DY)}
    (hend : s + hist.length = c.serializedIndex.val)
    (hmemX : ∀ r ∈ hist, r.queryX ∈ qX)
    (hmemY : ∀ r ∈ hist, r.queryY ∈ qY)
    (hfits : TaggedResistingFits F gradX gradY U V s hist) :
    TaggedResistingFits F gradX gradY U' V' s hist := by
  induction hist generalizing s with
  | nil => trivial
  | cons a hist ih =>
      simp only [TaggedResistingFits] at hfits ⊢
      have hsc : s < c.serializedIndex.val := by simp at hend; omega
      have haX : a.queryX ∈ qX := hmemX a (by simp)
      have haY : a.queryY ∈ qY := hmemY a (by simp)
      have hstable := firstOrderRecord_rotated_eq_of_tagged_reveal
        (F := F) hr hzero hchain hsc haX haY hfits.2.1
      have hp := hr.project_eq hzero
      refine ⟨hfits.1.trans hstable.symm, ?_, ?_⟩
      · rw [hp.1 a.queryX haX, hp.2 a.queryY haY]
        exact hfits.2.1
      · apply ih (s := s + 1)
        · simp at hend ⊢; omega
        · intro r hrmem; exact hmemX r (by simp [hrmem])
        · intro r hrmem; exact hmemY r (by simp [hrmem])
        · exact hfits.2.2

/-- Completion of the hidden columns preserves every exact reply in a
finite tagged resisting transcript. -/
theorem TaggedResistingFits.of_completion {T n DX DY K : Nat}
    {F : UnscaledPrimal T → UnscaledDual T n → ℝ}
    {gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T}
    {gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n}
    {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U U' : Fin (3 * (T - 1)) → EVec DX}
    {V V' : Fin (n * (T - 1)) → EVec DY}
    (hprojX : ∀ X ∈ qX, frameProject U' X = frameProject U X)
    (hprojY : ∀ Y ∈ qY, frameProject V' Y = frameProject V Y)
    (hembed : ∀ x : UnscaledPrimal T, ∀ y : UnscaledDual T n,
      SupportedBelow K (serializeUnscaled x y) →
      frameEmbed U' x = frameEmbed U x ∧
        frameEmbed V' y = frameEmbed V y)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    {s : Nat} {hist : List (FirstOrderRecord DX DY)}
    (hend : s + hist.length = K)
    (hmemX : ∀ r ∈ hist, r.queryX ∈ qX)
    (hmemY : ∀ r ∈ hist, r.queryY ∈ qY)
    (hfits : TaggedResistingFits F gradX gradY U V s hist) :
    TaggedResistingFits F gradX gradY U' V' s hist := by
  induction hist generalizing s with
  | nil => trivial
  | cons a hist ih =>
      simp only [TaggedResistingFits] at hfits ⊢
      have hsK : s < K := by simp at hend; omega
      have haX : a.queryX ∈ qX := hmemX a (by simp)
      have haY : a.queryY ∈ qY := hmemY a (by simp)
      have hstable := firstOrderRecord_rotated_eq_of_tagged_completion
        (F := F) hprojX hprojY hembed hchain hsK haX haY hfits.2.1
      refine ⟨hfits.1.trans hstable.symm, ?_, ?_⟩
      · rw [hprojX a.queryX haX, hprojY a.queryY haY]
        exact hfits.2.1
      · apply ih (s := s + 1)
        · simp at hend ⊢; omega
        · intro r hrmem; exact hmemX r (by simp [hrmem])
        · intro r hrmem; exact hmemY r (by simp [hrmem])
        · exact hfits.2.2

/-- Convert the project's typed history component into the list interface used
by the online frame induction.  The conversion contains exactly the oracle
reply fields and therefore grants no extra access to the objective. -/
def productRotatedInstance {T n DX DY : Nat}
    (X : Set (EVec DX)) (Y : Set (EVec DY))
    (U : Fin (3 * (T - 1)) → EVec DX)
    (V : Fin (n * (T - 1)) → EVec DY)
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n) :
    NCCInstance DX DY where
  X := X
  Y := Y
  f := rotatedF U V F
  gradX := rotatedGradX U V gradX
  gradY := rotatedGradY U V gradY
  x0 := 0

def firstOrderRecordReply {DX DY : Nat} (r : FirstOrderRecord DX DY) :
    Oracle.OracleReply DX DY where
  value := r.value
  gradX := r.gradX
  gradY := r.gradY

def listReplyHistory {DX DY : Nat} (hist : List (FirstOrderRecord DX DY)) :
    Oracle.ReplyHistory DX DY hist.length :=
  fun i => firstOrderRecordReply (hist.get i)

def componentBlackBox {DX DY : Nat} {X : Set (EVec DX)} {Y : Set (EVec DY)}
    (A : Oracle.DeterministicFOComponent X Y) :
    DeterministicFOBlackBox DX DY where
  nextQuery hist := A.nextQuery hist.length (listReplyHistory hist)
  output _ := 0

/-- The list adapter and the project's typed recursion generate the same
chronological query/reply transcript. -/
theorem runHistory_componentBlackBox_eq_queriedRecords
    {T n DX DY : Nat} {X : Set (EVec DX)} {Y : Set (EVec DY)}
    (A : Oracle.DeterministicFOComponent X Y)
    (U : Fin (3 * (T - 1)) → EVec DX)
    (V : Fin (n * (T - 1)) → EVec DY)
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (t : Nat) :
    runHistory (componentBlackBox A) (rotatedF U V F)
        (rotatedGradX U V gradX) (rotatedGradY U V gradY) t =
      List.ofFn (fun i : Fin t =>
        let q := Oracle.DeterministicFOComponent.queriedAt A
          (productRotatedInstance X Y U V F gradX gradY) i.val
        firstOrderRecord (rotatedF U V F)
          (rotatedGradX U V gradX) (rotatedGradY U V gradY) q) := by
  let P := productRotatedInstance X Y U V F gradX gradY
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [runHistory, ih, List.ofFn_succ']
      let hist : List (FirstOrderRecord DX DY) := List.ofFn (fun i : Fin t =>
        let q := Oracle.DeterministicFOComponent.queriedAt A P i.val
        firstOrderRecord (rotatedF U V F)
          (rotatedGradX U V gradX) (rotatedGradY U V gradY) q)
      have hnext : (componentBlackBox A).nextQuery hist =
          Oracle.DeterministicFOComponent.queriedAt A P t := by
        rw [Oracle.DeterministicFOComponent.queriedAt_eq_nextQuery]
        let nextSigma : (Σ s, Oracle.ReplyHistory DX DY s) → Oracle.Query DX DY :=
          fun h => A.nextQuery h.1 h.2
        have hsigma : (⟨hist.length, listReplyHistory hist⟩ :
              Σ s, Oracle.ReplyHistory DX DY s) =
            ⟨t, Oracle.DeterministicFOComponent.queriedTranscript A P t⟩ := by
          have hlen : hist.length = t := by simp [hist]
          refine Sigma.ext hlen ?_
          apply (Fin.heq_fun_iff hlen).2
          intro i
          simp [hist, listReplyHistory, firstOrderRecordReply,
            Oracle.DeterministicFOComponent.queriedTranscript,
            Oracle.DeterministicFOComponent.replyAt, Oracle.firstOrderOracle,
            firstOrderRecord, P, productRotatedInstance]
        exact congrArg nextSigma hsigma
      change hist ++ [_] = _
      rw [hnext]
      simpa [hist, List.concat_eq_append, P]

/-- Online tagged resisting state for an arbitrary deterministic domain
component.  This derives transcript consistency; it does not assume it. -/
theorem exists_partial_tagged_resisting_state
    {T n DX DY K : Nat} {X : Set (EVec DX)} {Y : Set (EVec DY)}
    (A : Oracle.DeterministicFOComponent X Y)
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY) :
    ∀ t ≤ K, ∃ U V hist,
      hist.length = t ∧
      IsCausalHistory (componentBlackBox A) hist ∧
      IsPartialOrthonormalFrame U ∧ IsPartialOrthonormalFrame V ∧
      TaggedFramesZeroFrom t U V ∧ TaggedFramesUnitBelow t U V ∧
      TaggedResistingFits F gradX gradY U V 0 hist := by
  intro t htK
  induction t with
  | zero =>
      refine ⟨0, 0, [], rfl, ?_, isPartialOrthonormalFrame_zero,
        isPartialOrthonormalFrame_zero, ?_, ?_, ?_⟩
      · simp [IsCausalHistory, CausalExtension]
      · intro c hc; cases c <;> simp [TaggedColumnIsZero]
      · intro c hc; omega
      · simp [TaggedResistingFits]
  | succ t ih =>
      have htK' : t ≤ K := by omega
      obtain ⟨U, V, hist, hlen, hcausal, hpU, hpV, hz, hu, hfits⟩ := ih htK'
      let q := (componentBlackBox A).nextQuery hist
      let qX : List (EVec DX) := hist.map FirstOrderRecord.queryX ++ [q.1]
      let qY : List (EVec DY) := hist.map FirstOrderRecord.queryY ++ [q.2]
      have htM : t < (T - 1) * (n + 3) := by omega
      have hcapXt : 3 * (T - 1) + qX.length < DX := by simp [qX, hlen]; omega
      have hcapYt : n * (T - 1) + qY.length < DY := by simp [qY, hlen]; omega
      obtain ⟨U1, V1, hr, hpU1, hpV1, hz1, hu1⟩ :=
        exists_tagged_frame_reveal qX qY htM hcapXt hcapYt hpU hpV hz hu
      let c : UnscaledTag T n := UnscaledTag.tagAt ⟨t, htM⟩
      have hcval : c.serializedIndex.val = t := by
        simpa [c] using congrArg Fin.val
          (UnscaledTag.serializedIndex_tagAt (⟨t, htM⟩ : Fin ((T - 1) * (n + 3))))
      have hr' : TaggedFrameReveal c qX qY U U1 V V1 := by simpa [c] using hr
      have hzC : TaggedFramesZeroFrom c.serializedIndex.val U V := by simpa [hcval] using hz
      have hmemX : ∀ r ∈ hist, r.queryX ∈ qX := by
        intro r hmem; exact List.mem_append_left _ (List.mem_map.mpr ⟨r, hmem, rfl⟩)
      have hmemY : ∀ r ∈ hist, r.queryY ∈ qY := by
        intro r hmem; exact List.mem_append_left _ (List.mem_map.mpr ⟨r, hmem, rfl⟩)
      have hfits1 : TaggedResistingFits F gradX gradY U1 V1 0 hist := by
        apply hfits.of_reveal hr' hzC hchain
        · simpa [hlen, hcval]
        · exact hmemX
        · exact hmemY
      have hqX : q.1 ∈ qX := by simp [qX]
      have hqY : q.2 ∈ qY := by simp [qY]
      have hproj := hr'.project_eq hzC
      have hqsuppOld : SupportedBelow t
          (serializeUnscaled (frameProject U q.1) (frameProject V q.2)) :=
        supportedBelow_serializeProjection_of_taggedZero hz q.1 q.2
      have hqsupp : SupportedBelow t
          (serializeUnscaled (frameProject U1 q.1) (frameProject V1 q.2)) := by
        rw [hproj.1 q.1 hqX, hproj.2 q.2 hqY]
        exact hqsuppOld
      let rnew : FirstOrderRecord DX DY :=
        firstOrderRecord (rotatedF U1 V1 F)
          (rotatedGradX U1 V1 gradX) (rotatedGradY U1 V1 gradY) q
      have hfitsNew : TaggedResistingFits F gradX gradY U1 V1 0
          (hist ++ [rnew]) := by
        apply hfits1.snoc rnew
        · rfl
        · simpa [hlen, rnew, firstOrderRecord] using hqsupp
      have hcausalNew : IsCausalHistory (componentBlackBox A) (hist ++ [rnew]) := by
        unfold IsCausalHistory at hcausal ⊢
        apply hcausal.snoc rnew
        rfl
      refine ⟨U1, V1, hist ++ [rnew], ?_, hcausalNew,
        hpU1, hpV1, hz1, hu1, hfitsNew⟩
      simp [hlen]

theorem TaggedResistingFits.forall_records {T n DX DY s : Nat}
    {F : UnscaledPrimal T → UnscaledDual T n → ℝ}
    {gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T}
    {gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n}
    {U : Fin (3 * (T - 1)) → EVec DX}
    {V : Fin (n * (T - 1)) → EVec DY}
    {hist : List (FirstOrderRecord DX DY)}
    (hfits : TaggedResistingFits F gradX gradY U V s hist) :
    ∀ a ∈ hist, a = firstOrderRecord (rotatedF U V F)
      (rotatedGradX U V gradX) (rotatedGradY U V gradY)
      (a.queryX, a.queryY) := by
  induction hist generalizing s with
  | nil => simp
  | cons a hist ih =>
      simp only [TaggedResistingFits] at hfits
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hfits.1
      · exact ih hfits.2.2 b hb

theorem TaggedResistingFits.get_supported {T n DX DY s : Nat}
    {F : UnscaledPrimal T → UnscaledDual T n → ℝ}
    {gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T}
    {gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n}
    {U : Fin (3 * (T - 1)) → EVec DX}
    {V : Fin (n * (T - 1)) → EVec DY}
    {hist : List (FirstOrderRecord DX DY)}
    (hfits : TaggedResistingFits F gradX gradY U V s hist)
    (i : Fin hist.length) :
    SupportedBelow (s + i.val)
      (serializeUnscaled (frameProject U (hist.get i).queryX)
        (frameProject V (hist.get i).queryY)) := by
  induction hist generalizing s with
  | nil => exact Fin.elim0 i
  | cons a hist ih =>
      simp only [TaggedResistingFits] at hfits
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hfits.2.1
      · have hh := ih hfits.2.2 j
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh

/-- The first `K` exact records produced by the arbitrary component adapter
all have zero terminal serialized base coordinate.  Transcript equality is a
conclusion of causality plus exact replies, not a premise. -/
theorem finite_horizon_tagged_transcript
    {T n DX DY K : Nat} {X : Set (EVec DX)} {Y : Set (EVec DY)}
    (A : Oracle.DeterministicFOComponent X Y)
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY) :
    ∃ U V hist,
      hist = runHistory (componentBlackBox A) (rotatedF U V F)
        (rotatedGradX U V gradX) (rotatedGradY U V gradY) K ∧
      IsPartialOrthonormalFrame U ∧ IsPartialOrthonormalFrame V ∧
      TaggedFramesZeroFrom K U V ∧ TaggedFramesUnitBelow K U V ∧
      ∀ i : Fin hist.length,
        serializeUnscaled (frameProject U (hist.get i).queryX)
          (frameProject V (hist.get i).queryY)
          (⟨(T - 1) * (n + 3) - 1, by omega⟩ :
            Fin ((T - 1) * (n + 3))) = 0 := by
  obtain ⟨U, V, hist, hlen, hcausal, hpU, hpV, hz, hu, hfits⟩ :=
    exists_partial_tagged_resisting_state A F gradX gradY hchain hKM
      hcapX hcapY K le_rfl
  have hactual := hfits.forall_records
  have hrun0 := causal_actual_history_eq_run (componentBlackBox A)
    (rotatedF U V F) (rotatedGradX U V gradX) (rotatedGradY U V gradY)
    hcausal hactual
  have hrun : hist = runHistory (componentBlackBox A) (rotatedF U V F)
      (rotatedGradX U V gradX) (rotatedGradY U V gradY) K := by
    simpa [hlen] using hrun0
  have hdim : 0 < (T - 1) * (n + 3) := by omega
  refine ⟨U, V, hist, hrun, hpU, hpV, hz, hu, ?_⟩
  intro i
  have hs := hfits.get_supported i
  apply hs
  have hiK : i.val < K := by simpa [hlen] using i.isLt
  simpa using Nat.le_sub_one_of_lt (hiK.trans hKM)

/-- Full-frame form of the finite-horizon resisting oracle.  The online
partial frames are completed after the first `K` queries, and the preceding
completion-stability theorem proves that the same list is still the exact
oracle transcript for the completed orthonormal frames. -/
theorem finite_horizon_tagged_transcript_orthonormal
    {T n DX DY K : Nat} {X : Set (EVec DX)} {Y : Set (EVec DY)}
    (A : Oracle.DeterministicFOComponent X Y)
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY) :
    ∃ U V hist,
      hist = runHistory (componentBlackBox A) (rotatedF U V F)
        (rotatedGradX U V gradX) (rotatedGradY U V gradY) K ∧
      IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      ∀ i : Fin hist.length,
        serializeUnscaled (frameProject U (hist.get i).queryX)
          (frameProject V (hist.get i).queryY)
          (⟨(T - 1) * (n + 3) - 1, by omega⟩ :
            Fin ((T - 1) * (n + 3))) = 0 := by
  obtain ⟨U0, V0, hist, hlen, hcausal, hpU, hpV, hz, hu, hfits⟩ :=
    exists_partial_tagged_resisting_state A F gradX gradY hchain hKM
      hcapX hcapY K le_rfl
  let qX : List (EVec DX) := hist.map FirstOrderRecord.queryX
  let qY : List (EVec DY) := hist.map FirstOrderRecord.queryY
  have hcapX' : 3 * (T - 1) + qX.length < DX := by
    simp [qX, hlen]
    omega
  have hcapY' : n * (T - 1) + qY.length < DY := by
    simp [qY, hlen]
    omega
  obtain ⟨U, V, hU, hV, hprojX, hprojY, hembed⟩ :=
    exists_tagged_frame_completion qX qY (by omega) hcapX' hcapY'
      hpU hpV hz hu
  have hfits' : TaggedResistingFits F gradX gradY U V 0 hist :=
    hfits.of_completion hprojX hprojY hembed hchain (by simpa [hlen])
      (by
        intro r hr
        exact List.mem_map.mpr ⟨r, hr, rfl⟩)
      (by
        intro r hr
        exact List.mem_map.mpr ⟨r, hr, rfl⟩)
  have hactual := hfits'.forall_records
  have hrun0 := causal_actual_history_eq_run (componentBlackBox A)
    (rotatedF U V F) (rotatedGradX U V gradX) (rotatedGradY U V gradY)
    hcausal hactual
  have hrun : hist = runHistory (componentBlackBox A) (rotatedF U V F)
      (rotatedGradX U V gradX) (rotatedGradY U V gradY) K := by
    simpa [hlen] using hrun0
  refine ⟨U, V, hist, hrun, hU, hV, ?_⟩
  intro i
  have hs := hfits'.get_supported i
  have hiK : i.val < K := by simpa [hlen] using i.isLt
  apply hs
  simpa using Nat.le_sub_one_of_lt (hiK.trans hKM)

/-- Direct `queriedAt` form with genuine complete product rotations. -/
theorem finite_horizon_tagged_queried_terminal_orthonormal
    {T n DX DY K : Nat} {X : Set (EVec DX)} {Y : Set (EVec DY)}
    (A : Oracle.DeterministicFOComponent X Y)
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY) :
    ∃ U V, IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      ∀ t < K,
        let q := Oracle.DeterministicFOComponent.queriedAt A
          (productRotatedInstance X Y U V F gradX gradY) t
        serializeUnscaled (frameProject U q.1) (frameProject V q.2)
          (⟨(T - 1) * (n + 3) - 1, by omega⟩ :
            Fin ((T - 1) * (n + 3))) = 0 := by
  obtain ⟨U, V, hist, hrun, hU, hV, hterminal⟩ :=
    finite_horizon_tagged_transcript_orthonormal A F gradX gradY hchain
      hKM hcapX hcapY
  have hrecords := runHistory_componentBlackBox_eq_queriedRecords
    A U V F gradX gradY K
  have hall : hist = List.ofFn (fun i : Fin K =>
      let q := Oracle.DeterministicFOComponent.queriedAt A
        (productRotatedInstance X Y U V F gradX gradY) i.val
      firstOrderRecord (rotatedF U V F)
        (rotatedGradX U V gradX) (rotatedGradY U V gradY) q) :=
    hrun.trans hrecords
  have hlen : hist.length = K := by
    rw [hrun]
    exact runHistory_length _ _ _ _ K
  refine ⟨U, V, hU, hV, ?_⟩
  intro t ht
  let i : Fin hist.length := ⟨t, by simpa [hlen] using ht⟩
  have hh := hterminal i
  let q := Oracle.DeterministicFOComponent.queriedAt A
    (productRotatedInstance X Y U V F gradX gradY) t
  have hiHist : t < hist.length := by simpa [hlen] using ht
  have hopt := congrArg
    (fun l : List (FirstOrderRecord DX DY) => l[t]?) hall
  have hrec : hist.get i = firstOrderRecord (rotatedF U V F)
      (rotatedGradX U V gradX) (rotatedGradY U V gradY) q := by
    simpa [List.getElem?_eq_getElem, hiHist, ht, i, q] using hopt
  have hqX : (hist.get i).queryX = q.1 := by
    simpa [firstOrderRecord] using congrArg FirstOrderRecord.queryX hrec
  have hqY : (hist.get i).queryY = q.2 := by
    simpa [firstOrderRecord] using congrArg FirstOrderRecord.queryY hrec
  rw [hqX, hqY] at hh
  simpa [q] using hh

/-- Direct `queriedAt` form of the resisting-oracle conclusion. -/
theorem finite_horizon_tagged_queried_terminal
    {T n DX DY K : Nat} {X : Set (EVec DX)} {Y : Set (EVec DY)}
    (A : Oracle.DeterministicFOComponent X Y)
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY) :
    ∃ U V,
      IsPartialOrthonormalFrame U ∧ IsPartialOrthonormalFrame V ∧
      TaggedFramesZeroFrom K U V ∧ TaggedFramesUnitBelow K U V ∧
      ∀ t < K,
        let q := Oracle.DeterministicFOComponent.queriedAt A
          (productRotatedInstance X Y U V F gradX gradY) t
        serializeUnscaled (frameProject U q.1) (frameProject V q.2)
          (⟨(T - 1) * (n + 3) - 1, by omega⟩ :
            Fin ((T - 1) * (n + 3))) = 0 := by
  obtain ⟨U, V, hist, hrun, hpU, hpV, hz, hu, hterminal⟩ :=
    finite_horizon_tagged_transcript A F gradX gradY hchain hKM hcapX hcapY
  have hrecords := runHistory_componentBlackBox_eq_queriedRecords
    A U V F gradX gradY K
  have hall : hist = List.ofFn (fun i : Fin K =>
      let q := Oracle.DeterministicFOComponent.queriedAt A
        (productRotatedInstance X Y U V F gradX gradY) i.val
      firstOrderRecord (rotatedF U V F)
        (rotatedGradX U V gradX) (rotatedGradY U V gradY) q) :=
    hrun.trans hrecords
  have hlen : hist.length = K := by
    rw [hrun]
    exact runHistory_length _ _ _ _ K
  refine ⟨U, V, hpU, hpV, hz, hu, ?_⟩
  intro t ht
  let i : Fin hist.length := ⟨t, by simpa [hlen] using ht⟩
  have hh := hterminal i
  let q := Oracle.DeterministicFOComponent.queriedAt A
    (productRotatedInstance X Y U V F gradX gradY) t
  have hiHist : t < hist.length := by simpa [hlen] using ht
  have hopt := congrArg
    (fun l : List (FirstOrderRecord DX DY) => l[t]?) hall
  have hrec : hist.get i = firstOrderRecord (rotatedF U V F)
      (rotatedGradX U V gradX) (rotatedGradY U V gradY) q := by
    simpa [List.getElem?_eq_getElem, hiHist, ht, i, q] using hopt
  have hqX : (hist.get i).queryX = q.1 := by
    simpa [firstOrderRecord] using congrArg FirstOrderRecord.queryX hrec
  have hqY : (hist.get i).queryY = q.2 := by
    simpa [firstOrderRecord] using congrArg FirstOrderRecord.queryY hrec
  rw [hqX, hqY] at hh
  simpa [q] using hh

/-- Generic stationarity-failure consequence.  In the paper application,
`Stationary` is the OS predicate and `hfailure` is supplied by the terminal
gradient certificate. -/
theorem finite_horizon_tagged_queried_failure
    {T n DX DY K : Nat} {X : Set (EVec DX)} {Y : Set (EVec DY)}
    (A : Oracle.DeterministicFOComponent X Y)
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY)
    (Stationary : EVec DX → Prop)
    (hfailure : ∀ U V (q : Oracle.Query DX DY), q.1 ∈ X → q.2 ∈ Y →
      serializeUnscaled (frameProject U q.1) (frameProject V q.2)
        (⟨(T - 1) * (n + 3) - 1, by omega⟩ :
          Fin ((T - 1) * (n + 3))) = 0 →
      ¬ Stationary q.1) :
    ∃ U V, ∀ t < K,
      ¬ Stationary
        (Oracle.DeterministicFOComponent.queriedAt A
          (productRotatedInstance X Y U V F gradX gradY) t).1 := by
  obtain ⟨U, V, hpU, hpV, hz, hu, hterminal⟩ :=
    finite_horizon_tagged_queried_terminal A F gradX gradY hchain
      hKM hcapX hcapY
  refine ⟨U, V, ?_⟩
  intro t ht
  let P := productRotatedInstance X Y U V F gradX gradY
  let q := Oracle.DeterministicFOComponent.queriedAt A P t
  have hmem := Oracle.DeterministicFOComponent.queriedAt_mem A P t
  exact hfailure U V q hmem.1 hmem.2 (hterminal t ht)

/-- Direct connection to the project's queried-iterate OS failure predicate. -/
theorem finite_horizon_tagged_OS_failure
    {T n DX DY K : Nat} {X : Set (EVec DX)} {Y : Set (EVec DY)}
    (A : Oracle.DeterministicFOComponent X Y)
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY)
    (ell eps : ℝ)
    (hfailure : ∀ U V (q : Oracle.Query DX DY), q.1 ∈ X → q.2 ∈ Y →
      serializeUnscaled (frameProject U q.1) (frameProject V q.2)
        (⟨(T - 1) * (n + 3) - 1, by omega⟩ :
          Fin ((T - 1) * (n + 3))) = 0 →
      ¬ IsOptimizationStationary X (ValueOn Y (rotatedF U V F)) ell eps q.1) :
    ∃ U V, Oracle.DeterministicFOComponent.FailsWithin A
      (productRotatedInstance X Y U V F gradX gradY) ell eps K := by
  obtain ⟨U, V, hpU, hpV, hz, hu, hterminal⟩ :=
    finite_horizon_tagged_queried_terminal A F gradX gradY hchain
      hKM hcapX hcapY
  refine ⟨U, V, ?_⟩
  intro t ht
  let P := productRotatedInstance X Y U V F gradX gradY
  let q := Oracle.DeterministicFOComponent.queriedAt A P t
  have hmem := Oracle.DeterministicFOComponent.queriedAt_mem A P t
  exact hfailure U V q hmem.1 hmem.2 (hterminal t ht)

/-- OS-failure theorem with complete primal and dual orthonormal frames.  This
is the product-preserving analogue of the usual resisting-oracle lower-bound
step: it applies to every deterministic domain component, without assuming
that component is zero-respecting. -/
theorem finite_horizon_tagged_OS_failure_orthonormal
    {T n DX DY K : Nat} {X : Set (EVec DX)} {Y : Set (EVec DY)}
    (A : Oracle.DeterministicFOComponent X Y)
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY)
    (ell eps : ℝ)
    (hfailure : ∀ U V (q : Oracle.Query DX DY), q.1 ∈ X → q.2 ∈ Y →
      serializeUnscaled (frameProject U q.1) (frameProject V q.2)
        (⟨(T - 1) * (n + 3) - 1, by omega⟩ :
          Fin ((T - 1) * (n + 3))) = 0 →
      ¬ IsOptimizationStationary X (ValueOn Y (rotatedF U V F)) ell eps q.1) :
    ∃ U V, IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      Oracle.DeterministicFOComponent.FailsWithin A
        (productRotatedInstance X Y U V F gradX gradY) ell eps K := by
  obtain ⟨U, V, hU, hV, hterminal⟩ :=
    finite_horizon_tagged_queried_terminal_orthonormal A F gradX gradY
      hchain hKM hcapX hcapY
  refine ⟨U, V, hU, hV, ?_⟩
  intro t ht
  let P := productRotatedInstance X Y U V F gradX gradY
  let q := Oracle.DeterministicFOComponent.queriedAt A P t
  have hmem := Oracle.DeterministicFOComponent.queriedAt_mem A P t
  exact hfailure U V q hmem.1 hmem.2 (hterminal t ht)

/-- Hitting-time spelling of the preceding result, using the exact predicate
from `Oracle.ZeroChain`.  Unlike
`queried_iterate_lower_bound_of_zero_chain`, the zero-respecting behavior is
not assumed of `A`: the tagged product rotations are chosen online so that
the actual queried transcript has that behavior in the hidden coordinates. -/
theorem finite_horizon_tagged_queried_hitting_time_orthonormal
    {T n DX DY K : Nat} {X : Set (EVec DX)} {Y : Set (EVec DY)}
    (A : Oracle.DeterministicFOComponent X Y)
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY)
    (ell eps : ℝ)
    (hfailure : ∀ U V (q : Oracle.Query DX DY), q.1 ∈ X → q.2 ∈ Y →
      serializeUnscaled (frameProject U q.1) (frameProject V q.2)
        (⟨(T - 1) * (n + 3) - 1, by omega⟩ :
          Fin ((T - 1) * (n + 3))) = 0 →
      ¬ IsOptimizationStationary X (ValueOn Y (rotatedF U V F)) ell eps q.1) :
    ∃ U V, IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      QueriedIterateHittingTimeAtLeast
        (fun t => (Oracle.DeterministicFOComponent.queriedAt A
          (productRotatedInstance X Y U V F gradX gradY) t).1)
        id
        (IsOptimizationStationary X (ValueOn Y (rotatedF U V F)) ell eps) K := by
  obtain ⟨U, V, hU, hV, hfail⟩ :=
    finite_horizon_tagged_OS_failure_orthonormal A F gradX gradY hchain
      hKM hcapX hcapY ell eps hfailure
  refine ⟨U, V, hU, hV, ?_⟩
  simpa [QueriedIterateHittingTimeAtLeast,
    Oracle.DeterministicFOComponent.FailsWithin,
    Oracle.DeterministicFOComponent.HitsAt, productRotatedInstance] using hfail

/-- Concrete domain form used by the paper: unconstrained ambient primal
space and the Euclidean dual ball of diameter `D`. -/
theorem finite_horizon_tagged_OS_failure_univ_ball
    {T n DX DY K : Nat} (D : ℝ)
    (A : Oracle.DeterministicFOComponent
      (Set.univ : Set (EVec DX)) (diameterBall DY D))
    (F : UnscaledPrimal T → UnscaledDual T n → ℝ)
    (gradX : UnscaledPrimal T → UnscaledDual T n → UnscaledPrimal T)
    (gradY : UnscaledPrimal T → UnscaledDual T n → UnscaledDual T n)
    (hchain : NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf gradX gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY)
    (ell eps : ℝ)
    (hfailure : ∀ U V (q : Oracle.Query DX DY),
      q.1 ∈ (Set.univ : Set (EVec DX)) → q.2 ∈ diameterBall DY D →
      serializeUnscaled (frameProject U q.1) (frameProject V q.2)
        (⟨(T - 1) * (n + 3) - 1, by omega⟩ :
          Fin ((T - 1) * (n + 3))) = 0 →
      ¬ IsOptimizationStationary (Set.univ : Set (EVec DX))
        (ValueOn (diameterBall DY D) (rotatedF U V F)) ell eps q.1) :
    ∃ U V, IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      Oracle.DeterministicFOComponent.FailsWithin A
        (productRotatedInstance (Set.univ : Set (EVec DX))
          (diameterBall DY D) U V F gradX gradY) ell eps K := by
  exact finite_horizon_tagged_OS_failure_orthonormal A F gradX gradY
    hchain hKM hcapX hcapY ell eps hfailure

/-- Concrete specialization to the genuine serialized gradient of the
unscaled hard objective. -/
theorem finite_horizon_unscaled_packed_transcript
    {T n DX DY K : Nat} {X : Set (EVec DX)} {Y : Set (EVec DY)}
    (A : Oracle.DeterministicFOComponent X Y)
    (hn : 0 < n) (P : UnscaledParameters)
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY) :
    ∃ U V hist,
      hist = runHistory (componentBlackBox A)
        (rotatedF U V (unscaledObjective (T := T) hn P))
        (rotatedGradX U V (packedTrueGradX (T := T) hn P))
        (rotatedGradY U V (packedTrueGradY (T := T) hn P)) K ∧
      IsPartialOrthonormalFrame U ∧ IsPartialOrthonormalFrame V ∧
      TaggedFramesZeroFrom K U V ∧ TaggedFramesUnitBelow K U V ∧
      ∀ i : Fin hist.length,
        serializeUnscaled (frameProject U (hist.get i).queryX)
          (frameProject V (hist.get i).queryY)
          (⟨(T - 1) * (n + 3) - 1, by omega⟩ :
            Fin ((T - 1) * (n + 3))) = 0 := by
  exact finite_horizon_tagged_transcript A
    (unscaledObjective (T := T) hn P)
    (packedTrueGradX (T := T) hn P) (packedTrueGradY (T := T) hn P)
    (packedTrueGradient_tagged_zeroChain hn P) hKM hcapX hcapY

end

end NCCLowerBoundVerification
