import NCC.Construction.ZeroChain
import NCC.Construction.Terminal
import NCCLowerBoundVerification.Oracle.ZeroRespectingAlgorithm
import NCCLowerBoundVerification.Lower.ScaledObjective

/-!
# Exact current primal/dual serialization for the local oracle

The public primal vector is `(s_i,a_i,b_i)` stage by stage. The discovery
order is `(a_i,y_i,0,...,y_i,n-1,b_i,s_i)`. This file checks that fixed
permutation against the actual partial gradients, including the dual sign.
The old serialization parameter is always `m+1`, so there are exactly `m`
stages and `m*(n+3)` discovery coordinates.
-/

namespace NCC.Lower.Serialization

noncomputable section

-- Normalize the definitional `(m+1)-1` dimensions when applying the
-- predecessor-indexed serialization lemmas.
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open NCCLowerBoundVerification
open NCC.Construction
open Composite

abbrev Chain (m n : ℕ) := Inner.Vec (m * (n + 3))

abbrev decodePrimal {m n : ℕ} (q : Chain m n) : Primal m :=
  ZeroChain.toPrimal (m := m + 1) (n := n) q

abbrev decodeDual {m n : ℕ} (q : Chain m n) : Dual m n :=
  ZeroChain.toDual (m := m + 1) (n := n) q

def aIndex {m : ℕ} (n : ℕ) (i : Fin m) : Fin (m * (n + 3)) := serializedAIndex (T := m + 1) (n := n) i
def bIndex {m : ℕ} (n : ℕ) (i : Fin m) : Fin (m * (n + 3)) := serializedBIndex (T := m + 1) (n := n) i
def sIndex {m : ℕ} (n : ℕ) (i : Fin m) : Fin (m * (n + 3)) := serializedStateIndex (T := m + 1) (n := n) i
def yIndex {m n : ℕ} (i : Fin m) (k : Fin n) : Fin (m * (n + 3)) := serializedDualIndex (T := m + 1) i k

@[simp] theorem decodeDual_block {m n : ℕ} (q : Chain m n) (i : Fin m) (k : Fin n) :
    decodeDual q (finProdFinEquiv (i, k)) = q (yIndex i k) := by
  exact ZeroChain.toDual_block (m := m + 1) q i k

theorem aIndex_prod {m : ℕ} (n : ℕ) (i : Fin m) :
    aIndex n i = finProdFinEquiv (i, (⟨0, by omega⟩ : Fin (n + 3))) := by
  apply Fin.ext
  simp [aIndex, serializedAIndex, finProdFinEquiv, Nat.mul_comm]

theorem bIndex_prod {m : ℕ} (n : ℕ) (i : Fin m) :
    bIndex n i = finProdFinEquiv (i, (⟨n + 1, by omega⟩ : Fin (n + 3))) := by
  apply Fin.ext
  simp [bIndex, serializedBIndex, finProdFinEquiv, Nat.mul_comm]
  omega

theorem sIndex_prod {m : ℕ} (n : ℕ) (i : Fin m) :
    sIndex n i = finProdFinEquiv (i, (⟨n + 2, by omega⟩ : Fin (n + 3))) := by
  apply Fin.ext
  simp [sIndex, serializedStateIndex, finProdFinEquiv, Nat.mul_comm]
  omega

theorem yIndex_prod {m n : ℕ} (i : Fin m) (k : Fin n) :
    yIndex i k = finProdFinEquiv (i, (⟨k.val + 1, by omega⟩ : Fin (n + 3))) := by
  apply Fin.ext
  simp [yIndex, serializedDualIndex, finProdFinEquiv, Nat.mul_comm]
  omega

theorem index_cases {m n : ℕ} (j : Fin (m * (n + 3))) :
    (∃ i, j = aIndex n i) ∨ (∃ i k, j = yIndex i k) ∨
      (∃ i, j = bIndex n i) ∨ (∃ i, j = sIndex n i) := by
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  by_cases ha : k.val = 0
  · left
    exact ⟨i, by rw [aIndex_prod]; congr 1; exact Prod.ext rfl (Fin.ext ha)⟩
  right
  by_cases hy : k.val ≤ n
  · left
    refine ⟨i, ⟨k.val - 1, by omega⟩, ?_⟩
    rw [yIndex_prod]
    congr 1
    exact Prod.ext rfl (Fin.ext (by dsimp; omega))
  right
  by_cases hb : k.val = n + 1
  · left
    exact ⟨i, by rw [bIndex_prod]; congr 1; exact Prod.ext rfl (Fin.ext hb)⟩
  right
  refine ⟨i, ?_⟩
  rw [sIndex_prod]
  congr 1
  exact Prod.ext rfl (Fin.ext (by dsimp; omega))

def serialize {m n : ℕ} (x : Primal m) (y : Dual m n) : Chain m n := fun j =>
  let ik := finProdFinEquiv.symm j
  if ha : ik.2.val = 0 then entrance x ik.1
  else if hy : ik.2.val ≤ n then y (finProdFinEquiv (ik.1, ⟨ik.2.val - 1, by omega⟩))
  else if hb : ik.2.val = n + 1 then exit x ik.1 else state x ik.1

@[simp] theorem serialize_a {m n : ℕ} (x : Primal m) (y : Dual m n) (i : Fin m) :
    serialize x y (aIndex n i) = entrance x i := by rw [aIndex_prod]; simp [serialize]

@[simp] theorem serialize_b {m n : ℕ} (x : Primal m) (y : Dual m n) (i : Fin m) :
    serialize x y (bIndex n i) = exit x i := by rw [bIndex_prod]; simp [serialize]

@[simp] theorem serialize_s {m n : ℕ} (x : Primal m) (y : Dual m n) (i : Fin m) :
    serialize x y (sIndex n i) = state x i := by rw [sIndex_prod]; simp [serialize]

@[simp] theorem serialize_y {m n : ℕ} (x : Primal m) (y : Dual m n) (i : Fin m) (k : Fin n) :
    serialize x y (yIndex i k) = y (finProdFinEquiv (i, k)) := by
  rw [yIndex_prod]
  simp [serialize]

@[simp] theorem toPrimal_serialize {m n : ℕ} (x : Primal m) (y : Dual m n) :
    decodePrimal (serialize x y) = x := by
  have hs : serializedState (T := m + 1) (n := n) (serialize x y) = state x := by
    funext i
    exact serialize_s x y i
  have ha : serializedA (T := m + 1) (n := n) (serialize x y) = entrance x := by
    funext i
    exact serialize_a x y i
  have hb : serializedB (T := m + 1) (n := n) (serialize x y) = exit x := by
    funext i
    exact serialize_b x y i
  rw [decodePrimal, ZeroChain.toPrimal, hs, ha, hb, Frontier.primal_reconstruct]

@[simp] theorem toDual_serialize {m n : ℕ} (x : Primal m) (y : Dual m n) :
    decodeDual (serialize x y) = y := by
  funext j
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [decodeDual_block]
  exact serialize_y x y i k

@[simp] theorem serialize_parts {m n : ℕ} (q : Chain m n) :
    serialize (decodePrimal q) (decodeDual q) = q := by
  funext j
  rcases index_cases j with ⟨i, rfl⟩ | ⟨i, k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [serialize_a, ZeroChain.entrance_toPrimal]
    rfl
  · rw [serialize_y, decodeDual_block]
  · rw [serialize_b, ZeroChain.exit_toPrimal]
    rfl
  · rw [serialize_s, ZeroChain.state_toPrimal]
    rfl

theorem toPrimal_basis_a {m n : ℕ} (i : Fin m) :
    decodePrimal (NCPLVerification.evecBasis (aIndex n i)) =
      primal 0 (Pi.single i 1) 0 := by
  unfold decodePrimal ZeroChain.toPrimal
  congr 1
  · funext r
    simp [serializedState, aIndex, NCPLVerification.evecBasis,
      (serializedAIndex_ne_stateIndex (T := m + 1) (n := n) i r).symm]
  · funext r
    simp [serializedA, aIndex, NCPLVerification.evecBasis, Pi.single_apply,
      serializedAIndex_eq_iff (T := m + 1) (n := n)]
  · funext r
    simp [serializedB, aIndex, NCPLVerification.evecBasis,
      (serializedAIndex_ne_BIndex (T := m + 1) (n := n) i r).symm]

theorem toPrimal_basis_b {m n : ℕ} (i : Fin m) :
    decodePrimal (NCPLVerification.evecBasis (bIndex n i)) =
      primal 0 0 (Pi.single i 1) := by
  unfold decodePrimal ZeroChain.toPrimal
  congr 1
  · funext r
    simp [serializedState, bIndex, NCPLVerification.evecBasis,
      (serializedBIndex_ne_stateIndex (T := m + 1) (n := n) i r).symm]
  · funext r
    simp [serializedA, bIndex, NCPLVerification.evecBasis, serializedAIndex_ne_BIndex (T := m + 1) (n := n) r i]
  · funext r
    simp [serializedB, bIndex, NCPLVerification.evecBasis, Pi.single_apply,
      (serializedBIndex_injective (T := m + 1) (n := n)).eq_iff]

theorem toPrimal_basis_s {m n : ℕ} (i : Fin m) :
    decodePrimal (NCPLVerification.evecBasis (sIndex n i)) = stateDirection i := by
  unfold decodePrimal ZeroChain.toPrimal stateDirection
  congr 1
  · funext r
    simp [serializedState, sIndex, NCPLVerification.evecBasis, Pi.single_apply,
      (serializedStateIndex_injective (T := m + 1) (n := n)).eq_iff]
  · funext r
    simp [serializedA, sIndex, NCPLVerification.evecBasis, serializedAIndex_ne_stateIndex (T := m + 1) (n := n) r i]
  · funext r
    simp [serializedB, sIndex, NCPLVerification.evecBasis, serializedBIndex_ne_stateIndex (T := m + 1) (n := n) r i]

theorem toPrimal_basis_y {m n : ℕ} (i : Fin m) (k : Fin n) :
    decodePrimal (NCPLVerification.evecBasis (yIndex i k)) = 0 := by
  change primal _ _ _ = 0
  have hs : serializedState (T := m + 1) (n := n) (NCPLVerification.evecBasis (yIndex i k)) = 0 := by
    funext r
    simp [serializedState, yIndex, NCPLVerification.evecBasis, serializedStateIndex_ne_dualIndex (T := m + 1) (n := n) r i k]
  have ha : serializedA (T := m + 1) (n := n) (NCPLVerification.evecBasis (yIndex i k)) = 0 := by
    funext r
    simp [serializedA, yIndex, NCPLVerification.evecBasis, serializedAIndex_ne_dualIndex (T := m + 1) (n := n) r i k]
  have hb : serializedB (T := m + 1) (n := n) (NCPLVerification.evecBasis (yIndex i k)) = 0 := by
    funext r
    simp [serializedB, yIndex, NCPLVerification.evecBasis, serializedBIndex_ne_dualIndex (T := m + 1) (n := n) r i k]
  rw [hs, ha, hb]
  funext j
  simp [primal]

theorem toDual_basis_a {m n : ℕ} (i : Fin m) :
    decodeDual (NCPLVerification.evecBasis (aIndex n i)) = 0 := by
  funext j
  obtain ⟨⟨r, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [decodeDual_block]
  simp [aIndex, yIndex, NCPLVerification.evecBasis, (serializedAIndex_ne_dualIndex (T := m + 1) (n := n) i r k).symm]

theorem toDual_basis_b {m n : ℕ} (i : Fin m) :
    decodeDual (NCPLVerification.evecBasis (bIndex n i)) = 0 := by
  funext j
  obtain ⟨⟨r, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [decodeDual_block]
  simp [bIndex, yIndex, NCPLVerification.evecBasis, (serializedBIndex_ne_dualIndex (T := m + 1) (n := n) i r k).symm]

theorem toDual_basis_s {m n : ℕ} (i : Fin m) :
    decodeDual (NCPLVerification.evecBasis (sIndex n i)) = 0 := by
  funext j
  obtain ⟨⟨r, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [decodeDual_block]
  simp [sIndex, yIndex, NCPLVerification.evecBasis, (serializedStateIndex_ne_dualIndex (T := m + 1) (n := n) i r k).symm]

theorem toDual_basis_y {m n : ℕ} (i : Fin m) (k : Fin n) :
    decodeDual (NCPLVerification.evecBasis (yIndex i k)) =
      NCPLVerification.evecBasis (finProdFinEquiv (i, k)) := by
  funext j
  obtain ⟨⟨r, u⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [decodeDual_block]
  simp [yIndex, NCPLVerification.evecBasis, Prod.ext_iff,
    serializedDualIndex_eq_iff (T := m + 1) (n := n)]

theorem gradient_pairing {m n : ℕ} (hn : 0 < n) (q d : Chain m n) :
    (∑ j, ZeroChain.coordinateGradient (m := m + 1) hn q j * d j) =
      (∑ i, Regularity.gradientX hn (decodePrimal q) (decodeDual q) i * decodePrimal d i) +
      ∑ k, Regularity.gradientY hn (decodePrimal q) (decodeDual q) k * decodeDual d k := by
  exact ZeroChain.coordinateGradient_pairing (m := m + 1) hn q d

theorem coordinateGradient_a {m n : ℕ} (hn : 0 < n) (q : Chain m n) (i : Fin m) :
    ZeroChain.coordinateGradient (m := m + 1) hn q (aIndex n i) =
      entrance (Regularity.gradientX hn (decodePrimal q) (decodeDual q)) i := by
  have h := gradient_pairing hn q (NCPLVerification.evecBasis (aIndex n i))
  rw [toPrimal_basis_a, toDual_basis_a,
    show primal 0 (Pi.single i 1) 0 = NCPLVerification.evecBasis
      (finProdFinEquiv (i, ⟨1, by omega⟩)) from Terminal.entranceDirection_eq_basis i] at h
  simpa [NCPLVerification.evecBasis, entrance] using h

theorem coordinateGradient_b {m n : ℕ} (hn : 0 < n) (q : Chain m n) (i : Fin m) :
    ZeroChain.coordinateGradient (m := m + 1) hn q (bIndex n i) =
      exit (Regularity.gradientX hn (decodePrimal q) (decodeDual q)) i := by
  have h := gradient_pairing hn q (NCPLVerification.evecBasis (bIndex n i))
  rw [toPrimal_basis_b, toDual_basis_b,
    show primal 0 0 (Pi.single i 1) = NCPLVerification.evecBasis
      (finProdFinEquiv (i, ⟨2, by omega⟩)) from Terminal.exitDirection_eq_basis i] at h
  simpa [NCPLVerification.evecBasis, exit] using h

theorem coordinateGradient_s {m n : ℕ} (hn : 0 < n) (q : Chain m n) (i : Fin m) :
    ZeroChain.coordinateGradient (m := m + 1) hn q (sIndex n i) =
      state (Regularity.gradientX hn (decodePrimal q) (decodeDual q)) i := by
  have h := gradient_pairing hn q (NCPLVerification.evecBasis (sIndex n i))
  rw [toPrimal_basis_s, toDual_basis_s, Frontier.stateDirection_eq_basis] at h
  simpa [NCPLVerification.evecBasis, state] using h

theorem coordinateGradient_y {m n : ℕ} (hn : 0 < n) (q : Chain m n) (i : Fin m) (k : Fin n) :
    ZeroChain.coordinateGradient (m := m + 1) hn q (yIndex i k) =
      Regularity.gradientY hn (decodePrimal q) (decodeDual q) (finProdFinEquiv (i, k)) := by
  have h := gradient_pairing hn q (NCPLVerification.evecBasis (yIndex i k))
  rw [toPrimal_basis_y, toDual_basis_y] at h
  simpa [NCPLVerification.evecBasis] using h

/-- The unsigned actual gradient has precisely the same support guarantee
as the signed saddle field. This is proved from the current coordinate
derivative correspondence at zero, not assumed as a discovery certificate. -/
theorem coordinateGradient_zeroChain {m n : ℕ} (hn : 0 < n) :
    NCPLVerification.IsFirstOrderZeroChain (ZeroChain.coordinateGradient (m := m + 1) hn) := by
  intro r q hz j hj
  rw [ZeroChain.coordinateGradient_eq_old_at_zero (m := m + 1) hn q j (hz j (by omega))]
  rcases index_cases j with ⟨i, rfl⟩ | ⟨i, k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · exact NCCLowerBound.Simplified.CompositeZeroChain.coordinateGradient_A_one_step (M := m + 1) hn Outer.c_R q hz i hj
  · exact NCCLowerBound.Simplified.CompositeZeroChain.coordinateGradient_Y_one_step (M := m + 1) hn Outer.c_R q hz i k hj
  · exact NCCLowerBound.Simplified.CompositeZeroChain.coordinateGradient_B_one_step (M := m + 1) hn Outer.c_R q hz i hj
  · exact NCCLowerBound.Simplified.CompositeZeroChain.coordinateGradient_state_one_step (M := m + 1) hn Outer.c_R q hz i hj

/-- The serialized actual local saddle oracle, in the checked permutation. -/
def field {m n : ℕ} (hn : 0 < n) (q : Chain m n) : Chain m n :=
  serialize (Regularity.gradientX hn (decodePrimal q) (decodeDual q))
    (-Regularity.gradientY hn (decodePrimal q) (decodeDual q))

theorem field_zeroChain {m n : ℕ} (hn : 0 < n) :
    NCPLVerification.IsFirstOrderZeroChain (field (m := m) hn) := by
  intro r q hz j hj
  have h := coordinateGradient_zeroChain hn r q hz j hj
  unfold field
  rcases index_cases j with ⟨i, rfl⟩ | ⟨i, k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩
  · rw [serialize_a]
    exact (coordinateGradient_a hn q i).symm.trans h
  · rw [serialize_y, Pi.neg_apply, ← coordinateGradient_y hn q i k, h, neg_zero]
  · rw [serialize_b]
    exact (coordinateGradient_b hn q i).symm.trans h
  · rw [serialize_s]
    exact (coordinateGradient_s hn q i).symm.trans h

def fieldOf {m n : ℕ}
    (gx : Primal m → Dual m n → Primal m) (gy : Primal m → Dual m n → Dual m n)
    (q : Chain m n) : Chain m n :=
  serialize (gx (decodePrimal q) (decodeDual q))
    (-gy (decodePrimal q) (decodeDual q))

theorem serialize_scaleCoords {m n : ℕ} (c : ℝ) (x : Primal m) (y : Dual m n) :
    serialize (scaleCoords c x) (scaleCoords c y) = scaleCoords c (serialize x y) := by
  funext j
  rcases index_cases j with ⟨i, rfl⟩ | ⟨i, k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
    simp [scaleCoords, entrance, exit, state]

theorem toPrimal_unscaleCoords {m n : ℕ} (lambda : ℝ) (q : Chain m n) :
    decodePrimal (unscaleCoords lambda q) = unscaleCoords lambda (decodePrimal q) := by
  funext j
  unfold decodePrimal ZeroChain.toPrimal primal unscaleCoords serializedState serializedA serializedB
  dsimp
  split_ifs <;> rfl

theorem toDual_unscaleCoords {m n : ℕ} (lambda : ℝ) (q : Chain m n) :
    decodeDual (unscaleCoords lambda q) = unscaleCoords lambda (decodeDual q) := by
  funext j
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  simp only [unscaleCoords, decodeDual_block]

theorem fieldOf_scaled {m n : ℕ} (lambda amp : ℝ)
    (gx : Primal m → Dual m n → Primal m) (gy : Primal m → Dual m n → Dual m n) :
    fieldOf (scaledGradX lambda amp gx) (scaledGradY lambda amp gy) =
      scaledVectorField lambda amp (fieldOf gx gy) := by
  funext q
  unfold fieldOf scaledGradX scaledGradY scaledVectorField
  dsimp only
  rw [toPrimal_unscaleCoords, toDual_unscaleCoords]
  have hneg (y : Dual m n) : -scaleCoords (amp / lambda) y = scaleCoords (amp / lambda) (-y) := by
    funext j
    simp [scaleCoords]
  rw [hneg, serialize_scaleCoords]

theorem scaled_field_zeroChain {m n : ℕ} (hn : 0 < n) (lambda amp : ℝ) :
    NCPLVerification.IsFirstOrderZeroChain
      (fieldOf (scaledGradX lambda amp (Regularity.gradientX (m := m) hn))
        (scaledGradY lambda amp (Regularity.gradientY hn))) := by
  rw [fieldOf_scaled]
  exact scaledVectorField_isFirstOrderZeroChain (field_zeroChain hn)

/-- Position of a serialized coordinate in the oracle's standard
primal-then-dual list. No objective-dependent permutation is used. -/
def standardIndex {m n : ℕ} (j : Fin (m * (n + 3))) : Fin (m * 3 + m * n) :=
  let ik := finProdFinEquiv.symm j
  if ha : ik.2.val = 0 then Fin.castAdd (m * n) (finProdFinEquiv (ik.1, (⟨1, by omega⟩ : Fin 3)))
  else if hy : ik.2.val ≤ n then
    Fin.natAdd (m * 3) (finProdFinEquiv (ik.1, (⟨ik.2.val - 1, by omega⟩ : Fin n)))
  else if ik.2.val = n + 1 then Fin.castAdd (m * n) (finProdFinEquiv (ik.1, (⟨2, by omega⟩ : Fin 3)))
  else Fin.castAdd (m * n) (finProdFinEquiv (ik.1, (⟨0, by omega⟩ : Fin 3)))

theorem serialize_eq_standard {m n : ℕ} (x : Primal m) (y : Dual m n)
    (j : Fin (m * (n + 3))) :
    serialize x y j = Oracle.standardJointVector x y (standardIndex j) := by
  unfold serialize standardIndex
  dsimp
  split
  · simp [Oracle.standardJointVector, entrance]
  · split
    · simp [Oracle.standardJointVector]
    · split
      · simp [Oracle.standardJointVector, exit]
      · simp [Oracle.standardJointVector, state]

/-- Pull back the exact oracle-model zero-respecting predicate through the
fixed current serialization. Values remain in the histories; only support
of the actually returned gradient coordinates is used. -/
theorem queried_zeroRespecting {m n : ℕ} {X : Set (Primal m)} {Y : Set (Dual m n)}
    (A : Oracle.DeterministicFOComponent X Y) (P : NCCInstance (m * 3) (m * n))
    (hzero : A.IsZeroRespectingOn P) :
    NCPLVerification.QueriesAreZeroRespecting (fieldOf P.gradX P.gradY)
      (fun t => serialize (A.queriedAt P t).1 (A.queriedAt P t).2) := by
  intro t j hj
  have hq : Oracle.standardJointQuery (A.queriedAt P t) (standardIndex j) ≠ 0 := by
    simpa only [Oracle.standardJointQuery, ← serialize_eq_standard] using hj
  obtain ⟨s, hst, hs⟩ := hzero t (standardIndex j) hq
  refine ⟨s, hst, ?_⟩
  rw [Oracle.standardSaddleField_standardJointQuery] at hs
  simpa only [fieldOf, toPrimal_serialize, toDual_serialize, serialize_eq_standard] using hs

end

end NCC.Lower.Serialization
