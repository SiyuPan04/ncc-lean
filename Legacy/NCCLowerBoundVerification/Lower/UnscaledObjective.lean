import NCCLowerBoundVerification.Lower.InnerChain
import NCCLowerBoundVerification.Lower.ComponentInterfaces
import NCCLowerBoundVerification.Lower.WallMargin
import NCCLowerBoundVerification.Lower.RadialBudget
import NCCLowerBoundVerification.Lower.GreenMatrix
import NCCLowerBoundVerification.Oracle.ZeroChain
import NCPLVerification.InnerDifferentiability

/-!
# The assembled unscaled lower-bound objective

The coordinates are flattened exactly as in `eq:chain-order`.  A primal
vector has `3 * (T - 1)` entries `(a_i,b_i,s_{i+1})`; a dual vector has
`n * (T - 1)` entries.  The serialized joint vector orders every block as
`(a_i,y¹_i,…,yⁿ_i,b_i,s_{i+1})`.
-/

namespace NCCLowerBoundVerification

noncomputable section

open Set

structure UnscaledParameters where
  theta : ℝ
  delta : ℝ
  P0 : ℝ
  tauS : ℝ
  alpha : ℝ
  beta : ℝ
  gamma : ℝ
  mu : ℝ
  eta : ℝ
  P1 : ℝ
  K : ℝ
  theta_pos : 0 < theta
  delta_pos : 0 < delta
  P0_gt_one : 1 < P0
  tauS_pos : 0 < tauS

abbrev UnscaledPrimal (T : Nat) := EVec (3 * (T - 1))
abbrev UnscaledDual (T n : Nat) := EVec (n * (T - 1))
abbrev SerializedSpace (T n : Nat) := EVec ((T - 1) * (n + 3))

def primalAIndex {T : Nat} (i : Fin (T - 1)) : Fin (3 * (T - 1)) :=
  ⟨3 * i.val, by omega⟩

def primalBIndex {T : Nat} (i : Fin (T - 1)) : Fin (3 * (T - 1)) :=
  ⟨3 * i.val + 1, by omega⟩

def primalStateIndex {T : Nat} (i : Fin (T - 1)) : Fin (3 * (T - 1)) :=
  ⟨3 * i.val + 2, by omega⟩

def dualBlockIndex {T n : Nat} (i : Fin (T - 1)) (k : Fin n) :
    Fin (n * (T - 1)) :=
  ⟨n * i.val + k.val, by
    have hstep : n * i.val + k.val < n * i.val + n :=
      Nat.add_lt_add_left k.isLt _
    have hle : n * (i.val + 1) ≤ n * (T - 1) :=
      Nat.mul_le_mul_left n (Nat.succ_le_iff.mpr i.isLt)
    rw [Nat.mul_succ] at hle
    omega⟩

def serializedAIndex {T n : Nat} (i : Fin (T - 1)) :
    Fin ((T - 1) * (n + 3)) :=
  ⟨i.val * (n + 3), by
    have hn : 0 < n + 3 := by omega
    nlinarith [i.isLt]⟩

def serializedDualIndex {T n : Nat} (i : Fin (T - 1)) (k : Fin n) :
    Fin ((T - 1) * (n + 3)) :=
  ⟨i.val * (n + 3) + 1 + k.val, by
    have hi : i.val + 1 ≤ T - 1 := Nat.succ_le_iff.mpr i.isLt
    have hlocal : 1 + k.val < n + 3 := by omega
    calc
      i.val * (n + 3) + 1 + k.val < i.val * (n + 3) + (n + 3) := by omega
      _ = (i.val + 1) * (n + 3) := by ring
      _ ≤ (T - 1) * (n + 3) := Nat.mul_le_mul_right _ hi⟩

def serializedBIndex {T n : Nat} (i : Fin (T - 1)) :
    Fin ((T - 1) * (n + 3)) :=
  ⟨i.val * (n + 3) + n + 1, by
    have hi : i.val + 1 ≤ T - 1 := Nat.succ_le_iff.mpr i.isLt
    calc
      i.val * (n + 3) + n + 1 < i.val * (n + 3) + (n + 3) := by omega
      _ = (i.val + 1) * (n + 3) := by ring
      _ ≤ (T - 1) * (n + 3) := Nat.mul_le_mul_right _ hi⟩

def serializedStateIndex {T n : Nat} (i : Fin (T - 1)) :
    Fin ((T - 1) * (n + 3)) :=
  ⟨i.val * (n + 3) + n + 2, by
    have hi : i.val + 1 ≤ T - 1 := Nat.succ_le_iff.mpr i.isLt
    calc
      i.val * (n + 3) + n + 2 < i.val * (n + 3) + (n + 3) := by omega
      _ = (i.val + 1) * (n + 3) := by ring
      _ ≤ (T - 1) * (n + 3) := Nat.mul_le_mul_right _ hi⟩

theorem serializedAIndex_injective {T n : Nat} :
    Function.Injective (serializedAIndex (T := T) (n := n)) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  change i.val * (n + 3) = j.val * (n + 3) at hv
  exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < n + 3) hv

@[simp] theorem serializedAIndex_eq_iff {T n : Nat} (i j : Fin (T - 1)) :
    serializedAIndex (n := n) i = serializedAIndex (n := n) j ↔ i = j :=
  (serializedAIndex_injective.eq_iff)

theorem serializedAIndex_ne_dualIndex {T n : Nat}
    (i j : Fin (T - 1)) (k : Fin n) :
    serializedAIndex (n := n) i ≠ serializedDualIndex j k := by
  intro h
  have hv := congrArg Fin.val h
  change i.val * (n + 3) = j.val * (n + 3) + 1 + k.val at hv
  have hjlt : j.val < i.val := by
    by_contra hji
    have : i.val ≤ j.val := by omega
    have := Nat.mul_le_mul_right (n + 3) this
    omega
  have hilt : i.val < j.val + 1 := by
    by_contra hij
    have : j.val + 1 ≤ i.val := by omega
    have hm := Nat.mul_le_mul_right (n + 3) this
    have hstep : (j.val + 1) * (n + 3) = j.val * (n + 3) + (n + 3) := by ring
    rw [hstep] at hm
    omega
  omega

theorem serializedAIndex_ne_BIndex {T n : Nat} (i j : Fin (T - 1)) :
    serializedAIndex (n := n) i ≠ serializedBIndex (n := n) j := by
  intro h
  have hv := congrArg Fin.val h
  change i.val * (n + 3) = j.val * (n + 3) + n + 1 at hv
  have hjlt : j.val < i.val := by
    by_contra hji
    have hm := Nat.mul_le_mul_right (n + 3) (show i.val ≤ j.val by omega)
    omega
  have hilt : i.val < j.val + 1 := by
    by_contra hij
    have hm := Nat.mul_le_mul_right (n + 3) (show j.val + 1 ≤ i.val by omega)
    have hstep : (j.val + 1) * (n + 3) = j.val * (n + 3) + (n + 3) := by ring
    rw [hstep] at hm
    omega
  omega

theorem serializedAIndex_ne_stateIndex {T n : Nat} (i j : Fin (T - 1)) :
    serializedAIndex (n := n) i ≠ serializedStateIndex (n := n) j := by
  intro h
  have hv := congrArg Fin.val h
  change i.val * (n + 3) = j.val * (n + 3) + n + 2 at hv
  have hjlt : j.val < i.val := by
    by_contra hji
    have hm := Nat.mul_le_mul_right (n + 3) (show i.val ≤ j.val by omega)
    omega
  have hilt : i.val < j.val + 1 := by
    by_contra hij
    have hm := Nat.mul_le_mul_right (n + 3) (show j.val + 1 ≤ i.val by omega)
    have hstep : (j.val + 1) * (n + 3) = j.val * (n + 3) + (n + 3) := by ring
    rw [hstep] at hm
    omega
  omega

private theorem blockOffset_eq {m i j u v : Nat} (_hm : 0 < m)
    (hu : u < m) (hv : v < m) (h : i * m + u = j * m + v) :
    i = j ∧ u = v := by
  have hij : i = j := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hij | hji
    · have hleft : i * m + u < (i + 1) * m := by
        rw [Nat.add_mul]
        omega
      have hright : (i + 1) * m ≤ j * m :=
        Nat.mul_le_mul_right m (by omega)
      omega
    · have hleft : j * m + v < (j + 1) * m := by
        rw [Nat.add_mul]
        omega
      have hright : (j + 1) * m ≤ i * m :=
        Nat.mul_le_mul_right m (by omega)
      omega
  subst j
  exact ⟨rfl, by omega⟩

theorem serializedBIndex_injective {T n : Nat} :
    Function.Injective (serializedBIndex (T := T) (n := n)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  have hb := blockOffset_eq (m := n + 3) (i := i.val) (j := j.val)
    (u := n + 1) (v := n + 1) (by omega) (by omega) (by omega) hv
  exact hb.1

theorem serializedBIndex_ne_dualIndex {T n : Nat}
    (i j : Fin (T - 1)) (k : Fin n) :
    serializedBIndex (n := n) i ≠ serializedDualIndex j k := by
  intro h
  have hv := congrArg Fin.val h
  have hb := blockOffset_eq (m := n + 3) (i := i.val) (j := j.val)
    (u := n + 1) (v := 1 + k.val) (by omega) (by omega) (by omega) (by
      simpa [serializedBIndex, serializedDualIndex, Nat.add_assoc] using hv)
  omega

theorem serializedBIndex_ne_stateIndex {T n : Nat} (i j : Fin (T - 1)) :
    serializedBIndex (n := n) i ≠ serializedStateIndex (n := n) j := by
  intro h
  have hv := congrArg Fin.val h
  have hb := blockOffset_eq (m := n + 3) (i := i.val) (j := j.val)
    (u := n + 1) (v := n + 2) (by omega) (by omega) (by omega) (by
      simpa [serializedBIndex, serializedStateIndex, Nat.add_assoc] using hv)
  omega

theorem serializedDualIndex_injective {T n : Nat} :
    Function.Injective (fun p : Fin (T - 1) × Fin n ↦
      serializedDualIndex p.1 p.2) := by
  intro p r h
  rcases p with ⟨i, k⟩
  rcases r with ⟨j, u⟩
  have hv := congrArg Fin.val h
  have hb := blockOffset_eq (m := n + 3) (i := i.val) (j := j.val)
    (u := 1 + k.val) (v := 1 + u.val) (by omega) (by omega) (by omega) (by
      simpa [serializedDualIndex, Nat.add_assoc] using hv)
  apply Prod.ext
  · apply Fin.ext
    exact hb.1
  · apply Fin.ext
    exact Nat.add_left_cancel hb.2

@[simp] theorem serializedDualIndex_eq_iff {T n : Nat}
    (i j : Fin (T - 1)) (k u : Fin n) :
    serializedDualIndex i k = serializedDualIndex j u ↔ i = j ∧ k = u := by
  constructor
  · intro h
    have hp : (i, k) = (j, u) := serializedDualIndex_injective h
    exact ⟨congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem serializedStateIndex_ne_dualIndex {T n : Nat}
    (i j : Fin (T - 1)) (k : Fin n) :
    serializedStateIndex (n := n) i ≠ serializedDualIndex j k := by
  intro h
  have hv := congrArg Fin.val h
  have hb := blockOffset_eq (m := n + 3) (i := i.val) (j := j.val)
    (u := n + 2) (v := 1 + k.val) (by omega) (by omega) (by omega) (by
      simpa [serializedStateIndex, serializedDualIndex, Nat.add_assoc] using hv)
  omega

theorem serializedStateIndex_injective {T n : Nat} :
    Function.Injective (serializedStateIndex (T := T) (n := n)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  exact (blockOffset_eq (m := n + 3) (i := i.val) (j := j.val)
    (u := n + 2) (v := n + 2) (by omega) (by omega) (by omega) (by
      simpa [serializedStateIndex, Nat.add_assoc] using hv)).1

def primalA {T : Nat} (x : UnscaledPrimal T) (i : Fin (T - 1)) : ℝ :=
  x (primalAIndex i)

def primalB {T : Nat} (x : UnscaledPrimal T) (i : Fin (T - 1)) : ℝ :=
  x (primalBIndex i)

def primalState {T : Nat} (x : UnscaledPrimal T) (i : Fin (T - 1)) : ℝ :=
  x (primalStateIndex i)

def dualBlock {T n : Nat} (y : UnscaledDual T n)
    (i : Fin (T - 1)) : EVec n :=
  fun k ↦ y (dualBlockIndex i k)

/-- `s_i` in zero-based block `i`; the paper fixes `s₁ = 2`. -/
def currentState {T : Nat} (x : UnscaledPrimal T) (i : Fin (T - 1)) : ℝ :=
  if h : i.val = 0 then 2
  else primalState x ⟨i.val - 1, by omega⟩

def clippedCurrent {T : Nat} (P : UnscaledParameters)
    (x : UnscaledPrimal T) (i : Fin (T - 1)) : ℝ :=
  pi1 P.delta P.P0 (currentState x i)

def clippedNext {T : Nat} (P : UnscaledParameters)
    (x : UnscaledPrimal T) (i : Fin (T - 1)) : ℝ :=
  pi1 P.delta P.P0 (primalState x i)

def pulseSq {T : Nat} (x : UnscaledPrimal T) : ℝ :=
  Finset.univ.sum fun i : Fin (T - 1) ↦
    (primalA x i) ^ 2 + (primalB x i) ^ 2

def unscaledBlock {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (x : UnscaledPrimal T) (y : UnscaledDual T n) (i : Fin (T - 1)) : ℝ :=
  entrancePulse P.alpha P.theta P.P0 (clippedCurrent P x i)
      (clippedNext P x i) (primalA x i) +
    innerChain hn (innerC hn) (primalA x i) (primalB x i) (dualBlock y i) +
    innerC1 hn * (primalA x i) ^ 2 + innerC2 hn * (primalB x i) ^ 2 +
    P.gamma * ((primalA x i) ^ 2 + (primalB x i) ^ 2) +
    exitPulse P.beta P.theta (clippedCurrent P x i) (primalB x i)
      (clippedNext P x i)

/-- Definition `def:unscaled-objective`, with `s₁=2` built into
`currentState`. -/
def unscaledObjective {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (x : UnscaledPrimal T) (y : UnscaledDual T n) : ℝ :=
  -P.eta * (Finset.univ.sum fun i : Fin (T - 1) ↦
      Psi1 (clippedNext P x i)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦
      Sigma2 P.tauS (primalState x i)) +
    P.mu * (Finset.univ.sum fun i : Fin (T - 1) ↦
      Psi2 (clippedNext P x i) * Sigma1 P.theta (clippedCurrent P x i)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦ unscaledBlock hn P x y i) +
    Sigma3 P.P0 P.P1 P.K (pulseSq x)

/-! ## The paper's serialized joint coordinates -/

def serializedA {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) : ℝ := q (serializedAIndex (n := n) i)

def serializedY {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) (k : Fin n) : ℝ :=
  q (serializedDualIndex i k)

def serializedB {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) : ℝ := q (serializedBIndex (n := n) i)

def serializedState {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) : ℝ := q (serializedStateIndex (n := n) i)

def serializedDualBlock {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) : EVec n := fun k ↦ serializedY q i k

def serializedCurrentState {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) : ℝ :=
  if h : i.val = 0 then 2
  else serializedState q ⟨i.val - 1, by omega⟩

def serializedClippedCurrent {T n : Nat} (P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) : ℝ :=
  pi1 P.delta P.P0 (serializedCurrentState q i)

def serializedClippedNext {T n : Nat} (P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) : ℝ :=
  pi1 P.delta P.P0 (serializedState q i)

def serializedPulseSq {T n : Nat} (q : SerializedSpace T n) : ℝ :=
  Finset.univ.sum fun i : Fin (T - 1) ↦
    (serializedA q i) ^ 2 + (serializedB q i) ^ 2

def serializedBlock {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) : ℝ :=
  entrancePulse P.alpha P.theta P.P0 (serializedClippedCurrent P q i)
      (serializedClippedNext P q i) (serializedA q i) +
    innerChain hn (innerC hn) (serializedA q i) (serializedB q i)
      (serializedDualBlock q i) +
    innerC1 hn * (serializedA q i) ^ 2 +
    innerC2 hn * (serializedB q i) ^ 2 +
    P.gamma * ((serializedA q i) ^ 2 + (serializedB q i) ^ 2) +
    exitPulse P.beta P.theta (serializedClippedCurrent P q i)
      (serializedB q i) (serializedClippedNext P q i)

def serializedObjective {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (q : SerializedSpace T n) : ℝ :=
  -P.eta * (Finset.univ.sum fun i : Fin (T - 1) ↦
      Psi1 (serializedClippedNext P q i)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦
      Sigma2 P.tauS (serializedState q i)) +
    P.mu * (Finset.univ.sum fun i : Fin (T - 1) ↦
      Psi2 (serializedClippedNext P q i) *
        Sigma1 P.theta (serializedClippedCurrent P q i)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦ serializedBlock hn P q i) +
    Sigma3 P.P0 P.P1 P.K (serializedPulseSq q)

/-- The serialized vector has exactly the paper's first and last entries. -/
theorem serializedA_first_index {T n : Nat} (hT : 1 < T) :
    (serializedAIndex (n := n) (⟨0, by omega⟩ : Fin (T - 1))).val = 0 := by
  simp [serializedAIndex]

theorem serializedState_last_index {T n : Nat} (hT : 1 < T) :
    (serializedStateIndex (n := n)
      (⟨T - 2, by omega⟩ : Fin (T - 1))).val =
        (T - 1) * (n + 3) - 1 := by
  have hcount : T - 1 = (T - 2) + 1 := by omega
  change (T - 2) * (n + 3) + n + 2 = (T - 1) * (n + 3) - 1
  rw [hcount]
  rw [Nat.add_mul]
  omega

/-! ## Concrete coordinate saddle field -/

def serializedGradA {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) : ℝ :=
  entrancePulseDerivA P.alpha P.theta P.P0
      (serializedClippedCurrent P q i) (serializedClippedNext P q i)
      (serializedA q i) +
    innerGradA hn (innerC hn) (serializedDualBlock q i) +
    2 * (innerC1 hn + P.gamma) * serializedA q i +
    2 * Sigma3Deriv P.P0 P.P1 P.K (serializedPulseSq q) * serializedA q i

def serializedGradB {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) : ℝ :=
  innerGradB hn (innerC hn) (serializedDualBlock q i) +
    2 * (innerC2 hn + P.gamma) * serializedB q i +
    exitPulseDerivB P.beta P.theta (serializedClippedCurrent P q i)
      (serializedB q i) (serializedClippedNext P q i) +
    2 * Sigma3Deriv P.P0 P.P1 P.K (serializedPulseSq q) * serializedB q i

/-- This is the saddle sign `-∂_y F`, already built into
`innerSaddleGradW`. -/
def serializedSaddleGradY {T n : Nat} (hn : 0 < n) (_P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) (k : Fin n) : ℝ :=
  innerSaddleGradW hn (innerC hn) (serializedA q i) (serializedB q i)
    (serializedDualBlock q i) k

def serializedNextStateContribution {T n : Nat} (P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) : ℝ :=
  if h : i.val + 1 < T - 1 then
    let j : Fin (T - 1) := ⟨i.val + 1, h⟩
    P.mu * Psi2 (serializedClippedNext P q j) *
        Sigma1Deriv P.theta (serializedClippedNext P q i) *
          pi1Deriv P.delta P.P0 (serializedState q i) -
      P.alpha * Psi2Deriv (serializedClippedNext P q i) *
        pi1Deriv P.delta P.P0 (serializedState q i) *
          Lambda2 P.theta (serializedClippedNext P q j) *
            pi2 P.P0 (serializedA q j) -
      P.beta * Psi2Deriv (serializedClippedNext P q i) *
        pi1Deriv P.delta P.P0 (serializedState q i) *
          Psi2 (serializedB q j) * exitRelay P.theta (serializedClippedNext P q j)
  else 0

def serializedGradState {T n : Nat} (P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) : ℝ :=
  let raw := serializedState q i;
  let cur := serializedClippedCurrent P q i;
  let nxt := serializedClippedNext P q i;
  let clipDeriv := pi1Deriv P.delta P.P0 raw;
  -P.eta * Psi1Deriv nxt * clipDeriv + Sigma2Deriv P.tauS raw +
    P.mu * Psi2Deriv nxt * clipDeriv * Sigma1 P.theta cur -
    P.alpha * Psi2 cur * deriv (Lambda2 P.theta) nxt * clipDeriv *
      pi2 P.P0 (serializedA q i) +
    exitPulseDerivNext P.beta P.theta cur (serializedB q i) nxt * clipDeriv +
    serializedNextStateContribution P q i

theorem serializedGradA_uses_concrete_coefficients {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedGradA hn P q i =
      entrancePulseDerivA P.alpha P.theta P.P0
          (serializedClippedCurrent P q i) (serializedClippedNext P q i)
          (serializedA q i) +
        innerGradA hn (innerC hn) (serializedDualBlock q i) +
        2 * (innerC1 hn + P.gamma) * serializedA q i +
        2 * Sigma3Deriv P.P0 P.P1 P.K (serializedPulseSq q) *
          serializedA q i := by
  rfl

def serializedSaddleField {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (q : SerializedSpace T n) : SerializedSpace T n :=
  (Finset.univ.sum fun i : Fin (T - 1) ↦
      (Pi.single (serializedAIndex (n := n) i) (serializedGradA hn P q i) :
        SerializedSpace T n)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦
      Finset.univ.sum fun k : Fin n ↦
        (Pi.single (serializedDualIndex i k) (serializedSaddleGradY hn P q i k) :
          SerializedSpace T n)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦
      (Pi.single (serializedBIndex (n := n) i) (serializedGradB hn P q i) :
        SerializedSpace T n)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦
      (Pi.single (serializedStateIndex (n := n) i) (serializedGradState P q i) :
        SerializedSpace T n))

@[simp] theorem serializedA_zero {T n : Nat} (i : Fin (T - 1)) :
    serializedA (0 : SerializedSpace T n) i = 0 := by
  simp [serializedA]

@[simp] theorem serializedB_zero {T n : Nat} (i : Fin (T - 1)) :
    serializedB (0 : SerializedSpace T n) i = 0 := by
  simp [serializedB]

@[simp] theorem serializedState_zero {T n : Nat} (i : Fin (T - 1)) :
    serializedState (0 : SerializedSpace T n) i = 0 := by
  simp [serializedState]

@[simp] theorem serializedY_zero {T n : Nat} (i : Fin (T - 1)) (k : Fin n) :
    serializedY (0 : SerializedSpace T n) i k = 0 := by
  simp [serializedY]

@[simp] theorem serializedDualBlock_zero {T n : Nat} (i : Fin (T - 1)) :
    serializedDualBlock (0 : SerializedSpace T n) i = 0 := by
  funext k
  simp [serializedDualBlock]

@[simp] theorem serializedPulseSq_zero {T n : Nat} :
    serializedPulseSq (0 : SerializedSpace T n) = 0 := by
  simp [serializedPulseSq]

theorem pi1_zero_of_parameters (P : UnscaledParameters) :
    pi1 P.delta P.P0 0 = 0 := by
  apply pi1_eq_self P.delta_pos P.P0_gt_one
  · unfold stateLower
    linarith [P.delta_pos]
  · norm_num [stateUpper]

theorem pi1Deriv_zero_of_parameters (P : UnscaledParameters) :
    pi1Deriv P.delta P.P0 0 = 1 := by
  apply pi1Deriv_eq_one P.delta_pos P.P0_gt_one
  · unfold stateLower
    linarith [P.delta_pos]
  · norm_num [stateUpper]

theorem serializedClippedCurrent_zero_of_ne_first {T n : Nat}
    (P : UnscaledParameters) (i : Fin (T - 1)) (hi : i.val ≠ 0) :
    serializedClippedCurrent P (0 : SerializedSpace T n) i = 0 := by
  simp [serializedClippedCurrent, serializedCurrentState, hi,
    pi1_zero_of_parameters]

@[simp] theorem serializedClippedNext_zero {T n : Nat}
    (P : UnscaledParameters) (i : Fin (T - 1)) :
    serializedClippedNext P (0 : SerializedSpace T n) i = 0 := by
  simp [serializedClippedNext, pi1_zero_of_parameters]

theorem serializedGradA_zero_at_origin_of_ne_first {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (i : Fin (T - 1)) (hi : i.val ≠ 0) :
    serializedGradA hn P (0 : SerializedSpace T n) i = 0 := by
  simp [serializedGradA, serializedClippedCurrent_zero_of_ne_first P i hi,
    entrancePulseDerivA, innerGradA, Psi2_zero]

@[simp] theorem serializedSaddleGradY_zero_at_origin {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (i : Fin (T - 1)) (k : Fin n) :
    serializedSaddleGradY hn P (0 : SerializedSpace T n) i k = 0 := by
  simp [serializedSaddleGradY, innerSaddleGradW, innerSource,
    regularizedPathCoord]
  unfold pathLaplacianCoord
  split <;> split <;> simp

@[simp] theorem serializedGradB_zero_at_origin {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (i : Fin (T - 1)) :
    serializedGradB hn P (0 : SerializedSpace T n) i = 0 := by
  simp [serializedGradB, innerGradB, exitPulseDerivB, Psi2Deriv_zero]

@[simp] theorem serializedNextStateContribution_zero_at_origin {T n : Nat}
    (P : UnscaledParameters) (i : Fin (T - 1)) :
    serializedNextStateContribution P (0 : SerializedSpace T n) i = 0 := by
  unfold serializedNextStateContribution
  split
  · simp [Psi2_zero, Psi2Deriv_zero]
  · rfl

@[simp] theorem serializedGradState_zero_at_origin {T n : Nat}
    (P : UnscaledParameters) (i : Fin (T - 1)) :
    serializedGradState P (0 : SerializedSpace T n) i = 0 := by
  simp [serializedGradState, pi1Deriv_zero_of_parameters,
    Sigma2Deriv_zero P.tauS_pos,
    Psi1Deriv_eq_zero_of_le_half (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Psi2Deriv_zero, Psi2_zero, pi2_zero, exitPulseDerivNext]

/-! ## Actual Fréchet gradient -/

def serializedTrueGradient {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (q : SerializedSpace T n) : SerializedSpace T n :=
  NCPLVerification.continuousLinearMapCoordinates
    (NCPLVerification.evecFderiv (serializedObjective hn P) q)

theorem serializedObjective_evecDifferentiableAt {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters) (q : SerializedSpace T n) :
    NCPLVerification.EVecDifferentiableAt (serializedObjective hn P) q := by
  letI : AddCommGroup (SerializedSpace T n) :=
    Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (SerializedSpace T n) := Pi.normedSpace.toModule
  letI : TopologicalSpace (SerializedSpace T n) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold NCPLVerification.EVecDifferentiableAt
  have hpsi1 : Differentiable ℝ Psi1 := by
    exact NCPLVerification.differentiable_carmonPsi
  have hpsi2 : Differentiable ℝ Psi2 := by
    unfold Psi2
    fun_prop
  have hpi1 : Differentiable ℝ (pi1 P.delta P.P0) :=
    (pi1_contDiff P.delta_pos P.P0_gt_one).differentiable (by simp)
  have hpi2 : Differentiable ℝ (pi2 P.P0) :=
    (pi2_contDiff P.P0_gt_one).differentiable (by simp)
  have hsigma1 : Differentiable ℝ (Sigma1 P.theta) :=
    (Sigma1_contDiff P.theta).differentiable (by simp)
  have hsigma2 : Differentiable ℝ (Sigma2 P.tauS) :=
    (Sigma2_contDiff P.tauS).differentiable (by simp)
  have hsigma3 : Differentiable ℝ (Sigma3 P.P0 P.P1 P.K) :=
    (Sigma3_contDiff P.P0 P.P1 P.K).differentiable (by simp)
  have hlambda2 : Differentiable ℝ (Lambda2 P.theta) :=
    (@Lambda2_contDiff P.theta 1).differentiable (by norm_num)
  have ha (i : Fin (T - 1)) :
      DifferentiableAt ℝ (fun z : SerializedSpace T n ↦ serializedA z i) q := by
    unfold serializedA
    fun_prop
  have hb (i : Fin (T - 1)) :
      DifferentiableAt ℝ (fun z : SerializedSpace T n ↦ serializedB z i) q := by
    unfold serializedB
    fun_prop
  have hstate (i : Fin (T - 1)) :
      DifferentiableAt ℝ (fun z : SerializedSpace T n ↦ serializedState z i) q := by
    unfold serializedState
    fun_prop
  have hy (i : Fin (T - 1)) (k : Fin n) :
      DifferentiableAt ℝ (fun z : SerializedSpace T n ↦ serializedY z i k) q := by
    unfold serializedY
    fun_prop
  have hcurrent (i : Fin (T - 1)) :
      DifferentiableAt ℝ
        (fun z : SerializedSpace T n ↦ serializedCurrentState z i) q := by
    unfold serializedCurrentState
    split
    · fun_prop
    · exact hstate _
  have hnext (i : Fin (T - 1)) :
      DifferentiableAt ℝ
        (fun z : SerializedSpace T n ↦ serializedClippedNext P z i) q := by
    unfold serializedClippedNext
    exact hpi1.differentiableAt.comp q (hstate i)
  have hcur (i : Fin (T - 1)) :
      DifferentiableAt ℝ
        (fun z : SerializedSpace T n ↦ serializedClippedCurrent P z i) q := by
    unfold serializedClippedCurrent
    exact hpi1.differentiableAt.comp q (hcurrent i)
  have hdual (i : Fin (T - 1)) :
      DifferentiableAt ℝ
        (fun z : SerializedSpace T n ↦ serializedDualBlock z i) q := by
    rw [differentiableAt_pi]
    intro k
    exact hy i k
  have hpulse : DifferentiableAt ℝ
      (fun z : SerializedSpace T n ↦ serializedPulseSq z) q := by
    unfold serializedPulseSq
    apply DifferentiableAt.fun_sum
    intro i _
    exact ((ha i).pow 2).add ((hb i).pow 2)
  have hinner (i : Fin (T - 1)) : DifferentiableAt ℝ
      (fun z : SerializedSpace T n ↦
        innerChain hn (innerC hn) (serializedA z i) (serializedB z i)
          (serializedDualBlock z i)) q := by
    unfold innerChain innerForcing regularizedPathQuad
    have hquad : DifferentiableAt ℝ
        (fun z : SerializedSpace T n ↦
          pathRegularization n * vecSq (serializedDualBlock z i) +
            pathEnergy n (serializedDualBlock z i)) q := by
      unfold vecSq NCPLVerification.vecSq
      cases n with
      | zero => omega
      | succ m =>
        unfold pathEnergy serializedDualBlock
        fun_prop
    fun_prop
  have hblock (i : Fin (T - 1)) : DifferentiableAt ℝ
      (fun z : SerializedSpace T n ↦ serializedBlock hn P z i) q := by
    unfold serializedBlock entrancePulse exitPulse exitRelay
    have hPi2 := hpi2.differentiableAt.comp q (ha i)
    have hPsiCur := hpsi2.differentiableAt.comp q (hcur i)
    have hPsiNext := hpsi2.differentiableAt.comp q (hnext i)
    have hPsiB := hpsi2.differentiableAt.comp q (hb i)
    have hLambda := hlambda2.differentiableAt.comp q (hnext i)
    fun_prop
  unfold serializedObjective
  have hmemory : DifferentiableAt ℝ
      (fun z : SerializedSpace T n ↦
        Finset.univ.sum fun i : Fin (T - 1) ↦
          Psi1 (serializedClippedNext P z i)) q := by
    apply DifferentiableAt.fun_sum
    intro i _
    exact hpsi1.differentiableAt.comp q (hnext i)
  have hwall : DifferentiableAt ℝ
      (fun z : SerializedSpace T n ↦
        Finset.univ.sum fun i : Fin (T - 1) ↦
          Sigma2 P.tauS (serializedState z i)) q := by
    apply DifferentiableAt.fun_sum
    intro i _
    exact hsigma2.differentiableAt.comp q (hstate i)
  have horder : DifferentiableAt ℝ
      (fun z : SerializedSpace T n ↦
        Finset.univ.sum fun i : Fin (T - 1) ↦
          Psi2 (serializedClippedNext P z i) *
            Sigma1 P.theta (serializedClippedCurrent P z i)) q := by
    apply DifferentiableAt.fun_sum
    intro i _
    exact (hpsi2.differentiableAt.comp q (hnext i)).mul
      (hsigma1.differentiableAt.comp q (hcur i))
  have hblocks : DifferentiableAt ℝ
      (fun z : SerializedSpace T n ↦
        Finset.univ.sum fun i : Fin (T - 1) ↦ serializedBlock hn P z i) q := by
    apply DifferentiableAt.fun_sum
    intro i _
    exact hblock i
  exact (((hmemory.const_mul (-P.eta)).add hwall).add
    (horder.const_mul P.mu)).add hblocks |>.add
      (hsigma3.differentiableAt.comp q hpulse)

theorem serializedTrueGradient_represents_fderiv {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters) (q : SerializedSpace T n)
    (hdiff : NCPLVerification.EVecDifferentiableAt
      (serializedObjective hn P) q) :
    NCPLVerification.HasEVecFDerivAt (serializedObjective hn P)
      (NCPLVerification.evecDot (serializedTrueGradient hn P q)) q := by
  have hf := hdiff.hasEVecFDerivAt
  unfold NCPLVerification.HasEVecFDerivAt at hf ⊢
  convert hf using 1
  · apply ContinuousLinearMap.ext
    intro h
    rw [NCPLVerification.evecDot_apply]
    exact (NCPLVerification.continuousLinearMap_apply_eq_coordinates
      (NCPLVerification.evecFderiv (serializedObjective hn P) q) h).symm

theorem hasEVecFDerivAt_serializedObjective {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters) (q : SerializedSpace T n) :
    NCPLVerification.HasEVecFDerivAt (serializedObjective hn P)
      (NCPLVerification.evecDot (serializedTrueGradient hn P q)) q :=
  serializedTrueGradient_represents_fderiv hn P q
    (serializedObjective_evecDifferentiableAt hn P q)

/-- The affine line that varies exactly one serialized coordinate. -/
def serializedCoordinateLine {T n : Nat} (q : SerializedSpace T n)
    (j : Fin ((T - 1) * (n + 3))) (t : ℝ) : SerializedSpace T n :=
  fun k ↦ q k + (t - q j) * NCPLVerification.evecBasis j k

/-- A coordinate of the true gradient is the ordinary derivative obtained by
varying exactly that serialized coordinate.  This is the bridge used below to
check the four concrete coordinate families. -/
theorem hasDerivAt_serializedObjective_coordinateLine {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n)
    (j : Fin ((T - 1) * (n + 3))) :
    HasDerivAt
      (fun t : ℝ ↦ serializedObjective hn P (serializedCoordinateLine q j t))
      (serializedTrueGradient hn P q j) (q j) := by
  have hu : HasDerivAt (fun t : ℝ ↦ serializedCoordinateLine q j t)
      (NCPLVerification.evecBasis j) (q j) := by
    rw [hasDerivAt_pi]
    intro k
    have hk := (hasDerivAt_const (q j) (q k)).add
      (((hasDerivAt_id (q j)).sub_const (q j)).mul_const
        (NCPLVerification.evecBasis j k))
    convert hk using 1
    · funext t
      rfl
    · ring
  have hf : HasFDerivAt (serializedObjective hn P)
      (NCPLVerification.evecDot (serializedTrueGradient hn P q)) q := by
    simpa only [NCPLVerification.HasEVecFDerivAt] using
      hasEVecFDerivAt_serializedObjective hn P q
  have hf' : HasFDerivAt (serializedObjective hn P)
      (NCPLVerification.evecDot (serializedTrueGradient hn P q))
      (serializedCoordinateLine q j (q j)) := by
    have hline : serializedCoordinateLine q j (q j) = q := by
      funext k
      simp [serializedCoordinateLine]
    rw [hline]
    exact hf
  have hc := hf'.comp (q j) hu
  have hd := hc.hasDerivAt
  convert hd using 1
  · apply AddCommGroup.ext
    rfl
  · apply Module.ext
    rfl
  · rfl
  · simp [NCPLVerification.evecDot_apply, NCPLVerification.evecBasis]

@[simp] theorem serializedA_coordinateLine_A {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedA (serializedCoordinateLine q (serializedAIndex (n := n) i) t) l =
      if l = i then t else serializedA q l := by
  by_cases hli : l = i
  · subst l
    simp [serializedA, serializedCoordinateLine,
      NCPLVerification.evecBasis]
  · have hidx : serializedAIndex (n := n) l ≠ serializedAIndex (n := n) i := by
      exact fun h ↦ hli (serializedAIndex_injective h)
    simp [serializedA, serializedCoordinateLine,
      NCPLVerification.evecBasis, hli, hidx]

@[simp] theorem serializedY_coordinateLine_A {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (k : Fin n) (t : ℝ) :
    serializedY (serializedCoordinateLine q (serializedAIndex (n := n) i) t) l k =
      serializedY q l k := by
  have hidx : serializedDualIndex l k ≠ serializedAIndex (n := n) i :=
    (serializedAIndex_ne_dualIndex i l k).symm
  simp [serializedY, serializedCoordinateLine,
    NCPLVerification.evecBasis, hidx]

@[simp] theorem serializedDualBlock_coordinateLine_A {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedDualBlock
        (serializedCoordinateLine q (serializedAIndex (n := n) i) t) l =
      serializedDualBlock q l := by
  funext k
  simp [serializedDualBlock]

@[simp] theorem serializedB_coordinateLine_A {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedB (serializedCoordinateLine q (serializedAIndex (n := n) i) t) l =
      serializedB q l := by
  have hidx : serializedBIndex (n := n) l ≠ serializedAIndex (n := n) i :=
    (serializedAIndex_ne_BIndex i l).symm
  simp [serializedB, serializedCoordinateLine,
    NCPLVerification.evecBasis, hidx]

@[simp] theorem serializedState_coordinateLine_A {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedState
        (serializedCoordinateLine q (serializedAIndex (n := n) i) t) l =
      serializedState q l := by
  have hidx : serializedStateIndex (n := n) l ≠ serializedAIndex (n := n) i :=
    (serializedAIndex_ne_stateIndex i l).symm
  simp [serializedState, serializedCoordinateLine,
    NCPLVerification.evecBasis, hidx]

theorem serializedTrueGradient_A {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedTrueGradient hn P q (serializedAIndex (n := n) i) =
      serializedGradA hn P q i := by
  have hblock : HasDerivAt
      (fun t : ℝ ↦
        entrancePulse P.alpha P.theta P.P0 (serializedClippedCurrent P q i)
            (serializedClippedNext P q i) t +
          innerChain hn (innerC hn) t (serializedB q i)
            (serializedDualBlock q i) +
          innerC1 hn * t ^ 2 + innerC2 hn * (serializedB q i) ^ 2 +
          P.gamma * (t ^ 2 + (serializedB q i) ^ 2) +
          exitPulse P.beta P.theta (serializedClippedCurrent P q i)
            (serializedB q i) (serializedClippedNext P q i))
      (entrancePulseDerivA P.alpha P.theta P.P0
          (serializedClippedCurrent P q i) (serializedClippedNext P q i)
          (serializedA q i) +
        innerGradA hn (innerC hn) (serializedDualBlock q i) +
        2 * (innerC1 hn + P.gamma) * serializedA q i)
      (serializedA q i) := by
    have he := hasDerivAt_entrancePulse_a P.alpha P.theta P.P0
      (serializedClippedCurrent P q i) (serializedClippedNext P q i)
      (serializedA q i)
    have hi := hasDerivAt_innerChain_a hn (innerC hn)
      (serializedA q i) (serializedB q i) (serializedDualBlock q i)
    have hsq : HasDerivAt (fun t : ℝ ↦ t ^ 2)
        (2 * serializedA q i) (serializedA q i) := by
      convert (hasDerivAt_id (serializedA q i)).pow 2 using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      · funext t
        rfl
      · simp only [id_eq]
        ring
    have h := (((he.add hi).add (hsq.const_mul (innerC1 hn))).add
      (hasDerivAt_const (serializedA q i)
        (innerC2 hn * (serializedB q i) ^ 2))).add
      ((hsq.add_const ((serializedB q i) ^ 2)).const_mul P.gamma) |>.add
        (hasDerivAt_const (serializedA q i)
          (exitPulse P.beta P.theta (serializedClippedCurrent P q i)
            (serializedB q i) (serializedClippedNext P q i)))
    convert h using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      rfl
    · ring
  have hblocks : HasDerivAt
      (fun t : ℝ ↦ ∑ l : Fin (T - 1),
        serializedBlock hn P
          (serializedCoordinateLine q (serializedAIndex (n := n) i) t) l)
      (entrancePulseDerivA P.alpha P.theta P.P0
          (serializedClippedCurrent P q i) (serializedClippedNext P q i)
          (serializedA q i) +
        innerGradA hn (innerC hn) (serializedDualBlock q i) +
        2 * (innerC1 hn + P.gamma) * serializedA q i)
      (serializedA q i) := by
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (T - 1),
          serializedBlock hn P
            (serializedCoordinateLine q (serializedAIndex (n := n) i) t) l)
        (∑ l : Fin (T - 1), if l = i then
          (entrancePulseDerivA P.alpha P.theta P.P0
              (serializedClippedCurrent P q i) (serializedClippedNext P q i)
              (serializedA q i) +
            innerGradA hn (innerC hn) (serializedDualBlock q i) +
            2 * (innerC1 hn + P.gamma) * serializedA q i) else 0)
        (serializedA q i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa [serializedBlock, serializedClippedCurrent,
          serializedClippedNext, serializedCurrentState, serializedDualBlock]
          using hblock
      · have hc := hasDerivAt_const (serializedA q i) (serializedBlock hn P q l)
        simpa [serializedBlock, serializedClippedCurrent,
          serializedClippedNext, serializedCurrentState, serializedDualBlock,
          hli] using hc
    simpa using hs
  have hpulse : HasDerivAt
      (fun t : ℝ ↦ serializedPulseSq
        (serializedCoordinateLine q (serializedAIndex (n := n) i) t))
      (2 * serializedA q i) (serializedA q i) := by
    unfold serializedPulseSq
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (T - 1),
          ((serializedA
              (serializedCoordinateLine q (serializedAIndex (n := n) i) t) l) ^ 2 +
           (serializedB
              (serializedCoordinateLine q (serializedAIndex (n := n) i) t) l) ^ 2))
        (∑ l : Fin (T - 1), if l = i then 2 * serializedA q i else 0)
        (serializedA q i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa using ((hasDerivAt_id (serializedA q i)).pow 2).add_const
          ((serializedB q i) ^ 2)
      · simpa [hli] using hasDerivAt_const (serializedA q i)
          ((serializedA q l) ^ 2)
    convert hs using 1
    · simp
  have hpulseBase : serializedPulseSq
      (serializedCoordinateLine q (serializedAIndex (n := n) i)
        (serializedA q i)) = serializedPulseSq q := by
    unfold serializedPulseSq
    apply Finset.sum_congr rfl
    intro l _
    by_cases hli : l = i <;> simp [hli]
  have hsigmaBase : HasDerivAt (Sigma3 P.P0 P.P1 P.K)
      (Sigma3Deriv P.P0 P.P1 P.K (serializedPulseSq q))
      (serializedPulseSq
        (serializedCoordinateLine q (serializedAIndex (n := n) i)
          (serializedA q i))) := by
    rw [hpulseBase]
    exact hasDerivAt_Sigma3 P.P0 P.P1 P.K (serializedPulseSq q)
  have hrad := hsigmaBase.comp (serializedA q i) hpulse
  have hconst : HasDerivAt
      (fun _ : ℝ ↦
        -P.eta * (∑ l : Fin (T - 1), Psi1 (serializedClippedNext P q l)) +
        (∑ l : Fin (T - 1), Sigma2 P.tauS (serializedState q l)) +
        P.mu * (∑ l : Fin (T - 1), Psi2 (serializedClippedNext P q l) *
          Sigma1 P.theta (serializedClippedCurrent P q l))) 0
      (serializedA q i) := hasDerivAt_const _ _
  have hall := hconst.add hblocks |>.add hrad
  have hline := hasDerivAt_serializedObjective_coordinateLine hn P q
    (serializedAIndex (n := n) i)
  have hcalc : HasDerivAt
      (fun t : ℝ ↦ serializedObjective hn P
        (serializedCoordinateLine q (serializedAIndex (n := n) i) t))
      (serializedGradA hn P q i) (serializedA q i) := by
    convert hall using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp [serializedObjective, serializedClippedCurrent,
        serializedClippedNext, serializedCurrentState]
    · simp [serializedGradA]
      ring
  exact hline.unique hcalc

@[simp] theorem serializedA_coordinateLine_B {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedA (serializedCoordinateLine q (serializedBIndex (n := n) i) t) l =
      serializedA q l := by
  have hidx := serializedAIndex_ne_BIndex (n := n) l i
  simp [serializedA, serializedCoordinateLine, NCPLVerification.evecBasis, hidx]

@[simp] theorem serializedY_coordinateLine_B {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (k : Fin n) (t : ℝ) :
    serializedY (serializedCoordinateLine q (serializedBIndex (n := n) i) t) l k =
      serializedY q l k := by
  have hidx : serializedDualIndex l k ≠ serializedBIndex (n := n) i :=
    (serializedBIndex_ne_dualIndex i l k).symm
  simp [serializedY, serializedCoordinateLine, NCPLVerification.evecBasis, hidx]

@[simp] theorem serializedDualBlock_coordinateLine_B {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedDualBlock
        (serializedCoordinateLine q (serializedBIndex (n := n) i) t) l =
      serializedDualBlock q l := by
  funext k
  simp [serializedDualBlock]

@[simp] theorem serializedB_coordinateLine_B {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedB (serializedCoordinateLine q (serializedBIndex (n := n) i) t) l =
      if l = i then t else serializedB q l := by
  by_cases hli : l = i
  · subst l
    simp [serializedB, serializedCoordinateLine, NCPLVerification.evecBasis]
  · have hidx : serializedBIndex (n := n) l ≠ serializedBIndex (n := n) i :=
      fun h ↦ hli (serializedBIndex_injective h)
    simp [serializedB, serializedCoordinateLine, NCPLVerification.evecBasis,
      hli, hidx]

@[simp] theorem serializedState_coordinateLine_B {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedState
        (serializedCoordinateLine q (serializedBIndex (n := n) i) t) l =
      serializedState q l := by
  have hidx : serializedStateIndex (n := n) l ≠ serializedBIndex (n := n) i :=
    (serializedBIndex_ne_stateIndex i l).symm
  simp [serializedState, serializedCoordinateLine, NCPLVerification.evecBasis,
    hidx]

theorem serializedTrueGradient_B {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedTrueGradient hn P q (serializedBIndex (n := n) i) =
      serializedGradB hn P q i := by
  have hsq : HasDerivAt (fun t : ℝ ↦ t ^ 2)
      (2 * serializedB q i) (serializedB q i) := by
    convert (hasDerivAt_id (serializedB q i)).pow 2 using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · rfl
    · simp only [id_eq]
      ring
  have hblock : HasDerivAt
      (fun t : ℝ ↦
        entrancePulse P.alpha P.theta P.P0 (serializedClippedCurrent P q i)
            (serializedClippedNext P q i) (serializedA q i) +
          innerChain hn (innerC hn) (serializedA q i) t
            (serializedDualBlock q i) +
          innerC1 hn * (serializedA q i) ^ 2 + innerC2 hn * t ^ 2 +
          P.gamma * ((serializedA q i) ^ 2 + t ^ 2) +
          exitPulse P.beta P.theta (serializedClippedCurrent P q i) t
            (serializedClippedNext P q i))
      (innerGradB hn (innerC hn) (serializedDualBlock q i) +
        2 * (innerC2 hn + P.gamma) * serializedB q i +
        exitPulseDerivB P.beta P.theta (serializedClippedCurrent P q i)
          (serializedB q i) (serializedClippedNext P q i))
      (serializedB q i) := by
    have hi := hasDerivAt_innerChain_b hn (innerC hn)
      (serializedA q i) (serializedB q i) (serializedDualBlock q i)
    have hx := hasDerivAt_exitPulse_b P.beta P.theta
      (serializedClippedCurrent P q i) (serializedB q i)
      (serializedClippedNext P q i)
    have h := (((hasDerivAt_const (serializedB q i)
      (entrancePulse P.alpha P.theta P.P0 (serializedClippedCurrent P q i)
        (serializedClippedNext P q i) (serializedA q i))).add hi).add
      (hasDerivAt_const (serializedB q i) (innerC1 hn * (serializedA q i) ^ 2))).add
      (hsq.const_mul (innerC2 hn)) |>.add
      ((hasDerivAt_const (serializedB q i) ((serializedA q i) ^ 2)).add hsq
        |>.const_mul P.gamma) |>.add hx
    convert h using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · rfl
    · ring
  have hblocks : HasDerivAt
      (fun t : ℝ ↦ ∑ l : Fin (T - 1), serializedBlock hn P
        (serializedCoordinateLine q (serializedBIndex (n := n) i) t) l)
      (innerGradB hn (innerC hn) (serializedDualBlock q i) +
        2 * (innerC2 hn + P.gamma) * serializedB q i +
        exitPulseDerivB P.beta P.theta (serializedClippedCurrent P q i)
          (serializedB q i) (serializedClippedNext P q i))
      (serializedB q i) := by
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (T - 1), serializedBlock hn P
          (serializedCoordinateLine q (serializedBIndex (n := n) i) t) l)
        (∑ l : Fin (T - 1), if l = i then
          (innerGradB hn (innerC hn) (serializedDualBlock q i) +
            2 * (innerC2 hn + P.gamma) * serializedB q i +
            exitPulseDerivB P.beta P.theta (serializedClippedCurrent P q i)
              (serializedB q i) (serializedClippedNext P q i)) else 0)
        (serializedB q i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa [serializedBlock, serializedClippedCurrent, serializedClippedNext,
          serializedCurrentState, serializedDualBlock] using hblock
      · simpa [serializedBlock, serializedClippedCurrent, serializedClippedNext,
          serializedCurrentState, serializedDualBlock, hli] using
          hasDerivAt_const (serializedB q i) (serializedBlock hn P q l)
    simpa using hs
  have hpulse : HasDerivAt
      (fun t : ℝ ↦ serializedPulseSq
        (serializedCoordinateLine q (serializedBIndex (n := n) i) t))
      (2 * serializedB q i) (serializedB q i) := by
    unfold serializedPulseSq
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (T - 1),
          ((serializedA (serializedCoordinateLine q
              (serializedBIndex (n := n) i) t) l) ^ 2 +
           (serializedB (serializedCoordinateLine q
              (serializedBIndex (n := n) i) t) l) ^ 2))
        (∑ l : Fin (T - 1), if l = i then 2 * serializedB q i else 0)
        (serializedB q i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa using hsq
      · simpa [hli] using hasDerivAt_const (serializedB q i)
          ((serializedA q l) ^ 2)
    convert hs using 1
    · simp
  have hpulseBase : serializedPulseSq
      (serializedCoordinateLine q (serializedBIndex (n := n) i)
        (serializedB q i)) = serializedPulseSq q := by
    unfold serializedPulseSq
    apply Finset.sum_congr rfl
    intro l _
    by_cases hli : l = i <;> simp [hli]
  have hsigmaBase : HasDerivAt (Sigma3 P.P0 P.P1 P.K)
      (Sigma3Deriv P.P0 P.P1 P.K (serializedPulseSq q))
      (serializedPulseSq (serializedCoordinateLine q
        (serializedBIndex (n := n) i) (serializedB q i))) := by
    rw [hpulseBase]
    exact hasDerivAt_Sigma3 P.P0 P.P1 P.K (serializedPulseSq q)
  have hrad := hsigmaBase.comp (serializedB q i) hpulse
  have hconst : HasDerivAt
      (fun _ : ℝ ↦
        -P.eta * (∑ l : Fin (T - 1), Psi1 (serializedClippedNext P q l)) +
        (∑ l : Fin (T - 1), Sigma2 P.tauS (serializedState q l)) +
        P.mu * (∑ l : Fin (T - 1), Psi2 (serializedClippedNext P q l) *
          Sigma1 P.theta (serializedClippedCurrent P q l))) 0
      (serializedB q i) := hasDerivAt_const _ _
  have hall := hconst.add hblocks |>.add hrad
  have hline := hasDerivAt_serializedObjective_coordinateLine hn P q
    (serializedBIndex (n := n) i)
  have hcalc : HasDerivAt
      (fun t : ℝ ↦ serializedObjective hn P
        (serializedCoordinateLine q (serializedBIndex (n := n) i) t))
      (serializedGradB hn P q i) (serializedB q i) := by
    convert hall using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp [serializedObjective, serializedClippedCurrent,
        serializedClippedNext, serializedCurrentState]
    · simp [serializedGradB]
      ring
  exact hline.unique hcalc

@[simp] theorem serializedA_coordinateLine_Y {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (k : Fin n) (t : ℝ) :
    serializedA (serializedCoordinateLine q (serializedDualIndex i k) t) l =
      serializedA q l := by
  have hidx := serializedAIndex_ne_dualIndex (n := n) l i k
  simp [serializedA, serializedCoordinateLine, NCPLVerification.evecBasis, hidx]

@[simp] theorem serializedB_coordinateLine_Y {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (k : Fin n) (t : ℝ) :
    serializedB (serializedCoordinateLine q (serializedDualIndex i k) t) l =
      serializedB q l := by
  have hidx := serializedBIndex_ne_dualIndex (n := n) l i k
  simp [serializedB, serializedCoordinateLine, NCPLVerification.evecBasis, hidx]

@[simp] theorem serializedState_coordinateLine_Y {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (k : Fin n) (t : ℝ) :
    serializedState (serializedCoordinateLine q (serializedDualIndex i k) t) l =
      serializedState q l := by
  have hidx := serializedStateIndex_ne_dualIndex (n := n) l i k
  simp [serializedState, serializedCoordinateLine, NCPLVerification.evecBasis,
    hidx]

@[simp] theorem serializedY_coordinateLine_Y {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (k u : Fin n) (t : ℝ) :
    serializedY (serializedCoordinateLine q (serializedDualIndex i k) t) l u =
      if l = i ∧ u = k then t else serializedY q l u := by
  by_cases hpair : l = i ∧ u = k
  · rcases hpair with ⟨rfl, rfl⟩
    simp [serializedY, serializedCoordinateLine, NCPLVerification.evecBasis]
  · have hidx : serializedDualIndex l u ≠ serializedDualIndex i k := by
      simpa [serializedDualIndex_eq_iff] using hpair
    simp [serializedY, serializedCoordinateLine, NCPLVerification.evecBasis,
      hpair, hidx]

theorem serializedDualBlock_coordinateLine_Y_same {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) (k : Fin n) (t : ℝ) :
    serializedDualBlock (serializedCoordinateLine q (serializedDualIndex i k) t) i =
      serializedDualBlock q i +
        (t - serializedY q i k) • NCPLVerification.evecBasis k := by
  funext u
  by_cases huk : u = k
  · subst u
    simp [serializedDualBlock, NCPLVerification.evecBasis]
  · simp [serializedDualBlock, NCPLVerification.evecBasis, huk]

theorem serializedDualBlock_coordinateLine_Y_ne {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (k : Fin n) (t : ℝ)
    (hli : l ≠ i) :
    serializedDualBlock (serializedCoordinateLine q (serializedDualIndex i k) t) l =
      serializedDualBlock q l := by
  funext u
  simp [serializedDualBlock, hli]

theorem serializedTrueGradient_Y {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n)
    (i : Fin (T - 1)) (k : Fin n) :
    serializedTrueGradient hn P q (serializedDualIndex i k) =
      -serializedSaddleGradY hn P q i k := by
  let w := serializedDualBlock q i
  let d := NCPLVerification.evecBasis k
  have hshift : HasDerivAt (fun t : ℝ ↦ t - serializedY q i k) 1
      (serializedY q i k) := by
    simpa using (hasDerivAt_id (serializedY q i k)).sub_const
      (serializedY q i k)
  let A := -regularizedPathBilinear n w d +
    innerScale n (innerC hn) *
      innerForcing hn (serializedA q i) (serializedB q i) d
  let Q := regularizedPathQuad n d
  have hinner : HasDerivAt
      (fun t : ℝ ↦ innerChain hn (innerC hn) (serializedA q i)
        (serializedB q i) (w + (t - serializedY q i k) • d)) A
      (serializedY q i k) := by
    have hpoly : HasDerivAt
        (fun t : ℝ ↦ innerChain hn (innerC hn) (serializedA q i)
            (serializedB q i) w + (t - serializedY q i k) * A -
          (1 / 2 : ℝ) * (t - serializedY q i k) ^ 2 * Q) A
        (serializedY q i k) := by
      convert ((hasDerivAt_const (serializedY q i k)
        (innerChain hn (innerC hn) (serializedA q i) (serializedB q i) w)).add
          (hshift.mul_const A)).sub
        ((((hshift.pow 2).const_mul (1 / 2 : ℝ)).mul_const Q)) using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      · rfl
      · simp [A, Q]
    convert hpoly using 1
    funext t
    exact innerChain_line_expansion hn (innerC hn) (serializedA q i)
      (serializedB q i) w d (t - serializedY q i k)
  have hbasis : NCPLVerification.evecBasis k = (Pi.single k 1 : EVec n) := by
    funext u
    by_cases huk : u = k
    · subst u
      simp [NCPLVerification.evecBasis]
    · simp [NCPLVerification.evecBasis, huk]
  have hbilinear : regularizedPathBilinear n w d =
      regularizedPathCoord w k := by
    dsimp [d]
    rw [hbasis, regularizedPathBilinear_comm,
      regularizedPathBilinear_single_left_eq_coord]
  have hforcing : innerForcing hn (serializedA q i) (serializedB q i) d =
      innerSource hn (serializedA q i) (serializedB q i) k := by
    dsimp [d]
    unfold innerForcing innerSource
    simp only [hbasis, Pi.single_apply]
    by_cases hfirst : innerFirst hn = k <;>
      by_cases hlast : innerLast hn = k <;> simp [hfirst, hlast]
  have hinner' : HasDerivAt
      (fun t : ℝ ↦ innerChain hn (innerC hn) (serializedA q i)
        (serializedB q i)
        (serializedDualBlock q i +
          (t - serializedY q i k) • NCPLVerification.evecBasis k))
      (-serializedSaddleGradY hn P q i k) (serializedY q i k) := by
    convert hinner using 1
    dsimp [A, w, d]
    unfold serializedSaddleGradY innerSaddleGradW
    rw [hbilinear, hforcing]
    dsimp [w]
    ring
  have hblocks : HasDerivAt
      (fun t : ℝ ↦ ∑ l : Fin (T - 1), serializedBlock hn P
        (serializedCoordinateLine q (serializedDualIndex i k) t) l)
      (-serializedSaddleGradY hn P q i k) (serializedY q i k) := by
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (T - 1), serializedBlock hn P
          (serializedCoordinateLine q (serializedDualIndex i k) t) l)
        (∑ l : Fin (T - 1), if l = i then
          -serializedSaddleGradY hn P q i k else 0) (serializedY q i k) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa [serializedBlock, serializedClippedCurrent, serializedClippedNext,
          serializedCurrentState, serializedDualBlock_coordinateLine_Y_same]
          using hinner'
      · simpa [serializedBlock, serializedClippedCurrent, serializedClippedNext,
          serializedCurrentState, serializedDualBlock_coordinateLine_Y_ne,
          hli] using hasDerivAt_const (serializedY q i k) (serializedBlock hn P q l)
    simpa using hs
  have hrest : HasDerivAt
      (fun _ : ℝ ↦
        -P.eta * (∑ l : Fin (T - 1), Psi1 (serializedClippedNext P q l)) +
        (∑ l : Fin (T - 1), Sigma2 P.tauS (serializedState q l)) +
        P.mu * (∑ l : Fin (T - 1), Psi2 (serializedClippedNext P q l) *
          Sigma1 P.theta (serializedClippedCurrent P q l)) +
        Sigma3 P.P0 P.P1 P.K (serializedPulseSq q)) 0
      (serializedY q i k) := hasDerivAt_const _ _
  have hall := hrest.add hblocks
  have hline := hasDerivAt_serializedObjective_coordinateLine hn P q
    (serializedDualIndex i k)
  have hcalc : HasDerivAt
      (fun t : ℝ ↦ serializedObjective hn P
        (serializedCoordinateLine q (serializedDualIndex i k) t))
      (-serializedSaddleGradY hn P q i k) (serializedY q i k) := by
    convert hall using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp [serializedObjective, serializedPulseSq, serializedClippedCurrent,
        serializedClippedNext, serializedCurrentState]
      ring
    · ring
  exact hline.unique hcalc

@[simp] theorem serializedA_coordinateLine_state {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedA (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) l =
      serializedA q l := by
  have hidx := serializedAIndex_ne_stateIndex (n := n) l i
  simp [serializedA, serializedCoordinateLine, NCPLVerification.evecBasis, hidx]

@[simp] theorem serializedB_coordinateLine_state {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedB (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) l =
      serializedB q l := by
  have hidx := serializedBIndex_ne_stateIndex (n := n) l i
  simp [serializedB, serializedCoordinateLine, NCPLVerification.evecBasis, hidx]

@[simp] theorem serializedY_coordinateLine_state {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (k : Fin n) (t : ℝ) :
    serializedY (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) l k =
      serializedY q l k := by
  have hidx : serializedDualIndex l k ≠ serializedStateIndex (n := n) i :=
    (serializedStateIndex_ne_dualIndex i l k).symm
  simp [serializedY, serializedCoordinateLine, NCPLVerification.evecBasis, hidx]

@[simp] theorem serializedDualBlock_coordinateLine_state {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedDualBlock
        (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) l =
      serializedDualBlock q l := by
  funext k
  simp [serializedDualBlock]

@[simp] theorem serializedState_coordinateLine_state {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedState
        (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) l =
      if l = i then t else serializedState q l := by
  by_cases hli : l = i
  · subst l
    simp [serializedState, serializedCoordinateLine, NCPLVerification.evecBasis]
  · have hidx : serializedStateIndex (n := n) l ≠
        serializedStateIndex (n := n) i := fun h ↦ hli (serializedStateIndex_injective h)
    simp [serializedState, serializedCoordinateLine, NCPLVerification.evecBasis,
      hli, hidx]

theorem serializedCurrentState_coordinateLine_state {T n : Nat}
    (q : SerializedSpace T n) (i l : Fin (T - 1)) (t : ℝ) :
    serializedCurrentState
        (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) l =
      if l.val = i.val + 1 then t else serializedCurrentState q l := by
  unfold serializedCurrentState
  by_cases hl0 : l.val = 0
  · simp [hl0]
  · simp only [hl0, ↓reduceDIte]
    by_cases hsucc : l.val = i.val + 1
    · have heq : (⟨l.val - 1, by omega⟩ : Fin (T - 1)) = i := by
        apply Fin.ext
        simp
        omega
      simp [hsucc]
    · have hne : (⟨l.val - 1, by omega⟩ : Fin (T - 1)) ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        simp at hv
        apply hsucc
        omega
      simp [hsucc, hne]

def serializedStateSelfSlice {T n : Nat} (P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) (t : ℝ) : ℝ :=
  let nxt := pi1 P.delta P.P0 t;
  -P.eta * Psi1 nxt + Sigma2 P.tauS t +
    P.mu * Psi2 nxt * Sigma1 P.theta (serializedClippedCurrent P q i) +
    entrancePulse P.alpha P.theta P.P0 (serializedClippedCurrent P q i)
      nxt (serializedA q i) +
    exitPulse P.beta P.theta (serializedClippedCurrent P q i)
      (serializedB q i) nxt

def serializedStateSelfGrad {T n : Nat} (P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) : ℝ :=
  let raw := serializedState q i;
  let cur := serializedClippedCurrent P q i;
  let nxt := serializedClippedNext P q i;
  let cd := pi1Deriv P.delta P.P0 raw;
  -P.eta * Psi1Deriv nxt * cd + Sigma2Deriv P.tauS raw +
    P.mu * Psi2Deriv nxt * cd * Sigma1 P.theta cur -
    P.alpha * Psi2 cur * deriv (Lambda2 P.theta) nxt * cd *
      pi2 P.P0 (serializedA q i) +
    exitPulseDerivNext P.beta P.theta cur (serializedB q i) nxt * cd

theorem hasDerivAt_serializedStateSelfSlice {T n : Nat}
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1)) :
    HasDerivAt (serializedStateSelfSlice P q i)
      (serializedStateSelfGrad P q i) (serializedState q i) := by
  let raw := serializedState q i
  let cur := serializedClippedCurrent P q i
  let nxt := serializedClippedNext P q i
  let cd := pi1Deriv P.delta P.P0 raw
  have hclip : HasDerivAt (pi1 P.delta P.P0) cd raw := by
    exact hasDerivAt_pi1 P.delta_pos P.P0_gt_one
  have hpsi1 := (hasDerivAt_Psi1 nxt).comp raw hclip
  have hsigma2 := hasDerivAt_Sigma2 P.tauS raw
  have hpsi2 := (hasDerivAt_Psi2 nxt).comp raw hclip
  have hlambda : HasDerivAt (Lambda2 P.theta)
      (deriv (Lambda2 P.theta) nxt) nxt := by
    exact ((@Lambda2_contDiff P.theta 1).differentiable (by norm_num) nxt).hasDerivAt
  have hlambda' := hlambda.comp raw hclip
  have hentrance : HasDerivAt
      (fun t : ℝ ↦ entrancePulse P.alpha P.theta P.P0 cur
        (pi1 P.delta P.P0 t) (serializedA q i))
      (-P.alpha * Psi2 cur * deriv (Lambda2 P.theta) nxt * cd *
        pi2 P.P0 (serializedA q i)) raw := by
    unfold entrancePulse
    convert (((hlambda'.mul_const (pi2 P.P0 (serializedA q i))).mul_const
      (Psi2 cur)).const_mul (-P.alpha)) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      dsimp [Function.comp_def]
      ring
    · ring
  have hexit0 := hasDerivAt_exitPulse_next P.beta P.theta cur
    (serializedB q i) nxt
  have hexit := hexit0.comp raw hclip
  have h := ((((hpsi1.const_mul (-P.eta)).add hsigma2).add
    ((hpsi2.mul_const (Sigma1 P.theta cur)).const_mul P.mu)).add
      hentrance).add hexit
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    simp [serializedStateSelfSlice, cur]
    ring
  · simp [serializedStateSelfGrad, raw, cur, nxt, cd]
    ring

def serializedStateSuccessorSlice {T n : Nat} (P : UnscaledParameters)
    (q : SerializedSpace T n) (j : Fin (T - 1)) (t : ℝ) : ℝ :=
  let cur := pi1 P.delta P.P0 t;
  P.mu * Psi2 (serializedClippedNext P q j) * Sigma1 P.theta cur +
    entrancePulse P.alpha P.theta P.P0 cur (serializedClippedNext P q j)
      (serializedA q j) +
    exitPulse P.beta P.theta cur (serializedB q j)
      (serializedClippedNext P q j)

theorem hasDerivAt_serializedStateSuccessorSlice {T n : Nat}
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1))
    (h : i.val + 1 < T - 1) :
    let j : Fin (T - 1) := ⟨i.val + 1, h⟩
    HasDerivAt (serializedStateSuccessorSlice P q j)
      (serializedNextStateContribution P q i) (serializedState q i) := by
  let j : Fin (T - 1) := ⟨i.val + 1, h⟩
  let raw := serializedState q i
  let cur := serializedClippedNext P q i
  let cd := pi1Deriv P.delta P.P0 raw
  have hclip : HasDerivAt (pi1 P.delta P.P0) cd raw :=
    hasDerivAt_pi1 P.delta_pos P.P0_gt_one
  have hsigma := (hasDerivAt_Sigma1 P.theta cur).comp raw hclip
  have hpsi := (hasDerivAt_Psi2 cur).comp raw hclip
  have hentrance : HasDerivAt
      (fun t : ℝ ↦ entrancePulse P.alpha P.theta P.P0
        (pi1 P.delta P.P0 t) (serializedClippedNext P q j)
          (serializedA q j))
      (-P.alpha * Psi2Deriv cur * cd *
        Lambda2 P.theta (serializedClippedNext P q j) *
          pi2 P.P0 (serializedA q j)) raw := by
    unfold entrancePulse
    convert ((((hpsi.mul_const
      (Lambda2 P.theta (serializedClippedNext P q j))).mul_const
        (pi2 P.P0 (serializedA q j))).const_mul (-P.alpha))) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      dsimp [Function.comp_def]
      ring
    · ring
  have hexit : HasDerivAt
      (fun t : ℝ ↦ exitPulse P.beta P.theta (pi1 P.delta P.P0 t)
        (serializedB q j) (serializedClippedNext P q j))
      (-P.beta * Psi2Deriv cur * cd * Psi2 (serializedB q j) *
        exitRelay P.theta (serializedClippedNext P q j)) raw := by
    unfold exitPulse
    convert (((hpsi.mul_const (Psi2 (serializedB q j))).mul_const
      (exitRelay P.theta (serializedClippedNext P q j))).const_mul (-P.beta)) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      dsimp [Function.comp_def]
      ring
    · ring
  have htotal := (((hsigma.mul_const (Psi2 (serializedClippedNext P q j))).const_mul
    P.mu).add hentrance).add hexit
  unfold serializedNextStateContribution
  simp only [dif_pos h]
  convert htotal using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    simp [serializedStateSuccessorSlice, j]
    ring
  · simp [j, raw, cur, cd]
    ring

def serializedObjectiveCore {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) (l : Fin (T - 1)) : ℝ :=
  -P.eta * Psi1 (serializedClippedNext P q l) +
    Sigma2 P.tauS (serializedState q l) +
    P.mu * Psi2 (serializedClippedNext P q l) *
      Sigma1 P.theta (serializedClippedCurrent P q l) +
    serializedBlock hn P q l

theorem serializedObjective_eq_sum_core {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) :
    serializedObjective hn P q =
      (∑ l : Fin (T - 1), serializedObjectiveCore hn P q l) +
        Sigma3 P.P0 P.P1 P.K (serializedPulseSq q) := by
  unfold serializedObjective serializedObjectiveCore
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  ring

theorem serializedTrueGradient_state {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedTrueGradient hn P q (serializedStateIndex (n := n) i) =
      serializedGradState P q i := by
  let raw := serializedState q i
  let self0 := serializedStateSelfSlice P q i raw
  have hself := hasDerivAt_serializedStateSelfSlice P q i
  have hpulse : ∀ t : ℝ, serializedPulseSq
      (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) =
        serializedPulseSq q := by
    intro t
    unfold serializedPulseSq
    apply Finset.sum_congr rfl
    intro l _
    simp
  by_cases hs : i.val + 1 < T - 1
  · let j : Fin (T - 1) := ⟨i.val + 1, hs⟩
    let succ0 := serializedStateSuccessorSlice P q j raw
    have hsucc := hasDerivAt_serializedStateSuccessorSlice P q i hs
    have hpoint (t : ℝ) (l : Fin (T - 1)) :
        serializedObjectiveCore hn P
            (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) l =
          serializedObjectiveCore hn P q l +
            (if l = i then serializedStateSelfSlice P q i t - self0 else 0) +
            (if l = j then serializedStateSuccessorSlice P q j t - succ0 else 0) := by
      by_cases hli : l = i
      · subst l
        have hij : i ≠ j := by
          intro h
          have hv := congrArg Fin.val h
          dsimp [j] at hv
          omega
        simp [serializedObjectiveCore, serializedBlock, serializedStateSelfSlice,
          serializedClippedCurrent, serializedClippedNext,
          serializedCurrentState_coordinateLine_state, hij, self0, raw]
        ring
      · by_cases hlj : l = j
        · subst l
          have hji : j ≠ i := by
            intro h
            exact hli h
          have hjval : j.val = i.val + 1 := by rfl
          have hcurj : serializedCurrentState q j = serializedState q i := by
            unfold serializedCurrentState
            have hj0 : j.val ≠ 0 := by
              dsimp [j]
              omega
            simp only [hj0, ↓reduceDIte]
            congr 1
          simp [serializedObjectiveCore, serializedBlock,
            serializedStateSuccessorSlice, serializedClippedCurrent,
            serializedClippedNext, serializedCurrentState_coordinateLine_state,
            hji, hjval, hcurj, succ0, raw]
          ring
        · have hval : l.val ≠ i.val + 1 := by
            intro hv
            apply hlj
            apply Fin.ext
            dsimp [j]
            exact hv
          simp [serializedObjectiveCore, serializedBlock,
            serializedClippedCurrent, serializedClippedNext,
            serializedCurrentState_coordinateLine_state, hli, hlj, hval]
    have hslice (t : ℝ) : serializedObjective hn P
          (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) =
        (serializedObjective hn P q - self0 - succ0) +
          serializedStateSelfSlice P q i t +
          serializedStateSuccessorSlice P q j t := by
      rw [serializedObjective_eq_sum_core, serializedObjective_eq_sum_core]
      rw [hpulse]
      calc
        (∑ l : Fin (T - 1), serializedObjectiveCore hn P
            (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) l) +
              Sigma3 P.P0 P.P1 P.K (serializedPulseSq q) =
            (∑ l : Fin (T - 1), (serializedObjectiveCore hn P q l +
              (if l = i then serializedStateSelfSlice P q i t - self0 else 0) +
              (if l = j then serializedStateSuccessorSlice P q j t - succ0 else 0))) +
              Sigma3 P.P0 P.P1 P.K (serializedPulseSq q) := by
                apply congrArg (fun z : ℝ ↦ z +
                  Sigma3 P.P0 P.P1 P.K (serializedPulseSq q))
                apply Finset.sum_congr rfl
                intro l _
                exact hpoint t l
        _ = _ := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp
          ring
    have hconst := hasDerivAt_const raw
      (serializedObjective hn P q - self0 - succ0)
    have hcalc0 := (hconst.add hself).add hsucc
    have hcalc : HasDerivAt
        (fun t : ℝ ↦ serializedObjective hn P
          (serializedCoordinateLine q (serializedStateIndex (n := n) i) t))
        (serializedGradState P q i) raw := by
      have heq : (fun t : ℝ ↦ serializedObjective hn P
          (serializedCoordinateLine q (serializedStateIndex (n := n) i) t)) =
          (fun t : ℝ ↦ (serializedObjective hn P q - self0 - succ0) +
            serializedStateSelfSlice P q i t +
            serializedStateSuccessorSlice P q j t) := by
        funext t
        exact hslice t
      have hc : HasDerivAt
          (fun t : ℝ ↦ serializedObjective hn P
            (serializedCoordinateLine q (serializedStateIndex (n := n) i) t))
          (0 + serializedStateSelfGrad P q i +
            serializedNextStateContribution P q i) raw := by
        rw [heq]
        exact hcalc0
      convert hc using 1
      simp [serializedGradState, serializedStateSelfGrad]
    have hline := hasDerivAt_serializedObjective_coordinateLine hn P q
      (serializedStateIndex (n := n) i)
    exact hline.unique hcalc

  · have hpoint (t : ℝ) (l : Fin (T - 1)) :
        serializedObjectiveCore hn P
            (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) l =
          serializedObjectiveCore hn P q l +
            (if l = i then serializedStateSelfSlice P q i t - self0 else 0) := by
      by_cases hli : l = i
      · subst l
        simp [serializedObjectiveCore, serializedBlock, serializedStateSelfSlice,
          serializedClippedCurrent, serializedClippedNext,
          serializedCurrentState_coordinateLine_state, self0, raw]
        ring
      · have hval : l.val ≠ i.val + 1 := by
          intro hv
          have hlt := l.isLt
          rw [hv] at hlt
          exact hs hlt
        simp [serializedObjectiveCore, serializedBlock,
          serializedClippedCurrent, serializedClippedNext,
          serializedCurrentState_coordinateLine_state, hli, hval]
    have hslice (t : ℝ) : serializedObjective hn P
          (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) =
        (serializedObjective hn P q - self0) + serializedStateSelfSlice P q i t := by
      rw [serializedObjective_eq_sum_core, serializedObjective_eq_sum_core]
      rw [hpulse]
      calc
        (∑ l : Fin (T - 1), serializedObjectiveCore hn P
            (serializedCoordinateLine q (serializedStateIndex (n := n) i) t) l) +
              Sigma3 P.P0 P.P1 P.K (serializedPulseSq q) =
            (∑ l : Fin (T - 1), (serializedObjectiveCore hn P q l +
              (if l = i then serializedStateSelfSlice P q i t - self0 else 0))) +
              Sigma3 P.P0 P.P1 P.K (serializedPulseSq q) := by
                apply congrArg (fun z : ℝ ↦ z +
                  Sigma3 P.P0 P.P1 P.K (serializedPulseSq q))
                apply Finset.sum_congr rfl
                intro l _
                exact hpoint t l
        _ = _ := by
          rw [Finset.sum_add_distrib]
          simp
          ring
    have hcalc0 := (hasDerivAt_const raw
      (serializedObjective hn P q - self0)).add hself
    have hcalc : HasDerivAt
        (fun t : ℝ ↦ serializedObjective hn P
          (serializedCoordinateLine q (serializedStateIndex (n := n) i) t))
        (serializedGradState P q i) raw := by
      have heq : (fun t : ℝ ↦ serializedObjective hn P
          (serializedCoordinateLine q (serializedStateIndex (n := n) i) t)) =
          (fun t : ℝ ↦ (serializedObjective hn P q - self0) +
            serializedStateSelfSlice P q i t) := by
        funext t
        exact hslice t
      have hc : HasDerivAt
          (fun t : ℝ ↦ serializedObjective hn P
            (serializedCoordinateLine q (serializedStateIndex (n := n) i) t))
          (0 + serializedStateSelfGrad P q i) raw := by
        rw [heq]
        exact hcalc0
      convert hc using 1
      simp [serializedGradState, serializedStateSelfGrad,
        serializedNextStateContribution, hs]
    have hline := hasDerivAt_serializedObjective_coordinateLine hn P q
      (serializedStateIndex (n := n) i)
    exact hline.unique hcalc

/-- The true Fréchet gradient with the dual coordinates sign-flipped and
reassembled in the paper's serialized order. -/
def serializedSignedTrueSaddleField {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) : SerializedSpace T n :=
  (∑ i : Fin (T - 1), Pi.single (serializedAIndex (n := n) i)
      (serializedTrueGradient hn P q (serializedAIndex (n := n) i))) +
    (∑ i : Fin (T - 1), ∑ k : Fin n,
      Pi.single (serializedDualIndex i k)
        (-serializedTrueGradient hn P q (serializedDualIndex i k))) +
    (∑ i : Fin (T - 1), Pi.single (serializedBIndex (n := n) i)
      (serializedTrueGradient hn P q (serializedBIndex (n := n) i))) +
    (∑ i : Fin (T - 1), Pi.single (serializedStateIndex (n := n) i)
      (serializedTrueGradient hn P q (serializedStateIndex (n := n) i)))

/-- The concrete displayed saddle field is exactly the signed true Fréchet
gradient, coordinate by coordinate.  This is the bridge that makes the
serialization zero-chain theorem a statement about the genuine oracle. -/
theorem serializedSaddleField_eq_signedTrueGradient {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) :
    serializedSaddleField hn P q = serializedSignedTrueSaddleField hn P q := by
  unfold serializedSaddleField serializedSignedTrueSaddleField
  simp_rw [serializedTrueGradient_A hn P q]
  simp_rw [serializedTrueGradient_B hn P q]
  simp_rw [serializedTrueGradient_state hn P q]
  simp_rw [serializedTrueGradient_Y hn P q]
  simp

/-! ## One-step causality of the concrete coordinate formulas -/

theorem serializedGradA_zero_of_unrevealed {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1))
    (hcurrent : serializedCurrentState q i = 0)
    (ha0 : serializedA q i = 0)
    (hy0 : serializedY q i (innerFirst hn) = 0) :
    serializedGradA hn P q i = 0 := by
  have hclip : serializedClippedCurrent P q i = 0 := by
    simp [serializedClippedCurrent, hcurrent, pi1_zero_of_parameters]
  simp [serializedGradA, entrancePulseDerivA, innerGradA,
    hclip, ha0, hy0, serializedDualBlock, Psi2_zero]

theorem serializedGradB_zero_of_unrevealed {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1))
    (hb0 : serializedB q i = 0)
    (hyLast : serializedY q i (innerLast hn) = 0) :
    serializedGradB hn P q i = 0 := by
  simp [serializedGradB, innerGradB, serializedDualBlock, hb0, hyLast,
    exitPulseDerivB, Psi2Deriv_zero]

theorem serializedSaddleGradY_zero_of_zero_tail {T n k : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1))
    (hb0 : serializedB q i = 0)
    (hy : ∀ j : Fin n, k ≤ j.val → serializedY q i j = 0)
    (j : Fin n) (hj : k + 1 ≤ j.val) :
    serializedSaddleGradY hn P q i j = 0 := by
  exact innerSaddleGradW_zero_of_zero_tail hn (innerC hn)
    (serializedA q i) (serializedB q i) hb0 (by
      intro u hu
      simpa [serializedDualBlock] using hy u hu) j hj

theorem serializedNextStateContribution_zero_of_unrevealed {T n : Nat}
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1))
    (hraw : serializedState q i = 0)
    (hnextState : ∀ h : i.val + 1 < T - 1,
      serializedState q ⟨i.val + 1, h⟩ = 0) :
    serializedNextStateContribution P q i = 0 := by
  unfold serializedNextStateContribution
  split
  · rename_i h
    dsimp only
    have hclipI : serializedClippedNext P q i = 0 := by
      simp [serializedClippedNext, hraw, pi1_zero_of_parameters]
    have hclipJ : serializedClippedNext P q ⟨i.val + 1, h⟩ = 0 := by
      simp [serializedClippedNext, hnextState h, pi1_zero_of_parameters]
    rw [hclipI, hclipJ, Psi2_zero, Psi2Deriv_zero]
    ring
  · rfl

theorem serializedGradState_zero_of_unrevealed {T n : Nat}
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1))
    (hraw : serializedState q i = 0)
    (hb0 : serializedB q i = 0)
    (hnextState : ∀ h : i.val + 1 < T - 1,
      serializedState q ⟨i.val + 1, h⟩ = 0) :
    serializedGradState P q i = 0 := by
  have hnxt : serializedClippedNext P q i = 0 := by
    simp [serializedClippedNext, hraw, pi1_zero_of_parameters]
  unfold serializedGradState
  simp only [hraw, hnxt]
  simp [pi1Deriv_zero_of_parameters, Sigma2Deriv_zero P.tauS_pos,
    Psi1Deriv_eq_zero_of_le_half (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Psi2Deriv_zero, hb0, exitPulseDerivNext, Psi2_zero,
    Lambda2_deriv_eq_zero_of_le_one P.theta_pos (by norm_num : (0 : ℝ) ≤ 1),
    serializedNextStateContribution_zero_of_unrevealed P q i hraw hnextState]

theorem serializedSaddleGradY_zero_of_block_zero {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1))
    (ha0 : serializedA q i = 0) (hb0 : serializedB q i = 0)
    (hy0 : ∀ k : Fin n, serializedY q i k = 0) (k : Fin n) :
    serializedSaddleGradY hn P q i k = 0 := by
  have hw : serializedDualBlock q i = 0 := by
    funext u
    exact hy0 u
  simp [serializedSaddleGradY, hw, ha0, hb0, innerSaddleGradW,
    innerSource, regularizedPathCoord]
  unfold pathLaplacianCoord
  split <;> split <;> simp

theorem serializedGradA_one_step {T n r : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n)
    (hz : NCPLVerification.SupportedBelow r q) (i : Fin (T - 1))
    (hi : r + 1 ≤ (serializedAIndex (n := n) i).val) :
    serializedGradA hn P q i = 0 := by
  change r + 1 ≤ i.val * (n + 3) at hi
  have ine : i.val ≠ 0 := by
    intro hieq
    simp [hieq] at hi
  let ip : Fin (T - 1) := ⟨i.val - 1, by omega⟩
  have ha0 : serializedA q i = 0 := by
    apply hz
    change r ≤ i.val * (n + 3)
    omega
  have hy0 : serializedY q i (innerFirst hn) = 0 := by
    apply hz
    change r ≤ i.val * (n + 3) + 1 + (innerFirst hn).val
    simp [innerFirst]
    omega
  have hs0 : serializedState q ip = 0 := by
    apply hz
    change r ≤ (i.val - 1) * (n + 3) + n + 2
    have hieq : i.val = (i.val - 1) + 1 := by omega
    rw [hieq] at hi
    rw [Nat.add_mul] at hi
    omega
  have hcur : serializedCurrentState q i = 0 := by
    simp [serializedCurrentState, ine, ip, hs0]
  exact serializedGradA_zero_of_unrevealed hn P q i hcur ha0 hy0

theorem serializedGradB_one_step {T n r : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n)
    (hz : NCPLVerification.SupportedBelow r q) (i : Fin (T - 1))
    (hi : r + 1 ≤ (serializedBIndex (n := n) i).val) :
    serializedGradB hn P q i = 0 := by
  change r + 1 ≤ i.val * (n + 3) + n + 1 at hi
  have hb0 : serializedB q i = 0 := by
    apply hz
    change r ≤ i.val * (n + 3) + n + 1
    omega
  have hy0 : serializedY q i (innerLast hn) = 0 := by
    apply hz
    change r ≤ i.val * (n + 3) + 1 + (n - 1)
    have hlast : n - 1 < n := by omega
    omega
  exact serializedGradB_zero_of_unrevealed hn P q i hb0 hy0

theorem serializedSaddleGradY_one_step {T n r : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (q : SerializedSpace T n)
    (hz : NCPLVerification.SupportedBelow r q) (i : Fin (T - 1)) (k : Fin n)
    (hi : r + 1 ≤ (serializedDualIndex i k).val) :
    serializedSaddleGradY hn P q i k = 0 := by
  change r + 1 ≤ i.val * (n + 3) + 1 + k.val at hi
  by_cases hk : k.val = 0
  · have ha0 : serializedA q i = 0 := by
      apply hz
      change r ≤ i.val * (n + 3)
      omega
    have hb0 : serializedB q i = 0 := by
      apply hz
      change r ≤ i.val * (n + 3) + n + 1
      omega
    have hy0 : ∀ u : Fin n, serializedY q i u = 0 := by
      intro u
      apply hz
      change r ≤ i.val * (n + 3) + 1 + u.val
      omega
    exact serializedSaddleGradY_zero_of_block_zero hn P q i ha0 hb0 hy0 k
  · let tail : Nat := k.val - 1
    have hb0 : serializedB q i = 0 := by
      apply hz
      change r ≤ i.val * (n + 3) + n + 1
      omega
    have hyTail : ∀ u : Fin n, tail ≤ u.val → serializedY q i u = 0 := by
      intro u hu
      apply hz
      change r ≤ i.val * (n + 3) + 1 + u.val
      dsimp [tail] at hu
      have hkeq : k.val = (k.val - 1) + 1 := by omega
      omega
    have htarget : tail + 1 ≤ k.val := by
      dsimp [tail]
      omega
    exact serializedSaddleGradY_zero_of_zero_tail hn P q i hb0 hyTail k htarget

theorem serializedGradState_one_step {T n r : Nat}
    (P : UnscaledParameters) (q : SerializedSpace T n)
    (hz : NCPLVerification.SupportedBelow r q) (i : Fin (T - 1))
    (hi : r + 1 ≤ (serializedStateIndex (n := n) i).val) :
    serializedGradState P q i = 0 := by
  change r + 1 ≤ i.val * (n + 3) + n + 2 at hi
  have hs0 : serializedState q i = 0 := by
    apply hz
    change r ≤ i.val * (n + 3) + n + 2
    omega
  have hb0 : serializedB q i = 0 := by
    apply hz
    change r ≤ i.val * (n + 3) + n + 1
    omega
  have hnext : ∀ h : i.val + 1 < T - 1,
      serializedState q ⟨i.val + 1, h⟩ = 0 := by
    intro h
    apply hz
    change r ≤ (i.val + 1) * (n + 3) + n + 2
    have hmul : i.val * (n + 3) ≤ (i.val + 1) * (n + 3) :=
      Nat.mul_le_mul_right (n + 3) (Nat.le_succ i.val)
    have hbase : r ≤ i.val * (n + 3) + n + 2 :=
      Nat.le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self r) hi)
    exact hbase.trans (Nat.add_le_add_right (Nat.add_le_add_right hmul n) 2)
  exact serializedGradState_zero_of_unrevealed P q i hs0 hb0 hnext

/-- Full `lem:serialization`: support below a prefix can reveal at most the
next coordinate in the exact order `(a_i,y¹_i,…,yⁿ_i,b_i,s_{i+1})`. -/
theorem serializedSaddleField_isFirstOrderZeroChain {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) :
    NCPLVerification.IsFirstOrderZeroChain
      (serializedSaddleField (T := T) hn P) := by
  intro r q hz j hj
  have sum_eval_zero : ∀ {m : Nat} (f : Fin m → SerializedSpace T n),
      (∀ i, f i j = 0) → (∑ i, f i) j = 0 := by
    intro m f hf
    have hp : (NCPLVerification.evecProj j) (∑ i, f i) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i _
      simpa only [NCPLVerification.evecProj_apply] using hf i
    simpa only [NCPLVerification.evecProj_apply] using hp
  have hA :
      (Finset.univ.sum fun i : Fin (T - 1) ↦
        (Pi.single (serializedAIndex (n := n) i) (serializedGradA hn P q i) :
          SerializedSpace T n)) j = 0 := by
    apply sum_eval_zero
    intro i
    by_cases heq : serializedAIndex (n := n) i = j
    · subst j
      simp [serializedGradA_one_step hn P q hz i hj]
    · simp [heq]
  have hY :
      (Finset.univ.sum fun i : Fin (T - 1) ↦
        Finset.univ.sum fun k : Fin n ↦
          (Pi.single (serializedDualIndex i k)
            (serializedSaddleGradY hn P q i k) : SerializedSpace T n)) j = 0 := by
    apply sum_eval_zero
    intro i
    apply sum_eval_zero
    intro k
    by_cases heq : serializedDualIndex i k = j
    · subst j
      simp [serializedSaddleGradY_one_step hn P q hz i k hj]
    · simp [heq]
  have hB :
      (Finset.univ.sum fun i : Fin (T - 1) ↦
        (Pi.single (serializedBIndex (n := n) i) (serializedGradB hn P q i) :
          SerializedSpace T n)) j = 0 := by
    apply sum_eval_zero
    intro i
    by_cases heq : serializedBIndex (n := n) i = j
    · subst j
      simp [serializedGradB_one_step hn P q hz i hj]
    · simp [heq]
  have hS :
      (Finset.univ.sum fun i : Fin (T - 1) ↦
        (Pi.single (serializedStateIndex (n := n) i)
          (serializedGradState P q i) : SerializedSpace T n)) j = 0 := by
    apply sum_eval_zero
    intro i
    by_cases heq : serializedStateIndex (n := n) i = j
    · subst j
      simp [serializedGradState_one_step P q hz i hj]
    · simp [heq]
  simp [serializedSaddleField, hA, hY, hB, hS]

theorem serializedSaddleField_isFirstOrderSaddleZeroChain {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters) :
    IsFirstOrderSaddleZeroChain (serializedSaddleField (T := T) hn P) :=
  isFirstOrderSaddleZeroChain_of_global
    (serializedSaddleField_isFirstOrderZeroChain hn P)

/-- At the origin the field is supported on coordinate zero.  Since coordinate
zero is `a₁`, this is the precise "only `a₁` may be revealed" clause of
`lem:serialization`. -/
theorem serializedSaddleField_zero_supported_a1 {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) :
    NCPLVerification.SupportedBelow 1
      (serializedSaddleField (T := T) hn P 0) := by
  exact serializedSaddleField_isFirstOrderZeroChain hn P 0 0
    (NCPLVerification.supportedBelow_zero _ 0)

/-- The two endpoint claims identify the first possible revealed coordinate
with `a₁` and the final coordinate with the terminal state `s_T`. -/
theorem serialization_endpoint_certificate {T n : Nat} (hT : 1 < T) :
    (serializedAIndex (n := n) (⟨0, by omega⟩ : Fin (T - 1))).val = 0 ∧
    (serializedStateIndex (n := n)
      (⟨T - 2, by omega⟩ : Fin (T - 1))).val =
        (T - 1) * (n + 3) - 1 :=
  ⟨serializedA_first_index hT, serializedState_last_index hT⟩

end

end NCCLowerBoundVerification
