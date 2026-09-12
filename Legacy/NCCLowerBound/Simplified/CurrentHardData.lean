import NCCLowerBound.Simplified.Framework
import NCCLowerBound.Simplified.CompositeZeroChain
import NCCLowerBound.Simplified.CompositeSmoothness
import NCCLowerBound.Simplified.CompositeSmoothnessAssembly
import NCCLowerBound.Simplified.InnerFiniteBall
import NCCLowerBound.Simplified.FiniteBallGap
import NCCLowerBound.Simplified.TerminalCertificate
import NCCLowerBoundVerification.Lower.UnscaledMaximizer
import NCCLowerBoundVerification.Lower.UniformSmoothness
import NCCLowerBoundVerification.Upper.ProxExistence

/-!
# Assembly of the current five-component hard instance

This file places the literal construction in the coordinate types used by
`Framework.UnscaledHardData`.  The framework stores primal blocks in the
order `(aᵢ,bᵢ,sᵢ)`, whereas `RestrictedBall` uses `(sᵢ,aᵢ,bᵢ)`; the maps
below are the explicit fixed coordinate permutation between those views.

The definitions in this file do not assume any gradient formula: every
gradient is extracted from the actual Fréchet derivative.  The signed
zero-chain is then identified with the independently differentiated
coordinate field in `CompositeZeroChain`.
-/

namespace NCCLowerBound
namespace Simplified
namespace CurrentHardData

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators
open Set
open NCCLowerBoundVerification
open InnerRelay Composite CompositeProperties RestrictedBall
open CompositeZeroChain InnerFiniteBall

abbrev Primal (M : Nat) := Framework.Primal M
abbrev Dual (M N : Nat) := Framework.Dual M N

/-! ## The two coordinate layouts -/

/-- Decode the framework's `(a,b,s)` storage into the mathematical blocks. -/
def decodeFrameworkPrimal {M : Nat} (x : Primal M) : PrimalPoint M :=
  (primalState x, primalA x, primalB x)

/-- Reorder `(a,b,s)` storage to the `(s,a,b)` flat storage used by the
finite-ball analysis. -/
def toFlatPrimal {M : Nat} (x : Primal M) : FlatPrimal M :=
  fun j =>
    let ik := finProdFinEquiv.symm j
    if ik.2.val = 0 then primalState x ik.1
    else if ik.2.val = 1 then primalA x ik.1
    else primalB x ik.1

/-- The pulse-only `(a,b)` projection. -/
def toPulse {M : Nat} (x : Primal M) : InnerFiniteBall.Pulse M :=
  fun j =>
    let ik := finProdFinEquiv.symm j
    if ik.2.val = 0 then primalA x ik.1 else primalB x ik.1

/-- The same primal point in the product storage used by the terminal
certificate: all memories first, followed by the two pulse coordinates. -/
def toTerminalPrimal {M : Nat} (x : Primal M) :
    TerminalCertificate.TerminalPrimal M :=
  (primalState x, toPulse x)

/-- `toTerminalPrimal` as a continuous linear coordinate permutation. -/
def toTerminalCLM {M : Nat} :
    Primal M →L[ℝ] TerminalCertificate.TerminalPrimal M :=
  LinearMap.toContinuousLinearMap
    ({ toFun := toTerminalPrimal
       map_add' := by
         intro x r
         apply Prod.ext
         · rfl
         · funext j
           simp [toTerminalPrimal, toPulse, primalA, primalB]
           split <;> rfl
       map_smul' := by
         intro c x
         apply Prod.ext
         · rfl
         · funext j
           simp [toTerminalPrimal, toPulse, primalA, primalB] } :
      Primal M →ₗ[ℝ] TerminalCertificate.TerminalPrimal M)

@[simp] theorem toTerminalCLM_apply {M : Nat} (x : Primal M) :
    toTerminalCLM x = toTerminalPrimal x := rfl

@[simp] theorem toTerminalPrimal_fst {M : Nat} (x : Primal M) :
    (toTerminalPrimal x).1 = primalState x := rfl

@[simp] theorem toTerminalPrimal_snd {M : Nat} (x : Primal M) :
    (toTerminalPrimal x).2 = toPulse x := rfl

@[simp] theorem flatState_toFlatPrimal {M : Nat} (x : Primal M) :
    flatState (toFlatPrimal x) = primalState x := by
  funext i
  simp [flatState, toFlatPrimal]

@[simp] theorem flatEntrance_toFlatPrimal {M : Nat} (x : Primal M) :
    flatEntrance (toFlatPrimal x) = primalA x := by
  funext i
  simp [flatEntrance, toFlatPrimal]

@[simp] theorem flatExit_toFlatPrimal {M : Nat} (x : Primal M) :
    flatExit (toFlatPrimal x) = primalB x := by
  funext i
  simp [flatExit, toFlatPrimal]

@[simp] theorem toFlatPrimal_zero {M : Nat} :
    toFlatPrimal (0 : Primal M) = 0 := by
  funext j
  simp [toFlatPrimal, primalState, primalA, primalB]

@[simp] theorem toFlatPrimal_sub {M : Nat} (x r : Primal M) :
    toFlatPrimal (x - r) = toFlatPrimal x - toFlatPrimal r := by
  funext j
  simp only [toFlatPrimal, Pi.sub_apply]
  split
  · rfl
  · split <;> rfl

/-- The storage permutation `(a,b,s) ↔ (s,a,b)` preserves the exact
squared Euclidean form used by all smoothness certificates. -/
theorem vecSq_toFlatPrimal {M : Nat} (x : Primal M) :
    vecSq (toFlatPrimal x) = vecSq x := by
  have hflat (z : FlatPrimal M) : vecSq z = ∑ i : Fin M,
      (flatState z i ^ 2 + flatEntrance z i ^ 2 + flatExit z i ^ 2) := by
    unfold vecSq NCPLVerification.vecSq
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    simp [Fin.sum_univ_succ, flatState, flatEntrance, flatExit]
    ring
  rw [hflat, NCCLowerBoundVerification.vecSq_unscaledPrimal_blocks]
  simp only [flatState_toFlatPrimal, flatEntrance_toFlatPrimal,
    flatExit_toFlatPrimal]
  apply Finset.sum_congr rfl
  intro i _
  ring

@[simp] theorem pulseA_toPulse {M : Nat} (x : Primal M) :
    InnerFiniteBall.pulseA (toPulse x) = primalA x := by
  funext i
  simp [InnerFiniteBall.pulseA, toPulse]

@[simp] theorem pulseB_toPulse {M : Nat} (x : Primal M) :
    InnerFiniteBall.pulseB (toPulse x) = primalB x := by
  funext i
  simp [InnerFiniteBall.pulseB, toPulse]

@[simp] theorem terminalPulseA_toPulse {M : Nat} (x : Primal M) :
    TerminalCertificate.pulseA (toPulse x) = primalA x := by
  funext i
  simp [TerminalCertificate.pulseA, toPulse]

@[simp] theorem terminalPulseB_toPulse {M : Nat} (x : Primal M) :
    TerminalCertificate.pulseB (toPulse x) = primalB x := by
  funext i
  simp [TerminalCertificate.pulseB, toPulse]

theorem vecSq_toPulse {M : Nat} (x : Primal M) :
    vecSq (toPulse x) = pulseSq x := by
  rw [InnerFiniteBall.vecSq_pulse]
  simp [pulseSq]
  rfl

/-- Flatten the framework dual blocks in the order used by `RestrictedBall`.
The dimensions differ syntactically by `N*M` versus `M*N`; the block map is
the actual permutation, not a coercion hidden in a theorem statement. -/
def dualIndexEquiv (M N : Nat) :
    Fin (M * N) ≃ Fin (N * ((M + 1) - 1)) where
  toFun j := ⟨j.val, by simpa [Nat.mul_comm] using j.isLt⟩
  invFun j := ⟨j.val, by simpa [Nat.mul_comm] using j.isLt⟩
  left_inv j := Fin.ext rfl
  right_inv j := Fin.ext rfl

@[simp] theorem dualIndexEquiv_val {M N : Nat} (j : Fin (M * N)) :
    (dualIndexEquiv M N j).val = j.val := rfl

@[simp] theorem dualIndexEquiv_symm_val {M N : Nat}
    (j : Fin (N * ((M + 1) - 1))) :
    ((dualIndexEquiv M N).symm j).val = j.val := rfl

def toFlatDual {M N : Nat} (y : Dual M N) : FlatDual M N :=
  fun j => y (dualIndexEquiv M N j)

/-- Inverse of `toFlatDual`. -/
def fromFlatDual {M N : Nat} (z : FlatDual M N) : Dual M N :=
  fun j => z ((dualIndexEquiv M N).symm j)

@[simp] theorem toFlatDual_sub {M N : Nat} (y v : Dual M N) :
    toFlatDual (y - v) = toFlatDual y - toFlatDual v := by
  rfl

@[simp] theorem dualBlock_fromFlatDual {M N : Nat} (z : FlatDual M N) :
    dualBlock (fromFlatDual z) = unflattenBlocks z := by
  funext i k
  unfold dualBlock fromFlatDual unflattenBlocks
  congr 1
  apply Fin.ext
  change N * i.val + k.val = k.val + N * i.val
  omega

@[simp] theorem unflattenBlocks_toFlatDual {M N : Nat} (y : Dual M N) :
    unflattenBlocks (toFlatDual y) = dualBlock y := by
  funext i k
  unfold unflattenBlocks toFlatDual dualBlock
  congr 1
  apply Fin.ext
  change k.val + N * i.val = N * i.val + k.val
  omega

@[simp] theorem toFlatDual_fromFlatDual {M N : Nat} (z : FlatDual M N) :
    toFlatDual (fromFlatDual z) = z := by
  funext j
  unfold toFlatDual fromFlatDual
  rw [Equiv.symm_apply_apply]

@[simp] theorem fromFlatDual_toFlatDual {M N : Nat} (y : Dual M N) :
    fromFlatDual (toFlatDual y) = y := by
  funext j
  unfold toFlatDual fromFlatDual
  change y ((dualIndexEquiv M N) ((dualIndexEquiv M N).symm j)) = y j
  rw [Equiv.apply_symm_apply]

theorem vecSq_toFlatDual {M N : Nat} (y : Dual M N) :
    vecSq (toFlatDual y) = vecSq y := by
  unfold vecSq NCPLVerification.vecSq toFlatDual
  exact Equiv.sum_comp (dualIndexEquiv M N) (fun i => y i ^ 2)

theorem vecSq_fromFlatDual {M N : Nat} (z : FlatDual M N) :
    vecSq (fromFlatDual z) = vecSq z := by
  have h := vecSq_toFlatDual (fromFlatDual z)
  simpa using h.symm

theorem jointSq_toFlat {M N : Nat} (x r : Primal M) (y v : Dual M N) :
    NCPLVerification.jointSq
        (toFlatPrimal x - toFlatPrimal r) (toFlatDual y - toFlatDual v) =
      NCPLVerification.jointSq (x - r) (y - v) := by
  change vecSq (toFlatPrimal x - toFlatPrimal r) +
      vecSq (toFlatDual y - toFlatDual v) =
    vecSq (x - r) + vecSq (y - v)
  rw [← toFlatPrimal_sub, ← toFlatDual_sub,
    vecSq_toFlatPrimal, vecSq_toFlatDual]

theorem mem_diameterBall_toFlatDual_iff {M N : Nat} {D : ℝ}
    (y : Dual M N) :
    toFlatDual y ∈ diameterBall (M * N) D ↔
      y ∈ diameterBall (N * M) D := by
  simp only [diameterBall, Set.mem_setOf_eq, vecSq_toFlatDual]
  rfl

theorem mem_diameterBall_fromFlatDual_iff {M N : Nat} {D : ℝ}
    (z : FlatDual M N) :
    fromFlatDual z ∈ diameterBall (N * M) D ↔
      z ∈ diameterBall (M * N) D := by
  rw [← mem_diameterBall_toFlatDual_iff (fromFlatDual z)]
  simp

/-! ## Actual objective and actual gradients -/

/-- The current five-component objective in the exact framework types. -/
def objective {M N : Nat} (hN : 0 < N) (K : ℝ) :
    Primal M → Dual M N → ℝ :=
  fun x y => hardObjective hN K (primalState x) (primalA x) (primalB x)
    (dualBlock y)

theorem objective_eq_chainObjective {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) (y : Dual M N) :
    objective hN K x y =
      chainObjective hN K (serializeUnscaled x y) := by
  unfold objective chainObjective
  have hs : serializedState (serializeUnscaled x y) = primalState x := by
    funext i
    simp
  have ha : serializedA (serializeUnscaled x y) = primalA x := by
    funext i
    simp
  have hb : serializedB (serializeUnscaled x y) = primalB x := by
    funext i
    simp
  have hy : serializedDualBlock (serializeUnscaled x y) = dualBlock y := by
    funext i k
    simp [serializedDualBlock]
  rw [hs, ha, hb, hy]

theorem objective_eq_flatHardObjective {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) (y : Dual M N) :
    objective hN K x y =
      flatHardObjective hN K (toFlatPrimal x) (toFlatDual y) := by
  simp [objective, flatHardObjective]

theorem chainObjective_differentiable {M N : Nat} (hN : 0 < N) (K : ℝ) :
    Differentiable ℝ (chainObjective (M := M) hN K) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞)
      (saddleObjective (M := M - 1) hN K) :=
    saddleObjective_contDiff hN K
  have hdecode : ContDiff ℝ (⊤ : ℕ∞) (chainDecoded (M := M) (N := N)) := by
    unfold chainDecoded serializedState serializedA serializedB
      serializedDualBlock serializedY
    fun_prop
  have heq : chainObjective (M := M) hN K =
      saddleObjective hN K ∘ chainDecoded := by
    funext q
    exact chainObjective_eq_saddleObjective hN K q
  rw [heq]
  exact (hcd.comp hdecode).differentiable (by simp)

/-- The serialized Fréchet gradient, defined by coordinate extraction. -/
def chainTrueGradient {M N : Nat} (hN : 0 < N) (K : ℝ)
    (q : ChainSpace M N) : ChainSpace M N :=
  NCPLVerification.continuousLinearMapCoordinates
    (fderiv ℝ (chainObjective hN K) q)

theorem chainTrueGradient_eq_coordinateGradient {M N : Nat}
    (hN : 0 < N) (K : ℝ) (q : ChainSpace M N) :
    chainTrueGradient hN K q = coordinateGradient hN K q := by
  funext j
  have hu : HasDerivAt (fun t : ℝ => serializedCoordinateLine q j t)
      (NCPLVerification.evecBasis j) (q j) := by
    rw [hasDerivAt_pi]
    intro k
    convert (hasDerivAt_const (q j) (q k)).add
      (((hasDerivAt_id (q j)).sub_const (q j)).mul_const
        (NCPLVerification.evecBasis j k)) using 1
    · funext t
      rfl
    · ring
  have hline : serializedCoordinateLine q j (q j) = q := by
    funext k
    simp [serializedCoordinateLine]
  have hf : HasFDerivAt (chainObjective hN K)
      (fderiv ℝ (chainObjective hN K) q) q :=
    (chainObjective_differentiable hN K q).hasFDerivAt
  have hf' : HasFDerivAt (chainObjective hN K)
      (fderiv ℝ (chainObjective hN K) q)
      (serializedCoordinateLine q j (q j)) := by
    rw [hline]
    exact hf
  have hc := hf'.comp_hasDerivAt (q j) hu
  have hcoord : deriv
      (chainObjective hN K ∘ serializedCoordinateLine q j)
      (q j) = fderiv ℝ (chainObjective hN K) q
        (NCPLVerification.evecBasis j) := by
    exact hc.deriv
  unfold chainTrueGradient NCPLVerification.continuousLinearMapCoordinates
    coordinateGradient
  change fderiv ℝ (chainObjective hN K) q
      (NCPLVerification.evecBasis j) =
    deriv (chainObjective hN K ∘ serializedCoordinateLine q j) (q j)
  exact hcoord.symm

/-- Pull the actual serialized derivative back to primal directions. -/
def gradX {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) (y : Dual M N) : Primal M :=
  let g := chainTrueGradient hN K (serializeUnscaled x y)
  NCPLVerification.continuousLinearMapCoordinates
    ((NCPLVerification.evecDot g).comp
      (serializeUnscaledCLM.comp
        (ContinuousLinearMap.inl ℝ (Primal M) (Dual M N))))

/-- Pull the actual serialized derivative back to dual directions. -/
def gradY {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) (y : Dual M N) : Dual M N :=
  let g := chainTrueGradient hN K (serializeUnscaled x y)
  NCPLVerification.continuousLinearMapCoordinates
    ((NCPLVerification.evecDot g).comp
      (serializeUnscaledCLM.comp
        (ContinuousLinearMap.inr ℝ (Primal M) (Dual M N))))

theorem evecDot_chainTrueGradient {M N : Nat} (hN : 0 < N) (K : ℝ)
    (q : ChainSpace M N) :
    NCPLVerification.evecDot (chainTrueGradient hN K q) =
      fderiv ℝ (chainObjective hN K) q := by
  ext h
  simp only [NCPLVerification.evecDot_apply, chainTrueGradient]
  exact (NCPLVerification.continuousLinearMap_apply_eq_coordinates
    (fderiv ℝ (chainObjective hN K) q) h).symm

theorem objective_hasFDerivAt {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) (y : Dual M N) :
    HasFDerivAt (Function.uncurry (objective hN K))
      ((NCPLVerification.evecDot
        (chainTrueGradient hN K (serializeUnscaled x y))).comp
          serializeUnscaledCLM) (x, y) := by
  have hc : HasFDerivAt (chainObjective hN K)
      (fderiv ℝ (chainObjective hN K) (serializeUnscaled x y))
      (serializeUnscaled x y) :=
    (chainObjective_differentiable hN K _).hasFDerivAt
  rw [← evecDot_chainTrueGradient hN K (serializeUnscaled x y)] at hc
  have hcomp := hc.comp (x, y)
    (serializeUnscaledCLM (T := M + 1) (n := N)).hasFDerivAt
  have heq : Function.uncurry (objective (M := M) hN K) =
      chainObjective (M := M + 1) hN K ∘
        (serializeUnscaledCLM (T := M + 1) (n := N)) := by
    funext p
    exact objective_eq_chainObjective hN K p.1 p.2
  rw [heq]
  exact hcomp

/-- The fields stored below represent the actual joint Fréchet derivative. -/
theorem gradient_representation {M N : Nat} (hN : 0 < N) (K : ℝ) :
    NCPLVerification.RepresentsJointGradient (objective (M := M) hN K)
      (gradX (M := M) hN K) (gradY (M := M) hN K) := by
  constructor
  · rintro ⟨x, y⟩
    exact (objective_hasFDerivAt hN K x y).differentiableAt
  · intro x y hx hy
    let g := chainTrueGradient hN K (serializeUnscaled x y)
    let L := (NCPLVerification.evecDot g).comp serializeUnscaledCLM
    have hf : fderiv ℝ (Function.uncurry (objective hN K)) (x, y) = L :=
      (objective_hasFDerivAt hN K x y).fderiv
    rw [hf]
    have hdecomp : (hx, hy) = (hx, 0) + (0, hy) := by
      apply Prod.ext
      · funext i
        change hx i = hx i + 0
        ring
      · funext j
        change hy j = 0 + hy j
        ring
    rw [hdecomp, map_add]
    have hxcoord := NCPLVerification.continuousLinearMap_apply_eq_coordinates
      (L.comp (ContinuousLinearMap.inl ℝ (Primal M) (Dual M N))) hx
    have hycoord := NCPLVerification.continuousLinearMap_apply_eq_coordinates
      (L.comp (ContinuousLinearMap.inr ℝ (Primal M) (Dual M N))) hy
    change L (hx, 0) + L (0, hy) = _
    rw [show L (hx, 0) =
        (L.comp (ContinuousLinearMap.inl ℝ (Primal M) (Dual M N))) hx by rfl,
      show L (0, hy) =
        (L.comp (ContinuousLinearMap.inr ℝ (Primal M) (Dual M N))) hy by rfl,
      hxcoord, hycoord]
    rfl

/-! ## Identification with the independently verified signed zero-chain -/

private theorem primalAIndex_injective_local {T : Nat} :
    Function.Injective (primalAIndex (T := T)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val = 3 * j.val at hv
  omega

private theorem primalBIndex_injective_local {T : Nat} :
    Function.Injective (primalBIndex (T := T)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val + 1 = 3 * j.val + 1 at hv
  omega

private theorem primalStateIndex_injective_local {T : Nat} :
    Function.Injective (primalStateIndex (T := T)) := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  change 3 * i.val + 2 = 3 * j.val + 2 at hv
  omega

@[simp] private theorem primalAIndex_eq_iff_local {T : Nat}
    (i j : Fin (T - 1)) : primalAIndex i = primalAIndex j ↔ i = j :=
  primalAIndex_injective_local.eq_iff

@[simp] private theorem primalBIndex_eq_iff_local {T : Nat}
    (i j : Fin (T - 1)) : primalBIndex i = primalBIndex j ↔ i = j :=
  primalBIndex_injective_local.eq_iff

@[simp] private theorem primalStateIndex_eq_iff_local {T : Nat}
    (i j : Fin (T - 1)) : primalStateIndex i = primalStateIndex j ↔ i = j :=
  primalStateIndex_injective_local.eq_iff

private theorem primalAIndex_ne_BIndex_local {T : Nat}
    (i j : Fin (T - 1)) : primalAIndex i ≠ primalBIndex j := by
  intro h
  have hv := congrArg Fin.val h
  change 3 * i.val = 3 * j.val + 1 at hv
  omega

private theorem primalAIndex_ne_stateIndex_local {T : Nat}
    (i j : Fin (T - 1)) : primalAIndex i ≠ primalStateIndex j := by
  intro h
  have hv := congrArg Fin.val h
  change 3 * i.val = 3 * j.val + 2 at hv
  omega

private theorem primalBIndex_ne_stateIndex_local {T : Nat}
    (i j : Fin (T - 1)) : primalBIndex i ≠ primalStateIndex j := by
  intro h
  have hv := congrArg Fin.val h
  change 3 * i.val + 1 = 3 * j.val + 2 at hv
  omega

private theorem evecDot_basis {d : Nat} (g : NCCLowerBoundVerification.EVec d)
    (j : Fin d) :
    NCPLVerification.evecDot g (NCPLVerification.evecBasis j) = g j := by
  simp [NCPLVerification.evecDot_apply, NCPLVerification.evecBasis]

private theorem serialize_basis_A {T n : Nat} (i : Fin (T - 1)) :
    serializeUnscaled
        (NCPLVerification.evecBasis (primalAIndex i) : UnscaledPrimal T)
        (0 : UnscaledDual T n) =
      (NCPLVerification.evecBasis (serializedAIndex (n := n) i) :
        SerializedSpace T n) := by
  apply SerializedSpace.ext_blocks
  · intro j
    rw [serializedA_serializeUnscaled]
    simp [primalA, serializedA, NCPLVerification.evecBasis,
      primalAIndex_eq_iff_local]
  · intro j k
    rw [serializedY_serializeUnscaled]
    simp [dualBlock, serializedY, NCPLVerification.evecBasis,
      (serializedAIndex_ne_dualIndex i j k).symm]
  · intro j
    rw [serializedB_serializeUnscaled]
    simp [primalB, serializedB, NCPLVerification.evecBasis,
      (primalAIndex_ne_BIndex_local i j).symm,
      (serializedAIndex_ne_BIndex i j).symm]
  · intro j
    rw [serializedState_serializeUnscaled]
    simp [primalState, serializedState, NCPLVerification.evecBasis,
      (primalAIndex_ne_stateIndex_local i j).symm,
      (serializedAIndex_ne_stateIndex i j).symm]

private theorem serialize_basis_B {T n : Nat} (i : Fin (T - 1)) :
    serializeUnscaled
        (NCPLVerification.evecBasis (primalBIndex i) : UnscaledPrimal T)
        (0 : UnscaledDual T n) =
      (NCPLVerification.evecBasis (serializedBIndex (n := n) i) :
        SerializedSpace T n) := by
  apply SerializedSpace.ext_blocks
  · intro j
    rw [serializedA_serializeUnscaled]
    simp [primalA, serializedA, NCPLVerification.evecBasis,
      primalAIndex_ne_BIndex_local, serializedAIndex_ne_BIndex]
  · intro j k
    rw [serializedY_serializeUnscaled]
    simp [dualBlock, serializedY, NCPLVerification.evecBasis,
      (serializedBIndex_ne_dualIndex i j k).symm]
  · intro j
    rw [serializedB_serializeUnscaled]
    by_cases hji : j = i
    · subst j
      simp [primalB, serializedB, NCPLVerification.evecBasis]
    · have hp : primalBIndex j ≠ primalBIndex i :=
        fun h => hji (primalBIndex_injective_local h)
      have hs : serializedBIndex (n := n) j ≠ serializedBIndex i :=
        fun h => hji (serializedBIndex_injective h)
      simp [primalB, serializedB, NCPLVerification.evecBasis, hji, hp, hs]
  · intro j
    rw [serializedState_serializeUnscaled]
    simp [primalState, serializedState, NCPLVerification.evecBasis,
      (primalBIndex_ne_stateIndex_local i j).symm,
      (serializedBIndex_ne_stateIndex i j).symm]

private theorem serialize_basis_state {T n : Nat} (i : Fin (T - 1)) :
    serializeUnscaled
        (NCPLVerification.evecBasis (primalStateIndex i) : UnscaledPrimal T)
        (0 : UnscaledDual T n) =
      (NCPLVerification.evecBasis (serializedStateIndex (n := n) i) :
        SerializedSpace T n) := by
  apply SerializedSpace.ext_blocks
  · intro j
    rw [serializedA_serializeUnscaled]
    simp [primalA, serializedA, NCPLVerification.evecBasis,
      primalAIndex_ne_stateIndex_local, serializedAIndex_ne_stateIndex]
  · intro j k
    rw [serializedY_serializeUnscaled]
    simp [dualBlock, serializedY, NCPLVerification.evecBasis,
      (serializedStateIndex_ne_dualIndex i j k).symm]
  · intro j
    rw [serializedB_serializeUnscaled]
    simp [primalB, serializedB, NCPLVerification.evecBasis,
      primalBIndex_ne_stateIndex_local, serializedBIndex_ne_stateIndex]
  · intro j
    rw [serializedState_serializeUnscaled]
    by_cases hji : j = i
    · subst j
      simp [primalState, serializedState, NCPLVerification.evecBasis]
    · have hp : primalStateIndex j ≠ primalStateIndex i :=
        fun h => hji (primalStateIndex_injective_local h)
      have hs : serializedStateIndex (n := n) j ≠ serializedStateIndex i :=
        fun h => hji (serializedStateIndex_injective h)
      simp [primalState, serializedState, NCPLVerification.evecBasis,
        hji, hp, hs]

private theorem dualBlockIndexPair_dualBlockIndex {T n : Nat}
    (i : Fin (T - 1)) (k : Fin n) :
    dualBlockIndexPair (dualBlockIndex i k) = (i, k) := by
  unfold dualBlockIndexPair
  have hcast : Fin.cast (Nat.mul_comm n (T - 1)) (dualBlockIndex i k) =
      finProdFinEquiv (i, k) := by
    apply Fin.ext
    simp [dualBlockIndex, finProdFinEquiv]
    omega
  rw [hcast, Equiv.symm_apply_apply]

private theorem serialize_basis_Y {T n : Nat}
    (i : Fin (T - 1)) (k : Fin n) :
    serializeUnscaled (0 : UnscaledPrimal T)
        (NCPLVerification.evecBasis (dualBlockIndex i k) : UnscaledDual T n) =
      (NCPLVerification.evecBasis (serializedDualIndex i k) :
        SerializedSpace T n) := by
  apply SerializedSpace.ext_blocks
  · intro j
    rw [serializedA_serializeUnscaled]
    simp [primalA, serializedA, NCPLVerification.evecBasis,
      serializedAIndex_ne_dualIndex]
  · intro j l
    rw [serializedY_serializeUnscaled]
    unfold dualBlock serializedY NCPLVerification.evecBasis
    by_cases hji : j = i
    · subst j
      by_cases hlk : l = k
      · subst l
        simp
      · have hd : dualBlockIndex i l ≠ dualBlockIndex i k := by
          intro h
          have hp := congrArg dualBlockIndexPair h
          rw [dualBlockIndexPair_dualBlockIndex,
            dualBlockIndexPair_dualBlockIndex] at hp
          exact hlk (congrArg Prod.snd hp)
        have hs : serializedDualIndex i l ≠ serializedDualIndex i k := by
          intro h
          have hp : (i, l) = (i, k) := serializedDualIndex_injective h
          exact hlk (congrArg Prod.snd hp)
        simp [hd, hs]
    · have hd : dualBlockIndex j l ≠ dualBlockIndex i k := by
        intro h
        have hp := congrArg dualBlockIndexPair h
        rw [dualBlockIndexPair_dualBlockIndex,
          dualBlockIndexPair_dualBlockIndex] at hp
        exact hji (congrArg Prod.fst hp)
      have hs : serializedDualIndex j l ≠ serializedDualIndex i k := by
        intro h
        have hp : (j, l) = (i, k) := serializedDualIndex_injective h
        exact hji (congrArg Prod.fst hp)
      simp [hd, hs]
  · intro j
    rw [serializedB_serializeUnscaled]
    simp [primalB, serializedB, NCPLVerification.evecBasis,
      serializedBIndex_ne_dualIndex]
  · intro j
    rw [serializedState_serializeUnscaled]
    simp [primalState, serializedState, NCPLVerification.evecBasis,
      serializedStateIndex_ne_dualIndex]

theorem primalA_gradX {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) (y : Dual M N) (i : Fin M) :
    primalA (gradX hN K x y) i =
      chainTrueGradient hN K (serializeUnscaled x y)
        (serializedAIndex (n := N) i) := by
  let g := chainTrueGradient hN K (serializeUnscaled x y)
  change ((NCPLVerification.evecDot g).comp
    (serializeUnscaledCLM.comp
      (ContinuousLinearMap.inl ℝ (Primal M) (Dual M N))))
        (NCPLVerification.evecBasis (primalAIndex i)) = _
  simp only [ContinuousLinearMap.comp_apply, serializeUnscaledCLM_apply,
    ContinuousLinearMap.inl_apply]
  rw [serialize_basis_A]
  exact evecDot_basis g (serializedAIndex i)

theorem primalB_gradX {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) (y : Dual M N) (i : Fin M) :
    primalB (gradX hN K x y) i =
      chainTrueGradient hN K (serializeUnscaled x y)
        (serializedBIndex (n := N) i) := by
  let g := chainTrueGradient hN K (serializeUnscaled x y)
  change ((NCPLVerification.evecDot g).comp
    (serializeUnscaledCLM.comp
      (ContinuousLinearMap.inl ℝ (Primal M) (Dual M N))))
        (NCPLVerification.evecBasis (primalBIndex i)) = _
  simp only [ContinuousLinearMap.comp_apply, serializeUnscaledCLM_apply,
    ContinuousLinearMap.inl_apply]
  rw [serialize_basis_B]
  exact evecDot_basis g (serializedBIndex i)

theorem primalState_gradX {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) (y : Dual M N) (i : Fin M) :
    primalState (gradX hN K x y) i =
      chainTrueGradient hN K (serializeUnscaled x y)
        (serializedStateIndex (n := N) i) := by
  let g := chainTrueGradient hN K (serializeUnscaled x y)
  change ((NCPLVerification.evecDot g).comp
    (serializeUnscaledCLM.comp
      (ContinuousLinearMap.inl ℝ (Primal M) (Dual M N))))
        (NCPLVerification.evecBasis (primalStateIndex i)) = _
  simp only [ContinuousLinearMap.comp_apply, serializeUnscaledCLM_apply,
    ContinuousLinearMap.inl_apply]
  rw [serialize_basis_state]
  exact evecDot_basis g (serializedStateIndex i)

theorem dualBlock_gradY {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) (y : Dual M N) (i : Fin M) (k : Fin N) :
    dualBlock (gradY hN K x y) i k =
      chainTrueGradient hN K (serializeUnscaled x y)
        (serializedDualIndex i k) := by
  let g := chainTrueGradient hN K (serializeUnscaled x y)
  change ((NCPLVerification.evecDot g).comp
    (serializeUnscaledCLM.comp
      (ContinuousLinearMap.inr ℝ (Primal M) (Dual M N))))
        (NCPLVerification.evecBasis (dualBlockIndex i k)) = _
  simp only [ContinuousLinearMap.comp_apply, serializeUnscaledCLM_apply,
    ContinuousLinearMap.inr_apply]
  rw [serialize_basis_Y]
  exact evecDot_basis g (serializedDualIndex i k)

theorem gradX_eq_unserializePrimal {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) (y : Dual M N) :
    gradX hN K x y = unserializePrimal
      (chainTrueGradient hN K (serializeUnscaled x y)) := by
  funext j
  obtain ⟨c, hc⟩ := UnscaledTag.primalIndex_surjective
    (T := M + 1) (n := N) j
  cases c with
  | a i =>
      simp [UnscaledTag.primalIndex] at hc
      subst j
      change primalA (gradX hN K x y) i = _
      rw [primalA_gradX]
      change _ = primalA (unserializePrimal
        (chainTrueGradient hN K (serializeUnscaled x y))) i
      rw [primalA_unserializePrimal]
      rfl
  | y i k => simp [UnscaledTag.primalIndex] at hc
  | b i =>
      simp [UnscaledTag.primalIndex] at hc
      subst j
      change primalB (gradX hN K x y) i = _
      rw [primalB_gradX]
      change _ = primalB (unserializePrimal
        (chainTrueGradient hN K (serializeUnscaled x y))) i
      rw [primalB_unserializePrimal]
      rfl
  | state i =>
      simp [UnscaledTag.primalIndex] at hc
      subst j
      change primalState (gradX hN K x y) i = _
      rw [primalState_gradX]
      change _ = primalState (unserializePrimal
        (chainTrueGradient hN K (serializeUnscaled x y))) i
      rw [primalState_unserializePrimal]
      rfl

theorem gradY_eq_unserializeDual {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) (y : Dual M N) :
    gradY hN K x y = unserializeDual
      (chainTrueGradient hN K (serializeUnscaled x y)) := by
  funext j
  obtain ⟨c, hc⟩ := UnscaledTag.dualIndex_surjective
    (T := M + 1) (n := N) j
  cases c with
  | a i => simp [UnscaledTag.dualIndex] at hc
  | y i k =>
      simp [UnscaledTag.dualIndex] at hc
      subst j
      change dualBlock (gradY hN K x y) i k = _
      rw [dualBlock_gradY]
      change _ = dualBlock (unserializeDual
        (chainTrueGradient hN K (serializeUnscaled x y))) i k
      rw [dualBlock_unserializeDual]
      rfl
  | b i => simp [UnscaledTag.dualIndex] at hc
  | state i => simp [UnscaledTag.dualIndex] at hc

/-- Pack/unpack of a serialized gradient, with the dual sign flip. -/
def packedSigned {T N : Nat} (g : ChainSpace T N) : ChainSpace T N :=
  serializeUnscaled (unserializePrimal g) (-unserializeDual g)

theorem packedSigned_eq_signedCoordinateField {T N : Nat}
    (hN : 0 < N) (K : ℝ) (q : ChainSpace T N) :
    packedSigned (chainTrueGradient hN K q) = signedCoordinateField hN K q := by
  classical
  rw [chainTrueGradient_eq_coordinateGradient]
  apply SerializedSpace.ext_blocks
  · intro i
    simp only [packedSigned]
    rw [serializedA_serializeUnscaled, primalA_unserializePrimal]
    unfold signedCoordinateField serializedA
    simp [serializedAIndex_ne_dualIndex, serializedAIndex_ne_BIndex,
      serializedAIndex_ne_stateIndex]
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hci
      have hne : serializedAIndex (n := N) c ≠ serializedAIndex i :=
        fun h => hci (serializedAIndex_injective h)
      simp [hne]
    · simp
  · intro i k
    simp only [packedSigned]
    rw [serializedY_serializeUnscaled]
    simp only [dualBlock, Pi.neg_apply]
    unfold unserializeDual
    rw [show dualBlockIndexPair (dualBlockIndex i k) = (i, k) from
      dualBlockIndexPair_dualBlockIndex i k]
    unfold signedCoordinateField serializedY
    simp [serializedAIndex_ne_dualIndex, serializedBIndex_ne_dualIndex,
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
    simp only [packedSigned]
    rw [serializedB_serializeUnscaled, primalB_unserializePrimal]
    unfold signedCoordinateField serializedB
    simp [serializedAIndex_ne_BIndex, serializedBIndex_ne_dualIndex,
      serializedBIndex_ne_stateIndex]
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hci
      have hne : serializedBIndex (n := N) c ≠ serializedBIndex i :=
        fun h => hci (serializedBIndex_injective h)
      simp [hne]
    · simp
  · intro i
    simp only [packedSigned]
    rw [serializedState_serializeUnscaled, primalState_unserializePrimal]
    unfold signedCoordinateField serializedState
    simp [serializedAIndex_ne_stateIndex, serializedBIndex_ne_stateIndex,
      serializedStateIndex_ne_dualIndex]
    rw [Finset.sum_eq_single i]
    · simp
    · intro c _ hci
      have hne : serializedStateIndex (n := N) c ≠
          serializedStateIndex i :=
        fun h => hci (serializedStateIndex_injective h)
      simp [hne]
    · simp

theorem tagged_field_eq_signedCoordinateField {M N : Nat}
    (hN : 0 < N) (K : ℝ) :
    taggedSerializedSaddleFieldOf (gradX (M := M) hN K) (gradY hN K) =
      signedCoordinateField (M := M + 1) hN K := by
  funext q
  unfold taggedSerializedSaddleFieldOf
  rw [gradX_eq_unserializePrimal, gradY_eq_unserializeDual]
  simp only [serializeUnscaled_unserialize]
  exact packedSigned_eq_signedCoordinateField hN K q

theorem saddle_zero_chain {M N : Nat} (hN : 0 < N) (K : ℝ) :
    NCPLVerification.IsFirstOrderZeroChain
      (taggedSerializedSaddleFieldOf (gradX (M := M) hN K) (gradY hN K)) := by
  rw [tagged_field_eq_signedCoordinateField hN K]
  exact signedCoordinateField_isFirstOrderZeroChain hN K

/-! ## Literal finite and unbounded maxima -/

def outerValue {M : Nat} (K : ℝ) (x : Primal M) : ℝ :=
  outerComponent K (primalState x) (primalA x) (primalB x)

theorem objective_eq_outer_add_inner {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) (y : Dual M N) :
    objective hN K x y = outerValue K x +
      innerObjective hN (toPulse x) (toFlatDual y) := by
  simp [objective, outerValue, innerObjective, hardObjective, toFlatDual]

/-- The chosen finite-ball maximizer, transported through the dual
coordinate permutation. -/
def finiteMaximizer {M N : Nat} (hN : 0 < N) (D : ℝ) (hD : 0 ≤ D)
    (x : Primal M) : Dual M N :=
  fromFlatDual (InnerFiniteBall.finiteMaximizer hN D hD (toPulse x))

theorem finiteMaximizer_spec {M N : Nat} (hN : 0 < N)
    (K D : ℝ) (hD : 0 ≤ D) (x : Primal M) :
    IsMaximizerOn (diameterBall (N * M) D) (objective hN K) x
      (finiteMaximizer hN D hD x) := by
  let z := InnerFiniteBall.finiteMaximizer hN D hD (toPulse x)
  have hz := InnerFiniteBall.finiteMaximizer_spec hN D hD (toPulse x)
  refine ⟨(mem_diameterBall_fromFlatDual_iff z).2 hz.1, ?_⟩
  intro y hy
  rw [objective_eq_outer_add_inner, objective_eq_outer_add_inner]
  have hmax := hz.2 (toFlatDual y)
    ((mem_diameterBall_toFlatDual_iff y).2 hy)
  simpa [finiteMaximizer, z] using
    add_le_add_left hmax (outerValue K x)

/-- The exact Green-kernel maximizer in framework dual storage. -/
def unconstrainedMaximizer {M N : Nat} (hN : 0 < N)
    (x : Primal M) : Dual M N :=
  fromFlatDual (InnerFiniteBall.unboundedMaximizer hN (toPulse x))

theorem unconstrainedMaximizer_spec {M N : Nat} (hN : 0 < N)
    (K : ℝ) (x : Primal M) :
    IsMaximizerOn Set.univ (objective hN K) x
      (unconstrainedMaximizer hN x) := by
  let z := InnerFiniteBall.unboundedMaximizer hN (toPulse x)
  have hz := InnerFiniteBall.unboundedMaximizer_spec hN (toPulse x)
  refine ⟨Set.mem_univ _, ?_⟩
  intro y _
  rw [objective_eq_outer_add_inner, objective_eq_outer_add_inner]
  have hmax := hz.2 (toFlatDual y) (Set.mem_univ _)
  simpa [unconstrainedMaximizer, z] using
    add_le_add_left hmax (outerValue K x)

/-! ## Exact value identities and actual value gradients -/

def finiteSourceValue {M N : Nat} (hN : 0 < N) (K D : ℝ) :
    Primal M → ℝ :=
  ValueOn (diameterBall (N * M) D) (objective hN K)

def unboundedSourceValue {M N : Nat} (hN : 0 < N) (K : ℝ) :
    Primal M → ℝ := ValueOn Set.univ (objective hN K)

theorem finiteSourceValue_eq {M N : Nat} (hN : 0 < N) (K D : ℝ)
    (hD : 0 ≤ D) (x : Primal M) :
    finiteSourceValue hN K D x = outerValue K x +
      InnerFiniteBall.finiteValue hN D (toPulse x) := by
  rw [show finiteSourceValue hN K D x =
      objective hN K x (finiteMaximizer hN D hD x) by
    exact value_eq_of_isMaximizerOn (finiteMaximizer_spec hN K D hD x)]
  rw [show InnerFiniteBall.finiteValue hN D (toPulse x) =
      innerObjective hN (toPulse x)
        (InnerFiniteBall.finiteMaximizer hN D hD (toPulse x)) by
    exact value_eq_of_isMaximizerOn
      (InnerFiniteBall.finiteMaximizer_spec hN D hD (toPulse x))]
  exact objective_eq_outer_add_inner hN K x
    (finiteMaximizer hN D hD x)

theorem unboundedSourceValue_eq {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : Primal M) :
    unboundedSourceValue hN K x = outerValue K x +
      InnerFiniteBall.unboundedValue hN (toPulse x) := by
  rw [show unboundedSourceValue hN K x =
      objective hN K x (unconstrainedMaximizer hN x) by
    exact value_eq_of_isMaximizerOn (unconstrainedMaximizer_spec hN K x)]
  rw [show InnerFiniteBall.unboundedValue hN (toPulse x) =
      innerObjective hN (toPulse x)
        (InnerFiniteBall.unboundedMaximizer hN (toPulse x)) by
    exact value_eq_of_isMaximizerOn
      (InnerFiniteBall.unboundedMaximizer_spec hN (toPulse x))]
  exact objective_eq_outer_add_inner hN K x (unconstrainedMaximizer hN x)

theorem toPulse_differentiable {M : Nat} :
    Differentiable ℝ (toPulse (M := M)) := by
  rw [differentiable_pi]
  intro j
  unfold toPulse
  dsimp only
  split
  · exact differentiable_apply _
  · exact differentiable_apply _

theorem decodeFrameworkPrimal_contDiff {M : Nat} :
    ContDiff ℝ (⊤ : ℕ∞) (decodeFrameworkPrimal (M := M)) := by
  unfold decodeFrameworkPrimal primalState primalA primalB
  fun_prop

theorem outerValue_differentiable {M : Nat} (K : ℝ) :
    Differentiable ℝ (outerValue (M := M) K) := by
  have h := (outerComponent_contDiff (M := M) K).comp
    decodeFrameworkPrimal_contDiff
  have heq : outerValue (M := M) K =
      (fun z : PrimalPoint M => outerComponent K z.1 z.2.1 z.2.2) ∘
        decodeFrameworkPrimal := by
    rfl
  rw [heq]
  exact h.differentiable (by simp)

theorem finiteSourceValue_differentiable {M N : Nat} (hN : 0 < N)
    (K : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    Differentiable ℝ (finiteSourceValue (M := M) hN K D) := by
  have heq : finiteSourceValue (M := M) hN K D = fun x =>
      outerValue K x + InnerFiniteBall.finiteValue hN D (toPulse x) := by
    funext x
    exact finiteSourceValue_eq hN K D hD x
  rw [heq]
  exact (outerValue_differentiable K).add
    ((InnerFiniteBall.finiteValue_differentiable hN hD).comp
      toPulse_differentiable)

theorem unboundedSourceValue_differentiable {M N : Nat} (hN10 : 10 ≤ N)
    (K : ℝ) :
    Differentiable ℝ
      (unboundedSourceValue (M := M) (by omega : 0 < N) K) := by
  have heq : unboundedSourceValue (M := M) (by omega : 0 < N) K = fun x =>
      outerValue K x +
        InnerFiniteBall.unboundedValue (by omega : 0 < N) (toPulse x) := by
    funext x
    exact unboundedSourceValue_eq (by omega : 0 < N) K x
  rw [heq]
  exact (outerValue_differentiable K).add
    ((InnerFiniteBall.unboundedValue_differentiable hN10).comp
      toPulse_differentiable)

def scopedValue {M N : Nat} (hN : 0 < N) (K : ℝ) :
    Framework.DualScope → Primal M → ℝ
  | .finite D _ => finiteSourceValue hN K D
  | .unbounded => unboundedSourceValue hN K

/-- The actual coordinate gradient of each actual `ValueOn`. -/
def valueGrad {M N : Nat} (hN : 0 < N) (K : ℝ)
    (q : Framework.DualScope) (x : Primal M) : Primal M :=
  NCPLVerification.continuousLinearMapCoordinates
    (fderiv ℝ (scopedValue hN K q) x)

theorem scopedValue_eq_ValueOn {M N : Nat} (hN : 0 < N) (K : ℝ)
    (q : Framework.DualScope) :
    scopedValue (M := M) hN K q =
      ValueOn (Framework.dualDomain (N * M) q) (objective hN K) := by
  cases q <;> rfl

theorem scopedValue_differentiable {M N : Nat} (hN10 : 10 ≤ N)
    (K : ℝ) (q : Framework.DualScope) :
    Differentiable ℝ (scopedValue (M := M) (by omega : 0 < N) K q) := by
  cases q with
  | finite D hD => exact finiteSourceValue_differentiable (by omega) K hD.le
  | unbounded => exact unboundedSourceValue_differentiable hN10 K

theorem valueGrad_represents {M N : Nat} (hN10 : 10 ≤ N) (K : ℝ)
    (q : Framework.DualScope) :
    RepresentsGradient
      (ValueOn (Framework.dualDomain (N * M) q)
        (objective (by omega : 0 < N) K))
      (valueGrad (M := M) (by omega : 0 < N) K q) := by
  rw [← scopedValue_eq_ValueOn (M := M) (by omega : 0 < N) K q]
  constructor
  · exact scopedValue_differentiable hN10 K q
  · intro x h
    exact NCPLVerification.continuousLinearMap_apply_eq_coordinates
      (fderiv ℝ (scopedValue (by omega : 0 < N) K q) x) h

/-! ## Maximizer growth and the genuine initial gap -/

/-- A slightly slackened maximizer-growth constant.  The raw Green-kernel
bound is `20 * sqrt 20`; using `21 * sqrt 20` preserves that bound and turns
the framework's non-strict diameter hypothesis into the strict interior
margin required by the finite-ball inactivity theorem. -/
def currentCy : ℝ := 21 * Real.sqrt 20

theorem currentCy_pos : 0 < currentCy := by
  unfold currentCy
  positivity

/-- Numerical constants used by the small-gradient and terminal clauses. -/
def currentG0 : ℝ := 1 / 4

def currentCp : ℝ := 20

def currentTau0 : ℝ := 1 / 4

theorem currentG0_pos : 0 < currentG0 := by
  norm_num [currentG0]

theorem currentCp_pos : 0 < currentCp := by
  norm_num [currentCp]

theorem currentTau0_pos : 0 < currentTau0 := by
  norm_num [currentTau0]

def currentCDelta (K : ℝ) : ℝ := 154 + |phasePotential K 2|

theorem currentCDelta_pos (K : ℝ) : 0 < currentCDelta K := by
  unfold currentCDelta
  positivity

theorem primalPulseSq_toFlatPrimal {M : Nat} (x : Primal M) :
    RestrictedBall.primalPulseSq (toFlatPrimal x) = pulseSq x := by
  simp [RestrictedBall.primalPulseSq, pulseSq]
  rfl

theorem unconstrainedMaximizer_growth {M N : Nat} (hN10 : 10 ≤ N)
    (x : Primal M) :
    vecSq (unconstrainedMaximizer (by omega : 0 < N) x) ≤
      (currentCy * (N : ℝ)) ^ 2 * pulseSq x := by
  have hg := RestrictedBall.flatWStar_growth hN10 (toFlatPrimal x)
  have hmax : InnerFiniteBall.unboundedMaximizer (by omega : 0 < N)
      (toPulse x) =
      RestrictedBall.flatWStar (by omega : 0 < N) (toFlatPrimal x) := by
    unfold InnerFiniteBall.unboundedMaximizer RestrictedBall.flatWStar
    simp
  have hsqrt : Real.sqrt (20 : ℝ) ^ 2 = 20 :=
    Real.sq_sqrt (by norm_num)
  have hcy : currentCy ^ 2 = 8820 := by
    unfold currentCy
    nlinarith
  have hconst : (8000 : ℝ) ≤ currentCy ^ 2 := by
    rw [hcy]
    norm_num
  have hscale0 : 0 ≤ (N : ℝ) ^ 2 * pulseSq x :=
    mul_nonneg (sq_nonneg _) (Framework.pulseSq_nonneg x)
  rw [unconstrainedMaximizer, vecSq_fromFlatDual, hmax]
  rw [primalPulseSq_toFlatPrimal] at hg
  calc
    vecSq (RestrictedBall.flatWStar (by omega : 0 < N)
        (toFlatPrimal x)) ≤ 8000 * (N : ℝ) ^ 2 * pulseSq x := hg
    _ ≤ currentCy ^ 2 * (N : ℝ) ^ 2 * pulseSq x := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hconst hscale0
    _ = (currentCy * (N : ℝ)) ^ 2 * pulseSq x := by
      rw [mul_pow]

private theorem norm_sq_le_vecSq {d : Nat}
    (v : NCCLowerBoundVerification.EVec d) : ‖v‖ ^ 2 ≤ vecSq v := by
  have hn := NCCLowerBoundVerification.Upper.norm_le_sqrt_vecSq v
  have hs := Real.sq_sqrt (by
    unfold vecSq NCPLVerification.vecSq
    positivity : 0 ≤ vecSq v)
  nlinarith [norm_nonneg v, Real.sqrt_nonneg (vecSq v)]

/-- A dimension-dependent positive strong-concavity modulus suffices for C1;
only the joint smoothness constant must be dimension-free. -/
theorem objective_strongConcave {M N : Nat} (hN : 0 < N) (K : ℝ) :
    ∃ mu0 : ℝ, 0 < mu0 ∧
      ∀ x : Primal M, StrongConcaveOn Set.univ mu0 (objective hN K x) := by
  refine ⟨pathRegularization N, pathRegularization_pos hN, ?_⟩
  intro x
  refine ⟨convex_univ, ?_⟩
  intro y _hy z _hz a b ha hb hab
  have hb_eq : b = 1 - a := by linarith
  subst b
  have hcoef : 0 ≤ (pathRegularization N / 2) * a * (1 - a) := by
    exact mul_nonneg
      (mul_nonneg (div_nonneg (pathRegularization_pos hN).le (by norm_num)) ha)
      hb
  have hsum :
      (∑ i : Fin M,
        (a * correctedH hN (primalA x i) (primalB x i) (dualBlock y i) +
          (1 - a) * correctedH hN (primalA x i) (primalB x i)
            (dualBlock z i) +
          (pathRegularization N / 2) * a * (1 - a) *
            vecSq (dualBlock y i - dualBlock z i))) ≤
      ∑ i : Fin M,
        correctedH hN (primalA x i) (primalB x i)
          (a • dualBlock y i + (1 - a) • dualBlock z i) := by
    exact Finset.sum_le_sum fun i _ =>
      correctedH_strongConcave hN (primalA x i) (primalB x i)
        (dualBlock y i) (dualBlock z i) ha (by linarith)
  have hnorm : ‖y - z‖ ^ 2 ≤
      ∑ i : Fin M, vecSq (dualBlock y i - dualBlock z i) := by
    calc
      ‖y - z‖ ^ 2 ≤ vecSq (y - z) := norm_sq_le_vecSq (y - z)
      _ = ∑ i : Fin M, vecSq (dualBlock y i - dualBlock z i) := by
        rw [vecSq_eq_sum_dualBlock]
        rfl
  have hpen := mul_le_mul_of_nonneg_left hnorm hcoef
  have hinner :
      a * innerComponent hN (primalA x) (primalB x) (dualBlock y) +
        (1 - a) * innerComponent hN (primalA x) (primalB x) (dualBlock z) +
        (pathRegularization N / 2) * a * (1 - a) * ‖y - z‖ ^ 2 ≤
      innerComponent hN (primalA x) (primalB x)
        (dualBlock (a • y + (1 - a) • z)) := by
    have hblock (i : Fin M) :
        dualBlock (a • y + (1 - a) • z) i =
          a • dualBlock y i + (1 - a) • dualBlock z i := by
      rfl
    unfold innerComponent at hsum ⊢
    simp_rw [hblock]
    rw [Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
    have hpen' :
        (pathRegularization N / 2) * a * (1 - a) * ‖y - z‖ ^ 2 ≤
          ∑ i : Fin M,
            (pathRegularization N / 2) * a * (1 - a) *
              vecSq (dualBlock y i - dualBlock z i) := by
      rw [← Finset.mul_sum]
      exact hpen
    have hstep := add_le_add_right hpen'
      ((∑ i : Fin M,
          a * correctedH hN (primalA x i) (primalB x i) (dualBlock y i)) +
        ∑ i : Fin M,
          (1 - a) * correctedH hN (primalA x i) (primalB x i) (dualBlock z i))
    exact hstep.trans hsum
  unfold objective hardObjective
  simp only [smul_eq_mul]
  have hout := outerValue K x
  change a * (outerComponent K (primalState x) (primalA x) (primalB x) +
        innerComponent hN (primalA x) (primalB x) (dualBlock y)) +
      (1 - a) * (outerComponent K (primalState x) (primalA x) (primalB x) +
        innerComponent hN (primalA x) (primalB x) (dualBlock z)) +
      a * (1 - a) * (pathRegularization N / 2 * ‖y - z‖ ^ 2) ≤
    outerComponent K (primalState x) (primalA x) (primalB x) +
      innerComponent hN (primalA x) (primalB x)
        (dualBlock (a • y + (1 - a) • z))
  nlinarith

@[simp] theorem primalA_zero {M : Nat} :
    primalA (0 : Primal M) = 0 := by rfl

@[simp] theorem primalB_zero {M : Nat} :
    primalB (0 : Primal M) = 0 := by rfl

@[simp] theorem primalState_zero {M : Nat} :
    primalState (0 : Primal M) = 0 := by rfl

@[simp] theorem dualBlock_zero {M N : Nat} :
    dualBlock (0 : Dual M N) = 0 := by rfl

theorem objective_origin_le_zero {M N : Nat} (hN : 0 < N) (K : ℝ)
    (y : Dual M N) : objective hN K 0 y ≤ 0 := by
  have hinner : innerComponent hN (primalA (0 : Primal M))
      (primalB (0 : Primal M)) (dualBlock y) ≤ 0 := by
    unfold innerComponent
    exact Finset.sum_nonpos fun i _ => correctedH_zero_primal_nonpos hN _
  have hout : outerComponent K (primalState (0 : Primal M))
      (primalA (0 : Primal M)) (primalB (0 : Primal M)) = 0 := by
    rw [primalState_zero, primalA_zero, primalB_zero]
    exact outerComponent_origin K
  rw [objective, hardObjective, hout]
  linarith

theorem objective_origin_zero {M N : Nat} (hN : 0 < N) (K : ℝ) :
    objective (M := M) hN K 0 0 = 0 := by
  rw [objective, primalState_zero, primalA_zero, primalB_zero, dualBlock_zero]
  exact Composite.hardObjective_origin (M := (M + 1) - 1) hN K

theorem finiteSourceValue_origin {M N : Nat} (hN : 0 < N)
    (K D : ℝ) (hD : 0 ≤ D) : finiteSourceValue (M := M) hN K D 0 = 0 := by
  rw [show finiteSourceValue (M := M) hN K D 0 =
      objective hN K 0 (finiteMaximizer hN D hD 0) by
    exact value_eq_of_isMaximizerOn (finiteMaximizer_spec hN K D hD 0)]
  apply le_antisymm
  · exact objective_origin_le_zero hN K _
  · rw [← objective_origin_zero (M := M) hN K]
    exact (finiteMaximizer_spec hN K D hD 0).2 0
      (zero_mem_diameterBall (N * M) D hD)

theorem unboundedSourceValue_origin {M N : Nat} (hN : 0 < N) (K : ℝ) :
    unboundedSourceValue (M := M) hN K 0 = 0 := by
  rw [show unboundedSourceValue (M := M) hN K 0 =
      objective hN K 0 (unconstrainedMaximizer hN 0) by
    exact value_eq_of_isMaximizerOn (unconstrainedMaximizer_spec hN K 0)]
  apply le_antisymm
  · exact objective_origin_le_zero hN K _
  · rw [← objective_origin_zero (M := M) hN K]
    exact (unconstrainedMaximizer_spec hN K 0).2 0 (Set.mem_univ _)

theorem finiteSourceValue_lower {M N : Nat} (hN10 : 10 ≤ N)
    {K D : ℝ} (hK : 0 < K) (hD : 0 ≤ D) (x : Primal M) :
    -(M : ℝ) * currentCDelta K ≤
      finiteSourceValue (by omega : 0 < N) K D x := by
  let hN : 0 < N := by omega
  have hzero := Composite.hardObjective_at_zeroDual_lower hN10 hK
    (primalState x) (primalA x) (primalB x)
  have hmax := (finiteMaximizer_spec hN K D hD x).2 0
    (zero_mem_diameterBall (N * M) D hD)
  rw [show finiteSourceValue hN K D x =
      objective hN K x (finiteMaximizer hN D hD x) by
    exact value_eq_of_isMaximizerOn (finiteMaximizer_spec hN K D hD x)]
  have hzero' : -(M : ℝ) * currentCDelta K ≤ objective hN K x 0 := by
    rw [objective, dualBlock_zero]
    change -(M : ℝ) * currentCDelta K ≤
      hardObjective hN K (primalState x) (primalA x) (primalB x)
        (fun _ _ => 0)
    simpa [currentCDelta] using hzero
  exact hzero'.trans hmax

theorem unboundedSourceValue_lower {M N : Nat} (hN10 : 10 ≤ N)
    {K : ℝ} (hK : 0 < K) (x : Primal M) :
    -(M : ℝ) * currentCDelta K ≤
      unboundedSourceValue (by omega : 0 < N) K x := by
  let hN : 0 < N := by omega
  have hzero := Composite.hardObjective_at_zeroDual_lower hN10 hK
    (primalState x) (primalA x) (primalB x)
  have hmax := (unconstrainedMaximizer_spec hN K x).2 0 (Set.mem_univ _)
  rw [show unboundedSourceValue hN K x =
      objective hN K x (unconstrainedMaximizer hN x) by
    exact value_eq_of_isMaximizerOn (unconstrainedMaximizer_spec hN K x)]
  have hzero' : -(M : ℝ) * currentCDelta K ≤ objective hN K x 0 := by
    rw [objective, dualBlock_zero]
    change -(M : ℝ) * currentCDelta K ≤
      hardObjective hN K (primalState x) (primalA x) (primalB x)
        (fun _ _ => 0)
    simpa [currentCDelta] using hzero
  exact hzero'.trans hmax

theorem scopedValue_lower {M N : Nat} (hN10 : 10 ≤ N)
    {K : ℝ} (hK : 0 < K) (q : Framework.DualScope) (x : Primal M) :
    -(M : ℝ) * currentCDelta K ≤
      scopedValue (by omega : 0 < N) K q x := by
  cases q with
  | finite D hD => exact finiteSourceValue_lower hN10 hK hD.le x
  | unbounded => exact unboundedSourceValue_lower hN10 hK x

theorem scopedValue_origin {M N : Nat} (hN10 : 10 ≤ N)
    (K : ℝ) (q : Framework.DualScope) :
    scopedValue (M := M) (by omega : 0 < N) K q 0 = 0 := by
  cases q with
  | finite D hD => exact finiteSourceValue_origin (by omega) K D hD.le
  | unbounded => exact unboundedSourceValue_origin (by omega) K

theorem scopedValue_bddBelow {M N : Nat} (hN10 : 10 ≤ N)
    {K : ℝ} (hK : 0 < K) (q : Framework.DualScope) :
    BddBelow (Set.range (scopedValue (M := M) (by omega : 0 < N) K q)) := by
  refine ⟨-(M : ℝ) * currentCDelta K, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact scopedValue_lower hN10 hK q x

theorem scopedValue_initial_gap {M N : Nat} (hN10 : 10 ≤ N)
    {K : ℝ} (hK : 0 < K) (q : Framework.DualScope) :
    scopedValue (M := M) (by omega : 0 < N) K q 0 -
        sInf (Set.range (scopedValue (M := M) (by omega : 0 < N) K q)) ≤
      currentCDelta K * (M + 1) := by
  have hinf : -(M : ℝ) * currentCDelta K ≤
      sInf (Set.range (scopedValue (M := M) (by omega : 0 < N) K q)) := by
    rw [le_csInf_iff (scopedValue_bddBelow hN10 hK q)
      (Set.range_nonempty _)]
    rintro _ ⟨x, rfl⟩
    exact scopedValue_lower hN10 hK q x
  rw [scopedValue_origin hN10 K q]
  have hc := (currentCDelta_pos K).le
  push_cast
  nlinarith

/-- The literal current construction, now packaged as framework data. -/
def currentHardData {M N : Nat} (hN : 0 < N) (K : ℝ) :
    Framework.UnscaledHardData M N where
  f := objective hN K
  gradX := gradX hN K
  gradY := gradY hN K
  valueGrad := valueGrad hN K
  unconstrainedMaximizer := unconstrainedMaximizer hN

/-- Assemble every framework field whose proof is intrinsic to this file.

The four hypotheses are precisely the remaining cross-file certificates:
the transported joint-smoothness estimate, finite/unbounded inactivity, and
the two terminal obstructions.  This theorem contains no proxy gradients or
proxy values: all clauses mention `currentHardData`, hence the actual
Fréchet derivatives defined above. -/
theorem currentHardProperties_of_certificates {M N : Nat}
    (hN10 : 10 ≤ N) (K ell0 : ℝ) (hK : 0 < K) (hell0 : 0 < ell0)
    (hsmooth : NCPLVerification.IsJointlySmooth ell0
      (gradX (M := M) (by omega : 0 < N) K)
      (gradY (M := M) (by omega : 0 < N) K))
    (hinactive : ∀ q x,
      Framework.terminalStateValue x ≤ (1 / 5 : ℝ) →
      vecSq (valueGrad (M := M) (N := N) (by omega : 0 < N) K q x) ≤
        currentTau0 ^ 2 →
      pulseSq x ≤ currentCp ^ 2)
    (hterminalFinite : ∀ (D : ℝ) (hD : 0 < D) (x : Primal M),
      (N : ℝ) ≤ D / (2 * currentCy * currentCp) →
      Framework.terminalStateValue x ≤ (1 / 5 : ℝ) →
      currentG0 ^ 2 ≤
        vecSq (valueGrad (M := M) (N := N) (by omega : 0 < N) K
          (.finite D hD) x))
    (hterminalUnbounded : ∀ x : Primal M,
      Framework.terminalStateValue x ≤ (1 / 5 : ℝ) →
      currentG0 ^ 2 ≤
        vecSq (valueGrad (M := M) (N := N) (by omega : 0 < N) K
          .unbounded x)) :
    Framework.UnscaledHardProperties
      (currentHardData (M := M) (N := N) (by omega : 0 < N) K)
      ell0 currentG0 (currentCDelta K) currentCy currentCp currentTau0 := by
  let hN : 0 < N := by omega
  refine
    { ell0_pos := hell0
      g0_pos := currentG0_pos
      cDelta_pos := currentCDelta_pos K
      cy_pos := currentCy_pos
      cp_pos := currentCp_pos
      tau0_pos := currentTau0_pos
      c1_gradient_representation := ?_
      c1_jointly_smooth := ?_
      c1_dual_strongly_concave := ?_
      c1_maximum_attained := ?_
      c1_value_gradient := ?_
      c2_saddle_zero_chain := ?_
      c3_unconstrained_isMaximizer := ?_
      c3_maximizer_growth := ?_
      c3_dual_inactivity := ?_
      c3_terminal_finite := ?_
      c3_terminal_unbounded := ?_
      c4_value_bddBelow := ?_
      c4_initial_gap := ?_ }
  · simpa [currentHardData] using gradient_representation (M := M) hN K
  · simpa [currentHardData] using hsmooth
  · simpa [currentHardData] using objective_strongConcave (M := M) hN K
  · intro q x
    cases q with
    | finite D hD =>
        exact ⟨finiteMaximizer hN D hD.le x, by
          simpa [currentHardData, Framework.dualDomain] using
            finiteMaximizer_spec hN K D hD.le x⟩
    | unbounded =>
        exact ⟨unconstrainedMaximizer hN x, by
          simpa [currentHardData, Framework.dualDomain] using
            unconstrainedMaximizer_spec hN K x⟩
  · intro q
    simpa [currentHardData] using valueGrad_represents (M := M) hN10 K q
  · simpa [currentHardData] using saddle_zero_chain (M := M) hN K
  · intro x
    simpa [currentHardData] using unconstrainedMaximizer_spec hN K x
  · intro x
    simpa [currentHardData] using unconstrainedMaximizer_growth (M := M) hN10 x
  · simpa [currentHardData] using hinactive
  · simpa [currentHardData] using hterminalFinite
  · simpa [currentHardData] using hterminalUnbounded
  · intro q
    change BddBelow (Set.range
      (ValueOn (Framework.dualDomain (N * M) q) (objective hN K)))
    rw [← scopedValue_eq_ValueOn (M := M) hN K q]
    exact scopedValue_bddBelow hN10 hK q
  · intro q
    change ValueOn (Framework.dualDomain (N * M) q) (objective hN K) 0 -
        sInf (Set.range
          (ValueOn (Framework.dualDomain (N * M) q) (objective hN K))) ≤
      currentCDelta K * (M + 1)
    rw [← scopedValue_eq_ValueOn (M := M) hN K q]
    exact scopedValue_initial_gap hN10 hK q

end

end CurrentHardData
end Simplified
end NCCLowerBound
