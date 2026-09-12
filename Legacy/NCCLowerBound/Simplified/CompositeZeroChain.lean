import NCCLowerBound.Simplified.CompositeProperties
import NCCLowerBoundVerification.Lower.UnscaledObjective

/-!
# The genuine signed first-order zero-chain of the simplified hard instance

The coordinates are serialized block by block in the literal order
`(a_i, y^i_1, ..., y^i_N, b_i, s_i)`.  Unlike a merely algebraic support
certificate, `coordinateGradient` below is obtained by differentiating the
actual objective along each affine coordinate line.  The dual entries are
then sign-flipped.
-/

namespace NCCLowerBound
namespace Simplified
namespace CompositeZeroChain

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators
open Composite CompositeProperties InnerRelay
open NCCLowerBoundVerification

/-! ## Literal serialization and objective -/

/-- `T - 1` blocks, each of width `N+3`.  We retain the serialization
parameter `T` from the verified framework so every block index is literally
`Fin (T - 1)` (and not merely propositionally equal to it). -/
abbrev ChainSpace (T N : Nat) := SerializedSpace T N

abbrev ChainIndex (T N : Nat) := Fin ((T - 1) * (N + 3))

def chainObjective {M N : Nat} (hN : 0 < N) (K : ℝ)
    (q : ChainSpace M N) : ℝ :=
  hardObjective hN K (serializedState q) (serializedA q) (serializedB q)
    (serializedDualBlock q)

def chainDecoded {M N : Nat} (q : ChainSpace M N) :
    SaddlePoint (M - 1) N :=
  ((serializedState q, serializedA q, serializedB q), serializedDualBlock q)

theorem chainObjective_eq_saddleObjective {M N : Nat} (hN : 0 < N)
    (K : ℝ) (q : ChainSpace M N) :
    chainObjective hN K q = saddleObjective hN K (chainDecoded q) := by
  rfl

/-! ## Actual coordinate gradient -/

/-- The genuine coordinate gradient: by definition this is the ordinary
derivative of the actual objective along the affine line replacing exactly
one serialized coordinate.  No separately supplied vector field or
certificate enters this definition. -/
def coordinateGradient {M N : Nat} (hN : 0 < N) (K : ℝ)
    (q : ChainSpace M N) : ChainSpace M N := fun j ↦
  deriv (fun t : ℝ ↦ chainObjective hN K (serializedCoordinateLine q j t))
    (q j)

theorem coordinateGradient_eq_partialDeriv {M N : Nat} (hN : 0 < N)
    (K : ℝ) (q : ChainSpace M N) (j : ChainIndex M N) :
    coordinateGradient hN K q j =
      deriv (fun t : ℝ ↦ chainObjective hN K
        (serializedCoordinateLine q j t)) (q j) := by
  rfl

/-! ## Genuine partial derivatives of one corrected relay -/

private theorem hasDerivAt_sq (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * x) x := by
  convert (hasDerivAt_id x).pow 2 using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    rfl
  · simp only [id_eq]
    ring

theorem hasDerivAt_correctedH_a {N : Nat} (hN : 0 < N)
    (a b : ℝ) (w : InnerRelay.EVec N) :
    HasDerivAt (fun t : ℝ ↦ correctedH hN t b w)
      (relayGradA hN a w) a := by
  have hforcing : HasDerivAt (fun t : ℝ ↦ endpointForcing hN t b w)
      (w (first hN)) a := by
    have h := ((hasDerivAt_id a).mul_const (w (first hN))).sub_const
      (b * w (last hN))
    have heq : (fun t : ℝ ↦ endpointForcing hN t b w) =
        (fun t : ℝ ↦ t * w (first hN) - b * w (last hN)) := by
      rfl
    rw [heq]
    convert h using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp only [id_eq]
    · ring
  have hrelay : HasDerivAt (fun t : ℝ ↦ relayH hN t b w)
      (relayScale hN * w (first hN)) a := by
    have h := (hasDerivAt_const a
      (-(1 / 2 : ℝ) * regularizedPathQuad N w)).add
        (hforcing.const_mul (relayScale hN))
    have heq : (fun t : ℝ ↦ relayH hN t b w) =
        (fun t : ℝ ↦
          -(1 / 2 : ℝ) * regularizedPathQuad N w +
            relayScale hN * endpointForcing hN t b w) := by
      rfl
    rw [heq]
    convert h using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp only [Pi.add_apply]
    · ring
  have hcorr := (((hasDerivAt_sq a).add_const (b ^ 2)).const_mul
    ((2 - rho hN) / 2))
  have h := hrelay.add hcorr
  unfold correctedH relayGradA
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    simp only [Pi.add_apply]
  · ring

theorem hasDerivAt_correctedH_b {N : Nat} (hN : 0 < N)
    (a b : ℝ) (w : InnerRelay.EVec N) :
    HasDerivAt (fun t : ℝ ↦ correctedH hN a t w)
      (relayGradB hN b w) b := by
  have hforcing : HasDerivAt (fun t : ℝ ↦ endpointForcing hN a t w)
      (-w (last hN)) b := by
    have h := (hasDerivAt_const b (a * w (first hN))).sub
      ((hasDerivAt_id b).mul_const (w (last hN)))
    have heq : (fun t : ℝ ↦ endpointForcing hN a t w) =
        (fun t : ℝ ↦ a * w (first hN) - t * w (last hN)) := by
      rfl
    rw [heq]
    convert h using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp only [Pi.sub_apply, id_eq]
    · ring
  have hrelay : HasDerivAt (fun t : ℝ ↦ relayH hN a t w)
      (-relayScale hN * w (last hN)) b := by
    have h := (hasDerivAt_const b
      (-(1 / 2 : ℝ) * regularizedPathQuad N w)).add
        (hforcing.const_mul (relayScale hN))
    have heq : (fun t : ℝ ↦ relayH hN a t w) =
        (fun t : ℝ ↦
          -(1 / 2 : ℝ) * regularizedPathQuad N w +
            relayScale hN * endpointForcing hN a t w) := by
      rfl
    rw [heq]
    convert h using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp only [Pi.add_apply]
    · ring
  have hcorr := (((hasDerivAt_const b (a ^ 2)).add
    (hasDerivAt_sq b)).const_mul ((2 - rho hN) / 2))
  have h := hrelay.add hcorr
  unfold correctedH relayGradB
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    simp only [Pi.add_apply]
  · ring

/-- Affine line which replaces coordinate `i` of `w` by `t`. -/
def relayCoordinateLine {N : Nat} (w : InnerRelay.EVec N)
    (i : Fin N) (t : ℝ) : InnerRelay.EVec N :=
  w + (t - w i) • NCPLVerification.evecBasis i

@[simp] theorem relayCoordinateLine_self {N : Nat} (w : InnerRelay.EVec N)
    (i : Fin N) : relayCoordinateLine w i (w i) = w := by
  simp [relayCoordinateLine]

theorem hasDerivAt_regularizedPathQuad_coordinateLine {N : Nat}
    (w : InnerRelay.EVec N) (i : Fin N) :
    HasDerivAt (fun t : ℝ ↦ regularizedPathQuad N (relayCoordinateLine w i t))
      (2 * regularizedPathCoord w i) (w i) := by
  let e : InnerRelay.EVec N := NCPLVerification.evecBasis i
  have hebasis : e = (Pi.single i 1 : InnerRelay.EVec N) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp [e, NCPLVerification.evecBasis]
    · simp [e, NCPLVerification.evecBasis, hji]
  have hbilinear : regularizedPathBilinear N w e =
      regularizedPathCoord w i := by
    rw [hebasis, regularizedPathBilinear_comm,
      regularizedPathBilinear_single_left_eq_coord]
  have hshift : HasDerivAt (fun t : ℝ ↦ t - w i) 1 (w i) := by
    simpa using (hasDerivAt_id (w i)).sub_const (w i)
  have hpoly : HasDerivAt
      (fun t : ℝ ↦ regularizedPathQuad N w +
        (t - w i) ^ 2 * regularizedPathQuad N e +
        2 * (t - w i) * regularizedPathBilinear N w e)
      (2 * regularizedPathCoord w i) (w i) := by
    convert ((hasDerivAt_const (w i) (regularizedPathQuad N w)).add
      ((hshift.pow 2).mul_const (regularizedPathQuad N e))).add
      ((hshift.const_mul 2).mul_const (regularizedPathBilinear N w e)) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp only [Pi.add_apply, Pi.pow_apply]
    · rw [hbilinear]
      ring
  convert hpoly using 1
  funext t
  unfold relayCoordinateLine
  rw [regularizedPathQuad_add_expansion,
    regularizedPathQuad_smul, regularizedPathBilinear_smul_right]
  ring

theorem hasDerivAt_endpointForcing_coordinateLine {N : Nat} (hN : 0 < N)
    (a b : ℝ) (w : InnerRelay.EVec N) (i : Fin N) :
    HasDerivAt
      (fun t : ℝ ↦ endpointForcing hN a b (relayCoordinateLine w i t))
      (endpointSource hN a b i) (w i) := by
  have hcoord (j : Fin N) : HasDerivAt
      (fun t : ℝ ↦ relayCoordinateLine w i t j)
      (NCPLVerification.evecBasis i j) (w i) := by
    unfold relayCoordinateLine
    convert
      (hasDerivAt_const (w i) (w j)).add
        (((hasDerivAt_id (w i)).sub_const (w i)).mul_const
          (NCPLVerification.evecBasis i j)) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      rfl
    · ring
  unfold endpointForcing endpointSource
  convert ((hcoord (first hN)).const_mul a).sub
    ((hcoord (last hN)).const_mul b) using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · apply funext
    intro t
    simp only [Pi.sub_apply]
  · classical
    by_cases hf : i = first hN <;> by_cases hl : i = last hN <;>
      simp [NCPLVerification.evecBasis, Pi.single_apply, hf, hl, eq_comm]

theorem hasDerivAt_correctedH_w {N : Nat} (hN : 0 < N)
    (a b : ℝ) (w : InnerRelay.EVec N) (i : Fin N) :
    HasDerivAt (fun t : ℝ ↦ correctedH hN a b (relayCoordinateLine w i t))
      (-relaySaddleGradW hN a b w i) (w i) := by
  have hq := hasDerivAt_regularizedPathQuad_coordinateLine w i
  have hf := hasDerivAt_endpointForcing_coordinateLine hN a b w i
  unfold correctedH relayH relaySaddleGradW
  convert (((hq.const_mul (-(1 / 2 : ℝ))).add
    (hf.const_mul (relayScale hN))).add_const
      ((2 - rho hN) / 2 * (a ^ 2 + b ^ 2))) using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    simp only [Pi.add_apply]
  · ring

/-! ## Concrete entries of the actual coordinate gradient -/

def chainGradA {M N : Nat} (hN : 0 < N) (q : ChainSpace M N)
    (i : Fin (M - 1)) : ℝ :=
  -4 * frontierSwitch (previousMemory (serializedState q) i) *
      (1 - frontierSwitch (serializedState q i)) *
      deriv pulseClip (serializedA q i) +
    relayGradA hN (serializedA q i) (serializedDualBlock q i)

def chainGradB {M N : Nat} (hN : 0 < N) (q : ChainSpace M N)
    (i : Fin (M - 1)) : ℝ :=
  -frontierSwitch (previousMemory (serializedState q) i) *
      stateClip (serializedState q i) *
      (1 - frontierSwitch (serializedState q i)) *
      deriv pulseClip (serializedB q i) +
    relayGradB hN (serializedB q i) (serializedDualBlock q i)

def chainSaddleGradY {M N : Nat} (hN : 0 < N) (q : ChainSpace M N)
    (i : Fin (M - 1)) (k : Fin N) : ℝ :=
  relaySaddleGradW hN (serializedA q i) (serializedB q i)
    (serializedDualBlock q i) k

theorem coordinateGradient_A {M N : Nat} (hN : 0 < N) (K : ℝ)
    (q : ChainSpace M N) (i : Fin (M - 1)) :
    coordinateGradient hN K q (serializedAIndex (n := N) i) =
      chainGradA hN q i := by
  have hstate (t : ℝ) :
      serializedState
          (serializedCoordinateLine q (serializedAIndex (n := N) i) t) =
        serializedState q := by
    funext l
    exact serializedState_coordinateLine_A q i l t
  have hb (t : ℝ) :
      serializedB
          (serializedCoordinateLine q (serializedAIndex (n := N) i) t) =
        serializedB q := by
    funext l
    exact serializedB_coordinateLine_A q i l t
  have hy (t : ℝ) :
      serializedDualBlock
          (serializedCoordinateLine q (serializedAIndex (n := N) i) t) =
        serializedDualBlock q := by
    funext l
    exact serializedDualBlock_coordinateLine_A q i l t
  have hpulse : HasDerivAt pulseClip
      (deriv pulseClip (serializedA q i)) (serializedA q i) :=
    (pulseClip_contDiff.differentiable (by simp) (serializedA q i)).hasDerivAt
  have hent : HasDerivAt
      (fun t : ℝ ↦ entranceComponent
        (serializedState
          (serializedCoordinateLine q (serializedAIndex (n := N) i) t))
        (serializedA
          (serializedCoordinateLine q (serializedAIndex (n := N) i) t)))
      (-4 * frontierSwitch (previousMemory (serializedState q) i) *
        (1 - frontierSwitch (serializedState q i)) *
          deriv pulseClip (serializedA q i)) (serializedA q i) := by
    unfold entranceComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (M - 1), entranceSummand
          (serializedState
            (serializedCoordinateLine q (serializedAIndex (n := N) i) t))
          (serializedA
            (serializedCoordinateLine q (serializedAIndex (n := N) i) t)) l)
        (∑ l : Fin (M - 1), if l = i then
          -4 * frontierSwitch (previousMemory (serializedState q) i) *
            (1 - frontierSwitch (serializedState q i)) *
              deriv pulseClip (serializedA q i)
          else 0) (serializedA q i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa [entranceSummand, hstate] using hpulse.const_mul
          (-4 * frontierSwitch (previousMemory (serializedState q) i) *
            (1 - frontierSwitch (serializedState q i)))
      · simpa [entranceSummand, hli, hstate] using
          hasDerivAt_const (serializedA q i)
          (entranceSummand (serializedState q) (serializedA q) l)
    classical
    rw [Finset.sum_ite_eq'] at hs
    simpa using hs
  have hinner : HasDerivAt
      (fun t : ℝ ↦ innerComponent hN
        (serializedA
          (serializedCoordinateLine q (serializedAIndex (n := N) i) t))
        (serializedB
          (serializedCoordinateLine q (serializedAIndex (n := N) i) t))
        (serializedDualBlock
          (serializedCoordinateLine q (serializedAIndex (n := N) i) t)))
      (relayGradA hN (serializedA q i) (serializedDualBlock q i))
      (serializedA q i) := by
    unfold innerComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (M - 1),
          correctedH hN
            (serializedA
              (serializedCoordinateLine q (serializedAIndex (n := N) i) t) l)
            (serializedB
              (serializedCoordinateLine q (serializedAIndex (n := N) i) t) l)
            (serializedDualBlock
              (serializedCoordinateLine q (serializedAIndex (n := N) i) t) l))
        (∑ l : Fin (M - 1), if l = i then
          relayGradA hN (serializedA q i) (serializedDualBlock q i) else 0)
        (serializedA q i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa using hasDerivAt_correctedH_a hN (serializedA q i)
          (serializedB q i) (serializedDualBlock q i)
      · simpa [hli] using hasDerivAt_const (serializedA q i)
          (correctedH hN (serializedA q l) (serializedB q l)
            (serializedDualBlock q l))
    classical
    rw [Finset.sum_ite_eq'] at hs
    simpa using hs
  have hrest : HasDerivAt
      (fun _ : ℝ ↦
        phaseComponent K (serializedState q) +
          orderingComponent (serializedState q) +
          exitComponent (serializedState q) (serializedB q)) 0
      (serializedA q i) :=
    hasDerivAt_const _ _
  have hcalc : HasDerivAt
      (fun t : ℝ ↦ chainObjective hN K
        (serializedCoordinateLine q (serializedAIndex (n := N) i) t))
      (chainGradA hN q i) (serializedA q i) := by
    convert (hrest.add hent).add hinner using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp [chainObjective, hardObjective, outerComponent, hstate, hb, hy]
      ring
    · simp [chainGradA]
  simpa [coordinateGradient, serializedA] using hcalc.deriv

theorem coordinateGradient_B {M N : Nat} (hN : 0 < N) (K : ℝ)
    (q : ChainSpace M N) (i : Fin (M - 1)) :
    coordinateGradient hN K q (serializedBIndex (n := N) i) =
      chainGradB hN q i := by
  have hstate (t : ℝ) :
      serializedState
          (serializedCoordinateLine q (serializedBIndex (n := N) i) t) =
        serializedState q := by
    funext l
    exact serializedState_coordinateLine_B q i l t
  have ha (t : ℝ) :
      serializedA
          (serializedCoordinateLine q (serializedBIndex (n := N) i) t) =
        serializedA q := by
    funext l
    exact serializedA_coordinateLine_B q i l t
  have hy (t : ℝ) :
      serializedDualBlock
          (serializedCoordinateLine q (serializedBIndex (n := N) i) t) =
        serializedDualBlock q := by
    funext l
    exact serializedDualBlock_coordinateLine_B q i l t
  have hpulse : HasDerivAt pulseClip
      (deriv pulseClip (serializedB q i)) (serializedB q i) :=
    (pulseClip_contDiff.differentiable (by simp) (serializedB q i)).hasDerivAt
  have hexit : HasDerivAt
      (fun t : ℝ ↦ exitComponent
        (serializedState
          (serializedCoordinateLine q (serializedBIndex (n := N) i) t))
        (serializedB
          (serializedCoordinateLine q (serializedBIndex (n := N) i) t)))
      (-frontierSwitch (previousMemory (serializedState q) i) *
        stateClip (serializedState q i) *
        (1 - frontierSwitch (serializedState q i)) *
          deriv pulseClip (serializedB q i)) (serializedB q i) := by
    unfold exitComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (M - 1), exitSummand
          (serializedState
            (serializedCoordinateLine q (serializedBIndex (n := N) i) t))
          (serializedB
            (serializedCoordinateLine q (serializedBIndex (n := N) i) t)) l)
        (∑ l : Fin (M - 1), if l = i then
          -frontierSwitch (previousMemory (serializedState q) i) *
            stateClip (serializedState q i) *
            (1 - frontierSwitch (serializedState q i)) *
              deriv pulseClip (serializedB q i)
          else 0) (serializedB q i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa [exitSummand, hstate] using hpulse.const_mul
          (-frontierSwitch (previousMemory (serializedState q) i) *
            stateClip (serializedState q i) *
            (1 - frontierSwitch (serializedState q i)))
      · simpa [exitSummand, hli, hstate] using
          hasDerivAt_const (serializedB q i)
            (exitSummand (serializedState q) (serializedB q) l)
    classical
    rw [Finset.sum_ite_eq'] at hs
    simpa using hs
  have hinner : HasDerivAt
      (fun t : ℝ ↦ innerComponent hN
        (serializedA
          (serializedCoordinateLine q (serializedBIndex (n := N) i) t))
        (serializedB
          (serializedCoordinateLine q (serializedBIndex (n := N) i) t))
        (serializedDualBlock
          (serializedCoordinateLine q (serializedBIndex (n := N) i) t)))
      (relayGradB hN (serializedB q i) (serializedDualBlock q i))
      (serializedB q i) := by
    unfold innerComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (M - 1),
          correctedH hN
            (serializedA
              (serializedCoordinateLine q (serializedBIndex (n := N) i) t) l)
            (serializedB
              (serializedCoordinateLine q (serializedBIndex (n := N) i) t) l)
            (serializedDualBlock
              (serializedCoordinateLine q (serializedBIndex (n := N) i) t) l))
        (∑ l : Fin (M - 1), if l = i then
          relayGradB hN (serializedB q i) (serializedDualBlock q i) else 0)
        (serializedB q i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa using hasDerivAt_correctedH_b hN (serializedA q i)
          (serializedB q i) (serializedDualBlock q i)
      · simpa [hli] using hasDerivAt_const (serializedB q i)
          (correctedH hN (serializedA q l) (serializedB q l)
            (serializedDualBlock q l))
    classical
    rw [Finset.sum_ite_eq'] at hs
    simpa using hs
  have hrest : HasDerivAt
      (fun _ : ℝ ↦
        phaseComponent K (serializedState q) +
          orderingComponent (serializedState q) +
          entranceComponent (serializedState q) (serializedA q)) 0
      (serializedB q i) := hasDerivAt_const _ _
  have hcalc : HasDerivAt
      (fun t : ℝ ↦ chainObjective hN K
        (serializedCoordinateLine q (serializedBIndex (n := N) i) t))
      (chainGradB hN q i) (serializedB q i) := by
    convert (hrest.add hexit).add hinner using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp [chainObjective, hardObjective, outerComponent, hstate, ha, hy]
    · simp [chainGradB]
  simpa [coordinateGradient, serializedB] using hcalc.deriv

theorem coordinateGradient_Y {M N : Nat} (hN : 0 < N) (K : ℝ)
    (q : ChainSpace M N) (i : Fin (M - 1)) (k : Fin N) :
    coordinateGradient hN K q (serializedDualIndex i k) =
      -chainSaddleGradY hN q i k := by
  have hsame : HasDerivAt
      (fun t : ℝ ↦ correctedH hN (serializedA q i) (serializedB q i)
        (serializedDualBlock
          (serializedCoordinateLine q (serializedDualIndex i k) t) i))
      (-chainSaddleGradY hN q i k) (serializedY q i k) := by
    simpa [chainSaddleGradY, relayCoordinateLine,
      serializedDualBlock_coordinateLine_Y_same, serializedY,
      serializedDualBlock] using
      hasDerivAt_correctedH_w hN (serializedA q i) (serializedB q i)
        (serializedDualBlock q i) k
  have hstate (t : ℝ) :
      serializedState
          (serializedCoordinateLine q (serializedDualIndex i k) t) =
        serializedState q := by
    funext l
    exact serializedState_coordinateLine_Y q i l k t
  have ha (t : ℝ) :
      serializedA (serializedCoordinateLine q (serializedDualIndex i k) t) =
        serializedA q := by
    funext l
    exact serializedA_coordinateLine_Y q i l k t
  have hb (t : ℝ) :
      serializedB (serializedCoordinateLine q (serializedDualIndex i k) t) =
        serializedB q := by
    funext l
    exact serializedB_coordinateLine_Y q i l k t
  have hinner : HasDerivAt
      (fun t : ℝ ↦ innerComponent hN
        (serializedA
          (serializedCoordinateLine q (serializedDualIndex i k) t))
        (serializedB
          (serializedCoordinateLine q (serializedDualIndex i k) t))
        (serializedDualBlock
          (serializedCoordinateLine q (serializedDualIndex i k) t)))
      (-chainSaddleGradY hN q i k) (serializedY q i k) := by
    unfold innerComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (M - 1),
          correctedH hN
            (serializedA
              (serializedCoordinateLine q (serializedDualIndex i k) t) l)
            (serializedB
              (serializedCoordinateLine q (serializedDualIndex i k) t) l)
            (serializedDualBlock
              (serializedCoordinateLine q (serializedDualIndex i k) t) l))
        (∑ l : Fin (M - 1), if l = i then
          -chainSaddleGradY hN q i k else 0) (serializedY q i k) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa using hsame
      · simpa [hli, serializedDualBlock_coordinateLine_Y_ne] using
          hasDerivAt_const (serializedY q i k)
            (correctedH hN (serializedA q l) (serializedB q l)
              (serializedDualBlock q l))
    classical
    rw [Finset.sum_ite_eq'] at hs
    simpa using hs
  have houter : HasDerivAt
      (fun _ : ℝ ↦ outerComponent K (serializedState q)
        (serializedA q) (serializedB q)) 0 (serializedY q i k) :=
    hasDerivAt_const _ _
  have hcalc : HasDerivAt
      (fun t : ℝ ↦ chainObjective hN K
        (serializedCoordinateLine q (serializedDualIndex i k) t))
      (-chainSaddleGradY hN q i k) (serializedY q i k) := by
    convert houter.add hinner using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp [chainObjective, hardObjective, outerComponent, hstate, ha, hb]
    · ring
  simpa [coordinateGradient, serializedY] using hcalc.deriv

/-! ## The memory coordinate and its only possible successor -/

def replaceCoordinate {m : Nat} (s : Fin m → ℝ) (i : Fin m) (t : ℝ) :
    Fin m → ℝ := fun l ↦ if l = i then t else s l

@[simp] theorem replaceCoordinate_self {m : Nat} (s : Fin m → ℝ)
    (i : Fin m) (t : ℝ) : replaceCoordinate s i t i = t := by
  simp [replaceCoordinate]

@[simp] theorem replaceCoordinate_ne {m : Nat} (s : Fin m → ℝ)
    (i l : Fin m) (t : ℝ) (hli : l ≠ i) :
    replaceCoordinate s i t l = s l := by
  simp [replaceCoordinate, hli]

theorem previousMemory_replaceCoordinate {m : Nat} (s : Fin m → ℝ)
    (i l : Fin m) (t : ℝ) :
    previousMemory (replaceCoordinate s i t) l =
      if l.val = i.val + 1 then t else previousMemory s l := by
  unfold previousMemory
  by_cases hl0 : l.val = 0
  · simp [hl0]
  · simp only [hl0, ↓reduceDIte]
    by_cases hsucc : l.val = i.val + 1
    · simp [hsucc, replaceCoordinate]
    · have hfin : (⟨l.val - 1, by omega⟩ : Fin m) ≠ i := by
        intro h
        have hv := congrArg Fin.val h
        simp only at hv
        omega
      simp [hsucc, replaceCoordinate, hfin]

theorem serializedState_coordinateLine_eq_replace {M N : Nat}
    (q : ChainSpace M N) (i : Fin (M - 1)) (t : ℝ) :
    serializedState
        (serializedCoordinateLine q (serializedStateIndex (n := N) i) t) =
      replaceCoordinate (serializedState q) i t := by
  funext l
  simp [replaceCoordinate]

/-- An unrevealed memory coordinate has zero genuine partial derivative.  The
only data needed beyond its own zero value are the three entries of the next
block that can mention it: the next memory and the next entrance/exit pulses. -/
theorem coordinateGradient_state_zero_of_unrevealed {M N : Nat}
    (hN : 0 < N) (K : ℝ) (q : ChainSpace M N) (i : Fin (M - 1))
    (hs0 : serializedState q i = 0)
    (hb0 : serializedB q i = 0)
    (hnextState : ∀ h : i.val + 1 < M - 1,
      serializedState q ⟨i.val + 1, h⟩ = 0)
    (hnextA : ∀ h : i.val + 1 < M - 1,
      serializedA q ⟨i.val + 1, h⟩ = 0)
    (hnextB : ∀ h : i.val + 1 < M - 1,
      serializedB q ⟨i.val + 1, h⟩ = 0) :
    coordinateGradient hN K q (serializedStateIndex (n := N) i) = 0 := by
  let line : ℝ → ChainSpace M N := fun t ↦
    serializedCoordinateLine q (serializedStateIndex (n := N) i) t
  have hstate (t : ℝ) : serializedState (line t) =
      replaceCoordinate (serializedState q) i t := by
    exact serializedState_coordinateLine_eq_replace q i t
  have ha (t : ℝ) : serializedA (line t) = serializedA q := by
    funext l
    exact serializedA_coordinateLine_state q i l t
  have hb (t : ℝ) : serializedB (line t) = serializedB q := by
    funext l
    exact serializedB_coordinateLine_state q i l t
  have hy (t : ℝ) : serializedDualBlock (line t) =
      serializedDualBlock q := by
    funext l
    exact serializedDualBlock_coordinateLine_state q i l t
  have hA0 : HasDerivAt frontierSwitch 0 0 := by
    have hd := frontierSwitch_contDiff.differentiable (by simp) (0 : ℝ)
    simpa [frontierSwitch_deriv_eq_zero_of_le_fifth
      (by norm_num : (0 : ℝ) ≤ 1 / 5)] using hd.hasDerivAt
  have hphase : HasDerivAt
      (fun t : ℝ ↦ phaseComponent K (serializedState (line t))) 0 0 := by
    unfold phaseComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (M - 1),
          phasePotential K (serializedState (line t) l))
        (∑ l : Fin (M - 1), if l = i then 0 else 0) 0 := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        have hp0 : phasePotentialDeriv K 0 = 0 := by
          rw [← deriv_phasePotential]
          exact phasePotential_deriv_zero K
        simpa [hstate, replaceCoordinate, hs0, hp0] using
          hasDerivAt_phasePotential K 0
      · simpa [hstate, replaceCoordinate, hli] using
          hasDerivAt_const 0 (phasePotential K (serializedState q l))
    simpa using hs
  have hordering : HasDerivAt
      (fun t : ℝ ↦ orderingComponent (serializedState (line t))) 0 0 := by
    unfold orderingComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (M - 1),
          orderingSummand (serializedState (line t)) l)
        (∑ _l : Fin (M - 1), 0) 0 := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        have hd := ((hA0.const_mul 24).mul_const
          (1 - stateClip (previousMemory (serializedState q) i))).mul_const
            (1 - frontierSwitch (previousMemory (serializedState q) i))
        simpa [orderingSummand, hstate, replaceCoordinate, hs0,
          previousMemory_replaceCoordinate, frontierSwitch_zero] using hd
      · by_cases hsucc : l.val = i.val + 1
        · have hlt : i.val + 1 < M - 1 := by omega
          have hsl : serializedState q l = 0 := by
            have hleq : l = (⟨i.val + 1, hlt⟩ : Fin (M - 1)) :=
              Fin.ext hsucc
            simpa [hleq] using hnextState hlt
          simpa [orderingSummand, hstate, replaceCoordinate, hli,
            previousMemory_replaceCoordinate, hsucc, hsl,
            frontierSwitch_zero] using hasDerivAt_const 0 (0 : ℝ)
        · simpa [orderingSummand, hstate, replaceCoordinate, hli,
            previousMemory_replaceCoordinate, hsucc] using
            hasDerivAt_const 0
              (orderingSummand (serializedState q) l)
    simpa using hs
  have hentrance : HasDerivAt
      (fun t : ℝ ↦ entranceComponent (serializedState (line t))
        (serializedA (line t))) 0 0 := by
    unfold entranceComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (M - 1),
          entranceSummand (serializedState (line t))
            (serializedA (line t)) l)
        (∑ _l : Fin (M - 1), 0) 0 := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        have hd := (((hasDerivAt_const 0 (1 : ℝ)).sub hA0).const_mul
          (-4 * frontierSwitch (previousMemory (serializedState q) i))).mul_const
            (pulseClip (serializedA q i))
        simpa [entranceSummand, hstate, ha, replaceCoordinate, hs0,
          previousMemory_replaceCoordinate, frontierSwitch_zero] using hd
      · by_cases hsucc : l.val = i.val + 1
        · have hlt : i.val + 1 < M - 1 := by omega
          have hal : serializedA q l = 0 := by
            have hleq : l = (⟨i.val + 1, hlt⟩ : Fin (M - 1)) :=
              Fin.ext hsucc
            simpa [hleq] using hnextA hlt
          simpa [entranceSummand, hstate, ha, replaceCoordinate, hli,
            previousMemory_replaceCoordinate, hsucc, hal, pulseClip_zero] using
              hasDerivAt_const 0 (0 : ℝ)
        · simpa [entranceSummand, hstate, ha, replaceCoordinate, hli,
            previousMemory_replaceCoordinate, hsucc] using
            hasDerivAt_const 0
              (entranceSummand (serializedState q) (serializedA q) l)
    simpa using hs
  have hexit : HasDerivAt
      (fun t : ℝ ↦ exitComponent (serializedState (line t))
        (serializedB (line t))) 0 0 := by
    unfold exitComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin (M - 1),
          exitSummand (serializedState (line t)) (serializedB (line t)) l)
        (∑ _l : Fin (M - 1), 0) 0 := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa [exitSummand, hstate, hb, replaceCoordinate, hs0, hb0,
          previousMemory_replaceCoordinate, pulseClip_zero] using
            hasDerivAt_const 0 (0 : ℝ)
      · by_cases hsucc : l.val = i.val + 1
        · have hlt : i.val + 1 < M - 1 := by omega
          have hbl : serializedB q l = 0 := by
            have hleq : l = (⟨i.val + 1, hlt⟩ : Fin (M - 1)) :=
              Fin.ext hsucc
            simpa [hleq] using hnextB hlt
          simpa [exitSummand, hstate, hb, replaceCoordinate, hli,
            previousMemory_replaceCoordinate, hsucc, hbl, pulseClip_zero] using
              hasDerivAt_const 0 (0 : ℝ)
        · simpa [exitSummand, hstate, hb, replaceCoordinate, hli,
            previousMemory_replaceCoordinate, hsucc] using
            hasDerivAt_const 0
              (exitSummand (serializedState q) (serializedB q) l)
    simpa using hs
  have hinner : HasDerivAt
      (fun _ : ℝ ↦ innerComponent hN (serializedA q) (serializedB q)
        (serializedDualBlock q)) 0 0 := hasDerivAt_const _ _
  have hcalc : HasDerivAt (fun t : ℝ ↦ chainObjective hN K (line t)) 0 0 := by
    convert (((hphase.add hordering).add hentrance).add hexit).add hinner using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp [chainObjective, hardObjective, outerComponent, hstate, ha, hb, hy]
    · ring
  unfold coordinateGradient
  have hbase : q (serializedStateIndex (n := N) i) = 0 := hs0
  rw [hbase]
  simpa [line] using hcalc.deriv

/-! ## One-step support propagation in the literal paper order -/

theorem coordinateGradient_A_one_step {M N r : Nat} (hN : 0 < N) (K : ℝ)
    (q : ChainSpace M N) (hz : NCPLVerification.SupportedBelow r q)
    (i : Fin (M - 1))
    (hi : r + 1 ≤ (serializedAIndex (n := N) i).val) :
    coordinateGradient hN K q (serializedAIndex (n := N) i) = 0 := by
  change r + 1 ≤ i.val * (N + 3) at hi
  have ine : i.val ≠ 0 := by
    intro hieq
    simp [hieq] at hi
  let ip : Fin (M - 1) := ⟨i.val - 1, by omega⟩
  have ha0 : serializedA q i = 0 := by
    apply hz
    change r ≤ i.val * (N + 3)
    omega
  have hy0 : serializedY q i (first hN) = 0 := by
    apply hz
    change r ≤ i.val * (N + 3) + 1 + (first hN).val
    simp [first, innerFirst]
    omega
  have hs0 : serializedState q ip = 0 := by
    apply hz
    change r ≤ (i.val - 1) * (N + 3) + N + 2
    have hieq : i.val = (i.val - 1) + 1 := by omega
    rw [hieq] at hi
    rw [Nat.add_mul] at hi
    omega
  have hprev : previousMemory (serializedState q) i = 0 := by
    rw [previousMemory_succ _ i (by omega)]
    exact hs0
  rw [coordinateGradient_A hN K q i]
  have hrelay : relayGradA hN (serializedA q i)
      (serializedDualBlock q i) = 0 := by
    apply relayGradA_zero hN ha0
    simpa [serializedDualBlock] using hy0
  simp [chainGradA, hprev, frontierSwitch_zero, hrelay]

theorem coordinateGradient_B_one_step {M N r : Nat} (hN : 0 < N) (K : ℝ)
    (q : ChainSpace M N) (hz : NCPLVerification.SupportedBelow r q)
    (i : Fin (M - 1))
    (hi : r + 1 ≤ (serializedBIndex (n := N) i).val) :
    coordinateGradient hN K q (serializedBIndex (n := N) i) = 0 := by
  change r + 1 ≤ i.val * (N + 3) + N + 1 at hi
  have hb0 : serializedB q i = 0 := by
    apply hz
    change r ≤ i.val * (N + 3) + N + 1
    omega
  have hs0 : serializedState q i = 0 := by
    apply hz
    change r ≤ i.val * (N + 3) + N + 2
    omega
  have hy0 : serializedY q i (last hN) = 0 := by
    apply hz
    change r ≤ i.val * (N + 3) + 1 + (N - 1)
    have hlast : N - 1 < N := by omega
    omega
  rw [coordinateGradient_B hN K q i]
  have hrelay : relayGradB hN (serializedB q i)
      (serializedDualBlock q i) = 0 := by
    apply relayGradB_zero hN hb0
    simpa [serializedDualBlock] using hy0
  simp [chainGradB, hs0, stateClip_zero, hrelay]

theorem coordinateGradient_Y_one_step {M N r : Nat} (hN : 0 < N) (K : ℝ)
    (q : ChainSpace M N) (hz : NCPLVerification.SupportedBelow r q)
    (i : Fin (M - 1)) (k : Fin N)
    (hi : r + 1 ≤ (serializedDualIndex i k).val) :
    coordinateGradient hN K q (serializedDualIndex i k) = 0 := by
  rw [coordinateGradient_Y hN K q i k]
  change -relaySaddleGradW hN (serializedA q i) (serializedB q i)
      (serializedDualBlock q i) k = 0
  change r + 1 ≤ i.val * (N + 3) + 1 + k.val at hi
  have hsaddle : relaySaddleGradW hN (serializedA q i) (serializedB q i)
      (serializedDualBlock q i) k = 0 := by
    by_cases hk : k.val = 0
    · have ha0 : serializedA q i = 0 := by
        apply hz
        change r ≤ i.val * (N + 3)
        omega
      have hb0 : serializedB q i = 0 := by
        apply hz
        change r ≤ i.val * (N + 3) + N + 1
        omega
      have hw0 : serializedDualBlock q i = 0 := by
        funext u
        apply hz
        change r ≤ i.val * (N + 3) + 1 + u.val
        omega
      rw [hw0]
      simp [relaySaddleGradW, endpointSource, ha0, hb0,
        regularizedPathCoord, pathLaplacianCoord]
    · let tail : Nat := k.val - 1
      have hb0 : serializedB q i = 0 := by
        apply hz
        change r ≤ i.val * (N + 3) + N + 1
        omega
      have hw : ∀ u : Fin N, tail ≤ u.val →
          serializedDualBlock q i u = 0 := by
        intro u hu
        apply hz
        change r ≤ i.val * (N + 3) + 1 + u.val
        dsimp [tail] at hu
        have hkeq : k.val = (k.val - 1) + 1 := by omega
        omega
      apply relaySaddleGradW_zero_of_zero_tail
        (k := tail) hN (serializedA q i) (serializedB q i) hb0 hw k
      dsimp [tail]
      omega
  rw [hsaddle]
  ring

theorem coordinateGradient_state_one_step {M N r : Nat} (hN : 0 < N)
    (K : ℝ) (q : ChainSpace M N)
    (hz : NCPLVerification.SupportedBelow r q) (i : Fin (M - 1))
    (hi : r + 1 ≤ (serializedStateIndex (n := N) i).val) :
    coordinateGradient hN K q (serializedStateIndex (n := N) i) = 0 := by
  change r + 1 ≤ i.val * (N + 3) + N + 2 at hi
  have hs0 : serializedState q i = 0 := by
    apply hz
    change r ≤ i.val * (N + 3) + N + 2
    omega
  have hb0 : serializedB q i = 0 := by
    apply hz
    change r ≤ i.val * (N + 3) + N + 1
    omega
  have hnextState : ∀ h : i.val + 1 < M - 1,
      serializedState q ⟨i.val + 1, h⟩ = 0 := by
    intro h
    apply hz
    change r ≤ (i.val + 1) * (N + 3) + N + 2
    rw [Nat.add_mul]
    omega
  have hnextA : ∀ h : i.val + 1 < M - 1,
      serializedA q ⟨i.val + 1, h⟩ = 0 := by
    intro h
    apply hz
    change r ≤ (i.val + 1) * (N + 3)
    rw [Nat.add_mul]
    omega
  have hnextB : ∀ h : i.val + 1 < M - 1,
      serializedB q ⟨i.val + 1, h⟩ = 0 := by
    intro h
    apply hz
    change r ≤ (i.val + 1) * (N + 3) + N + 1
    rw [Nat.add_mul]
    omega
  exact coordinateGradient_state_zero_of_unrevealed hN K q i hs0 hb0
    hnextState hnextA hnextB

/-! ## Reassembly with the saddle sign and the full zero-chain theorem -/

/-- The actual coordinate derivatives, reassembled in the paper order, with
exactly the dual coordinates sign-flipped. -/
def signedCoordinateField {M N : Nat} (hN : 0 < N) (K : ℝ)
    (q : ChainSpace M N) : ChainSpace M N :=
  (∑ i : Fin (M - 1), Pi.single (serializedAIndex (n := N) i)
      (coordinateGradient hN K q (serializedAIndex (n := N) i))) +
    (∑ i : Fin (M - 1), ∑ k : Fin N,
      Pi.single (serializedDualIndex i k)
        (-coordinateGradient hN K q (serializedDualIndex i k))) +
    (∑ i : Fin (M - 1), Pi.single (serializedBIndex (n := N) i)
      (coordinateGradient hN K q (serializedBIndex (n := N) i))) +
    (∑ i : Fin (M - 1), Pi.single (serializedStateIndex (n := N) i)
      (coordinateGradient hN K q (serializedStateIndex (n := N) i)))

/-- Full signed first-order saddle zero-chain for the actual partial
derivatives of the five-component objective. -/
theorem signedCoordinateField_isFirstOrderZeroChain {M N : Nat}
    (hN : 0 < N) (K : ℝ) :
    NCPLVerification.IsFirstOrderZeroChain
      (signedCoordinateField (M := M) hN K) := by
  intro r q hz j hj
  have sum_eval_zero : ∀ {m : Nat} (f : Fin m → ChainSpace M N),
      (∀ i, f i j = 0) → (∑ i, f i) j = 0 := by
    intro m f hf
    have hp : (NCPLVerification.evecProj j) (∑ i, f i) = 0 := by
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i _
      simpa only [NCPLVerification.evecProj_apply] using hf i
    simpa only [NCPLVerification.evecProj_apply] using hp
  have hA :
      (∑ i : Fin (M - 1), Pi.single (serializedAIndex (n := N) i)
        (coordinateGradient hN K q (serializedAIndex (n := N) i)) :
          ChainSpace M N) j = 0 := by
    apply sum_eval_zero
    intro i
    by_cases heq : serializedAIndex (n := N) i = j
    · subst j
      simp [coordinateGradient_A_one_step hN K q hz i hj]
    · simp [heq]
  have hY :
      (∑ i : Fin (M - 1), ∑ k : Fin N,
        (Pi.single (serializedDualIndex i k)
          (-coordinateGradient hN K q (serializedDualIndex i k)) :
            ChainSpace M N)) j = 0 := by
    apply sum_eval_zero
    intro i
    apply sum_eval_zero
    intro k
    by_cases heq : serializedDualIndex i k = j
    · subst j
      simp [coordinateGradient_Y_one_step hN K q hz i k hj]
    · simp [heq]
  have hB :
      (∑ i : Fin (M - 1), Pi.single (serializedBIndex (n := N) i)
        (coordinateGradient hN K q (serializedBIndex (n := N) i)) :
          ChainSpace M N) j = 0 := by
    apply sum_eval_zero
    intro i
    by_cases heq : serializedBIndex (n := N) i = j
    · subst j
      simp [coordinateGradient_B_one_step hN K q hz i hj]
    · simp [heq]
  have hS :
      (∑ i : Fin (M - 1), Pi.single (serializedStateIndex (n := N) i)
        (coordinateGradient hN K q (serializedStateIndex (n := N) i)) :
          ChainSpace M N) j = 0 := by
    apply sum_eval_zero
    intro i
    by_cases heq : serializedStateIndex (n := N) i = j
    · subst j
      simp [coordinateGradient_state_one_step hN K q hz i hj]
    · simp [heq]
  simp only [signedCoordinateField, Pi.add_apply]
  rw [hA, hY, hB, hS]
  ring

/-- At the origin the genuine signed saddle oracle can expose at most the
first serialized coordinate `a₁`. -/
theorem signedCoordinateField_origin_supportedBelow_one {M N : Nat}
    (hN : 0 < N) (K : ℝ) :
    NCPLVerification.SupportedBelow 1
      (signedCoordinateField (M := M) hN K (0 : ChainSpace M N)) := by
  intro j hj
  exact signedCoordinateField_isFirstOrderZeroChain hN K 0
    (0 : ChainSpace M N) (by simp [NCPLVerification.SupportedBelow]) j hj
