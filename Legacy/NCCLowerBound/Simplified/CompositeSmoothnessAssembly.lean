import NCCLowerBound.Simplified.CompositeSmoothness
import NCCLowerBound.Simplified.CompositeZeroChain
import NCCLowerBoundVerification.Upper.ProxExistence

/-!
# Sparse assembly of the smoothness certificate

The purpose of this file is to turn the scalar and one-relay estimates from
`CompositeSmoothness` into a dimension-free estimate for the complete chain.
The outer summands are treated as four-coordinate local functions.  Their
energies are assembled using the fact that a memory coordinate occurs only
as the current state of one block and the predecessor of the next block.
-/

namespace NCCLowerBound
namespace Simplified
namespace CompositeSmoothnessAssembly

noncomputable section

open scoped BigOperators NNReal
open Set Finset
open NCCLowerBoundVerification
open InnerRelay Composite CompositeProperties RestrictedBall
open CompositeSmoothness

abbrev EVec := NCCLowerBoundVerification.EVec

private theorem vecSq_nonneg {n : Nat} (v : EVec n) : 0 ≤ vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  positivity

private theorem norm_le_sqrt_vecSq {n : Nat} (v : EVec n) :
    ‖v‖ ≤ Real.sqrt (vecSq v) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  have hi : v i ^ 2 ≤ vecSq v := by
    unfold vecSq NCPLVerification.vecSq
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j))
      (Finset.mem_univ i)
  have hs0 := Real.sqrt_nonneg (vecSq v)
  have hs2 := Real.sq_sqrt (vecSq_nonneg v)
  have habs : |v i| ≤ Real.sqrt (vecSq v) := by
    nlinarith [sq_abs (v i), abs_nonneg (v i)]
  simpa only [Real.norm_eq_abs] using habs

/-! ## Bounded-Lipschitz scalar calculus -/

private structure BL {E : Type*} [PseudoMetricSpace E] (f : E → ℝ) where
  B : ℝ
  B_nonneg : 0 ≤ B
  bound : ∀ x, |f x| ≤ B
  C : NNReal
  lipschitz : LipschitzWith C f

namespace BL

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
  {f g : E → ℝ}

def const (c : ℝ) : BL (fun _ : E => c) := {
  B := |c|
  B_nonneg := abs_nonneg c
  bound := fun _ => le_rfl
  C := 0
  lipschitz := LipschitzWith.const c
}

def neg (hf : BL f) : BL (fun x => -f x) := {
  B := hf.B
  B_nonneg := hf.B_nonneg
  bound := by intro x; simpa using hf.bound x
  C := hf.C
  lipschitz := hf.lipschitz.neg
}

def add (hf : BL f) (hg : BL g) : BL (fun x => f x + g x) := {
  B := hf.B + hg.B
  B_nonneg := add_nonneg hf.B_nonneg hg.B_nonneg
  bound := by
    intro x
    exact (abs_add_le _ _).trans (add_le_add (hf.bound x) (hg.bound x))
  C := hf.C + hg.C
  lipschitz := hf.lipschitz.add hg.lipschitz
}

def sub (hf : BL f) (hg : BL g) : BL (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

def smul (c : ℝ) (hf : BL f) : BL (fun x => c * f x) := {
  B := |c| * hf.B
  B_nonneg := mul_nonneg (abs_nonneg c) hf.B_nonneg
  bound := by
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf.bound x) (abs_nonneg c)
  C := Real.toNNReal |c| * hf.C
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, show c * f x - c * f y = c * (f x - f y) by ring,
      abs_mul]
    have h := hf.lipschitz.dist_le_mul x y
    rw [Real.dist_eq] at h
    have hc : (↑(Real.toNNReal |c|) : ℝ) = |c| :=
      Real.coe_toNNReal |c| (abs_nonneg c)
    rw [NNReal.coe_mul, hc]
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left h (abs_nonneg c))
}

def mul (hf : BL f) (hg : BL g) : BL (fun x => f x * g x) := by
  let C : ℝ := hf.B * hg.C + hg.B * hf.C
  have hC : 0 ≤ C := by
    exact add_nonneg
      (mul_nonneg hf.B_nonneg (NNReal.coe_nonneg hg.C))
      (mul_nonneg hg.B_nonneg (NNReal.coe_nonneg hf.C))
  refine {
    B := hf.B * hg.B
    B_nonneg := mul_nonneg hf.B_nonneg hg.B_nonneg
    bound := ?_
    C := ⟨C, hC⟩
    lipschitz := ?_
  }
  · intro x
    rw [abs_mul]
    exact mul_le_mul (hf.bound x) (hg.bound x) (abs_nonneg _) hf.B_nonneg
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, show f x * g x - f y * g y =
      f x * (g x - g y) + g y * (f x - f y) by ring]
    calc
      |f x * (g x - g y) + g y * (f x - f y)| ≤
          |f x| * |g x - g y| + |g y| * |f x - f y| := by
        simpa only [abs_mul] using abs_add_le
          (f x * (g x - g y)) (g y * (f x - f y))
      _ ≤ hf.B * (hg.C * dist x y) + hg.B * (hf.C * dist x y) := by
        exact add_le_add
          (mul_le_mul (hf.bound x)
            (by simpa [Real.dist_eq] using hg.lipschitz.dist_le_mul x y)
            (abs_nonneg _) hf.B_nonneg)
          (mul_le_mul (hg.bound y)
            (by simpa [Real.dist_eq] using hf.lipschitz.dist_le_mul x y)
            (abs_nonneg _) hg.B_nonneg)
      _ = C * dist x y := by dsimp [C]; ring

def comp (hf : BL f) {u : F → E} {C : NNReal}
    (hu : LipschitzWith C u) : BL (fun x => f (u x)) := {
  B := hf.B
  B_nonneg := hf.B_nonneg
  bound := fun x => hf.bound (u x)
  C := hf.C * C
  lipschitz := hf.lipschitz.comp hu
}

end BL

private def realBL_of_deriv_bounds (f f' : ℝ → ℝ) (B C : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hval : ∀ t, |f t| ≤ B)
    (hderiv : ∀ t, HasDerivAt f (f' t) t) (hprime : ∀ t, |f' t| ≤ C) :
    BL f := by
  refine {
    B := B
    B_nonneg := hB
    bound := hval
    C := ⟨C, hC⟩
    lipschitz := ?_
  }
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro t
    exact (hderiv t).differentiableAt
  · intro t
    rw [(hderiv t).deriv]
    exact_mod_cast hprime t

/-! ## Concrete scalar packages -/

private theorem frontierSwitch_deriv_eq_zero_of_not_mem
    {t : ℝ} (ht : t ∉ Set.Icc (-(1 : ℝ)) 2) :
    deriv frontierSwitch t = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · exact frontierSwitch_deriv_eq_zero_of_le_fifth (by linarith)
  · have heq : Set.EqOn frontierSwitch (fun _ : ℝ => 1)
        (Set.Ioi (1 : ℝ)) := by
      intro x hx
      exact frontierSwitch_eq_one_of_one_le hx.le
    have ht' : t ∈ Set.Ioi (1 : ℝ) := by
      show (1 : ℝ) < t
      linarith
    simpa using heq.deriv isOpen_Ioi ht'

private theorem frontierSwitch_deriv_bounded :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |deriv frontierSwitch t| ≤ C := by
  have hcont : Continuous (fun t : ℝ => |deriv frontierSwitch t|) :=
    (frontierSwitch_contDiff.continuous_deriv (by
      exact_mod_cast (show (1 : ℕ∞) ≤ ⊤ from le_top))).abs
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.continuousOn)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (-(1 : ℝ)) 2
  · exact (hC _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  · rw [frontierSwitch_deriv_eq_zero_of_not_mem ht, abs_zero]
    exact le_max_right _ _

private noncomputable def frontierDerivBound : ℝ :=
  Classical.choose frontierSwitch_deriv_bounded

private theorem frontierDerivBound_spec :
    0 ≤ frontierDerivBound ∧
      ∀ t, |deriv frontierSwitch t| ≤ frontierDerivBound :=
  Classical.choose_spec frontierSwitch_deriv_bounded

private noncomputable def scalarSecondBound (K : ℝ) : ℝ :=
  Classical.choose (scalar_interfaces_common_second_deriv_bound K)

private theorem scalarSecondBound_spec (K : ℝ) :
    0 ≤ scalarSecondBound K ∧ ∀ t : ℝ,
      |deriv (deriv stateClip) t| ≤ scalarSecondBound K ∧
      |deriv (deriv pulseClip) t| ≤ scalarSecondBound K ∧
      |deriv (deriv frontierSwitch) t| ≤ scalarSecondBound K ∧
      |deriv (deriv (phasePotential K)) t| ≤ scalarSecondBound K :=
  Classical.choose_spec (scalar_interfaces_common_second_deriv_bound K)

private theorem hasDerivAt_deriv_stateClip (t : ℝ) :
    HasDerivAt (deriv stateClip) (deriv (deriv stateClip) t) t := by
  have htwo : ContDiff ℝ (2 : ℕ∞) stateClip :=
    stateClip_contDiff.of_le (by
      exact_mod_cast (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact (htwo.differentiable_deriv_two t).hasDerivAt

private theorem hasDerivAt_deriv_pulseClip (t : ℝ) :
    HasDerivAt (deriv pulseClip) (deriv (deriv pulseClip) t) t := by
  have htwo : ContDiff ℝ (2 : ℕ∞) pulseClip :=
    pulseClip_contDiff.of_le (by
      exact_mod_cast (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact (htwo.differentiable_deriv_two t).hasDerivAt

private theorem hasDerivAt_deriv_frontierSwitch (t : ℝ) :
    HasDerivAt (deriv frontierSwitch) (deriv (deriv frontierSwitch) t) t := by
  have htwo : ContDiff ℝ (2 : ℕ∞) frontierSwitch :=
    frontierSwitch_contDiff.of_le (by
      exact_mod_cast (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact (htwo.differentiable_deriv_two t).hasDerivAt

private theorem hasDerivAt_deriv_phasePotential (K t : ℝ) :
    HasDerivAt (deriv (phasePotential K))
      (deriv (deriv (phasePotential K)) t) t := by
  have htwo : ContDiff ℝ (2 : ℕ∞) (phasePotential K) :=
    (phasePotential_contDiff K).of_le (by
      exact_mod_cast (show (2 : ℕ∞) ≤ ⊤ from le_top))
  exact (htwo.differentiable_deriv_two t).hasDerivAt

private noncomputable def stateBL : BL stateClip :=
  realBL_of_deriv_bounds stateClip (deriv stateClip) 3 1 (by norm_num)
    (by norm_num) stateClip_abs_le_three
    (fun t => (stateClip_contDiff.differentiable (by simp) t).hasDerivAt)
    (fun t => by
      rcases stateClip_deriv_mem_unitInterval t with ⟨h0, h1⟩
      rw [abs_of_nonneg h0]
      exact h1)

private noncomputable def pulseBL : BL pulseClip :=
  realBL_of_deriv_bounds pulseClip (deriv pulseClip) 22 1 (by norm_num)
    (by norm_num) pulseClip_abs_le_twentyTwo
    (fun t => (pulseClip_contDiff.differentiable (by simp) t).hasDerivAt)
    (fun t => by
      rcases pulseClip_deriv_mem_unitInterval t with ⟨h0, h1⟩
      rw [abs_of_nonneg h0]
      exact h1)

private noncomputable def frontierBL : BL frontierSwitch :=
  realBL_of_deriv_bounds frontierSwitch (deriv frontierSwitch) 1
    frontierDerivBound (by norm_num) frontierDerivBound_spec.1
    (fun t => by
      rcases frontierSwitch_mem_unitInterval t with ⟨h0, h1⟩
      rw [abs_of_nonneg h0]
      exact h1)
    (fun t => (frontierSwitch_contDiff.differentiable (by simp) t).hasDerivAt)
    frontierDerivBound_spec.2

private noncomputable def stateDerivBL (K : ℝ) : BL (deriv stateClip) :=
  realBL_of_deriv_bounds (deriv stateClip) (deriv (deriv stateClip)) 1
    (scalarSecondBound K) (by norm_num) (scalarSecondBound_spec K).1
    (fun t => by
      rcases stateClip_deriv_mem_unitInterval t with ⟨h0, h1⟩
      rw [abs_of_nonneg h0]
      exact h1)
    hasDerivAt_deriv_stateClip
    (fun t => (scalarSecondBound_spec K).2 t |>.1)

private noncomputable def pulseDerivBL (K : ℝ) : BL (deriv pulseClip) :=
  realBL_of_deriv_bounds (deriv pulseClip) (deriv (deriv pulseClip)) 1
    (scalarSecondBound K) (by norm_num) (scalarSecondBound_spec K).1
    (fun t => by
      rcases pulseClip_deriv_mem_unitInterval t with ⟨h0, h1⟩
      rw [abs_of_nonneg h0]
      exact h1)
    hasDerivAt_deriv_pulseClip
    (fun t => (scalarSecondBound_spec K).2 t |>.2.1)

private noncomputable def frontierDerivBL (K : ℝ) : BL (deriv frontierSwitch) :=
  realBL_of_deriv_bounds (deriv frontierSwitch)
    (deriv (deriv frontierSwitch)) frontierDerivBound
    (scalarSecondBound K) frontierDerivBound_spec.1
    (scalarSecondBound_spec K).1 frontierDerivBound_spec.2
    hasDerivAt_deriv_frontierSwitch
    (fun t => (scalarSecondBound_spec K).2 t |>.2.2.1)

private noncomputable def phaseDerivBL (K : ℝ) (hK : 0 < K) :
    BL (deriv (phasePotential K)) :=
  realBL_of_deriv_bounds (deriv (phasePotential K))
    (deriv (deriv (phasePotential K))) (K + 25) (scalarSecondBound K)
    (by linarith) (scalarSecondBound_spec K).1
    (phasePotential_first_deriv_bounded hK)
    (fun t => hasDerivAt_deriv_phasePotential K t)
    (fun t => (scalarSecondBound_spec K).2 t |>.2.2.2)

/-! ## One four-coordinate outer block -/

/-- Local order is `(predecessor memory, current memory, entrance, exit)`. -/
abbrev LocalOuterSpace := EVec 4

private def pIdx : Fin 4 := ⟨0, by omega⟩
private def sIdx : Fin 4 := ⟨1, by omega⟩
private def aIdx : Fin 4 := ⟨2, by omega⟩
private def bIdx : Fin 4 := ⟨3, by omega⟩

def localOuter (K : ℝ) (z : LocalOuterSpace) : ℝ :=
  phasePotential K (z sIdx) +
    24 * frontierSwitch (z sIdx) * (1 - stateClip (z pIdx)) *
      (1 - frontierSwitch (z pIdx)) +
    (-4) * frontierSwitch (z pIdx) * (1 - frontierSwitch (z sIdx)) *
      pulseClip (z aIdx) +
    (-1) * frontierSwitch (z pIdx) * stateClip (z sIdx) *
      (1 - frontierSwitch (z sIdx)) * pulseClip (z bIdx)

/-- Explicit predecessor-memory partial derivative. -/
def localGradP (z : LocalOuterSpace) : ℝ :=
  24 * frontierSwitch (z sIdx) *
      ((-deriv stateClip (z pIdx)) * (1 - frontierSwitch (z pIdx)) -
        (1 - stateClip (z pIdx)) * deriv frontierSwitch (z pIdx)) +
    (-4) * deriv frontierSwitch (z pIdx) *
      (1 - frontierSwitch (z sIdx)) * pulseClip (z aIdx) +
    (-1) * deriv frontierSwitch (z pIdx) * stateClip (z sIdx) *
      (1 - frontierSwitch (z sIdx)) * pulseClip (z bIdx)

/-- Explicit current-memory partial derivative. -/
def localGradS (K : ℝ) (z : LocalOuterSpace) : ℝ :=
  deriv (phasePotential K) (z sIdx) +
    24 * deriv frontierSwitch (z sIdx) * (1 - stateClip (z pIdx)) *
      (1 - frontierSwitch (z pIdx)) +
    4 * frontierSwitch (z pIdx) * deriv frontierSwitch (z sIdx) *
      pulseClip (z aIdx) +
    (-1) * frontierSwitch (z pIdx) *
      (deriv stateClip (z sIdx) * (1 - frontierSwitch (z sIdx)) -
        stateClip (z sIdx) * deriv frontierSwitch (z sIdx)) *
      pulseClip (z bIdx)

def localGradA (z : LocalOuterSpace) : ℝ :=
  (-4) * frontierSwitch (z pIdx) * (1 - frontierSwitch (z sIdx)) *
    deriv pulseClip (z aIdx)

def localGradB (z : LocalOuterSpace) : ℝ :=
  (-1) * frontierSwitch (z pIdx) * stateClip (z sIdx) *
    (1 - frontierSwitch (z sIdx)) * deriv pulseClip (z bIdx)

def explicitLocalGradient (K : ℝ) (z : LocalOuterSpace) : LocalOuterSpace :=
  fun k =>
    if k.val = 0 then localGradP z
    else if k.val = 1 then localGradS K z
    else if k.val = 2 then localGradA z
    else localGradB z

namespace BL

def coord {f : ℝ → ℝ} (hf : BL f) (i : Fin 4) :
    BL (fun z : LocalOuterSpace => f (z i)) :=
  hf.comp (LipschitzWith.eval i)

def oneSub {E : Type*} [PseudoMetricSpace E] {f : E → ℝ} (hf : BL f) :
    BL (fun x => 1 - f x) :=
  (BL.const 1).sub hf

end BL

private noncomputable def localGradPBL (K : ℝ) : BL localGradP := by
  let Ap := frontierBL.coord pIdx
  let As := frontierBL.coord sIdx
  let Cp := stateBL.coord pIdx
  let Cs := stateBL.coord sIdx
  let Pa := pulseBL.coord aIdx
  let Pb := pulseBL.coord bIdx
  let dAp := (frontierDerivBL K).coord pIdx
  let dCp := (stateDerivBL K).coord pIdx
  let ord := BL.smul 24
    (As.mul ((dCp.neg.mul Ap.oneSub).sub (Cp.oneSub.mul dAp)))
  let ent := BL.smul (-4) ((dAp.mul As.oneSub).mul Pa)
  let ext := BL.smul (-1) (((dAp.mul Cs).mul As.oneSub).mul Pb)
  convert (ord.add ent).add ext using 1
  funext z
  unfold localGradP
  ring

private noncomputable def localGradSBL (K : ℝ) (hK : 0 < K) :
    BL (localGradS K) := by
  let Ap := frontierBL.coord pIdx
  let As := frontierBL.coord sIdx
  let Cp := stateBL.coord pIdx
  let Cs := stateBL.coord sIdx
  let Pa := pulseBL.coord aIdx
  let Pb := pulseBL.coord bIdx
  let dAs := (frontierDerivBL K).coord sIdx
  let dCs := (stateDerivBL K).coord sIdx
  let dU := (phaseDerivBL K hK).coord sIdx
  let ord := BL.smul 24 ((dAs.mul Cp.oneSub).mul Ap.oneSub)
  let ent := BL.smul 4 ((Ap.mul dAs).mul Pa)
  let ext := BL.smul (-1)
    ((Ap.mul ((dCs.mul As.oneSub).sub (Cs.mul dAs))).mul Pb)
  convert ((dU.add ord).add ent).add ext using 1
  funext z
  unfold localGradS
  ring

private noncomputable def localGradABL (K : ℝ) : BL localGradA := by
  let Ap := frontierBL.coord pIdx
  let As := frontierBL.coord sIdx
  let dPa := (pulseDerivBL K).coord aIdx
  let h := BL.smul (-4) ((Ap.mul As.oneSub).mul dPa)
  convert h using 1
  funext z
  unfold localGradA
  ring

private noncomputable def localGradBBL (K : ℝ) : BL localGradB := by
  let Ap := frontierBL.coord pIdx
  let As := frontierBL.coord sIdx
  let Cs := stateBL.coord sIdx
  let dPb := (pulseDerivBL K).coord bIdx
  let h := BL.smul (-1) (((Ap.mul Cs).mul As.oneSub).mul dPb)
  convert h using 1
  funext z
  unfold localGradB
  ring

noncomputable def localOuterC (K : ℝ) (hK : 0 < K) : ℝ :=
  (localGradPBL K).C + (localGradSBL K hK).C +
    (localGradABL K).C + (localGradBBL K).C

theorem localOuterC_nonneg (K : ℝ) (hK : 0 < K) :
    0 ≤ localOuterC K hK := by
  unfold localOuterC
  positivity

private theorem explicitLocalGradient_coord_bound (K : ℝ) (hK : 0 < K)
    (z w : LocalOuterSpace) (k : Fin 4) :
    |explicitLocalGradient K z k - explicitLocalGradient K w k| ≤
      localOuterC K hK * Real.sqrt (vecSq (z - w)) := by
  have hnorm := norm_le_sqrt_vecSq (z - w)
  have hP := (localGradPBL K).lipschitz.dist_le_mul z w
  have hS := (localGradSBL K hK).lipschitz.dist_le_mul z w
  have hA := (localGradABL K).lipschitz.dist_le_mul z w
  have hB := (localGradBBL K).lipschitz.dist_le_mul z w
  rw [Real.dist_eq] at hP hS hA hB
  have hCP : ((localGradPBL K).C : ℝ) ≤ localOuterC K hK := by
    unfold localOuterC
    nlinarith [NNReal.coe_nonneg (localGradSBL K hK).C,
      NNReal.coe_nonneg (localGradABL K).C,
      NNReal.coe_nonneg (localGradBBL K).C]
  have hCS : ((localGradSBL K hK).C : ℝ) ≤ localOuterC K hK := by
    unfold localOuterC
    nlinarith [NNReal.coe_nonneg (localGradPBL K).C,
      NNReal.coe_nonneg (localGradABL K).C,
      NNReal.coe_nonneg (localGradBBL K).C]
  have hCA : ((localGradABL K).C : ℝ) ≤ localOuterC K hK := by
    unfold localOuterC
    nlinarith [NNReal.coe_nonneg (localGradPBL K).C,
      NNReal.coe_nonneg (localGradSBL K hK).C,
      NNReal.coe_nonneg (localGradBBL K).C]
  have hCB : ((localGradBBL K).C : ℝ) ≤ localOuterC K hK := by
    unfold localOuterC
    nlinarith [NNReal.coe_nonneg (localGradPBL K).C,
      NNReal.coe_nonneg (localGradSBL K hK).C,
      NNReal.coe_nonneg (localGradABL K).C]
  rw [dist_eq_norm] at hP hS hA hB
  fin_cases k
  · simp only [explicitLocalGradient, ↓reduceIte]
    exact hP.trans <| (mul_le_mul_of_nonneg_right hCP (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hnorm (localOuterC_nonneg K hK))
  · simp only [explicitLocalGradient, ↓reduceIte]
    exact hS.trans <| (mul_le_mul_of_nonneg_right hCS (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hnorm (localOuterC_nonneg K hK))
  · simp only [explicitLocalGradient, ↓reduceIte]
    exact hA.trans <| (mul_le_mul_of_nonneg_right hCA (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hnorm (localOuterC_nonneg K hK))
  · simp only [explicitLocalGradient, ↓reduceIte]
    exact hB.trans <| (mul_le_mul_of_nonneg_right hCB (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hnorm (localOuterC_nonneg K hK))

/-- Dimension-free Euclidean Lipschitz estimate for one local outer block. -/
theorem explicitLocalGradient_vecSq_sub_le (K : ℝ) (hK : 0 < K)
    (z w : LocalOuterSpace) :
    vecSq (explicitLocalGradient K z - explicitLocalGradient K w) ≤
      (2 * localOuterC K hK) ^ 2 * vecSq (z - w) := by
  have hs : 0 ≤ vecSq (z - w) := vecSq_nonneg _
  have hroot := Real.sq_sqrt hs
  have hcoord : ∀ k : Fin 4,
      (explicitLocalGradient K z k - explicitLocalGradient K w k) ^ 2 ≤
        localOuterC K hK ^ 2 * vecSq (z - w) := by
    intro k
    have hk := explicitLocalGradient_coord_bound K hK z w k
    have hleft : 0 ≤ |explicitLocalGradient K z k -
        explicitLocalGradient K w k| := abs_nonneg _
    have hright : 0 ≤ localOuterC K hK * Real.sqrt (vecSq (z - w)) :=
      mul_nonneg (localOuterC_nonneg K hK) (Real.sqrt_nonneg _)
    have hsq := (sq_le_sq₀ hleft hright).2 hk
    rw [sq_abs, mul_pow, hroot] at hsq
    simpa only [Pi.sub_apply] using hsq
  calc
    vecSq (explicitLocalGradient K z - explicitLocalGradient K w) ≤
        ∑ _k : Fin 4, localOuterC K hK ^ 2 * vecSq (z - w) := by
      unfold vecSq NCPLVerification.vecSq
      exact Finset.sum_le_sum fun k _ => hcoord k
    _ = 4 * (localOuterC K hK ^ 2 * vecSq (z - w)) := by simp
    _ = (2 * localOuterC K hK) ^ 2 * vecSq (z - w) := by ring

/-! ## The local field is the actual Fréchet gradient -/

def explicitLocalGradientCLM (K : ℝ) (z : LocalOuterSpace) :
    LocalOuterSpace →L[ℝ] ℝ :=
  ∑ k : Fin 4, (explicitLocalGradient K z k) •
    NCPLVerification.evecProj k

theorem explicitLocalGradientCLM_apply (K : ℝ) (z d : LocalOuterSpace) :
    explicitLocalGradientCLM K z d =
      ∑ k : Fin 4, explicitLocalGradient K z k * d k := by
  unfold explicitLocalGradientCLM
  rw [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp [NCPLVerification.evecProj_apply]

theorem hasFDerivAt_localOuter (K : ℝ) (z : LocalOuterSpace) :
    HasFDerivAt (localOuter K) (explicitLocalGradientCLM K z) z := by
  letI : AddCommGroup LocalOuterSpace := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ LocalOuterSpace := Pi.normedSpace.toModule
  letI : TopologicalSpace LocalOuterSpace :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have hp : HasFDerivAt (fun w : LocalOuterSpace => w pIdx)
      (NCPLVerification.evecProj pIdx) z :=
    (NCPLVerification.evecProj pIdx).hasFDerivAt
  have hs : HasFDerivAt (fun w : LocalOuterSpace => w sIdx)
      (NCPLVerification.evecProj sIdx) z :=
    (NCPLVerification.evecProj sIdx).hasFDerivAt
  have ha : HasFDerivAt (fun w : LocalOuterSpace => w aIdx)
      (NCPLVerification.evecProj aIdx) z :=
    (NCPLVerification.evecProj aIdx).hasFDerivAt
  have hb : HasFDerivAt (fun w : LocalOuterSpace => w bIdx)
      (NCPLVerification.evecProj bIdx) z :=
    (NCPLVerification.evecProj bIdx).hasFDerivAt
  have hAp := ((frontierSwitch_contDiff.differentiable (by simp)
    (z pIdx)).hasDerivAt.hasFDerivAt.comp z hp)
  have hAs := ((frontierSwitch_contDiff.differentiable (by simp)
    (z sIdx)).hasDerivAt.hasFDerivAt.comp z hs)
  have hCp := ((stateClip_contDiff.differentiable (by simp)
    (z pIdx)).hasDerivAt.hasFDerivAt.comp z hp)
  have hCs := ((stateClip_contDiff.differentiable (by simp)
    (z sIdx)).hasDerivAt.hasFDerivAt.comp z hs)
  have hPa := ((pulseClip_contDiff.differentiable (by simp)
    (z aIdx)).hasDerivAt.hasFDerivAt.comp z ha)
  have hPb := ((pulseClip_contDiff.differentiable (by simp)
    (z bIdx)).hasDerivAt.hasFDerivAt.comp z hb)
  have hU := (hasDerivAt_phasePotential K (z sIdx)).hasFDerivAt.comp z hs
  have hOneP := (hasFDerivAt_const (x := z) (1 : ℝ)).sub hCp
  have hOneAp := (hasFDerivAt_const (x := z) (1 : ℝ)).sub hAp
  have hOneAs := (hasFDerivAt_const (x := z) (1 : ℝ)).sub hAs
  have hord := (((hAs.const_mul 24).mul hOneP).mul hOneAp)
  have hent := (((hAp.const_mul (-4)).mul hOneAs).mul hPa)
  have hext := ((((hAp.const_mul (-1)).mul hCs).mul hOneAs).mul hPb)
  have hraw := ((hU.add hord).add hent).add hext
  convert hraw using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  all_goals try { apply TopologicalSpace.ext <;> rfl }
  · funext w
    unfold localOuter
    simp [Function.comp_def]
  · ext d
    rw [explicitLocalGradientCLM_apply]
    simp [explicitLocalGradient, localGradP, localGradS, localGradA,
      localGradB, Fin.sum_univ_succ, NCPLVerification.evecProj_apply,
      pIdx, sIdx, aIdx, bIdx, Function.comp_def, deriv_phasePotential]
    ring

/-- Coordinate extraction from the Fréchet derivative is exactly the
explicit local field used in the Lipschitz estimate. -/
theorem continuousLinearMapCoordinates_fderiv_localOuter (K : ℝ)
    (z : LocalOuterSpace) :
    NCPLVerification.continuousLinearMapCoordinates
        (fderiv ℝ (localOuter K) z) = explicitLocalGradient K z := by
  have hf := (hasFDerivAt_localOuter K z).fderiv
  funext k
  unfold NCPLVerification.continuousLinearMapCoordinates
  rw [hf, explicitLocalGradientCLM_apply]
  classical
  simp [NCPLVerification.evecBasis, explicitLocalGradient]

/-! ## Sparse assembly over the chain -/

/-- The four inputs seen by one outer summand: predecessor memory, current
memory, entrance pulse, and exit pulse. -/
def outerLocalInput {M : Nat} (x : FlatPrimal M) (i : Fin M) :
    LocalOuterSpace :=
  ![previousMemory (flatState x) i, flatState x i,
    flatEntrance x i, flatExit x i]

@[simp] theorem outerLocalInput_p {M : Nat} (x : FlatPrimal M) (i : Fin M) :
    outerLocalInput x i pIdx = previousMemory (flatState x) i := by
  simp [outerLocalInput, pIdx]

@[simp] theorem outerLocalInput_s {M : Nat} (x : FlatPrimal M) (i : Fin M) :
    outerLocalInput x i sIdx = flatState x i := by
  simp [outerLocalInput, sIdx]

@[simp] theorem outerLocalInput_a {M : Nat} (x : FlatPrimal M) (i : Fin M) :
    outerLocalInput x i aIdx = flatEntrance x i := by
  simp [outerLocalInput, aIdx]

@[simp] theorem outerLocalInput_b {M : Nat} (x : FlatPrimal M) (i : Fin M) :
    outerLocalInput x i bIdx = flatExit x i := by
  simp [outerLocalInput, bIdx]

private theorem flatPrimal_vecSq_expansion {M : Nat} (x : FlatPrimal M) :
    vecSq x = ∑ i : Fin M,
      ((flatState x i) ^ 2 + (flatEntrance x i) ^ 2 + (flatExit x i) ^ 2) := by
  unfold vecSq NCPLVerification.vecSq
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp [flatState, flatEntrance, flatExit, Fin.sum_univ_succ, add_assoc]

private abbrev NonzeroBlock (M : Nat) := {i : Fin M // i.val ≠ 0}

private def predecessorFlatIndex {M : Nat} (i : NonzeroBlock M) : Fin (M * 3) :=
  finProdFinEquiv
    (⟨i.val.val - 1, by omega⟩, (⟨0, by omega⟩ : Fin 3))

private theorem predecessorFlatIndex_injective {M : Nat} :
    Function.Injective (predecessorFlatIndex (M := M)) := by
  intro i j h
  have h' := finProdFinEquiv.injective h
  apply Subtype.ext
  apply Fin.ext
  have hv := congrArg (fun p : Fin M × Fin 3 => p.1.val) h'
  dsimp [predecessorFlatIndex] at hv
  omega

private theorem sum_sq_comp_injective_le_vecSq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Nat}
    (idx : ι → Fin m) (hidx : Function.Injective idx) (x : EVec m) :
    (∑ i, (x (idx i)) ^ 2) ≤ vecSq x := by
  classical
  unfold vecSq NCPLVerification.vecSq
  calc
    (∑ i, (x (idx i)) ^ 2) =
        (∑ j ∈ Finset.univ.image idx, (x j) ^ 2) := by
          rw [Finset.sum_image hidx.injOn]
    _ ≤ ∑ j, (x j) ^ 2 :=
      Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg (x j))

private theorem sum_previousMemory_sub_sq_le {M : Nat}
    (x r : FlatPrimal M) :
    (∑ i : Fin M,
      (previousMemory (flatState x) i -
        previousMemory (flatState r) i) ^ 2) ≤ vecSq (x - r) := by
  let F : Fin M → ℝ := fun i =>
    (previousMemory (flatState x) i -
      previousMemory (flatState r) i) ^ 2
  have hpart := Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin M => i.val ≠ 0) F
  have hzero : (∑ i : {i : Fin M // ¬ i.val ≠ 0}, F i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi0 : i.val.val = 0 := by omega
    simp [F, previousMemory, hi0]
  have hall : (∑ i : Fin M, F i) = ∑ i : NonzeroBlock M, F i := by
    rw [hzero, add_zero] at hpart
    exact hpart.symm
  rw [show (∑ i : Fin M,
      (previousMemory (flatState x) i -
        previousMemory (flatState r) i) ^ 2) = ∑ i : Fin M, F i by rfl,
    hall]
  have hcoord : (∑ i : NonzeroBlock M, F i) =
      ∑ i : NonzeroBlock M, ((x - r) (predecessorFlatIndex i)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    simp [F, previousMemory, i.property, flatState, predecessorFlatIndex]
  rw [hcoord]
  exact sum_sq_comp_injective_le_vecSq _ predecessorFlatIndex_injective (x - r)

private theorem outerLocalInput_vecSq_expansion {M : Nat}
    (x r : FlatPrimal M) (i : Fin M) :
    vecSq (outerLocalInput x i - outerLocalInput r i) =
      (previousMemory (flatState x) i -
          previousMemory (flatState r) i) ^ 2 +
        (flatState x i - flatState r i) ^ 2 +
        (flatEntrance x i - flatEntrance r i) ^ 2 +
        (flatExit x i - flatExit r i) ^ 2 := by
  unfold vecSq NCPLVerification.vecSq
  simp [outerLocalInput, Fin.sum_univ_succ]
  ring

/-- Every primal coordinate enters at most two local outer blocks.  This is
the dimension-free overlap estimate used below. -/
theorem sum_outerLocalInput_vecSq_le {M : Nat} (x r : FlatPrimal M) :
    (∑ i : Fin M, vecSq (outerLocalInput x i - outerLocalInput r i)) ≤
      2 * vecSq (x - r) := by
  have hp := sum_previousMemory_sub_sq_le x r
  have hflat :
      (∑ i : Fin M,
        ((flatState x i - flatState r i) ^ 2 +
          (flatEntrance x i - flatEntrance r i) ^ 2 +
          (flatExit x i - flatExit r i) ^ 2)) = vecSq (x - r) := by
    rw [flatPrimal_vecSq_expansion]
    rfl
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hflat
  simp_rw [outerLocalInput_vecSq_expansion]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  nlinarith

private def stateFlatIndex {M : Nat} (i : Fin M) : Fin (M * 3) :=
  finProdFinEquiv (i, (⟨0, by omega⟩ : Fin 3))

private def entranceFlatIndex {M : Nat} (i : Fin M) : Fin (M * 3) :=
  finProdFinEquiv (i, (⟨1, by omega⟩ : Fin 3))

private def exitFlatIndex {M : Nat} (i : Fin M) : Fin (M * 3) :=
  finProdFinEquiv (i, (⟨2, by omega⟩ : Fin 3))

private theorem stateFlatIndex_injective {M : Nat} :
    Function.Injective (stateFlatIndex (M := M)) := by
  intro i j h
  exact congrArg Prod.fst (finProdFinEquiv.injective h)

private theorem entranceFlatIndex_injective {M : Nat} :
    Function.Injective (entranceFlatIndex (M := M)) := by
  intro i j h
  exact congrArg Prod.fst (finProdFinEquiv.injective h)

private theorem exitFlatIndex_injective {M : Nat} :
    Function.Injective (exitFlatIndex (M := M)) := by
  intro i j h
  exact congrArg Prod.fst (finProdFinEquiv.injective h)

private def predecessorOutputIndex {M : Nat} (i : NonzeroBlock M) :
    Fin (M * 3) :=
  stateFlatIndex ⟨i.val.val - 1, by omega⟩

private theorem predecessorOutputIndex_injective {M : Nat} :
    Function.Injective (predecessorOutputIndex (M := M)) := by
  intro i j h
  have h' := stateFlatIndex_injective h
  apply Subtype.ext
  apply Fin.ext
  have hv := congrArg Fin.val h'
  dsimp [predecessorOutputIndex] at hv
  omega

private theorem vecSq_sum_single_of_injective
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Nat}
    (idx : ι → Fin m) (hidx : Function.Injective idx) (f : ι → ℝ) :
    vecSq (∑ i, Pi.single (idx i) (f i) : EVec m) = ∑ i, (f i) ^ 2 := by
  classical
  unfold vecSq NCPLVerification.vecSq
  let s : Finset (Fin m) := Finset.univ.image idx
  rw [← Finset.sum_subset (Finset.subset_univ s)]
  · rw [Finset.sum_image hidx.injOn]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.sum_apply, Pi.single_apply]
    simp [hidx.eq_iff]
  · intro j _ hjs
    simp only [Finset.sum_apply, Pi.single_apply]
    have hne : ∀ i, idx i ≠ j := by
      intro i hij
      apply hjs
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hij⟩
    have hne' : ∀ i, j ≠ idx i := fun i => (hne i).symm
    simp [hne']

private theorem sum_single_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : Nat} (idx : ι → Fin m) (f g : ι → ℝ) :
    (∑ i, Pi.single (idx i) (f i) : EVec m) -
        (∑ i, Pi.single (idx i) (g i) : EVec m) =
      ∑ i, Pi.single (idx i) (f i - g i) := by
  classical
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ext j
  by_cases h : j = idx i <;> simp [Pi.single_apply, h]

/-- The predecessor-coordinate part of the outer gradient. -/
def outerPreviousField {M : Nat} (K : ℝ) (x : FlatPrimal M) :
    FlatPrimal M :=
  ∑ i : NonzeroBlock M,
    Pi.single (predecessorOutputIndex i)
      (localGradP (outerLocalInput x i))

/-- The current-memory part of the outer gradient. -/
def outerStateField {M : Nat} (K : ℝ) (x : FlatPrimal M) :
    FlatPrimal M :=
  ∑ i : Fin M, Pi.single (stateFlatIndex i)
    (localGradS K (outerLocalInput x i))

/-- The entrance-pulse part of the outer gradient. -/
def outerEntranceField {M : Nat} (K : ℝ) (x : FlatPrimal M) :
    FlatPrimal M :=
  ∑ i : Fin M, Pi.single (entranceFlatIndex i)
    (localGradA (outerLocalInput x i))

/-- The exit-pulse part of the outer gradient. -/
def outerExitField {M : Nat} (K : ℝ) (x : FlatPrimal M) :
    FlatPrimal M :=
  ∑ i : Fin M, Pi.single (exitFlatIndex i)
    (localGradB (outerLocalInput x i))

/-- Explicit sparse gradient of the four outer components. -/
def outerPrimalField {M : Nat} (K : ℝ) (x : FlatPrimal M) :
    FlatPrimal M :=
  outerPreviousField K x + outerStateField K x +
    outerEntranceField K x + outerExitField K x

private theorem vecSq_outerPrevious_sub {M : Nat} (K : ℝ)
    (x r : FlatPrimal M) :
    vecSq (outerPreviousField K x - outerPreviousField K r) =
      ∑ i : NonzeroBlock M,
        (localGradP (outerLocalInput x i) -
          localGradP (outerLocalInput r i)) ^ 2 := by
  unfold outerPreviousField
  rw [sum_single_sub]
  exact vecSq_sum_single_of_injective _ predecessorOutputIndex_injective _

private theorem vecSq_outerState_sub {M : Nat} (K : ℝ)
    (x r : FlatPrimal M) :
    vecSq (outerStateField K x - outerStateField K r) =
      ∑ i : Fin M,
        (localGradS K (outerLocalInput x i) -
          localGradS K (outerLocalInput r i)) ^ 2 := by
  unfold outerStateField
  rw [sum_single_sub]
  exact vecSq_sum_single_of_injective _ stateFlatIndex_injective _

private theorem vecSq_outerEntrance_sub {M : Nat} (K : ℝ)
    (x r : FlatPrimal M) :
    vecSq (outerEntranceField K x - outerEntranceField K r) =
      ∑ i : Fin M,
        (localGradA (outerLocalInput x i) -
          localGradA (outerLocalInput r i)) ^ 2 := by
  unfold outerEntranceField
  rw [sum_single_sub]
  exact vecSq_sum_single_of_injective _ entranceFlatIndex_injective _

private theorem vecSq_outerExit_sub {M : Nat} (K : ℝ)
    (x r : FlatPrimal M) :
    vecSq (outerExitField K x - outerExitField K r) =
      ∑ i : Fin M,
        (localGradB (outerLocalInput x i) -
          localGradB (outerLocalInput r i)) ^ 2 := by
  unfold outerExitField
  rw [sum_single_sub]
  exact vecSq_sum_single_of_injective _ exitFlatIndex_injective _

private theorem sum_comp_injective_le_sum_of_nonneg
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (idx : ι → κ) (hidx : Function.Injective idx)
    (f : κ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    (∑ i, f (idx i)) ≤ ∑ k, f k := by
  classical
  calc
    (∑ i, f (idx i)) = ∑ k ∈ Finset.univ.image idx, f k := by
      rw [Finset.sum_image hidx.injOn]
    _ ≤ ∑ k, f k := Finset.sum_le_univ_sum_of_nonneg hf

private theorem vecSq_add_four_le {m : Nat} (a b c d : EVec m) :
    vecSq (a + b + c + d) ≤
      4 * (vecSq a + vecSq b + vecSq c + vecSq d) := by
  unfold vecSq NCPLVerification.vecSq
  calc
    (∑ i, (a + b + c + d) i ^ 2) ≤
        ∑ i, 4 * (a i ^ 2 + b i ^ 2 + c i ^ 2 + d i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (a i - b i),
        sq_nonneg (a i + b i - 2 * c i),
        sq_nonneg (a i + b i + c i - 3 * d i)]
    _ = 4 * ((∑ i, a i ^ 2) + (∑ i, b i ^ 2) +
        (∑ i, c i ^ 2) + (∑ i, d i ^ 2)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
      simp_rw [← Finset.mul_sum]

private theorem outerPrimalField_sub_decomposition {M : Nat} (K : ℝ)
    (x r : FlatPrimal M) :
    outerPrimalField K x - outerPrimalField K r =
      (outerPreviousField K x - outerPreviousField K r) +
      (outerStateField K x - outerStateField K r) +
      (outerEntranceField K x - outerEntranceField K r) +
      (outerExitField K x - outerExitField K r) := by
  ext j
  simp [outerPrimalField]
  ring

/-- The full outer field is dimension-free Lipschitz.  The constant comes
from the local four-coordinate estimate and overlap two, never from `M`. -/
theorem outerPrimalField_vecSq_sub_le {M : Nat} (K : ℝ) (hK : 0 < K)
    (x r : FlatPrimal M) :
    vecSq (outerPrimalField K x - outerPrimalField K r) ≤
      (6 * localOuterC K hK) ^ 2 * vecSq (x - r) := by
  let P := outerPreviousField K x - outerPreviousField K r
  let S := outerStateField K x - outerStateField K r
  let A := outerEntranceField K x - outerEntranceField K r
  let B := outerExitField K x - outerExitField K r
  have hfour := vecSq_add_four_le P S A B
  rw [outerPrimalField_sub_decomposition]
  change vecSq (P + S + A + B) ≤ _
  have hP := vecSq_outerPrevious_sub K x r
  have hS := vecSq_outerState_sub K x r
  have hA := vecSq_outerEntrance_sub K x r
  have hB := vecSq_outerExit_sub K x r
  have hPall : vecSq P ≤ ∑ i : Fin M,
      (localGradP (outerLocalInput x i) -
        localGradP (outerLocalInput r i)) ^ 2 := by
    rw [hP]
    exact sum_comp_injective_le_sum_of_nonneg
      (fun i : NonzeroBlock M => i.val) Subtype.val_injective
      (fun i : Fin M => (localGradP (outerLocalInput x i) -
        localGradP (outerLocalInput r i)) ^ 2)
      (fun _ => sq_nonneg _)
  have hlocal : (∑ i : Fin M,
      vecSq (explicitLocalGradient K (outerLocalInput x i) -
        explicitLocalGradient K (outerLocalInput r i))) ≤
      (2 * localOuterC K hK) ^ 2 *
        ∑ i : Fin M, vecSq (outerLocalInput x i - outerLocalInput r i) := by
    calc
      _ ≤ ∑ i : Fin M, (2 * localOuterC K hK) ^ 2 *
          vecSq (outerLocalInput x i - outerLocalInput r i) :=
        Finset.sum_le_sum (fun i _ =>
          explicitLocalGradient_vecSq_sub_le K hK
            (outerLocalInput x i) (outerLocalInput r i))
      _ = _ := by rw [Finset.mul_sum]
  have hinput := sum_outerLocalInput_vecSq_le x r
  have hcomponents :
      vecSq P + vecSq S + vecSq A + vecSq B ≤
        ∑ i : Fin M,
          vecSq (explicitLocalGradient K (outerLocalInput x i) -
            explicitLocalGradient K (outerLocalInput r i)) := by
    have hgrad (i : Fin M) :
        vecSq (explicitLocalGradient K (outerLocalInput x i) -
            explicitLocalGradient K (outerLocalInput r i)) =
          (localGradP (outerLocalInput x i) -
              localGradP (outerLocalInput r i)) ^ 2 +
            (localGradS K (outerLocalInput x i) -
              localGradS K (outerLocalInput r i)) ^ 2 +
            (localGradA (outerLocalInput x i) -
              localGradA (outerLocalInput r i)) ^ 2 +
            (localGradB (outerLocalInput x i) -
              localGradB (outerLocalInput r i)) ^ 2 := by
      unfold vecSq NCPLVerification.vecSq
      simp [explicitLocalGradient, Fin.sum_univ_succ]
      ring
    rw [hS, hA, hB]
    simp_rw [hgrad]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib]
    linarith
  have hC0 : 0 ≤ localOuterC K hK := localOuterC_nonneg K hK
  have hsq0 : 0 ≤ (2 * localOuterC K hK) ^ 2 := sq_nonneg _
  nlinarith [vecSq_nonneg P, vecSq_nonneg S, vecSq_nonneg A,
    vecSq_nonneg B]

/-! ## Blockwise assembly of the corrected relay -/

/-- Serialize one relay input in the order `(a,w,b)`. -/
def relayInput {N : Nat} (a b : ℝ) (w : EVec N) : EVec (N + 2) :=
  Fin.cons a (Fin.snoc w b)

@[simp] theorem jointA_relayInput {N : Nat} (a b : ℝ) (w : EVec N) :
    jointA (relayInput a b w) = a := by
  simp [jointA, relayInput]

@[simp] theorem jointW_relayInput {N : Nat} (a b : ℝ) (w : EVec N) :
    jointW (relayInput a b w) = w := by
  unfold jointW relayInput
  funext i
  rw [show (⟨i.val + 1, by omega⟩ : Fin (N + 2)) = i.castSucc.succ by
    apply Fin.ext
    simp]
  simp

@[simp] theorem jointB_relayInput {N : Nat} (a b : ℝ) (w : EVec N) :
    jointB (relayInput a b w) = b := by
  unfold jointB relayInput
  rw [show (⟨N + 1, by omega⟩ : Fin (N + 2)) = Fin.last (N + 1) by
    apply Fin.ext
    simp]
  simp

theorem vecSq_relayInput {N : Nat} (a b : ℝ) (w : EVec N) :
    vecSq (relayInput a b w) = a ^ 2 + vecSq w + b ^ 2 := by
  rw [vecSq_joint_decomposition]
  simp

@[simp] theorem relayInput_first {N : Nat} (a b : ℝ) (w : EVec N) :
    relayInput a b w ⟨0, by omega⟩ = a := by
  simp [relayInput]

@[simp] theorem relayInput_middle {N : Nat} (a b : ℝ) (w : EVec N)
    (k : Fin N) :
    relayInput a b w ⟨k.val + 1, by omega⟩ = w k := by
  unfold relayInput
  rw [show (⟨k.val + 1, by omega⟩ : Fin (N + 2)) = k.castSucc.succ by
    apply Fin.ext
    simp]
  simp

@[simp] theorem relayInput_last {N : Nat} (a b : ℝ) (w : EVec N) :
    relayInput a b w ⟨N + 1, by omega⟩ = b := by
  unfold relayInput
  rw [show (⟨N + 1, by omega⟩ : Fin (N + 2)) = Fin.last (N + 1) by
    apply Fin.ext
    simp]
  simp

private def blockRelayInput {M N : Nat} (x : FlatPrimal M)
    (y : FlatDual M N) (i : Fin M) : EVec (N + 2) :=
  relayInput (flatEntrance x i) (flatExit x i) (unflattenBlocks y i)

private def innerAField {M N : Nat} (hN : 0 < N)
    (x : FlatPrimal M) (y : FlatDual M N) : FlatPrimal M :=
  ∑ i : Fin M, Pi.single (entranceFlatIndex i)
    (relayField hN (blockRelayInput x y i) ⟨0, by omega⟩)

private def innerBField {M N : Nat} (hN : 0 < N)
    (x : FlatPrimal M) (y : FlatDual M N) : FlatPrimal M :=
  ∑ i : Fin M, Pi.single (exitFlatIndex i)
    (relayField hN (blockRelayInput x y i) ⟨N + 1, by omega⟩)

/-- The primal part of the signed relay field. -/
def innerPrimalField {M N : Nat} (hN : 0 < N)
    (x : FlatPrimal M) (y : FlatDual M N) : FlatPrimal M :=
  innerAField hN x y + innerBField hN x y

/-- The dual part of the signed relay field.  Recall that the true dual
gradient of the concave relay is its negative. -/
def innerSignedDualField {M N : Nat} (hN : 0 < N)
    (x : FlatPrimal M) (y : FlatDual M N) : FlatDual M N :=
  flattenBlocks (fun i k =>
    relayField hN (blockRelayInput x y i) ⟨k.val + 1, by omega⟩)

private theorem vecSq_innerA_sub {M N : Nat} (hN : 0 < N)
    (x r : FlatPrimal M) (y v : FlatDual M N) :
    vecSq (innerAField hN x y - innerAField hN r v) =
      ∑ i : Fin M,
        (relayField hN (blockRelayInput x y i) ⟨0, by omega⟩ -
          relayField hN (blockRelayInput r v i) ⟨0, by omega⟩) ^ 2 := by
  unfold innerAField
  rw [sum_single_sub]
  exact vecSq_sum_single_of_injective _ entranceFlatIndex_injective _

private theorem vecSq_innerB_sub {M N : Nat} (hN : 0 < N)
    (x r : FlatPrimal M) (y v : FlatDual M N) :
    vecSq (innerBField hN x y - innerBField hN r v) =
      ∑ i : Fin M,
        (relayField hN (blockRelayInput x y i) ⟨N + 1, by omega⟩ -
          relayField hN (blockRelayInput r v i) ⟨N + 1, by omega⟩) ^ 2 := by
  unfold innerBField
  rw [sum_single_sub]
  exact vecSq_sum_single_of_injective _ exitFlatIndex_injective _

private theorem vecSq_add_le_two {m : Nat} (u v : EVec m) :
    vecSq (u + v) ≤ 2 * vecSq u + 2 * vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (u i - v i)]

private theorem blockRelayInput_vecSq_sub {M N : Nat}
    (x r : FlatPrimal M) (y v : FlatDual M N) (i : Fin M) :
    vecSq (blockRelayInput x y i - blockRelayInput r v i) =
      (flatEntrance x i - flatEntrance r i) ^ 2 +
        vecSq (unflattenBlocks y i - unflattenBlocks v i) +
        (flatExit x i - flatExit r i) ^ 2 := by
  have heq : blockRelayInput x y i - blockRelayInput r v i =
      relayInput (flatEntrance x i - flatEntrance r i)
        (flatExit x i - flatExit r i)
        (unflattenBlocks y i - unflattenBlocks v i) := by
    have hsnoc :
        (Fin.snoc (unflattenBlocks y i) (flatExit x i) -
          Fin.snoc (unflattenBlocks v i) (flatExit r i) : Fin (N + 1) → ℝ) =
        Fin.snoc (unflattenBlocks y i - unflattenBlocks v i)
          (flatExit x i - flatExit r i) := by
      funext k
      refine Fin.lastCases ?_ (fun j => ?_) k <;> simp
    have hcons :
        (Fin.cons (flatEntrance x i)
            (Fin.snoc (unflattenBlocks y i) (flatExit x i)) -
          Fin.cons (flatEntrance r i)
            (Fin.snoc (unflattenBlocks v i) (flatExit r i)) : Fin (N + 2) → ℝ) =
        Fin.cons (flatEntrance x i - flatEntrance r i)
          (Fin.snoc (unflattenBlocks y i - unflattenBlocks v i)
            (flatExit x i - flatExit r i)) := by
      funext k
      refine Fin.cases ?_ (fun j => ?_) k
      · simp
      · simpa only [Fin.cons_succ, Pi.sub_apply] using congrFun hsnoc j
    simpa only [blockRelayInput, relayInput] using hcons
  rw [heq, vecSq_relayInput]

private theorem flatDual_vecSq_sub_expansion {M N : Nat}
    (y v : FlatDual M N) :
    vecSq (y - v) =
      ∑ i : Fin M, vecSq (unflattenBlocks y i - unflattenBlocks v i) := by
  calc
    vecSq (y - v) = vecSq (flattenBlocks (unflattenBlocks (y - v))) := by
      rw [flattenBlocks_unflattenBlocks]
    _ = ∑ i : Fin M, vecSq (unflattenBlocks (y - v) i) :=
      vecSq_flattenBlocks (unflattenBlocks (y - v))
    _ = _ := by rfl

/-- The block relay inputs are an orthogonal reindexing of the two pulse
coordinates and the dual coordinates; the unused state coordinates only
increase the ambient input energy. -/
theorem sum_blockRelayInput_vecSq_sub_le {M N : Nat}
    (x r : FlatPrimal M) (y v : FlatDual M N) :
    (∑ i : Fin M,
      vecSq (blockRelayInput x y i - blockRelayInput r v i)) ≤
      NCPLVerification.jointSq (x - r) (y - v) := by
  have hflat := flatPrimal_vecSq_expansion (x - r)
  have hdual := flatDual_vecSq_sub_expansion y v
  have hstate0 : 0 ≤ ∑ i : Fin M,
      (flatState x i - flatState r i) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  simp_rw [blockRelayInput_vecSq_sub]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  change _ ≤ vecSq (x - r) + vecSq (y - v)
  rw [hdual]
  have hflat' : vecSq (x - r) =
      (∑ i : Fin M, (flatState x i - flatState r i) ^ 2) +
      (∑ i : Fin M, (flatEntrance x i - flatEntrance r i) ^ 2) +
      (∑ i : Fin M, (flatExit x i - flatExit r i) ^ 2) := by
    rw [hflat]
    simp only [flatState, flatEntrance, flatExit, Pi.sub_apply]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [hflat']
  nlinarith

private theorem innerPrimalField_sub_decomposition {M N : Nat}
    (hN : 0 < N) (x r : FlatPrimal M) (y v : FlatDual M N) :
    innerPrimalField hN x y - innerPrimalField hN r v =
      (innerAField hN x y - innerAField hN r v) +
      (innerBField hN x y - innerBField hN r v) := by
  ext j
  simp [innerPrimalField]
  ring

private theorem innerSignedDualField_sub_vecSq {M N : Nat}
    (hN : 0 < N) (x r : FlatPrimal M) (y v : FlatDual M N) :
    vecSq (innerSignedDualField hN x y - innerSignedDualField hN r v) =
      ∑ i : Fin M, vecSq (fun k : Fin N =>
        relayField hN (blockRelayInput x y i) ⟨k.val + 1, by omega⟩ -
          relayField hN (blockRelayInput r v i) ⟨k.val + 1, by omega⟩) := by
  have heq : innerSignedDualField hN x y - innerSignedDualField hN r v =
      flattenBlocks (fun i k =>
        relayField hN (blockRelayInput x y i) ⟨k.val + 1, by omega⟩ -
          relayField hN (blockRelayInput r v i) ⟨k.val + 1, by omega⟩) := by
    ext j
    rfl
  rw [heq, vecSq_flattenBlocks]

private theorem relayFieldDifference_vecSq {N : Nat} (hN : 0 < N)
    (q r : EVec (N + 2)) :
    vecSq (relayField hN q - relayField hN r) =
      (relayField hN q ⟨0, by omega⟩ -
          relayField hN r ⟨0, by omega⟩) ^ 2 +
        vecSq (fun k : Fin N =>
          relayField hN q ⟨k.val + 1, by omega⟩ -
            relayField hN r ⟨k.val + 1, by omega⟩) +
        (relayField hN q ⟨N + 1, by omega⟩ -
          relayField hN r ⟨N + 1, by omega⟩) ^ 2 := by
  rw [vecSq_joint_decomposition]
  rfl

/-- The assembled signed relay field has squared Lipschitz constant `200`,
uniformly in both the number and the length of the relay blocks. -/
theorem innerSignedField_vecSq_sub_le {M N : Nat} (hN10 : 10 ≤ N)
    (x r : FlatPrimal M) (y v : FlatDual M N) :
    NCPLVerification.jointSq
        (innerPrimalField (by omega : 0 < N) x y -
          innerPrimalField (by omega : 0 < N) r v)
        (innerSignedDualField (by omega : 0 < N) x y -
          innerSignedDualField (by omega : 0 < N) r v) ≤
      200 * NCPLVerification.jointSq (x - r) (y - v) := by
  let hN : 0 < N := by omega
  let A := innerAField hN x y - innerAField hN r v
  let B := innerBField hN x y - innerBField hN r v
  let Y := innerSignedDualField hN x y - innerSignedDualField hN r v
  have hprimal := vecSq_add_le_two A B
  have hA := vecSq_innerA_sub hN x r y v
  have hB := vecSq_innerB_sub hN x r y v
  have hY := innerSignedDualField_sub_vecSq hN x r y v
  have hblocks :
      (∑ i : Fin M,
        vecSq (relayField hN (blockRelayInput x y i) -
          relayField hN (blockRelayInput r v i))) ≤
        100 * ∑ i : Fin M,
          vecSq (blockRelayInput x y i - blockRelayInput r v i) := by
    calc
      _ ≤ ∑ i : Fin M, 100 *
          vecSq (blockRelayInput x y i - blockRelayInput r v i) :=
        Finset.sum_le_sum (fun i _ =>
          relayField_sub_vecSq_le hN10
            (blockRelayInput x y i) (blockRelayInput r v i))
      _ = _ := by rw [Finset.mul_sum]
  have houtput : vecSq A + vecSq Y + vecSq B =
      ∑ i : Fin M,
        vecSq (relayField hN (blockRelayInput x y i) -
          relayField hN (blockRelayInput r v i)) := by
    rw [hA, hY, hB]
    simp_rw [relayFieldDifference_vecSq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hinput := sum_blockRelayInput_vecSq_sub_le x r y v
  change (∑ i : Fin M,
      vecSq (blockRelayInput x y i - blockRelayInput r v i)) ≤
    vecSq (x - r) + vecSq (y - v) at hinput
  have hY0 : 0 ≤ vecSq Y := vecSq_nonneg Y
  rw [innerPrimalField_sub_decomposition]
  change NCPLVerification.jointSq (A + B) Y ≤ _
  change vecSq (A + B) + vecSq Y ≤
    200 * (vecSq (x - r) + vecSq (y - v))
  nlinarith

/-! ## The complete explicit signed field -/

def assembledPrimalField {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : FlatPrimal M) (y : FlatDual M N) : FlatPrimal M :=
  outerPrimalField K x + innerPrimalField hN x y

def assembledDualGradient {M N : Nat} (hN : 0 < N)
    (x : FlatPrimal M) (y : FlatDual M N) : FlatDual M N :=
  -innerSignedDualField hN x y

/-- A concrete constant depending only on the fixed scalar interface `K`.
It is independent of `M`, `N`, and the later diameter parameter. -/
def compositeEll0 (K : ℝ) (hK : 0 < K) : ℝ :=
  12 * localOuterC K hK + 20

theorem compositeEll0_pos (K : ℝ) (hK : 0 < K) :
    0 < compositeEll0 K hK := by
  unfold compositeEll0
  have hC := localOuterC_nonneg K hK
  linarith

private theorem assembledPrimalField_sub_decomposition {M N : Nat}
    (hN : 0 < N) (K : ℝ) (x r : FlatPrimal M) (y v : FlatDual M N) :
    assembledPrimalField hN K x y - assembledPrimalField hN K r v =
      (outerPrimalField K x - outerPrimalField K r) +
      (innerPrimalField hN x y - innerPrimalField hN r v) := by
  ext j
  simp [assembledPrimalField]
  ring

theorem assembledSignedField_vecSq_sub_le {M N : Nat}
    (hN10 : 10 ≤ N) (K : ℝ) (hK : 0 < K)
    (x r : FlatPrimal M) (y v : FlatDual M N) :
    NCPLVerification.jointSq
        (assembledPrimalField (by omega : 0 < N) K x y -
          assembledPrimalField (by omega : 0 < N) K r v)
        (innerSignedDualField (by omega : 0 < N) x y -
          innerSignedDualField (by omega : 0 < N) r v) ≤
      (compositeEll0 K hK) ^ 2 *
        NCPLVerification.jointSq (x - r) (y - v) := by
  let hN : 0 < N := by omega
  let O := outerPrimalField K x - outerPrimalField K r
  let I := innerPrimalField hN x y - innerPrimalField hN r v
  let Y := innerSignedDualField hN x y - innerSignedDualField hN r v
  have hadd := vecSq_add_le_two O I
  have houter := outerPrimalField_vecSq_sub_le K hK x r
  have hinner := innerSignedField_vecSq_sub_le hN10 x r y v
  change vecSq O ≤ (6 * localOuterC K hK) ^ 2 * vecSq (x - r) at houter
  change vecSq I + vecSq Y ≤
    200 * (vecSq (x - r) + vecSq (y - v)) at hinner
  have hx0 : 0 ≤ vecSq (x - r) := vecSq_nonneg _
  have hy0 : 0 ≤ vecSq (y - v) := vecSq_nonneg _
  have hY0 : 0 ≤ vecSq Y := vecSq_nonneg _
  have hC0 := localOuterC_nonneg K hK
  rw [assembledPrimalField_sub_decomposition]
  change vecSq (O + I) + vecSq Y ≤
    compositeEll0 K hK ^ 2 * (vecSq (x - r) + vecSq (y - v))
  unfold compositeEll0
  nlinarith

theorem assembledFields_jointlySmooth {M N : Nat} (hN10 : 10 ≤ N)
    (K : ℝ) (hK : 0 < K) :
    NCPLVerification.IsJointlySmooth (compositeEll0 K hK)
      (assembledPrimalField (M := M) (by omega : 0 < N) K)
      (assembledDualGradient (M := M) (by omega : 0 < N)) := by
  intro x y r v
  have h := assembledSignedField_vecSq_sub_le hN10 K hK x r y v
  unfold assembledDualGradient
  have hneg :
      (-innerSignedDualField (by omega : 0 < N) x y -
        -innerSignedDualField (by omega : 0 < N) r v) =
      -(innerSignedDualField (by omega : 0 < N) x y -
        innerSignedDualField (by omega : 0 < N) r v) := by
    ext j
    simp
    ring
  rw [hneg]
  have hsqneg : ∀ {m : Nat} (z : EVec m), vecSq (-z) = vecSq z := by
    intro m z
    unfold vecSq NCPLVerification.vecSq
    simp
  change vecSq (assembledPrimalField (by omega : 0 < N) K x y -
      assembledPrimalField (by omega : 0 < N) K r v) +
      vecSq (-(innerSignedDualField (by omega : 0 < N) x y -
        innerSignedDualField (by omega : 0 < N) r v)) ≤ _
  rw [hsqneg]
  exact h

/-! ## Identification with the actual Fréchet gradient -/

/-- Linear part of the affine four-coordinate decoder of one outer block. -/
def outerLocalDirection {M : Nat} (d : FlatPrimal M) (i : Fin M) :
    LocalOuterSpace :=
  ![if hi : i.val = 0 then 0
      else flatState d ⟨i.val - 1, by omega⟩,
    flatState d i, flatEntrance d i, flatExit d i]

def outerLocalDirectionLinear {M : Nat} (i : Fin M) :
    FlatPrimal M →ₗ[ℝ] LocalOuterSpace where
  toFun d := outerLocalDirection d i
  map_add' d e := by
    ext k
    fin_cases k
    · by_cases hi : i.val = 0 <;>
        simp [outerLocalDirection, flatState, flatEntrance, flatExit, hi]
    · simp [outerLocalDirection, flatState, flatEntrance, flatExit]
    · simp [outerLocalDirection, flatState, flatEntrance, flatExit]
    · simp [outerLocalDirection, flatState, flatEntrance, flatExit]
  map_smul' c d := by
    ext k
    fin_cases k
    · by_cases hi : i.val = 0 <;>
        simp [outerLocalDirection, flatState, flatEntrance, flatExit, hi]
    · simp [outerLocalDirection, flatState, flatEntrance, flatExit]
    · simp [outerLocalDirection, flatState, flatEntrance, flatExit]
    · simp [outerLocalDirection, flatState, flatEntrance, flatExit]

def outerLocalDirectionCLM {M : Nat} (i : Fin M) :
    FlatPrimal M →L[ℝ] LocalOuterSpace :=
  LinearMap.toContinuousLinearMap (outerLocalDirectionLinear i)

@[simp] theorem outerLocalDirectionCLM_apply {M : Nat}
    (i : Fin M) (d : FlatPrimal M) :
    outerLocalDirectionCLM i d = outerLocalDirection d i := rfl

private theorem outerLocalInput_affine {M : Nat} (x : FlatPrimal M)
    (i : Fin M) :
    outerLocalInput x i = outerLocalInput 0 i + outerLocalDirection x i := by
  ext k
  fin_cases k
  · by_cases hi : i.val = 0
    · simp [outerLocalInput, outerLocalDirection, previousMemory, hi,
        flatState, flatEntrance, flatExit]
    · simp [outerLocalInput, outerLocalDirection, previousMemory, hi,
        flatState, flatEntrance, flatExit]
  · simp [outerLocalInput, outerLocalDirection, flatState, flatEntrance,
      flatExit]
  · simp [outerLocalInput, outerLocalDirection, flatState, flatEntrance,
      flatExit]
  · simp [outerLocalInput, outerLocalDirection, flatState, flatEntrance,
      flatExit]

theorem hasFDerivAt_outerLocalInput {M : Nat} (x : FlatPrimal M)
    (i : Fin M) :
    HasFDerivAt (fun z : FlatPrimal M => outerLocalInput z i)
      (outerLocalDirectionCLM i) x := by
  have h := (hasFDerivAt_const (x := x) (outerLocalInput (0 : FlatPrimal M) i)).add
    (outerLocalDirectionCLM i).hasFDerivAt
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  all_goals try { apply TopologicalSpace.ext <;> rfl }
  all_goals try { simp only [zero_add] }
  funext z
  simpa only [Pi.add_apply, outerLocalDirectionCLM_apply] using
    outerLocalInput_affine z i

/-- Actual Fréchet derivative of one outer summand after insertion into the
full primal vector. -/
theorem hasFDerivAt_localOuter_comp_input {M : Nat} (K : ℝ)
    (x : FlatPrimal M) (i : Fin M) :
    HasFDerivAt (fun z : FlatPrimal M => localOuter K (outerLocalInput z i))
      ((explicitLocalGradientCLM K (outerLocalInput x i)).comp
        (outerLocalDirectionCLM i)) x := by
  exact (hasFDerivAt_localOuter K (outerLocalInput x i)).comp x
    (hasFDerivAt_outerLocalInput x i)

/-- Flattened version of the four purely primal outer components. -/
def flatOuterObjective {M : Nat} (K : ℝ) (x : FlatPrimal M) : ℝ :=
  outerComponent K (flatState x) (flatEntrance x) (flatExit x)

theorem flatOuterObjective_eq_sum_local {M : Nat} (K : ℝ)
    (x : FlatPrimal M) :
    flatOuterObjective K x = ∑ i : Fin M, localOuter K (outerLocalInput x i) := by
  unfold flatOuterObjective outerComponent phaseComponent orderingComponent
    entranceComponent exitComponent orderingSummand entranceSummand
    exitSummand localOuter
  simp only [outerLocalInput_p, outerLocalInput_s, outerLocalInput_a,
    outerLocalInput_b]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  ring

def flatOuterDerivative {M : Nat} (K : ℝ) (x : FlatPrimal M) :
    FlatPrimal M →L[ℝ] ℝ :=
  ∑ i : Fin M, (explicitLocalGradientCLM K (outerLocalInput x i)).comp
    (outerLocalDirectionCLM i)

theorem hasFDerivAt_flatOuterObjective {M : Nat} (K : ℝ)
    (x : FlatPrimal M) :
    HasFDerivAt (flatOuterObjective K) (flatOuterDerivative K x) x := by
  rw [show flatOuterObjective K =
      fun z : FlatPrimal M => ∑ i : Fin M, localOuter K (outerLocalInput z i) by
    funext z
    exact flatOuterObjective_eq_sum_local K z]
  unfold flatOuterDerivative
  apply HasFDerivAt.fun_sum
  intro i _
  exact hasFDerivAt_localOuter_comp_input K x i

private theorem evecDot_add {m : Nat} (u v d : EVec m) :
    NCPLVerification.evecDot (u + v) d =
      NCPLVerification.evecDot u d + NCPLVerification.evecDot v d := by
  simp only [NCPLVerification.evecDot_apply, Pi.add_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem evecDot_sum_single
    {ι : Type*} [Fintype ι] [DecidableEq ι] {m : Nat}
    (idx : ι → Fin m) (f : ι → ℝ) (d : EVec m) :
    NCPLVerification.evecDot
        (∑ i, Pi.single (idx i) (f i) : EVec m) d =
      ∑ i, f i * d (idx i) := by
  classical
  rw [NCPLVerification.evecDot_apply]
  simp_rw [Finset.sum_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [Pi.single_apply]

theorem flatOuterDerivative_apply {M : Nat} (K : ℝ)
    (x d : FlatPrimal M) :
    flatOuterDerivative K x d =
      NCPLVerification.evecDot (outerPrimalField K x) d := by
  have hterm (i : Fin M) :
      (explicitLocalGradientCLM K (outerLocalInput x i)).comp
          (outerLocalDirectionCLM i) d =
        localGradP (outerLocalInput x i) *
            (if hi : i.val = 0 then 0
              else flatState d ⟨i.val - 1, by omega⟩) +
          localGradS K (outerLocalInput x i) * flatState d i +
          localGradA (outerLocalInput x i) * flatEntrance d i +
          localGradB (outerLocalInput x i) * flatExit d i := by
    rw [ContinuousLinearMap.comp_apply, explicitLocalGradientCLM_apply]
    simp [explicitLocalGradient, outerLocalDirection, Fin.sum_univ_succ]
    ring
  let F : Fin M → ℝ := fun i =>
    localGradP (outerLocalInput x i) *
      (if hi : i.val = 0 then 0
        else flatState d ⟨i.val - 1, by omega⟩)
  have hpart := Fintype.sum_subtype_add_sum_subtype
    (fun i : Fin M => i.val ≠ 0) F
  have hzero : (∑ i : {i : Fin M // ¬ i.val ≠ 0}, F i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi0 : i.val.val = 0 := by omega
    simp [F, hi0]
  have hprev : (∑ i : Fin M, F i) =
      ∑ i : NonzeroBlock M,
        localGradP (outerLocalInput x i) *
          flatState d ⟨i.val.val - 1, by omega⟩ := by
    rw [hzero, add_zero] at hpart
    rw [hpart.symm]
    apply Finset.sum_congr rfl
    intro i _
    simp [F, i.property]
  unfold flatOuterDerivative
  rw [_root_.sum_apply]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  change (∑ i : Fin M, F i) + _ + _ + _ = _
  rw [hprev]
  unfold outerPrimalField
  rw [evecDot_add, evecDot_add, evecDot_add]
  unfold outerPreviousField outerStateField outerEntranceField outerExitField
  rw [evecDot_sum_single, evecDot_sum_single, evecDot_sum_single,
    evecDot_sum_single]
  simp [predecessorOutputIndex, stateFlatIndex, entranceFlatIndex,
    exitFlatIndex, flatState, flatEntrance, flatExit]

/-! ### The actual joint derivative of one relay -/

def relayObjective {N : Nat} (hN : 0 < N) (q : EVec (N + 2)) : ℝ :=
  correctedH hN (jointA q) (jointB q) (jointW q)

/-- True (unsigned) gradient of one relay in `(a,w,b)` order. -/
def relayTrueGradient {N : Nat} (hN : 0 < N) (q : EVec (N + 2)) :
    EVec (N + 2) := fun j =>
  if hj0 : j.val = 0 then relayGradA hN (jointA q) (jointW q)
  else if hjm : j.val ≤ N then
    -relaySaddleGradW hN (jointA q) (jointB q) (jointW q)
      ⟨j.val - 1, by omega⟩
  else relayGradB hN (jointB q) (jointW q)

private theorem relayObjective_contDiff {N : Nat} (hN : 0 < N) :
    ContDiff ℝ (⊤ : ℕ∞) (relayObjective hN) := by
  have ha : ContDiff ℝ (⊤ : ℕ∞) (jointA : EVec (N + 2) → ℝ) := by
    unfold jointA
    fun_prop
  have hb : ContDiff ℝ (⊤ : ℕ∞) (jointB : EVec (N + 2) → ℝ) := by
    unfold jointB
    fun_prop
  have hw : ContDiff ℝ (⊤ : ℕ∞) (jointW : EVec (N + 2) → EVec N) := by
    unfold jointW
    fun_prop
  have hsq : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : EVec (N + 2) => vecSq (jointW q)) := by
    unfold vecSq NCPLVerification.vecSq
    apply ContDiff.sum
    intro i _
    exact ((contDiff_apply ℝ ℝ i).comp hw).pow 2
  have hpath : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : EVec (N + 2) => pathEnergy N (jointW q)) := by
    cases N with
    | zero => simpa [pathEnergy] using
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞)
          (fun _ : EVec (0 + 2) => (0 : ℝ)))
    | succ n =>
      simp only [pathEnergy]
      apply ContDiff.sum
      intro i _
      exact (((contDiff_apply ℝ ℝ i.castSucc).comp hw).sub
        ((contDiff_apply ℝ ℝ i.succ).comp hw)).pow 2
  have hquad : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : EVec (N + 2) => regularizedPathQuad N (jointW q)) := by
    unfold regularizedPathQuad
    exact (contDiff_const.mul hsq).add hpath
  have hwfirst : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : EVec (N + 2) => jointW q (first hN)) :=
    (contDiff_apply ℝ ℝ (first hN)).comp hw
  have hwlast : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : EVec (N + 2) => jointW q (last hN)) :=
    (contDiff_apply ℝ ℝ (last hN)).comp hw
  have hforcing : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : EVec (N + 2) =>
        endpointForcing hN (jointA q) (jointB q) (jointW q)) := by
    unfold endpointForcing
    exact (ha.mul hwfirst).sub (hb.mul hwlast)
  unfold relayObjective correctedH relayH
  exact (((contDiff_const.mul hquad).add
    (contDiff_const.mul hforcing)).add
      (contDiff_const.mul ((ha.pow 2).add (hb.pow 2))))

/-- The affine line replacing one coordinate of an arbitrary Euclidean
vector.  Unlike `serializedCoordinateLine`, its dimension is unrestricted. -/
def evecCoordinateLine {m : Nat} (q : EVec m) (j : Fin m) (t : ℝ) :
    EVec m := q + (t - q j) • NCPLVerification.evecBasis j

private theorem coordinateLine_hasDerivAt {m : Nat} (q : EVec m)
    (j : Fin m) :
    HasDerivAt (fun t : ℝ => evecCoordinateLine q j t)
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

private theorem hasFDerivAt_evecDot_of_coordinate_derivatives {m : Nat}
    {f : EVec m → ℝ} {q g : EVec m} (hdiff : DifferentiableAt ℝ f q)
    (hcoord : ∀ j : Fin m,
      HasDerivAt (fun t : ℝ => f (evecCoordinateLine q j t))
        (g j) (q j)) :
    HasFDerivAt f (NCPLVerification.evecDot g) q := by
  have hf := hdiff.hasFDerivAt
  convert hf using 1
  apply ContinuousLinearMap.ext
  intro d
  rw [NCPLVerification.evecDot_apply]
  rw [NCPLVerification.continuousLinearMap_apply_eq_coordinates
    (fderiv ℝ f q) d]
  apply Finset.sum_congr rfl
  intro j _
  have hf' : HasFDerivAt f (fderiv ℝ f q)
      (evecCoordinateLine q j (q j)) := by
    rw [show evecCoordinateLine q j (q j) = q by
      simp [evecCoordinateLine]]
    exact hf
  have hc := hf'.comp (q j) (coordinateLine_hasDerivAt q j)
  have hu := (hcoord j).unique hc.hasDerivAt
  have hu' : g j =
      NCPLVerification.continuousLinearMapCoordinates (fderiv ℝ f q) j := by
    simpa [NCPLVerification.continuousLinearMapCoordinates] using hu
  rw [hu']

theorem hasDerivAt_relayObjective_coordinateLine {N : Nat}
    (hN : 0 < N) (q : EVec (N + 2)) (j : Fin (N + 2)) :
    HasDerivAt
      (fun t : ℝ => relayObjective hN (evecCoordinateLine q j t))
      (relayTrueGradient hN q j) (q j) := by
  by_cases hj0 : j.val = 0
  · have hj : j = (⟨0, by omega⟩ : Fin (N + 2)) := by
      apply Fin.ext
      exact hj0
    rw [hj]
    have haline (t : ℝ) :
        jointA (evecCoordinateLine q (⟨0, by omega⟩ : Fin (N + 2)) t) = t := by
      simp [jointA, evecCoordinateLine, NCPLVerification.evecBasis]
    have hbline (t : ℝ) :
        jointB (evecCoordinateLine q (⟨0, by omega⟩ : Fin (N + 2)) t) =
          jointB q := by
      simp [jointB, evecCoordinateLine, NCPLVerification.evecBasis]
    have hwline (t : ℝ) :
        jointW (evecCoordinateLine q (⟨0, by omega⟩ : Fin (N + 2)) t) =
          jointW q := by
      funext k
      simp [jointW, evecCoordinateLine, NCPLVerification.evecBasis]
    have hfun :
        (fun t => relayObjective hN
          (evecCoordinateLine q (⟨0, by omega⟩ : Fin (N + 2)) t)) =
        (fun t => correctedH hN t (jointB q) (jointW q)) := by
      funext t
      rw [relayObjective, haline t, hbline t, hwline t]
    rw [hfun]
    simpa [relayTrueGradient, jointA] using
      CompositeZeroChain.hasDerivAt_correctedH_a hN (jointA q)
        (jointB q) (jointW q)
  · by_cases hjm : j.val ≤ N
    · let k : Fin N := ⟨j.val - 1, by omega⟩
      have hj : j = (⟨k.val + 1, by omega⟩ : Fin (N + 2)) := by
        apply Fin.ext
        dsimp [k]
        omega
      rw [hj]
      have haline (t : ℝ) :
          jointA (evecCoordinateLine q
            (⟨k.val + 1, by omega⟩ : Fin (N + 2)) t) = jointA q := by
        simp [jointA, evecCoordinateLine, NCPLVerification.evecBasis]
      have hbline (t : ℝ) :
          jointB (evecCoordinateLine q
            (⟨k.val + 1, by omega⟩ : Fin (N + 2)) t) = jointB q := by
        simp [jointB, evecCoordinateLine, NCPLVerification.evecBasis] <;> omega
      have hline : (fun t => jointW
          (evecCoordinateLine q (⟨k.val + 1, by omega⟩ : Fin (N + 2)) t)) =
          CompositeZeroChain.relayCoordinateLine (jointW q) k := by
        funext t l
        simp [jointW, evecCoordinateLine,
          CompositeZeroChain.relayCoordinateLine,
          NCPLVerification.evecBasis, Fin.ext_iff]
      have hk0 : k.val + 1 ≠ 0 := by omega
      have hkN : k.val + 1 ≤ N := by omega
      have hfun :
          (fun t => relayObjective hN
            (evecCoordinateLine q
              (⟨k.val + 1, by omega⟩ : Fin (N + 2)) t)) =
          (fun t => correctedH hN (jointA q) (jointB q)
            (CompositeZeroChain.relayCoordinateLine (jointW q) k t)) := by
        funext t
        rw [relayObjective, haline t, hbline t, congrFun hline t]
      rw [hfun]
      simpa [relayTrueGradient, hk0, hkN, jointW, k] using
        CompositeZeroChain.hasDerivAt_correctedH_w hN (jointA q)
          (jointB q) (jointW q) k
    · have hjlast : j.val = N + 1 := by omega
      have hj : j = (⟨N + 1, by omega⟩ : Fin (N + 2)) := by
        apply Fin.ext
        exact hjlast
      rw [hj]
      have haline (t : ℝ) :
          jointA (evecCoordinateLine q (⟨N + 1, by omega⟩ : Fin (N + 2)) t) =
            jointA q := by
        simp [jointA, evecCoordinateLine, NCPLVerification.evecBasis]
      have hbline (t : ℝ) :
          jointB (evecCoordinateLine q (⟨N + 1, by omega⟩ : Fin (N + 2)) t) =
            t := by
        simp [jointB, evecCoordinateLine, NCPLVerification.evecBasis]
      have hwline (t : ℝ) :
          jointW (evecCoordinateLine q (⟨N + 1, by omega⟩ : Fin (N + 2)) t) =
            jointW q := by
        funext k
        simp [jointW, evecCoordinateLine, NCPLVerification.evecBasis] <;> omega
      have hfun :
          (fun t => relayObjective hN
            (evecCoordinateLine q (⟨N + 1, by omega⟩ : Fin (N + 2)) t)) =
          (fun t => correctedH hN (jointA q) t (jointW q)) := by
        funext t
        rw [relayObjective, haline t, hbline t, hwline t]
      rw [hfun]
      simpa [relayTrueGradient, jointB] using
        CompositeZeroChain.hasDerivAt_correctedH_b hN (jointA q)
          (jointB q) (jointW q)

theorem hasFDerivAt_relayObjective {N : Nat} (hN : 0 < N)
    (q : EVec (N + 2)) :
    HasFDerivAt (relayObjective hN)
      (NCPLVerification.evecDot (relayTrueGradient hN q)) q := by
  apply hasFDerivAt_evecDot_of_coordinate_derivatives
  · exact (relayObjective_contDiff hN).differentiable (by simp) q
  · exact hasDerivAt_relayObjective_coordinateLine hN q

/-! ### Assembly of the true inner derivative -/

def blockRelayInputJointLinear {M N : Nat} (i : Fin M) :
    (FlatPrimal M × FlatDual M N) →ₗ[ℝ] EVec (N + 2) where
  toFun z := blockRelayInput z.1 z.2 i
  map_add' z w := by
    ext k
    refine Fin.cases ?_ (fun l => ?_) k
    · simp [blockRelayInput, relayInput, flatEntrance]
    · refine Fin.lastCases ?_ (fun j => ?_) l
      · simp [blockRelayInput, relayInput, flatExit]
      · simp [blockRelayInput, relayInput, unflattenBlocks]
  map_smul' c z := by
    ext k
    refine Fin.cases ?_ (fun l => ?_) k
    · simp [blockRelayInput, relayInput, flatEntrance]
    · refine Fin.lastCases ?_ (fun j => ?_) l
      · simp [blockRelayInput, relayInput, flatExit]
      · simp [blockRelayInput, relayInput, unflattenBlocks]

def blockRelayInputJointCLM {M N : Nat} (i : Fin M) :
    (FlatPrimal M × FlatDual M N) →L[ℝ] EVec (N + 2) :=
  LinearMap.toContinuousLinearMap (blockRelayInputJointLinear i)

@[simp] theorem blockRelayInputJointCLM_apply {M N : Nat} (i : Fin M)
    (z : FlatPrimal M × FlatDual M N) :
    blockRelayInputJointCLM i z = blockRelayInput z.1 z.2 i := rfl

def flatInnerJointObjective {M N : Nat} (hN : 0 < N)
    (z : FlatPrimal M × FlatDual M N) : ℝ :=
  innerComponent hN (flatEntrance z.1) (flatExit z.1)
    (unflattenBlocks z.2)

theorem flatInnerJointObjective_eq_sum {M N : Nat} (hN : 0 < N)
    (z : FlatPrimal M × FlatDual M N) :
    flatInnerJointObjective hN z =
      ∑ i : Fin M, relayObjective hN (blockRelayInput z.1 z.2 i) := by
  simp [flatInnerJointObjective, innerComponent, relayObjective,
    blockRelayInput]

def flatInnerDerivative {M N : Nat} (hN : 0 < N)
    (x : FlatPrimal M) (y : FlatDual M N) :
    (FlatPrimal M × FlatDual M N) →L[ℝ] ℝ :=
  ∑ i : Fin M,
    (NCPLVerification.evecDot
      (relayTrueGradient hN (blockRelayInput x y i))).comp
        (blockRelayInputJointCLM i)

theorem hasFDerivAt_flatInnerJointObjective {M N : Nat} (hN : 0 < N)
    (x : FlatPrimal M) (y : FlatDual M N) :
    HasFDerivAt (flatInnerJointObjective hN)
      (flatInnerDerivative hN x y) (x, y) := by
  rw [show flatInnerJointObjective hN =
      fun z : FlatPrimal M × FlatDual M N =>
        ∑ i : Fin M, relayObjective hN (blockRelayInput z.1 z.2 i) by
    funext z
    exact flatInnerJointObjective_eq_sum hN z]
  unfold flatInnerDerivative
  apply HasFDerivAt.fun_sum
  intro i _
  exact (hasFDerivAt_relayObjective hN (blockRelayInput x y i)).comp
    (x, y) (blockRelayInputJointCLM i).hasFDerivAt

@[simp] theorem relayTrueGradient_first {N : Nat} (hN : 0 < N)
    (q : EVec (N + 2)) :
    relayTrueGradient hN q ⟨0, by omega⟩ = relayField hN q ⟨0, by omega⟩ := by
  rw [relayField_first]
  simp [relayTrueGradient]

@[simp] theorem relayTrueGradient_middle {N : Nat} (hN : 0 < N)
    (q : EVec (N + 2)) (k : Fin N) :
    relayTrueGradient hN q ⟨k.val + 1, by omega⟩ =
      -relayField hN q ⟨k.val + 1, by omega⟩ := by
  have hk0 : k.val + 1 ≠ 0 := by omega
  have hkN : k.val + 1 ≤ N := by omega
  simp [relayTrueGradient, hk0, hkN]

@[simp] theorem relayTrueGradient_last {N : Nat} (hN : 0 < N)
    (q : EVec (N + 2)) :
    relayTrueGradient hN q ⟨N + 1, by omega⟩ =
      relayField hN q ⟨N + 1, by omega⟩ := by
  simp [relayTrueGradient]

private theorem evecDot_relayTrueGradient {N : Nat} (hN : 0 < N)
    (q d : EVec (N + 2)) :
    NCPLVerification.evecDot (relayTrueGradient hN q) d =
      relayField hN q ⟨0, by omega⟩ * d ⟨0, by omega⟩ +
        (∑ k : Fin N,
          (-relayField hN q ⟨k.val + 1, by omega⟩) *
            d ⟨k.val + 1, by omega⟩) +
        relayField hN q ⟨N + 1, by omega⟩ *
          d ⟨N + 1, by omega⟩ := by
  rw [NCPLVerification.evecDot_apply]
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hmiddle :
      (∑ i : Fin N,
        relayTrueGradient hN q i.castSucc.succ * d i.castSucc.succ) =
      ∑ i : Fin N,
        (-relayField hN q ⟨i.val + 1, by omega⟩) *
          d ⟨i.val + 1, by omega⟩ := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.castSucc.succ =
        (⟨i.val + 1, by omega⟩ : Fin (N + 2)) := by
      apply Fin.ext
      simp
    rw [hi, relayTrueGradient_middle]
  rw [hmiddle]
  have hzero : (0 : Fin (N + 2)) = ⟨0, by omega⟩ := by rfl
  have hlast : (Fin.last N).succ =
      (⟨N + 1, by omega⟩ : Fin (N + 2)) := by
    apply Fin.ext
    simp
  rw [hzero, hlast, relayTrueGradient_first, relayTrueGradient_last]
  ring

private theorem evecDot_flattenBlocks {M N : Nat}
    (w : Fin M → EVec N) (y : FlatDual M N) :
    NCPLVerification.evecDot (flattenBlocks w) y =
      ∑ i : Fin M, ∑ k : Fin N, w i k * unflattenBlocks y i k := by
  rw [NCPLVerification.evecDot_apply]
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  simp [flattenBlocks, unflattenBlocks]

theorem flatInnerDerivative_apply {M N : Nat} (hN : 0 < N)
    (x dx : FlatPrimal M) (y dy : FlatDual M N) :
    flatInnerDerivative hN x y (dx, dy) =
      NCPLVerification.evecDot (innerPrimalField hN x y) dx +
        NCPLVerification.evecDot (assembledDualGradient hN x y) dy := by
  unfold flatInnerDerivative
  rw [_root_.sum_apply]
  simp_rw [ContinuousLinearMap.comp_apply, blockRelayInputJointCLM_apply,
    evecDot_relayTrueGradient]
  have hblock (i : Fin M) :
      blockRelayInput dx dy i =
        relayInput (flatEntrance dx i) (flatExit dx i)
          (unflattenBlocks dy i) := rfl
  simp_rw [hblock]
  simp_rw [relayInput_first, relayInput_middle, relayInput_last]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  unfold innerPrimalField
  rw [evecDot_add]
  unfold innerAField innerBField
  rw [evecDot_sum_single, evecDot_sum_single]
  unfold assembledDualGradient innerSignedDualField
  have hneg :
      (-(flattenBlocks (fun i k =>
        relayField hN (blockRelayInput x y i) ⟨k.val + 1, by omega⟩)) :
          FlatDual M N) =
      flattenBlocks (fun i k =>
        -relayField hN (blockRelayInput x y i) ⟨k.val + 1, by omega⟩) := by
    ext j
    rfl
  rw [hneg, evecDot_flattenBlocks]
  simp [entranceFlatIndex, exitFlatIndex, flatEntrance, flatExit]
  ring

/-! ### The complete genuine derivative and uniqueness -/

theorem flatJointObjective_eq_outer_add_inner {M N : Nat} (hN : 0 < N)
    (K : ℝ) (z : FlatPrimal M × FlatDual M N) :
    flatJointObjective hN K z =
      flatOuterObjective K z.1 + flatInnerJointObjective hN z := by
  rfl

def assembledJointDerivative {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : FlatPrimal M) (y : FlatDual M N) :
    (FlatPrimal M × FlatDual M N) →L[ℝ] ℝ :=
  (flatOuterDerivative K x).comp
      (ContinuousLinearMap.fst ℝ (FlatPrimal M) (FlatDual M N)) +
    flatInnerDerivative hN x y

theorem hasFDerivAt_flatJointObjective_assembled {M N : Nat}
    (hN : 0 < N) (K : ℝ) (x : FlatPrimal M) (y : FlatDual M N) :
    HasFDerivAt (flatJointObjective hN K)
      (assembledJointDerivative hN K x y) (x, y) := by
  letI : AddCommGroup (FlatPrimal M × FlatDual M N) :=
    Prod.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (FlatPrimal M × FlatDual M N) :=
    Prod.normedSpace.toModule
  letI : TopologicalSpace (FlatPrimal M × FlatDual M N) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  have ho := (hasFDerivAt_flatOuterObjective K x).comp (x, y)
    (ContinuousLinearMap.fst ℝ (FlatPrimal M) (FlatDual M N)).hasFDerivAt
  have hi := hasFDerivAt_flatInnerJointObjective hN x y
  have hraw := ho.add hi
  unfold assembledJointDerivative
  convert hraw using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  all_goals try { apply TopologicalSpace.ext <;> rfl }
  · funext z
    exact flatJointObjective_eq_outer_add_inner hN K z

theorem assembledGradient_represents_fderiv {M N : Nat} (hN : 0 < N)
    (K : ℝ) :
    NCPLVerification.RepresentsJointGradient
      (flatHardObjective (M := M) hN K)
      (assembledPrimalField hN K) (assembledDualGradient hN) := by
  constructor
  · exact (flatJointObjective_contDiff (M := M) hN K).differentiable (by simp)
  · intro x y dx dy
    have hf := (hasFDerivAt_flatJointObjective_assembled hN K x y).fderiv
    change (fderiv ℝ (flatJointObjective hN K) (x, y)) (dx, dy) = _
    rw [hf]
    unfold assembledJointDerivative
    simp only [add_apply, ContinuousLinearMap.comp_apply]
    rw [flatOuterDerivative_apply, flatInnerDerivative_apply]
    unfold assembledPrimalField
    change NCPLVerification.evecDot (outerPrimalField K x) dx +
      (NCPLVerification.evecDot (innerPrimalField hN x y) dx +
        NCPLVerification.evecDot (assembledDualGradient hN x y) dy) = _
    simp only [NCPLVerification.evecDot_apply, Pi.add_apply]
    simp_rw [add_mul]
    rw [Finset.sum_add_distrib]
    ring

/-- The explicit assembled primal field is exactly the actual ambient
Fréchet gradient defined in `CompositeSmoothness`. -/
theorem flatPrimalGradient_eq_assembled {M N : Nat} (hN : 0 < N)
    (K : ℝ) (x : FlatPrimal M) (y : FlatDual M N) :
    flatPrimalGradient hN K x y = assembledPrimalField hN K x y := by
  funext i
  have hrep := (assembledGradient_represents_fderiv (M := M) hN K).2
    x y (NCPLVerification.evecBasis i) (0 : FlatDual M N)
  change (fderiv ℝ (flatJointObjective hN K) (x, y))
      (NCPLVerification.evecBasis i, 0) = _ at hrep
  unfold flatPrimalGradient ambientGradX
  change fderiv ℝ (flatJointObjective hN K) (x, y)
      (NCPLVerification.evecBasis i, 0) = _
  rw [hrep]
  simp [NCPLVerification.evecBasis]

/-- The explicit dual field, with the concave sign restored, is exactly the
actual ambient dual Fréchet gradient. -/
theorem flatDualGradient_eq_assembled {M N : Nat} (hN : 0 < N)
    (K : ℝ) (x : FlatPrimal M) (y : FlatDual M N) :
    flatDualGradient hN K x y = assembledDualGradient hN x y := by
  funext j
  have hrep := (assembledGradient_represents_fderiv (M := M) hN K).2
    x y (0 : FlatPrimal M) (NCPLVerification.evecBasis j)
  change (fderiv ℝ (flatJointObjective hN K) (x, y))
      (0, NCPLVerification.evecBasis j) = _ at hrep
  unfold flatDualGradient ambientGradY
  change fderiv ℝ (flatJointObjective hN K) (x, y)
      (0, NCPLVerification.evecBasis j) = _
  rw [hrep]
  simp [NCPLVerification.evecBasis]

/-- Final C1 certificate for the actual gradients of the current five-part
construction.  The witness is fixed before `M` and `N` are quantified. -/
theorem flatActualGradients_jointlySmooth {M N : Nat} (hN10 : 10 ≤ N)
    (K : ℝ) (hK : 0 < K) :
    NCPLVerification.IsJointlySmooth (compositeEll0 K hK)
      (flatPrimalGradient (M := M) (by omega : 0 < N) K)
      (flatDualGradient (M := M) (by omega : 0 < N) K) := by
  intro x y r v
  rw [flatPrimalGradient_eq_assembled, flatPrimalGradient_eq_assembled,
    flatDualGradient_eq_assembled, flatDualGradient_eq_assembled]
  exact assembledFields_jointlySmooth hN10 K hK x y r v

/-- Quantifier order used by the lower-bound framework: one positive
constant works for every number of blocks and every relay length `N ≥ 10`. -/
theorem exists_uniform_flat_actual_joint_smoothness (K : ℝ) (hK : 0 < K) :
    ∃ ell0 : ℝ, 0 < ell0 ∧
      ∀ (M N : Nat) (hN10 : 10 ≤ N),
        NCPLVerification.IsJointlySmooth ell0
          (flatPrimalGradient (M := M) (by omega : 0 < N) K)
          (flatDualGradient (M := M) (by omega : 0 < N) K) := by
  exact ⟨compositeEll0 K hK, compositeEll0_pos K hK,
    fun M N hN10 => flatActualGradients_jointlySmooth hN10 K hK⟩
