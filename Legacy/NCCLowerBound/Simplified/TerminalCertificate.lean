import NCCLowerBound.Simplified.CompositeSmoothness
import NCCLowerBound.Simplified.CompositeZeroChain
import NCCLowerBound.Simplified.OuterAlgebra
import NCCLowerBound.Simplified.InnerFiniteBall

/-!
# Terminal certificates for the concrete five-component value

This file works with the literal state/pulse product.  A point consists of
the `M` stored memories and the `2M` pulse coordinates `(aᵢ,bᵢ)`; the seed
memory preceding the first block is fixed at one.  Every gradient coordinate
below is extracted from the actual Fréchet derivative.
-/

namespace NCCLowerBound
namespace Simplified
namespace TerminalCertificate

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators
open Set
open NCCLowerBoundVerification
open Composite CompositeProperties CompositeSmoothness
open CompositeZeroChain InnerRelay RestrictedBall

abbrev State (M : Nat) := NCCLowerBoundVerification.EVec M
abbrev Pulse (M : Nat) := NCCLowerBoundVerification.EVec (M * 2)
abbrev TerminalPrimal (M : Nat) := State M × Pulse M

def pulseA {M : Nat} (p : Pulse M) : Fin M → ℝ :=
  fun i ↦ p (finProdFinEquiv (i, ⟨0, by omega⟩))

def pulseB {M : Nat} (p : Pulse M) : Fin M → ℝ :=
  fun i ↦ p (finProdFinEquiv (i, ⟨1, by omega⟩))

def terminalOuterValue {M : Nat} (K : ℝ) (z : TerminalPrimal M) : ℝ :=
  outerComponent K z.1 (pulseA z.2) (pulseB z.2)

/-- Add any differentiable pulse-only value (finite-ball or unrestricted) to
the literal four outer components. -/
def terminalValue {M : Nat} (K : ℝ) (V : Pulse M → ℝ)
    (z : TerminalPrimal M) : ℝ :=
  terminalOuterValue K z + V z.2

private def decodeTerminal {M : Nat} (z : TerminalPrimal M) : PrimalPoint M :=
  (z.1, pulseA z.2, pulseB z.2)

theorem terminalOuterValue_contDiff {M : Nat} (K : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (terminalOuterValue (M := M) K) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (decodeTerminal (M := M)) := by
    unfold decodeTerminal pulseA pulseB
    fun_prop
  change ContDiff ℝ (⊤ : ℕ∞)
    ((fun x : PrimalPoint M ↦ outerComponent K x.1 x.2.1 x.2.2) ∘
      decodeTerminal)
  exact (outerComponent_contDiff (M := M) K).comp hd

theorem terminalValue_differentiable {M : Nat} (K : ℝ)
    {V : Pulse M → ℝ} (hV : Differentiable ℝ V) :
    Differentiable ℝ (terminalValue K V) := by
  exact (terminalOuterValue_contDiff K).differentiable (by simp) |>.add
    (hV.comp differentiable_snd)

/-- State coordinates of the actual Fréchet derivative. -/
def actualStateGradient {M : Nat} (f : TerminalPrimal M → ℝ)
    (z : TerminalPrimal M) : State M :=
  ambientGradX f z.1 z.2

/-- Pulse coordinates of the actual Fréchet derivative. -/
def actualPulseGradient {M : Nat} (f : TerminalPrimal M → ℝ)
    (z : TerminalPrimal M) : Pulse M :=
  ambientGradY f z.1 z.2

/-- Squared Euclidean norm of the actual coordinate gradient. -/
def actualGradientSq {M : Nat} (f : TerminalPrimal M → ℝ)
    (z : TerminalPrimal M) : ℝ :=
  vecSq (actualStateGradient f z) + vecSq (actualPulseGradient f z)

theorem actualGradient_represents_fderiv {M : Nat}
    {f : TerminalPrimal M → ℝ} (hf : Differentiable ℝ f) :
    NCPLVerification.RepresentsJointGradient (Function.curry f)
      (fun s p ↦ actualStateGradient f (s, p))
      (fun s p ↦ actualPulseGradient f (s, p)) := by
  simpa [actualStateGradient, actualPulseGradient] using
    representsJointGradient_ambient f hf

private theorem coordinate_sq_le_vecSq {m : Nat}
    (v : NCCLowerBoundVerification.EVec m) (i : Fin m) :
    v i ^ 2 ≤ vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j))
    (Finset.mem_univ i)

theorem stateGradient_coordinate_sq_le {M : Nat}
    (f : TerminalPrimal M → ℝ) (z : TerminalPrimal M) (i : Fin M) :
    actualStateGradient f z i ^ 2 ≤ actualGradientSq f z := by
  unfold actualGradientSq
  exact (coordinate_sq_le_vecSq (actualStateGradient f z) i).trans
    (le_add_of_nonneg_right (by
      unfold vecSq NCPLVerification.vecSq
      positivity))

/-! ## A fixed phase scale dominating every transition-state remainder -/

private theorem frontierSwitch_deriv_eq_zero_of_one_le {t : ℝ}
    (ht : (1 : ℝ) ≤ t) : deriv frontierSwitch t = 0 := by
  have heq : Set.EqOn frontierSwitch (fun _ : ℝ ↦ 1) (Set.Ioi (1 : ℝ)) := by
    intro x hx
    exact frontierSwitch_eq_one_of_one_le hx.le
  by_cases hEq : t = 1
  · subst t
    have hd := frontierSwitch_contDiff.differentiable (by simp) (1 : ℝ)
    have hright : HasDerivWithinAt frontierSwitch 0 (Set.Ici (1 : ℝ)) 1 := by
      exact (hasDerivWithinAt_const (1 : ℝ) (Set.Ici (1 : ℝ)) 1).congr_of_mem
        (fun x hx ↦ frontierSwitch_eq_one_of_one_le hx) (by simp)
    exact HasDerivWithinAt.deriv_eq_zero hright
      (uniqueDiffOn_Ici 1 1 (by simp))
  · have ht' : t ∈ Set.Ioi (1 : ℝ) := by exact lt_of_le_of_ne ht (Ne.symm hEq)
    have hz : deriv frontierSwitch t = deriv (fun _ : ℝ ↦ 1) t :=
      heq.deriv isOpen_Ioi ht'
    simpa using hz

theorem frontierSwitch_first_deriv_bounded :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ t : ℝ, |deriv frontierSwitch t| ≤ L := by
  have hcont : Continuous (fun t : ℝ ↦ |deriv frontierSwitch t|) := by
    have hcd : ContDiff ℝ (1 : ℕ∞) frontierSwitch :=
      frontierSwitch_contDiff.of_le (by
        exact_mod_cast (show (1 : ℕ∞) ≤ ⊤ from le_top))
    simpa [iteratedDeriv_one] using hcd.continuous_iteratedDeriv' 1 |>.abs
  obtain ⟨L, hL⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.continuousOn)
  refine ⟨max L 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (1 / 5 : ℝ) 1
  · exact (hL _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  · simp only [Set.mem_Icc, not_and_or, not_le] at ht
    rcases ht with ht | ht
    · rw [frontierSwitch_deriv_eq_zero_of_le_fifth ht.le, abs_zero]
      exact le_max_right _ _
    · rw [frontierSwitch_deriv_eq_zero_of_one_le ht.le, abs_zero]
      exact le_max_right _ _

def switchDerivBound : ℝ := Classical.choose frontierSwitch_first_deriv_bounded

theorem switchDerivBound_nonneg : 0 ≤ switchDerivBound :=
  (Classical.choose_spec frontierSwitch_first_deriv_bounded).1

theorem frontierSwitch_deriv_abs_le (t : ℝ) :
    |deriv frontierSwitch t| ≤ switchDerivBound :=
  (Classical.choose_spec frontierSwitch_first_deriv_bounded).2 t

/-- A concrete (choice-free at use sites) phase parameter.  The numerical
coefficients are the six local outer derivative bounds. -/
def terminalPhaseScale : ℝ := 47 + 500 * switchDerivBound

theorem terminalPhaseScale_pos : 0 < terminalPhaseScale := by
  unfold terminalPhaseScale
  nlinarith [switchDerivBound_nonneg]

/-! ## Exact local state derivative of the outer four components -/

def nextOrderingStateContribution {M : Nat} (s : Fin M → ℝ)
    (i : Fin M) : ℝ :=
  if h : i.val + 1 < M then
    let j : Fin M := ⟨i.val + 1, h⟩
    24 * frontierSwitch (s j) *
        (-deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
          (1 - stateClip (s i)) * deriv frontierSwitch (s i))
  else 0

def nextEntranceStateContribution {M : Nat} (s a : Fin M → ℝ)
    (i : Fin M) : ℝ :=
  if h : i.val + 1 < M then
    let j : Fin M := ⟨i.val + 1, h⟩
    (-4 * deriv frontierSwitch (s i) *
      (1 - frontierSwitch (s j)) * pulseClip (a j))
  else 0

def nextExitStateContribution {M : Nat} (s b : Fin M → ℝ)
    (i : Fin M) : ℝ :=
  if h : i.val + 1 < M then
    let j : Fin M := ⟨i.val + 1, h⟩
    (-deriv frontierSwitch (s i) * stateClip (s j) *
      (1 - frontierSwitch (s j)) * pulseClip (b j))
  else 0

def nextStateContribution {M : Nat} (s a b : Fin M → ℝ) (i : Fin M) : ℝ :=
  nextOrderingStateContribution s i + nextEntranceStateContribution s a i +
    nextExitStateContribution s b i

def outerStateDerivative {M : Nat} (K : ℝ) (s a b : Fin M → ℝ)
    (i : Fin M) : ℝ :=
  deriv (phasePotential K) (s i) +
    24 * deriv frontierSwitch (s i) *
      (1 - stateClip (previousMemory s i)) *
      (1 - frontierSwitch (previousMemory s i)) +
    4 * frontierSwitch (previousMemory s i) *
      deriv frontierSwitch (s i) * pulseClip (a i) -
    frontierSwitch (previousMemory s i) *
      (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
        stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i) +
    nextStateContribution s a b i

private theorem sum_current_successor {M : Nat} (i : Fin M)
    (own : ℝ) (next : Fin M → ℝ) :
    (∑ l : Fin M, if l = i then own
      else if l.val = i.val + 1 then next l else 0) =
      own + if h : i.val + 1 < M then next ⟨i.val + 1, h⟩ else 0 := by
  classical
  rw [← Finset.sum_erase_add Finset.univ
    (fun l : Fin M ↦ if l = i then own
      else if l.val = i.val + 1 then next l else 0)
    (Finset.mem_univ i)]
  simp only [↓reduceIte]
  rw [add_comm]
  congr 1
  by_cases h : i.val + 1 < M
  · simp only [h, ↓reduceDIte]
    let j : Fin M := ⟨i.val + 1, h⟩
    have hji : j ≠ i := by
      intro hEq
      have hv := congrArg Fin.val hEq
      dsimp [j] at hv
      omega
    rw [Finset.sum_eq_single j]
    · simp [j, hji]
    · intro l hl hlj
      have hli : l ≠ i := Finset.mem_erase.mp hl |>.1
      simp only [hli, ↓reduceIte]
      by_cases hsucc : l.val = i.val + 1
      · exfalso
        apply hlj
        apply Fin.ext
        simpa [j] using hsucc
      · simp [hsucc]
    · simp [j, hji]
  · simp only [h, ↓reduceDIte]
    apply Finset.sum_eq_zero
    intro l hl
    have hli : l ≠ i := Finset.mem_erase.mp hl |>.1
    simp only [hli, ↓reduceIte]
    have hsucc : l.val ≠ i.val + 1 := by
      intro hEq
      exact h (by omega)
    simp [hsucc]

theorem hasDerivAt_outerComponent_stateLine {M : Nat} (K : ℝ)
    (s a b : Fin M → ℝ) (i : Fin M) :
    HasDerivAt
      (fun t : ℝ ↦ outerComponent K (replaceCoordinate s i t) a b)
      (outerStateDerivative K s a b i) (s i) := by
  have hA : HasDerivAt frontierSwitch (deriv frontierSwitch (s i)) (s i) :=
    (frontierSwitch_contDiff.differentiable (by simp) (s i)).hasDerivAt
  have hC : HasDerivAt stateClip (deriv stateClip (s i)) (s i) :=
    (stateClip_contDiff.differentiable (by simp) (s i)).hasDerivAt
  have hU := hasDerivAt_phasePotential K (s i)
  have hphase : HasDerivAt
      (fun t : ℝ ↦ phaseComponent K (replaceCoordinate s i t))
      (deriv (phasePotential K) (s i)) (s i) := by
    unfold phaseComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin M,
          phasePotential K (replaceCoordinate s i t l))
        (∑ l : Fin M, if l = i then deriv (phasePotential K) (s i) else 0)
        (s i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa [replaceCoordinate, deriv_phasePotential] using hU
      · simpa [replaceCoordinate, hli] using
          hasDerivAt_const (s i) (phasePotential K (s l))
    classical
    rw [Finset.sum_ite_eq'] at hs
    simpa using hs
  have hordering : HasDerivAt
      (fun t : ℝ ↦ orderingComponent (replaceCoordinate s i t))
      (24 * deriv frontierSwitch (s i) *
          (1 - stateClip (previousMemory s i)) *
          (1 - frontierSwitch (previousMemory s i)) +
        nextOrderingStateContribution s i) (s i) := by
    unfold orderingComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin M,
          orderingSummand (replaceCoordinate s i t) l)
        (∑ l : Fin M, if l = i then
          24 * deriv frontierSwitch (s i) *
            (1 - stateClip (previousMemory s i)) *
            (1 - frontierSwitch (previousMemory s i))
          else if l.val = i.val + 1 then
            24 * frontierSwitch (s l) *
              (-deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
                (1 - stateClip (s i)) * deriv frontierSwitch (s i))
          else 0) (s i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        have hd := ((hA.const_mul 24).mul_const
          (1 - stateClip (previousMemory s i))).mul_const
            (1 - frontierSwitch (previousMemory s i))
        simpa [orderingSummand, replaceCoordinate,
          previousMemory_replaceCoordinate] using hd
      · by_cases hsucc : l.val = i.val + 1
        · have hd := (((hasDerivAt_const (s i) (1 : ℝ)).sub hC).mul
            ((hasDerivAt_const (s i) (1 : ℝ)).sub hA)).const_mul
              (24 * frontierSwitch (s l))
          convert hd using 1
          all_goals try { apply AddCommGroup.ext <;> rfl }
          · funext t
            simp [orderingSummand, replaceCoordinate, hli,
              previousMemory_replaceCoordinate, hsucc]
            ring
          · simp [hli, hsucc]
            ring
            simp
        · simpa [orderingSummand, replaceCoordinate, hli,
            previousMemory_replaceCoordinate, hsucc] using
            hasDerivAt_const (s i) (orderingSummand s l)
    rw [sum_current_successor i
      (24 * deriv frontierSwitch (s i) *
        (1 - stateClip (previousMemory s i)) *
        (1 - frontierSwitch (previousMemory s i)))
      (fun l ↦ 24 * frontierSwitch (s l) *
        (-deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
          (1 - stateClip (s i)) * deriv frontierSwitch (s i)))] at hs
    simpa [nextOrderingStateContribution] using hs
  have hentrance : HasDerivAt
      (fun t : ℝ ↦ entranceComponent (replaceCoordinate s i t) a)
      (4 * frontierSwitch (previousMemory s i) *
          deriv frontierSwitch (s i) * pulseClip (a i) +
        nextEntranceStateContribution s a i) (s i) := by
    unfold entranceComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin M,
          entranceSummand (replaceCoordinate s i t) a l)
        (∑ l : Fin M, if l = i then
          4 * frontierSwitch (previousMemory s i) *
            deriv frontierSwitch (s i) * pulseClip (a i)
          else if l.val = i.val + 1 then
            -4 * deriv frontierSwitch (s i) *
              (1 - frontierSwitch (s l)) * pulseClip (a l)
          else 0) (s i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        have hd := (((hasDerivAt_const (s i) (1 : ℝ)).sub hA).const_mul
          (-4 * frontierSwitch (previousMemory s i))).mul_const
            (pulseClip (a i))
        convert hd using 1
        all_goals try { apply AddCommGroup.ext <;> rfl }
        · funext t
          simp [entranceSummand, replaceCoordinate,
            previousMemory_replaceCoordinate]
        · simp
      · by_cases hsucc : l.val = i.val + 1
        · have hd := (hA.const_mul (-4)).mul_const
            ((1 - frontierSwitch (s l)) * pulseClip (a l))
          convert hd using 1
          all_goals try { apply AddCommGroup.ext <;> rfl }
          · funext t
            simp [entranceSummand, replaceCoordinate, hli,
              previousMemory_replaceCoordinate, hsucc]
            ring
          · simp [hli, hsucc]
            ring
        · simpa [entranceSummand, replaceCoordinate, hli,
            previousMemory_replaceCoordinate, hsucc] using
            hasDerivAt_const (s i) (entranceSummand s a l)
    rw [sum_current_successor i
      (4 * frontierSwitch (previousMemory s i) *
        deriv frontierSwitch (s i) * pulseClip (a i))
      (fun l ↦ -4 * deriv frontierSwitch (s i) *
        (1 - frontierSwitch (s l)) * pulseClip (a l))] at hs
    simpa [nextEntranceStateContribution] using hs
  have hexit : HasDerivAt
      (fun t : ℝ ↦ exitComponent (replaceCoordinate s i t) b)
      (-frontierSwitch (previousMemory s i) *
          (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
            stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i) +
        nextExitStateContribution s b i) (s i) := by
    unfold exitComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin M,
          exitSummand (replaceCoordinate s i t) b l)
        (∑ l : Fin M, if l = i then
          -frontierSwitch (previousMemory s i) *
            (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
              stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i)
          else if l.val = i.val + 1 then
            -deriv frontierSwitch (s i) * stateClip (s l) *
              (1 - frontierSwitch (s l)) * pulseClip (b l)
          else 0) (s i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        have hd := ((hC.mul
          ((hasDerivAt_const (s i) (1 : ℝ)).sub hA)).const_mul
            (-frontierSwitch (previousMemory s i))).mul_const
              (pulseClip (b i))
        convert hd using 1
        all_goals try { apply AddCommGroup.ext <;> rfl }
        · funext t
          simp [exitSummand, replaceCoordinate,
            previousMemory_replaceCoordinate]
          ring
          simp
        · simp
          ring
          simp
      · by_cases hsucc : l.val = i.val + 1
        · have hd := hA.const_mul
            (-stateClip (s l) * (1 - frontierSwitch (s l)) * pulseClip (b l))
          convert hd using 1
          all_goals try { apply AddCommGroup.ext <;> rfl }
          · funext t
            simp [exitSummand, replaceCoordinate, hli,
              previousMemory_replaceCoordinate, hsucc]
            ring
          · simp [hli, hsucc]
            ring
        · simpa [exitSummand, replaceCoordinate, hli,
            previousMemory_replaceCoordinate, hsucc] using
            hasDerivAt_const (s i) (exitSummand s b l)
    rw [sum_current_successor i
      (-frontierSwitch (previousMemory s i) *
        (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
          stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i))
      (fun l ↦ -deriv frontierSwitch (s i) * stateClip (s l) *
        (1 - frontierSwitch (s l)) * pulseClip (b l))] at hs
    simpa [nextExitStateContribution] using hs
  unfold outerComponent outerStateDerivative nextStateContribution
  convert ((hphase.add hordering).add hentrance).add hexit using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    rfl
  · ring

/-- Every state coordinate of the actual Fréchet derivative is exactly the
local formula above; a pulse-only value contributes zero in this direction. -/
theorem actualStateGradient_terminalValue_eq {M : Nat} (K : ℝ)
    {V : Pulse M → ℝ} (hV : Differentiable ℝ V)
    (z : TerminalPrimal M) (i : Fin M) :
    actualStateGradient (terminalValue K V) z i =
      outerStateDerivative K z.1 (pulseA z.2) (pulseB z.2) i := by
  have hsline : HasDerivAt (fun t : ℝ ↦ replaceCoordinate z.1 i t)
      (NCPLVerification.evecBasis i) (z.1 i) := by
    rw [hasDerivAt_pi]
    intro l
    convert (hasDerivAt_const (z.1 i) (z.1 l)).add
      (((hasDerivAt_id (z.1 i)).sub_const (z.1 i)).mul_const
        (NCPLVerification.evecBasis i l)) using 1
    · funext t
      by_cases hli : l = i
      · subst l
        simp [replaceCoordinate, NCPLVerification.evecBasis]
      · simp [replaceCoordinate, NCPLVerification.evecBasis, hli]
    · simp [NCPLVerification.evecBasis]
  have hcurve : HasDerivAt
      (fun t : ℝ ↦ (replaceCoordinate z.1 i t, z.2))
      (NCPLVerification.evecBasis i, 0) (z.1 i) :=
    hsline.prodMk (hasDerivAt_const (z.1 i) z.2)
  have hpoint : (replaceCoordinate z.1 i (z.1 i), z.2) = z := by
    apply Prod.ext
    · funext l
      by_cases hli : l = i
      · subst l
        simp [replaceCoordinate]
      · simp [replaceCoordinate, hli]
    · rfl
  have hf : HasFDerivAt (terminalValue K V)
      (fderiv ℝ (terminalValue K V) z) z :=
    (terminalValue_differentiable K hV z).hasFDerivAt
  have hcomp := hf.comp_hasDerivAt_of_eq (z.1 i) hcurve hpoint.symm
  have hline := (hasDerivAt_outerComponent_stateLine K z.1
    (pulseA z.2) (pulseB z.2) i).add_const (V z.2)
  have hexact : HasDerivAt
      (fun t : ℝ ↦ terminalValue K V (replaceCoordinate z.1 i t, z.2))
      (outerStateDerivative K z.1 (pulseA z.2) (pulseB z.2) i) (z.1 i) := by
    simpa [terminalValue, terminalOuterValue] using hline
  unfold actualStateGradient ambientGradX
  exact hcomp.unique hexact

def outerStateRemainder {M : Nat} (s a b : Fin M → ℝ) (i : Fin M) : ℝ :=
  24 * deriv frontierSwitch (s i) *
      (1 - stateClip (previousMemory s i)) *
      (1 - frontierSwitch (previousMemory s i)) +
    4 * frontierSwitch (previousMemory s i) *
      deriv frontierSwitch (s i) * pulseClip (a i) -
    frontierSwitch (previousMemory s i) *
      (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
        stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i) +
    nextStateContribution s a b i

theorem outerStateDerivative_eq_phase_add_remainder {M : Nat} (K : ℝ)
    (s a b : Fin M → ℝ) (i : Fin M) :
    outerStateDerivative K s a b i =
      deriv (phasePotential K) (s i) + outerStateRemainder s a b i := by
  unfold outerStateDerivative outerStateRemainder
  ring

private theorem one_sub_frontier_abs_le_one (t : ℝ) :
    |1 - frontierSwitch t| ≤ 1 := by
  rcases frontierSwitch_mem_unitInterval t with ⟨h0, h1⟩
  rw [abs_of_nonneg (sub_nonneg.mpr h1)]
  linarith

private theorem frontier_abs_le_one (t : ℝ) : |frontierSwitch t| ≤ 1 := by
  rcases frontierSwitch_mem_unitInterval t with ⟨h0, h1⟩
  rw [abs_of_nonneg h0]
  exact h1

private theorem one_sub_stateClip_abs_le_four (t : ℝ) :
    |1 - stateClip t| ≤ 4 := by
  calc
    |1 - stateClip t| ≤ |(1 : ℝ)| + |stateClip t| := abs_sub _ _
    _ = 1 + |stateClip t| := by norm_num
    _ ≤ 1 + 3 := by
      simpa [add_comm] using add_le_add_right (stateClip_abs_le_three t) 1
    _ = 4 := by norm_num

private theorem stateClip_deriv_abs_le_one (t : ℝ) :
    |deriv stateClip t| ≤ 1 := by
  rcases stateClip_deriv_mem_unitInterval t with ⟨h0, h1⟩
  rw [abs_of_nonneg h0]
  exact h1

private theorem mul2_mono_nonneg {x y X Y : ℝ}
    (_hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hX0 : 0 ≤ X)
    (hx : x ≤ X) (hy : y ≤ Y) : x * y ≤ X * Y := by
  calc
    x * y ≤ X * y := mul_le_mul_of_nonneg_right hx hy0
    _ ≤ X * Y := mul_le_mul_of_nonneg_left hy hX0

private theorem mul3_mono_nonneg {x y z X Y Z : ℝ}
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z)
    (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hx : x ≤ X) (hy : y ≤ Y) (hz : z ≤ Z) :
    x * y * z ≤ X * Y * Z := by
  have hxy : x * y ≤ X * Y := mul2_mono_nonneg hx0 hy0 hX0 hx hy
  exact mul2_mono_nonneg (mul_nonneg hx0 hy0) hz0 (mul_nonneg hX0 hY0) hxy hz

private theorem mul4_mono_nonneg {w x y z W X Y Z : ℝ}
    (hw0 : 0 ≤ w) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hz0 : 0 ≤ z)
    (hW0 : 0 ≤ W) (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hw : w ≤ W) (hx : x ≤ X) (hy : y ≤ Y) (hz : z ≤ Z) :
    w * x * y * z ≤ W * X * Y * Z := by
  have hwxy : w * x * y ≤ W * X * Y :=
    mul3_mono_nonneg hw0 hx0 hy0 hW0 hX0 hw hx hy
  exact mul2_mono_nonneg (mul_nonneg (mul_nonneg hw0 hx0) hy0) hz0
    (mul_nonneg (mul_nonneg hW0 hX0) hY0) hwxy hz

private theorem outer_own_ordering_abs_le {M : Nat}
    (s : Fin M → ℝ) (i : Fin M) :
    |24 * deriv frontierSwitch (s i) *
        (1 - stateClip (previousMemory s i)) *
        (1 - frontierSwitch (previousMemory s i))| ≤
      96 * switchDerivBound := by
  rw [abs_mul, abs_mul, abs_mul]
  norm_num only [abs_of_nonneg]
  calc
    24 * |deriv frontierSwitch (s i)| *
          |1 - stateClip (previousMemory s i)| *
        |1 - frontierSwitch (previousMemory s i)| ≤
        24 * switchDerivBound * 4 * 1 := by
      exact mul4_mono_nonneg (by positivity) (abs_nonneg _) (abs_nonneg _)
        (abs_nonneg _) (by norm_num) switchDerivBound_nonneg (by norm_num)
        (by norm_num) (frontierSwitch_deriv_abs_le _)
        (one_sub_stateClip_abs_le_four _) (one_sub_frontier_abs_le_one _)
    _ = 96 * switchDerivBound := by ring

private theorem outer_own_entrance_abs_le {M : Nat}
    (s a : Fin M → ℝ) (i : Fin M) :
    |4 * frontierSwitch (previousMemory s i) *
        deriv frontierSwitch (s i) * pulseClip (a i)| ≤
      88 * switchDerivBound := by
  rw [abs_mul, abs_mul, abs_mul]
  norm_num only [abs_of_nonneg]
  calc
    4 * |frontierSwitch (previousMemory s i)| *
          |deriv frontierSwitch (s i)| * |pulseClip (a i)| ≤
        4 * 1 * switchDerivBound * 22 := by
      exact mul4_mono_nonneg (by positivity) (abs_nonneg _) (abs_nonneg _)
        (abs_nonneg _) (by norm_num) (by norm_num) switchDerivBound_nonneg
        (by norm_num) (frontier_abs_le_one _) (frontierSwitch_deriv_abs_le _)
        (pulseClip_abs_le_twentyTwo _)
    _ = 88 * switchDerivBound := by ring

private theorem clip_switch_product_deriv_abs_le (t : ℝ) :
    |deriv stateClip t * (1 - frontierSwitch t) -
        stateClip t * deriv frontierSwitch t| ≤
      1 + 3 * switchDerivBound := by
  calc
    |deriv stateClip t * (1 - frontierSwitch t) -
        stateClip t * deriv frontierSwitch t| ≤
      |deriv stateClip t * (1 - frontierSwitch t)| +
        |stateClip t * deriv frontierSwitch t| := abs_sub _ _
    _ = |deriv stateClip t| * |1 - frontierSwitch t| +
        |stateClip t| * |deriv frontierSwitch t| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * 1 + 3 * switchDerivBound := by
      gcongr
      · exact stateClip_deriv_abs_le_one _
      · exact one_sub_frontier_abs_le_one _
      · exact stateClip_abs_le_three _
      · exact frontierSwitch_deriv_abs_le _
    _ = 1 + 3 * switchDerivBound := by ring

private theorem outer_own_exit_abs_le {M : Nat}
    (s b : Fin M → ℝ) (i : Fin M) :
    |-frontierSwitch (previousMemory s i) *
        (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
          stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i)| ≤
      22 + 66 * switchDerivBound := by
  rw [abs_mul, abs_mul, abs_neg]
  calc
    |frontierSwitch (previousMemory s i)| *
          |deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
            stateClip (s i) * deriv frontierSwitch (s i)| *
        |pulseClip (b i)| ≤
      1 * (1 + 3 * switchDerivBound) * 22 := by
        exact mul3_mono_nonneg (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
          (by norm_num) (by nlinarith [switchDerivBound_nonneg])
          (frontier_abs_le_one _) (clip_switch_product_deriv_abs_le _)
          (pulseClip_abs_le_twentyTwo _)
    _ = 22 + 66 * switchDerivBound := by ring

private theorem next_ordering_abs_le {M : Nat} (s : Fin M → ℝ)
    (i : Fin M) :
    |nextOrderingStateContribution s i| ≤
      24 + 96 * switchDerivBound := by
  unfold nextOrderingStateContribution
  split
  · rename_i h
    dsimp only
    rw [abs_mul, abs_mul]
    norm_num only [abs_of_nonneg]
    have hinside :
        |-deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
          (1 - stateClip (s i)) * deriv frontierSwitch (s i)| ≤
            1 + 4 * switchDerivBound := by
      calc
        |-deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
          (1 - stateClip (s i)) * deriv frontierSwitch (s i)| ≤
            |-deriv stateClip (s i) * (1 - frontierSwitch (s i))| +
              |(1 - stateClip (s i)) * deriv frontierSwitch (s i)| :=
          abs_sub _ _
        _ = |deriv stateClip (s i)| * |1 - frontierSwitch (s i)| +
            |1 - stateClip (s i)| * |deriv frontierSwitch (s i)| := by
          rw [abs_mul, abs_mul, abs_neg]
        _ ≤ 1 * 1 + 4 * switchDerivBound := by
          gcongr
          · exact stateClip_deriv_abs_le_one _
          · exact one_sub_frontier_abs_le_one _
          · exact one_sub_stateClip_abs_le_four _
          · exact frontierSwitch_deriv_abs_le _
        _ = 1 + 4 * switchDerivBound := by ring
    calc
      24 * |frontierSwitch (s ⟨i.val + 1, h⟩)| *
          |-deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
            (1 - stateClip (s i)) * deriv frontierSwitch (s i)| ≤
        24 * 1 * (1 + 4 * switchDerivBound) := by
        exact mul3_mono_nonneg (by positivity) (abs_nonneg _) (abs_nonneg _)
          (by norm_num) (by norm_num) (by norm_num)
          (frontier_abs_le_one _) hinside
      _ = 24 + 96 * switchDerivBound := by ring
  · rw [abs_zero]
    nlinarith [switchDerivBound_nonneg]

private theorem next_entrance_abs_le {M : Nat} (s a : Fin M → ℝ)
    (i : Fin M) :
    |nextEntranceStateContribution s a i| ≤ 88 * switchDerivBound := by
  unfold nextEntranceStateContribution
  split
  · rename_i h
    dsimp only
    rw [abs_mul, abs_mul, abs_mul, abs_neg]
    norm_num only [abs_of_nonneg]
    calc
      4 * |deriv frontierSwitch (s i)| *
          |1 - frontierSwitch (s ⟨i.val + 1, h⟩)| *
          |pulseClip (a ⟨i.val + 1, h⟩)| ≤
        4 * switchDerivBound * 1 * 22 := by
          exact mul4_mono_nonneg (by positivity) (abs_nonneg _) (abs_nonneg _)
            (abs_nonneg _) (by norm_num) switchDerivBound_nonneg (by norm_num)
            (by norm_num) (frontierSwitch_deriv_abs_le _)
            (one_sub_frontier_abs_le_one _) (pulseClip_abs_le_twentyTwo _)
      _ = 88 * switchDerivBound := by ring
  · rw [abs_zero]
    nlinarith [switchDerivBound_nonneg]

private theorem next_exit_abs_le {M : Nat} (s b : Fin M → ℝ)
    (i : Fin M) :
    |nextExitStateContribution s b i| ≤ 66 * switchDerivBound := by
  unfold nextExitStateContribution
  split
  · rename_i h
    dsimp only
    rw [abs_mul, abs_mul, abs_mul, abs_neg]
    calc
      |deriv frontierSwitch (s i)| * |stateClip (s ⟨i.val + 1, h⟩)| *
          |1 - frontierSwitch (s ⟨i.val + 1, h⟩)| *
          |pulseClip (b ⟨i.val + 1, h⟩)| ≤
        switchDerivBound * 3 * 1 * 22 := by
          exact mul4_mono_nonneg (abs_nonneg _) (abs_nonneg _) (abs_nonneg _)
            (abs_nonneg _) switchDerivBound_nonneg (by norm_num) (by norm_num)
            (frontierSwitch_deriv_abs_le _) (stateClip_abs_le_three _)
            (one_sub_frontier_abs_le_one _) (pulseClip_abs_le_twentyTwo _)
      _ = 66 * switchDerivBound := by ring
  · rw [abs_zero]
    nlinarith [switchDerivBound_nonneg]

theorem outerStateRemainder_abs_le {M : Nat} (s a b : Fin M → ℝ)
    (i : Fin M) :
    |outerStateRemainder s a b i| ≤ 46 + 500 * switchDerivBound := by
  have hnext : |nextStateContribution s a b i| ≤
      24 + 250 * switchDerivBound := by
    unfold nextStateContribution
    calc
      |nextOrderingStateContribution s i + nextEntranceStateContribution s a i +
          nextExitStateContribution s b i| ≤
        |nextOrderingStateContribution s i| +
          |nextEntranceStateContribution s a i| +
            |nextExitStateContribution s b i| := by
          have h1 := abs_add_le (nextOrderingStateContribution s i)
            (nextEntranceStateContribution s a i)
          have h2 := abs_add_le
            (nextOrderingStateContribution s i + nextEntranceStateContribution s a i)
            (nextExitStateContribution s b i)
          linarith
      _ ≤ (24 + 96 * switchDerivBound) + 88 * switchDerivBound +
          66 * switchDerivBound := by
        gcongr
        · exact next_ordering_abs_le s i
        · exact next_entrance_abs_le s a i
        · exact next_exit_abs_le s b i
      _ = 24 + 250 * switchDerivBound := by ring
  unfold outerStateRemainder
  calc
    |24 * deriv frontierSwitch (s i) *
          (1 - stateClip (previousMemory s i)) *
          (1 - frontierSwitch (previousMemory s i)) +
        4 * frontierSwitch (previousMemory s i) *
          deriv frontierSwitch (s i) * pulseClip (a i) -
        frontierSwitch (previousMemory s i) *
          (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
            stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i) +
        nextStateContribution s a b i| ≤
      |24 * deriv frontierSwitch (s i) *
          (1 - stateClip (previousMemory s i)) *
          (1 - frontierSwitch (previousMemory s i))| +
        |4 * frontierSwitch (previousMemory s i) *
          deriv frontierSwitch (s i) * pulseClip (a i)| +
        |-frontierSwitch (previousMemory s i) *
          (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
            stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i)| +
        |nextStateContribution s a b i| := by
      have h1 := abs_add_le
        (24 * deriv frontierSwitch (s i) *
          (1 - stateClip (previousMemory s i)) *
          (1 - frontierSwitch (previousMemory s i)))
        (4 * frontierSwitch (previousMemory s i) *
          deriv frontierSwitch (s i) * pulseClip (a i))
      have h2 := abs_sub
        (24 * deriv frontierSwitch (s i) *
            (1 - stateClip (previousMemory s i)) *
            (1 - frontierSwitch (previousMemory s i)) +
          4 * frontierSwitch (previousMemory s i) *
            deriv frontierSwitch (s i) * pulseClip (a i))
        (frontierSwitch (previousMemory s i) *
          (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
            stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i))
      have h3 := abs_add_le
        (24 * deriv frontierSwitch (s i) *
            (1 - stateClip (previousMemory s i)) *
            (1 - frontierSwitch (previousMemory s i)) +
          4 * frontierSwitch (previousMemory s i) *
            deriv frontierSwitch (s i) * pulseClip (a i) -
          frontierSwitch (previousMemory s i) *
            (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
              stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i))
        (nextStateContribution s a b i)
      have habs :
          |-frontierSwitch (previousMemory s i) *
              (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
                stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i)| =
            |frontierSwitch (previousMemory s i) *
              (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
                stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i)| := by
        rw [show -frontierSwitch (previousMemory s i) *
            (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
              stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i) =
          -(frontierSwitch (previousMemory s i) *
            (deriv stateClip (s i) * (1 - frontierSwitch (s i)) -
              stateClip (s i) * deriv frontierSwitch (s i)) * pulseClip (b i)) by ring,
          abs_neg]
      rw [habs]
      linarith
    _ ≤ 96 * switchDerivBound + 88 * switchDerivBound +
        (22 + 66 * switchDerivBound) + (24 + 250 * switchDerivBound) := by
      linarith [outer_own_ordering_abs_le s i,
        outer_own_entrance_abs_le s a i, outer_own_exit_abs_le s b i]
    _ = 46 + 500 * switchDerivBound := by ring

/-! ## The three concrete phase exclusions -/

theorem outerStateDerivative_le_neg_one_of_transition {M : Nat}
    (s a b : Fin M → ℝ) (i : Fin M)
    (hlow : (1 / 5 : ℝ) < s i) (hhigh : s i < 1) :
    outerStateDerivative terminalPhaseScale s a b i ≤ -1 := by
  rw [outerStateDerivative_eq_phase_add_remainder,
    phasePotential_deriv_eq_neg_K_add_one hlow hhigh]
  have hrem := (le_abs_self (outerStateRemainder s a b i)).trans
    (outerStateRemainder_abs_le s a b i)
  unfold terminalPhaseScale
  linarith

private theorem own_exit_positive_part_le_twentyTwo {M : Nat}
    (s b : Fin M → ℝ) (i : Fin M) :
    -frontierSwitch (previousMemory s i) * deriv stateClip (s i) *
        pulseClip (b i) ≤ 22 := by
  let q := frontierSwitch (previousMemory s i) * deriv stateClip (s i)
  have hA := frontierSwitch_mem_unitInterval (previousMemory s i)
  have hC := stateClip_deriv_mem_unitInterval (s i)
  have hq0 : 0 ≤ q := mul_nonneg hA.1 hC.1
  have hq1 : q ≤ 1 := by
    dsimp [q]
    simpa using mul2_mono_nonneg hA.1 hC.1 (by norm_num) hA.2 hC.2
  have hP := pulseClip_abs_le_twentyTwo (b i)
  have hPlo : -22 ≤ pulseClip (b i) := (abs_le.mp hP).1
  by_cases hp : 0 ≤ pulseClip (b i)
  · have := mul_nonneg hq0 hp
    dsimp [q] at this ⊢
    nlinarith
  · have hnp0 : 0 ≤ -pulseClip (b i) := by linarith
    have hnp22 : -pulseClip (b i) ≤ 22 := by linarith
    have hmul : q * (-pulseClip (b i)) ≤ 1 * 22 :=
      mul2_mono_nonneg hq0 hnp0 (by norm_num) hq1 hnp22
    dsimp [q] at hmul ⊢
    nlinarith

private theorem nextStateContribution_nonpos_of_farLeft {M : Nat}
    (s a b : Fin M → ℝ) (i : Fin M)
    (ht : s i ≤ -(1 / 10 : ℝ)) :
    nextStateContribution s a b i ≤ 0 := by
  have hifth : s i ≤ (1 / 5 : ℝ) := by linarith
  have hAd : deriv frontierSwitch (s i) = 0 :=
    frontierSwitch_deriv_eq_zero_of_le_fifth hifth
  have hA : frontierSwitch (s i) = 0 :=
    frontierSwitch_eq_zero_of_le_fifth hifth
  by_cases hsucc : i.val + 1 < M
  · let j : Fin M := ⟨i.val + 1, hsucc⟩
    have hAj0 := (frontierSwitch_mem_unitInterval (s j)).1
    have hCd0 := (stateClip_deriv_mem_unitInterval (s i)).1
    unfold nextStateContribution nextOrderingStateContribution
      nextEntranceStateContribution nextExitStateContribution
    simp only [hsucc, ↓reduceDIte]
    rw [hAd, hA]
    simp only [zero_mul, neg_zero, add_zero, sub_zero]
    have hprod : 0 ≤ frontierSwitch (s j) * deriv stateClip (s i) :=
      mul_nonneg hAj0 hCd0
    nlinarith
  · unfold nextStateContribution nextOrderingStateContribution
      nextEntranceStateContribution nextExitStateContribution
    simp [hsucc]

theorem outerStateDerivative_le_neg_two_of_farLeft {M : Nat}
    (s a b : Fin M → ℝ) (i : Fin M)
    (ht : s i ≤ -(1 / 10 : ℝ)) :
    outerStateDerivative terminalPhaseScale s a b i ≤ -2 := by
  have hifth : s i ≤ (1 / 5 : ℝ) := by linarith
  have hA : frontierSwitch (s i) = 0 :=
    frontierSwitch_eq_zero_of_le_fifth hifth
  have hAd : deriv frontierSwitch (s i) = 0 :=
    frontierSwitch_deriv_eq_zero_of_le_fifth hifth
  have hphase : deriv (phasePotential terminalPhaseScale) (s i) = -24 :=
    phasePotential_deriv_eq_neg_twentyFour ht
  have hexit := own_exit_positive_part_le_twentyTwo s b i
  have hnext := nextStateContribution_nonpos_of_farLeft s a b i ht
  unfold outerStateDerivative
  rw [hphase, hA, hAd]
  simp only [mul_zero, zero_mul, sub_zero, add_zero]
  nlinarith

theorem outerStateDerivative_le_neg_two_of_low_next_high {M : Nat}
    (s a b : Fin M → ℝ) (i : Fin M) (hsucc : i.val + 1 < M)
    (hlow : -(1 / 10 : ℝ) < s i) (hupper : s i ≤ (1 / 5 : ℝ))
    (hnext : (1 : ℝ) ≤ s ⟨i.val + 1, hsucc⟩) :
    outerStateDerivative terminalPhaseScale s a b i ≤ -2 := by
  let j : Fin M := ⟨i.val + 1, hsucc⟩
  have habs : |s i| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hC : stateClip (s i) = s i := stateClip_eq_self habs
  have hCd : deriv stateClip (s i) = 1 := stateClip_deriv_eq_one habs
  have hA : frontierSwitch (s i) = 0 :=
    frontierSwitch_eq_zero_of_le_fifth hupper
  have hAd : deriv frontierSwitch (s i) = 0 :=
    frontierSwitch_deriv_eq_zero_of_le_fifth hupper
  have hAj : frontierSwitch (s j) = 1 :=
    frontierSwitch_eq_one_of_one_le hnext
  have hphase := phasePotential_deriv_nonpos terminalPhaseScale_pos (s i)
  have hexit := own_exit_positive_part_le_twentyTwo s b i
  unfold outerStateDerivative nextStateContribution nextOrderingStateContribution
    nextEntranceStateContribution nextExitStateContribution
  simp only [hsucc, ↓reduceDIte]
  rw [hA, hAd, hC, hCd, hAj]
  norm_num only [zero_mul, mul_zero, sub_zero, sub_self, mul_one,
    add_zero, neg_zero]
  nlinarith

/-! ## Small actual gradient forces a unique discrete frontier -/

theorem smallGradient_excludes_farLeft {M : Nat} {V : Pulse M → ℝ}
    (hV : Differentiable ℝ V) (z : TerminalPrimal M)
    (hsmall : actualGradientSq (terminalValue terminalPhaseScale V) z ≤
      (1 / 4 : ℝ) ^ 2) (i : Fin M) :
    -(1 / 10 : ℝ) < z.1 i := by
  by_contra h
  have hd := outerStateDerivative_le_neg_two_of_farLeft z.1
    (pulseA z.2) (pulseB z.2) i (le_of_not_gt h)
  have hc := stateGradient_coordinate_sq_le
    (terminalValue terminalPhaseScale V) z i
  rw [actualStateGradient_terminalValue_eq terminalPhaseScale hV] at hc
  nlinarith

theorem smallGradient_state_phase {M : Nat} {V : Pulse M → ℝ}
    (hV : Differentiable ℝ V) (z : TerminalPrimal M)
    (hsmall : actualGradientSq (terminalValue terminalPhaseScale V) z ≤
      (1 / 4 : ℝ) ^ 2) (i : Fin M) :
    z.1 i ≤ (1 / 5 : ℝ) ∨ (1 : ℝ) ≤ z.1 i := by
  by_cases hlo : z.1 i ≤ (1 / 5 : ℝ)
  · exact Or.inl hlo
  · right
    by_contra hhigh
    have hd := outerStateDerivative_le_neg_one_of_transition z.1
      (pulseA z.2) (pulseB z.2) i (lt_of_not_ge hlo) (lt_of_not_ge hhigh)
    have hc := stateGradient_coordinate_sq_le
      (terminalValue terminalPhaseScale V) z i
    rw [actualStateGradient_terminalValue_eq terminalPhaseScale hV] at hc
    nlinarith

theorem smallGradient_excludes_low_next_high {M : Nat}
    {V : Pulse M → ℝ} (hV : Differentiable ℝ V) (z : TerminalPrimal M)
    (hsmall : actualGradientSq (terminalValue terminalPhaseScale V) z ≤
      (1 / 4 : ℝ) ^ 2) (i : Fin M) (hsucc : i.val + 1 < M)
    (hlow : z.1 i ≤ (1 / 5 : ℝ)) :
    ¬ (1 : ℝ) ≤ z.1 ⟨i.val + 1, hsucc⟩ := by
  intro hhigh
  have hlower := smallGradient_excludes_farLeft hV z hsmall i
  have hd := outerStateDerivative_le_neg_two_of_low_next_high z.1
    (pulseA z.2) (pulseB z.2) i hsucc hlower hlow hhigh
  have hc := stateGradient_coordinate_sq_le
    (terminalValue terminalPhaseScale V) z i
  rw [actualStateGradient_terminalValue_eq terminalPhaseScale hV] at hc
  nlinarith

def extendedState {M : Nat} (s : State M) (n : Nat) : ℝ :=
  if n = 0 then 1
  else if h : 1 ≤ n ∧ n ≤ M then s ⟨n - 1, by omega⟩ else 0

@[simp] theorem extendedState_zero {M : Nat} (s : State M) :
    extendedState s 0 = 1 := by simp [extendedState]

theorem extendedState_succ {M : Nat} (s : State M) (i : Nat)
    (hi : i < M) : extendedState s (i + 1) = s ⟨i, hi⟩ := by
  simp [extendedState, show 1 ≤ i + 1 ∧ i + 1 ≤ M by omega]

theorem smallGradient_unique_frontier {M : Nat} (hM : 1 ≤ M)
    {V : Pulse M → ℝ} (hV : Differentiable ℝ V) (z : TerminalPrimal M)
    (hsmall : actualGradientSq (terminalValue terminalPhaseScale V) z ≤
      (1 / 4 : ℝ) ^ 2)
    (hterminal : z.1 ⟨M - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    ∃! j, 1 ≤ j ∧ IsFrontier M (extendedState z.1) j := by
  apply existsUnique_frontier hM (extendedState z.1)
  · rw [extendedState_zero]
  · calc
      extendedState z.1 M = z.1 ⟨M - 1, by omega⟩ := by
        unfold extendedState
        simp [show M ≠ 0 by omega, show 1 ≤ M ∧ M ≤ M by omega]
      _ ≤ (1 / 5 : ℝ) := hterminal
  · intro n hn
    by_cases hn0 : n = 0
    · subst n
      right
      rw [extendedState_zero]
    · have hnpos : 1 ≤ n := by omega
      let i : Fin M := ⟨n - 1, by omega⟩
      have hp := smallGradient_state_phase hV z hsmall i
      simpa [extendedState, hn0, hnpos, hn, i] using hp
  · intro n hnM hnlow hnhigh
    by_cases hn0 : n = 0
    · subst n
      rw [extendedState_zero] at hnlow
      norm_num at hnlow
    · have hnpos : 1 ≤ n := by omega
      let i : Fin M := ⟨n - 1, by omega⟩
      have hsucc : i.val + 1 < M := by dsimp [i]; omega
      have hlo : z.1 i ≤ (1 / 5 : ℝ) := by
        simpa [extendedState, hn0, hnpos, show n ≤ M by omega, i] using hnlow
      have hhigh : (1 : ℝ) ≤ z.1 ⟨i.val + 1, hsucc⟩ := by
        have heq : n + 1 = (i.val + 1) + 1 := by dsimp [i]; omega
        rw [heq, extendedState_succ z.1 (i.val + 1) hsucc] at hnhigh
        exact hnhigh
      exact smallGradient_excludes_low_next_high hV z hsmall i hsucc hlo hhigh

/-! ## Radial pulse derivative and its one-frontier bound -/

def outerPulseRadialTerm {M : Nat} (s : State M) (p : Pulse M)
    (i : Fin M) : ℝ :=
  -4 * frontierSwitch (previousMemory s i) *
      (1 - frontierSwitch (s i)) * deriv pulseClip (pulseA p i) * pulseA p i -
    frontierSwitch (previousMemory s i) * stateClip (s i) *
      (1 - frontierSwitch (s i)) * deriv pulseClip (pulseB p i) * pulseB p i

def outerPulseRadial {M : Nat} (s : State M) (p : Pulse M) : ℝ :=
  ∑ i : Fin M, outerPulseRadialTerm s p i

theorem hasDerivAt_terminalOuterValue_pulseRadial {M : Nat} (K : ℝ)
    (s : State M) (p : Pulse M) :
    HasDerivAt (fun t : ℝ ↦ terminalOuterValue K (s, t • p))
      (outerPulseRadial s p) 1 := by
  have hpulseA (i : Fin M) : HasDerivAt
      (fun t : ℝ ↦ pulseClip (pulseA (t • p) i))
      (deriv pulseClip (pulseA p i) * pulseA p i) 1 := by
    have hp : HasDerivAt pulseClip (deriv pulseClip (pulseA p i))
        (pulseA p i) :=
      (pulseClip_contDiff.differentiable (by simp) _).hasDerivAt
    have hl : HasDerivAt (fun t : ℝ ↦ t * pulseA p i) (pulseA p i) 1 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).mul_const (pulseA p i)
    have hp' : HasDerivAt pulseClip (deriv pulseClip (pulseA p i))
        (1 * pulseA p i) := by simpa using hp
    simpa [Function.comp_def, pulseA, smul_eq_mul, mul_comm] using
      HasDerivAt.scomp 1 hp' hl
  have hpulseB (i : Fin M) : HasDerivAt
      (fun t : ℝ ↦ pulseClip (pulseB (t • p) i))
      (deriv pulseClip (pulseB p i) * pulseB p i) 1 := by
    have hp : HasDerivAt pulseClip (deriv pulseClip (pulseB p i))
        (pulseB p i) :=
      (pulseClip_contDiff.differentiable (by simp) _).hasDerivAt
    have hl : HasDerivAt (fun t : ℝ ↦ t * pulseB p i) (pulseB p i) 1 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).mul_const (pulseB p i)
    have hp' : HasDerivAt pulseClip (deriv pulseClip (pulseB p i))
        (1 * pulseB p i) := by simpa using hp
    simpa [Function.comp_def, pulseB, smul_eq_mul, mul_comm] using
      HasDerivAt.scomp 1 hp' hl
  have hent : HasDerivAt
      (fun t : ℝ ↦ entranceComponent s (pulseA (t • p)))
      (∑ i : Fin M, -4 * frontierSwitch (previousMemory s i) *
        (1 - frontierSwitch (s i)) *
          (deriv pulseClip (pulseA p i) * pulseA p i)) 1 := by
    unfold entranceComponent
    apply HasDerivAt.fun_sum
    intro i _
    simpa [entranceSummand, mul_assoc] using (hpulseA i).const_mul
      (-4 * frontierSwitch (previousMemory s i) *
        (1 - frontierSwitch (s i)))
  have hexit : HasDerivAt
      (fun t : ℝ ↦ exitComponent s (pulseB (t • p)))
      (∑ i : Fin M, -frontierSwitch (previousMemory s i) * stateClip (s i) *
        (1 - frontierSwitch (s i)) *
          (deriv pulseClip (pulseB p i) * pulseB p i)) 1 := by
    unfold exitComponent
    apply HasDerivAt.fun_sum
    intro i _
    simpa [exitSummand, mul_assoc] using (hpulseB i).const_mul
      (-frontierSwitch (previousMemory s i) * stateClip (s i) *
        (1 - frontierSwitch (s i)))
  have hconst : HasDerivAt
      (fun _ : ℝ ↦ phaseComponent K s + orderingComponent s) 0 1 :=
    hasDerivAt_const (x := (1 : ℝ)) _
  have hrad : outerPulseRadial s p =
      0 + (∑ i : Fin M, -4 * frontierSwitch (previousMemory s i) *
        (1 - frontierSwitch (s i)) *
          (deriv pulseClip (pulseA p i) * pulseA p i)) +
        ∑ i : Fin M, -frontierSwitch (previousMemory s i) * stateClip (s i) *
          (1 - frontierSwitch (s i)) *
            (deriv pulseClip (pulseB p i) * pulseB p i) := by
    unfold outerPulseRadial outerPulseRadialTerm
    rw [zero_add, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  convert (hconst.add hent |>.add hexit) using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    rfl

theorem previousMemory_eq_extendedState {M : Nat} (s : State M) (i : Fin M) :
    previousMemory s i = extendedState s i.val := by
  by_cases hi : i.val = 0
  · rw [previousMemory_first s i hi]
    simp [extendedState, hi]
  · have hipos : 1 ≤ i.val := by omega
    rw [previousMemory_succ s i (by omega)]
    unfold extendedState
    simp [hi, hipos, show i.val ≤ M by omega]

private theorem outerPulseRadialTerm_eq_zero_of_before {M : Nat}
    (s : State M) (p : Pulse M) {j : Nat}
    (hfront : IsFrontier M (extendedState s) j) (i : Fin M)
    (hi : i.val + 1 < j) : outerPulseRadialTerm s p i = 0 := by
  have hhigh := hfront.2.1 (i.val + 1) hi
  rw [extendedState_succ s i.val i.isLt] at hhigh
  have hA : frontierSwitch (s i) = 1 := frontierSwitch_eq_one_of_one_le hhigh
  unfold outerPulseRadialTerm
  rw [hA]
  ring

private theorem outerPulseRadialTerm_eq_zero_of_after {M : Nat}
    (s : State M) (p : Pulse M) {j : Nat}
    (hfront : IsFrontier M (extendedState s) j) (i : Fin M)
    (hi : j < i.val + 1) : outerPulseRadialTerm s p i = 0 := by
  have hji : j ≤ i.val := by omega
  have hlow := hfront.2.2 i.val hji (by omega)
  rw [← previousMemory_eq_extendedState s i] at hlow
  have hA : frontierSwitch (previousMemory s i) = 0 :=
    frontierSwitch_eq_zero_of_le_fifth hlow
  unfold outerPulseRadialTerm
  rw [hA]
  ring

private theorem coordinate_abs_le_sqrt_vecSq {m : Nat}
    (v : NCCLowerBoundVerification.EVec m) (i : Fin m) :
    |v i| ≤ Real.sqrt (vecSq v) := by
  have hs0 := Real.sqrt_nonneg (vecSq v)
  have hs2 := Real.sq_sqrt (by
    unfold vecSq NCPLVerification.vecSq
    positivity : 0 ≤ vecSq v)
  have hi := coordinate_sq_le_vecSq v i
  nlinarith [sq_abs (v i)]

private theorem active_outerPulseRadialTerm_ge {M : Nat}
    (s : State M) (p : Pulse M) (i : Fin M) :
    -7 * Real.sqrt (vecSq p) ≤ outerPulseRadialTerm s p i := by
  have hAprev := frontierSwitch_mem_unitInterval (previousMemory s i)
  have hA := frontierSwitch_mem_unitInterval (s i)
  have hPa := pulseClip_deriv_mem_unitInterval (pulseA p i)
  have hPb := pulseClip_deriv_mem_unitInterval (pulseB p i)
  have hC := stateClip_abs_le_three (s i)
  let qa := frontierSwitch (previousMemory s i) *
    (1 - frontierSwitch (s i)) * deriv pulseClip (pulseA p i)
  let qb := frontierSwitch (previousMemory s i) * stateClip (s i) *
    (1 - frontierSwitch (s i)) * deriv pulseClip (pulseB p i)
  have hqa : |qa| ≤ 1 := by
    dsimp [qa]
    rw [abs_mul, abs_mul, abs_of_nonneg hAprev.1,
      abs_of_nonneg (sub_nonneg.mpr hA.2), abs_of_nonneg hPa.1]
    have hsub0 : 0 ≤ 1 - frontierSwitch (s i) := by linarith [hA.2]
    have hsub1 : 1 - frontierSwitch (s i) ≤ 1 := by linarith [hA.1]
    have h12 : frontierSwitch (previousMemory s i) *
        (1 - frontierSwitch (s i)) ≤ 1 * 1 :=
      mul2_mono_nonneg hAprev.1 hsub0 (by norm_num) hAprev.2 hsub1
    have h123 := mul2_mono_nonneg
      (mul_nonneg hAprev.1 hsub0) hPa.1 (by norm_num) h12 hPa.2
    simpa using h123
  have hqb : |qb| ≤ 3 := by
    dsimp [qb]
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hAprev.1,
      abs_of_nonneg (sub_nonneg.mpr hA.2), abs_of_nonneg hPb.1]
    have hsub0 : 0 ≤ 1 - frontierSwitch (s i) := by linarith [hA.2]
    have hsub1 : 1 - frontierSwitch (s i) ≤ 1 := by linarith [hA.1]
    have h12 : frontierSwitch (previousMemory s i) * |stateClip (s i)| ≤
        1 * 3 := mul2_mono_nonneg hAprev.1 (abs_nonneg _) (by norm_num)
          hAprev.2 hC
    have h123 := mul2_mono_nonneg (mul_nonneg hAprev.1 (abs_nonneg _))
      hsub0 (by norm_num) h12 hsub1
    have h1234 := mul2_mono_nonneg
      (mul_nonneg (mul_nonneg hAprev.1 (abs_nonneg _)) hsub0)
      hPb.1 (by norm_num) h123 hPb.2
    norm_num at h1234 ⊢
    exact h1234
  have hqaMul : qa * pulseA p i ≤ |pulseA p i| := by
    calc
      qa * pulseA p i ≤ |qa * pulseA p i| := le_abs_self _
      _ = |qa| * |pulseA p i| := abs_mul _ _
      _ ≤ 1 * |pulseA p i| :=
        mul_le_mul_of_nonneg_right hqa (abs_nonneg _)
      _ = _ := one_mul _
  have hqbMul : qb * pulseB p i ≤ 3 * |pulseB p i| := by
    calc
      qb * pulseB p i ≤ |qb * pulseB p i| := le_abs_self _
      _ = |qb| * |pulseB p i| := abs_mul _ _
      _ ≤ 3 * |pulseB p i| :=
        mul_le_mul_of_nonneg_right hqb (abs_nonneg _)
  have ha := coordinate_abs_le_sqrt_vecSq p
    (finProdFinEquiv (i, ⟨0, by omega⟩))
  have hb := coordinate_abs_le_sqrt_vecSq p
    (finProdFinEquiv (i, ⟨1, by omega⟩))
  change |pulseA p i| ≤ Real.sqrt (vecSq p) at ha
  change |pulseB p i| ≤ Real.sqrt (vecSq p) at hb
  unfold outerPulseRadialTerm
  dsimp [qa, qb] at hqaMul hqbMul
  nlinarith

theorem outerPulseRadial_ge_of_frontier {M : Nat} (s : State M)
    (p : Pulse M) {j : Nat} (hjpos : 1 ≤ j)
    (hfront : IsFrontier M (extendedState s) j) :
    -7 * Real.sqrt (vecSq p) ≤ outerPulseRadial s p := by
  let jf : Fin M := ⟨j - 1, by have hjM := hfront.1; omega⟩
  have hsingle : outerPulseRadial s p = outerPulseRadialTerm s p jf := by
    unfold outerPulseRadial
    rw [Finset.sum_eq_single jf]
    · intro i _ hne
      have hval : i.val + 1 ≠ j := by
        intro heq
        apply hne
        apply Fin.ext
        dsimp [jf]
        omega
      rcases lt_or_gt_of_ne hval with hlt | hgt
      · exact outerPulseRadialTerm_eq_zero_of_before s p hfront i hlt
      · exact outerPulseRadialTerm_eq_zero_of_after s p hfront i hgt
    · simp
  rw [hsingle]
  exact active_outerPulseRadialTerm_ge s p jf

def pulseDot {M : Nat} (g p : Pulse M) : ℝ :=
  ∑ k : Fin (M * 2), g k * p k

private theorem pulseDot_sq_le {M : Nat} (g p : Pulse M) :
    pulseDot g p ^ 2 ≤ vecSq g * vecSq p := by
  simpa [pulseDot, vecSq, NCPLVerification.vecSq] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g p)

theorem terminalValue_pulseRadial_fderiv {M : Nat} (K : ℝ)
    {V : Pulse M → ℝ} (hV : Differentiable ℝ V)
    (z : TerminalPrimal M) :
    (fderiv ℝ (terminalValue K V) z) (0, z.2) =
      outerPulseRadial z.1 z.2 + (fderiv ℝ V z.2) z.2 := by
  have hpcurve : HasDerivAt (fun t : ℝ ↦ t • z.2) z.2 1 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) (1 : ℝ)).smul_const z.2
  have hcurve : HasDerivAt (fun t : ℝ ↦ (z.1, t • z.2)) (0, z.2) 1 :=
    (hasDerivAt_const (x := (1 : ℝ)) z.1).prodMk hpcurve
  have hfull : HasDerivAt
      (terminalValue K V ∘ fun t : ℝ ↦ (z.1, t • z.2))
      ((fderiv ℝ (terminalValue K V) z) (0, z.2)) 1 := by
    have hf := (terminalValue_differentiable K hV z).hasFDerivAt
    have hz : z = (z.1, (1 : ℝ) • z.2) := by simp
    exact hf.comp_hasDerivAt_of_eq 1 hcurve hz
  have hinner : HasDerivAt (fun t : ℝ ↦ V (t • z.2))
      ((fderiv ℝ V z.2) z.2) 1 := by
    have hf := (hV z.2).hasFDerivAt
    have hp' : HasDerivAt (fun t : ℝ ↦ t • z.2) z.2 1 := hpcurve
    have hz : z.2 = (1 : ℝ) • z.2 := by simp
    simpa [Function.comp_def] using hf.comp_hasDerivAt_of_eq 1 hp' hz
  have hexact : HasDerivAt
      (fun t : ℝ ↦ terminalValue K V (z.1, t • z.2))
      (outerPulseRadial z.1 z.2 + (fderiv ℝ V z.2) z.2) 1 := by
    convert (hasDerivAt_terminalOuterValue_pulseRadial K z.1 z.2).add hinner using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    funext t
    rfl
  exact hfull.unique hexact

theorem terminalValue_pulseRadial_eq_dot {M : Nat} (K : ℝ)
    {V : Pulse M → ℝ} (hV : Differentiable ℝ V)
    (z : TerminalPrimal M) :
    outerPulseRadial z.1 z.2 + (fderiv ℝ V z.2) z.2 =
      pulseDot (actualPulseGradient (terminalValue K V) z) z.2 := by
  rw [← terminalValue_pulseRadial_fderiv K hV z]
  have hrep := actualGradient_represents_fderiv
    (terminalValue_differentiable K hV)
  simpa [pulseDot] using hrep.2 z.1 z.2 0 z.2

private theorem smallGradient_pulseDot_le {M : Nat} (f : TerminalPrimal M → ℝ)
    (z : TerminalPrimal M)
    (hsmall : actualGradientSq f z ≤ (1 / 4 : ℝ) ^ 2) :
    pulseDot (actualPulseGradient f z) z.2 ≤
      (1 / 4 : ℝ) * Real.sqrt (vecSq z.2) := by
  let g := actualPulseGradient f z
  let d := pulseDot g z.2
  have hstate0 : 0 ≤ vecSq (actualStateGradient f z) := by
    unfold vecSq NCPLVerification.vecSq
    positivity
  have hg : vecSq g ≤ (1 / 4 : ℝ) ^ 2 := by
    dsimp [g]
    unfold actualGradientSq at hsmall
    linarith
  have hp0 : 0 ≤ vecSq z.2 := by
    unfold vecSq NCPLVerification.vecSq
    positivity
  have hgsq0 : 0 ≤ vecSq g := by
    unfold vecSq NCPLVerification.vecSq
    positivity
  have hdot := pulseDot_sq_le g z.2
  have hprod : vecSq g * vecSq z.2 ≤
      (1 / 4 : ℝ) ^ 2 * vecSq z.2 :=
    mul_le_mul_of_nonneg_right hg hp0
  have hs0 := Real.sqrt_nonneg (vecSq z.2)
  have hs2 := Real.sq_sqrt hp0
  by_cases hd : d ≤ 0
  · dsimp [d, g] at hd ⊢
    exact hd.trans (mul_nonneg (by norm_num) hs0)
  · have hdpos : 0 < d := lt_of_not_ge hd
    dsimp [d, g] at hdpos hdot ⊢
    nlinarith

theorem smallGradient_pulseSq_le_fourHundred {M : Nat} (hM : 1 ≤ M)
    {V : Pulse M → ℝ} (hV : Differentiable ℝ V)
    (hradial : ∀ p : Pulse M,
      (2 / 5 : ℝ) * vecSq p ≤ (fderiv ℝ V p) p)
    (z : TerminalPrimal M)
    (hsmall : actualGradientSq (terminalValue terminalPhaseScale V) z ≤
      (1 / 4 : ℝ) ^ 2)
    (hterminal : z.1 ⟨M - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    vecSq z.2 ≤ 20 ^ 2 := by
  obtain ⟨j, ⟨hjpos, hfront⟩, _⟩ :=
    smallGradient_unique_frontier hM hV z hsmall hterminal
  let r := Real.sqrt (vecSq z.2)
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hp0 : 0 ≤ vecSq z.2 := by
    unfold vecSq NCPLVerification.vecSq
    positivity
  have hr2 : r ^ 2 = vecSq z.2 := Real.sq_sqrt hp0
  have hout := outerPulseRadial_ge_of_frontier z.1 z.2 hjpos hfront
  have hinn := hradial z.2
  have hdot := smallGradient_pulseDot_le
    (terminalValue terminalPhaseScale V) z hsmall
  have heq := terminalValue_pulseRadial_eq_dot terminalPhaseScale hV z
  have hbudget : (2 / 5 : ℝ) * r ^ 2 - 7 * r ≤ (1 / 4 : ℝ) * r := by
    dsimp [r] at hout hdot hr2 ⊢
    rw [hr2]
    linarith
  have hr20 := pulse_norm_le_twenty hr0 (by norm_num) (by norm_num) hbudget
  nlinarith

theorem finiteValue_smallGradient_pulseSq_le {M N : Nat} (hM : 1 ≤ M)
    (hN10 : 10 ≤ N) {D : ℝ} (hD : 0 ≤ D) (z : TerminalPrimal M)
    (hsmall : actualGradientSq
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D)) z ≤
      (1 / 4 : ℝ) ^ 2)
    (hterminal : z.1 ⟨M - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    vecSq z.2 ≤ 20 ^ 2 := by
  apply smallGradient_pulseSq_le_fourHundred hM
    (InnerFiniteBall.finiteValue_differentiable (M := M)
      (by omega : 0 < N) hD) _ z hsmall hterminal
  intro p
  exact InnerFiniteBall.finiteValue_radial hN10 hD p

theorem unboundedValue_smallGradient_pulseSq_le {M N : Nat} (hM : 1 ≤ M)
    (hN10 : 10 ≤ N) (z : TerminalPrimal M)
    (hsmall : actualGradientSq
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N))) z ≤
      (1 / 4 : ℝ) ^ 2)
    (hterminal : z.1 ⟨M - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    vecSq z.2 ≤ 20 ^ 2 := by
  apply smallGradient_pulseSq_le_fourHundred hM
    (InnerFiniteBall.unboundedValue_differentiable (M := M) hN10) _ z
      hsmall hterminal
  intro p
  exact InnerFiniteBall.unboundedValue_radial hN10 p

/-! ## Exact frontier pulse coordinates for the unrestricted value -/

def pulseAIndex {M : Nat} (i : Fin M) : Fin (M * 2) :=
  finProdFinEquiv (i, ⟨0, by omega⟩)

def pulseBIndex {M : Nat} (i : Fin M) : Fin (M * 2) :=
  finProdFinEquiv (i, ⟨1, by omega⟩)

@[simp] theorem pulseA_replace_A {M : Nat} (p : Pulse M) (i : Fin M) (t : ℝ) :
    pulseA (replaceCoordinate p (pulseAIndex i) t) =
      replaceCoordinate (pulseA p) i t := by
  funext l
  by_cases hli : l = i
  · subst l
    simp [pulseA, pulseAIndex, replaceCoordinate]
  · simp [pulseA, pulseAIndex, replaceCoordinate, hli]

@[simp] theorem pulseB_replace_A {M : Nat} (p : Pulse M) (i : Fin M) (t : ℝ) :
    pulseB (replaceCoordinate p (pulseAIndex i) t) = pulseB p := by
  funext l
  simp [pulseB, pulseAIndex, replaceCoordinate]

@[simp] theorem pulseA_replace_B {M : Nat} (p : Pulse M) (i : Fin M) (t : ℝ) :
    pulseA (replaceCoordinate p (pulseBIndex i) t) = pulseA p := by
  funext l
  simp [pulseA, pulseBIndex, replaceCoordinate]

@[simp] theorem pulseB_replace_B {M : Nat} (p : Pulse M) (i : Fin M) (t : ℝ) :
    pulseB (replaceCoordinate p (pulseBIndex i) t) =
      replaceCoordinate (pulseB p) i t := by
  funext l
  by_cases hli : l = i
  · subst l
    simp [pulseB, pulseBIndex, replaceCoordinate]
  · simp [pulseB, pulseBIndex, replaceCoordinate, hli]

def explicitPulseGradA {M : Nat} (s : State M) (p : Pulse M) (i : Fin M) : ℝ :=
  -4 * frontierSwitch (previousMemory s i) * (1 - frontierSwitch (s i)) *
      deriv pulseClip (pulseA p i) + 2 * pulseA p i - pulseB p i

def explicitPulseGradB {M : Nat} (s : State M) (p : Pulse M) (i : Fin M) : ℝ :=
  -frontierSwitch (previousMemory s i) * stateClip (s i) *
      (1 - frontierSwitch (s i)) * deriv pulseClip (pulseB p i) -
    pulseA p i + 2 * pulseB p i

private theorem hasDerivAt_explicit_terminal_A {M : Nat} (K : ℝ)
    (s : State M) (p : Pulse M) (i : Fin M) :
    HasDerivAt
      (fun t : ℝ ↦ terminalValue K InnerFiniteBall.explicitValue
        (s, replaceCoordinate p (pulseAIndex i) t))
      (explicitPulseGradA s p i) (pulseA p i) := by
  have hpulse : HasDerivAt pulseClip (deriv pulseClip (pulseA p i))
      (pulseA p i) :=
    (pulseClip_contDiff.differentiable (by simp) _).hasDerivAt
  have hent : HasDerivAt
      (fun t : ℝ ↦ entranceComponent s
        (pulseA (replaceCoordinate p (pulseAIndex i) t)))
      (-4 * frontierSwitch (previousMemory s i) *
        (1 - frontierSwitch (s i)) * deriv pulseClip (pulseA p i))
      (pulseA p i) := by
    unfold entranceComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin M,
          entranceSummand s (replaceCoordinate (pulseA p) i t) l)
        (∑ l : Fin M, if l = i then
          -4 * frontierSwitch (previousMemory s i) *
            (1 - frontierSwitch (s i)) * deriv pulseClip (pulseA p i)
          else 0) (pulseA p i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa [entranceSummand, replaceCoordinate] using hpulse.const_mul
          (-4 * frontierSwitch (previousMemory s i) *
            (1 - frontierSwitch (s i)))
      · simpa [entranceSummand, replaceCoordinate, hli] using
          hasDerivAt_const (pulseA p i) (entranceSummand s (pulseA p) l)
    rw [Finset.sum_ite_eq'] at hs
    simpa using hs
  have houter : HasDerivAt
      (fun t : ℝ ↦ terminalOuterValue K
        (s, replaceCoordinate p (pulseAIndex i) t))
      (-4 * frontierSwitch (previousMemory s i) *
        (1 - frontierSwitch (s i)) * deriv pulseClip (pulseA p i))
      (pulseA p i) := by
    have hc : HasDerivAt
        (fun _ : ℝ ↦ phaseComponent K s + orderingComponent s) 0 (pulseA p i) :=
      hasDerivAt_const _ _
    have hx : HasDerivAt
        (fun _ : ℝ ↦ exitComponent s (pulseB p)) 0 (pulseA p i) :=
      hasDerivAt_const _ _
    convert (hc.add hent |>.add hx) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp [terminalOuterValue, outerComponent]
    · ring
  have hinner : HasDerivAt
      (fun t : ℝ ↦ InnerFiniteBall.explicitValue
        (replaceCoordinate p (pulseAIndex i) t))
      (2 * pulseA p i - pulseB p i) (pulseA p i) := by
    unfold InnerFiniteBall.explicitValue
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin M,
          ((replaceCoordinate (pulseA p) i t l) ^ 2 -
            replaceCoordinate (pulseA p) i t l * pulseB p l +
            (pulseB p l) ^ 2))
        (∑ l : Fin M, if l = i then 2 * pulseA p i - pulseB p i else 0)
        (pulseA p i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        convert (((hasDerivAt_id (pulseA p i)).pow 2).sub
          ((hasDerivAt_id (pulseA p i)).mul_const (pulseB p i))).add_const
            ((pulseB p i) ^ 2) using 1
        · funext t
          simp [replaceCoordinate]
        · simp
      · convert hasDerivAt_const (pulseA p i)
          ((pulseA p l) ^ 2 - pulseA p l * pulseB p l + (pulseB p l) ^ 2) using 1
        · funext t
          simp [replaceCoordinate, hli]
        · simp [hli]
    rw [Finset.sum_ite_eq'] at hs
    convert hs using 1
    · funext t
      change (∑ x : Fin M,
        ((pulseA (replaceCoordinate p (pulseAIndex i) t) x) ^ 2 -
          pulseA (replaceCoordinate p (pulseAIndex i) t) x *
            pulseB (replaceCoordinate p (pulseAIndex i) t) x +
          (pulseB (replaceCoordinate p (pulseAIndex i) t) x) ^ 2)) = _
      rw [pulseA_replace_A, pulseB_replace_A]
    · simp
  unfold explicitPulseGradA
  convert houter.add hinner using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    rfl
  · ring

theorem actualPulseGradient_explicit_A {M : Nat} (K : ℝ)
    (z : TerminalPrimal M) (i : Fin M) :
    actualPulseGradient
      (terminalValue K (InnerFiniteBall.explicitValue : Pulse M → ℝ)) z
      (pulseAIndex i) = explicitPulseGradA z.1 z.2 i := by
  have hpLine : HasDerivAt
      (fun t : ℝ ↦ replaceCoordinate z.2 (pulseAIndex i) t)
      (NCPLVerification.evecBasis (pulseAIndex i)) (pulseA z.2 i) := by
    rw [hasDerivAt_pi]
    intro k
    convert (hasDerivAt_const (pulseA z.2 i) (z.2 k)).add
      (((hasDerivAt_id (pulseA z.2 i)).sub_const (pulseA z.2 i)).mul_const
        (NCPLVerification.evecBasis (pulseAIndex i) k)) using 1
    · funext t
      by_cases hk : k = pulseAIndex i
      · subst k
        simp [replaceCoordinate, pulseA, pulseAIndex, NCPLVerification.evecBasis]
      · simp [replaceCoordinate, NCPLVerification.evecBasis, hk]
    · simp [NCPLVerification.evecBasis]
  have hcurve : HasDerivAt
      (fun t : ℝ ↦ (z.1, replaceCoordinate z.2 (pulseAIndex i) t))
      (0, NCPLVerification.evecBasis (pulseAIndex i)) (pulseA z.2 i) :=
    (hasDerivAt_const (pulseA z.2 i) z.1).prodMk hpLine
  have hpoint : (z.1, replaceCoordinate z.2 (pulseAIndex i) (pulseA z.2 i)) = z := by
    apply Prod.ext
    · rfl
    · funext k
      by_cases hk : k = pulseAIndex i
      · subst k
        simp [replaceCoordinate, pulseA, pulseAIndex]
      · simp [replaceCoordinate, hk]
  have hf := (terminalValue_differentiable K
    (InnerFiniteBall.explicitValue_contDiff.differentiable (by simp))) z
      |>.hasFDerivAt
  have hcomp := hf.comp_hasDerivAt_of_eq (pulseA z.2 i) hcurve hpoint.symm
  have hexact := hasDerivAt_explicit_terminal_A K z.1 z.2 i
  unfold actualPulseGradient ambientGradY
  exact hcomp.unique hexact

private theorem hasDerivAt_explicit_terminal_B {M : Nat} (K : ℝ)
    (s : State M) (p : Pulse M) (i : Fin M) :
    HasDerivAt
      (fun t : ℝ ↦ terminalValue K InnerFiniteBall.explicitValue
        (s, replaceCoordinate p (pulseBIndex i) t))
      (explicitPulseGradB s p i) (pulseB p i) := by
  have hpulse : HasDerivAt pulseClip (deriv pulseClip (pulseB p i))
      (pulseB p i) :=
    (pulseClip_contDiff.differentiable (by simp) _).hasDerivAt
  have hexit : HasDerivAt
      (fun t : ℝ ↦ exitComponent s
        (pulseB (replaceCoordinate p (pulseBIndex i) t)))
      (-frontierSwitch (previousMemory s i) * stateClip (s i) *
        (1 - frontierSwitch (s i)) * deriv pulseClip (pulseB p i))
      (pulseB p i) := by
    unfold exitComponent
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin M,
          exitSummand s (replaceCoordinate (pulseB p) i t) l)
        (∑ l : Fin M, if l = i then
          -frontierSwitch (previousMemory s i) * stateClip (s i) *
            (1 - frontierSwitch (s i)) * deriv pulseClip (pulseB p i)
          else 0) (pulseB p i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        simpa [exitSummand, replaceCoordinate] using hpulse.const_mul
          (-frontierSwitch (previousMemory s i) * stateClip (s i) *
            (1 - frontierSwitch (s i)))
      · simpa [exitSummand, replaceCoordinate, hli] using
          hasDerivAt_const (pulseB p i) (exitSummand s (pulseB p) l)
    rw [Finset.sum_ite_eq'] at hs
    simpa using hs
  have houter : HasDerivAt
      (fun t : ℝ ↦ terminalOuterValue K
        (s, replaceCoordinate p (pulseBIndex i) t))
      (-frontierSwitch (previousMemory s i) * stateClip (s i) *
        (1 - frontierSwitch (s i)) * deriv pulseClip (pulseB p i))
      (pulseB p i) := by
    have hc : HasDerivAt
        (fun _ : ℝ ↦ phaseComponent K s + orderingComponent s) 0 (pulseB p i) :=
      hasDerivAt_const _ _
    have he : HasDerivAt
        (fun _ : ℝ ↦ entranceComponent s (pulseA p)) 0 (pulseB p i) :=
      hasDerivAt_const _ _
    convert (hc.add he |>.add hexit) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp [terminalOuterValue, outerComponent]
    · ring
  have hinner : HasDerivAt
      (fun t : ℝ ↦ InnerFiniteBall.explicitValue
        (replaceCoordinate p (pulseBIndex i) t))
      (-pulseA p i + 2 * pulseB p i) (pulseB p i) := by
    unfold InnerFiniteBall.explicitValue
    have hs : HasDerivAt
        (fun t : ℝ ↦ ∑ l : Fin M,
          ((pulseA p l) ^ 2 - pulseA p l *
            replaceCoordinate (pulseB p) i t l +
            (replaceCoordinate (pulseB p) i t l) ^ 2))
        (∑ l : Fin M, if l = i then -pulseA p i + 2 * pulseB p i else 0)
        (pulseB p i) := by
      apply HasDerivAt.fun_sum
      intro l _
      by_cases hli : l = i
      · subst l
        convert (((hasDerivAt_const (pulseB p i) ((pulseA p i) ^ 2)).sub
          ((hasDerivAt_id (pulseB p i)).const_mul (pulseA p i))).add
            ((hasDerivAt_id (pulseB p i)).pow 2)) using 1
        · funext t
          simp [replaceCoordinate]
        · simp
      · convert hasDerivAt_const (pulseB p i)
          ((pulseA p l) ^ 2 - pulseA p l * pulseB p l + (pulseB p l) ^ 2) using 1
        · funext t
          simp [replaceCoordinate, hli]
        · simp [hli]
    rw [Finset.sum_ite_eq'] at hs
    convert hs using 1
    · funext t
      change (∑ x : Fin M,
        ((pulseA (replaceCoordinate p (pulseBIndex i) t) x) ^ 2 -
          pulseA (replaceCoordinate p (pulseBIndex i) t) x *
            pulseB (replaceCoordinate p (pulseBIndex i) t) x +
          (pulseB (replaceCoordinate p (pulseBIndex i) t) x) ^ 2)) = _
      rw [pulseA_replace_B, pulseB_replace_B]
    · simp
  unfold explicitPulseGradB
  convert houter.add hinner using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    rfl
  · ring

theorem actualPulseGradient_explicit_B {M : Nat} (K : ℝ)
    (z : TerminalPrimal M) (i : Fin M) :
    actualPulseGradient
      (terminalValue K (InnerFiniteBall.explicitValue : Pulse M → ℝ)) z
      (pulseBIndex i) = explicitPulseGradB z.1 z.2 i := by
  have hpLine : HasDerivAt
      (fun t : ℝ ↦ replaceCoordinate z.2 (pulseBIndex i) t)
      (NCPLVerification.evecBasis (pulseBIndex i)) (pulseB z.2 i) := by
    rw [hasDerivAt_pi]
    intro k
    convert (hasDerivAt_const (pulseB z.2 i) (z.2 k)).add
      (((hasDerivAt_id (pulseB z.2 i)).sub_const (pulseB z.2 i)).mul_const
        (NCPLVerification.evecBasis (pulseBIndex i) k)) using 1
    · funext t
      by_cases hk : k = pulseBIndex i
      · subst k
        simp [replaceCoordinate, pulseB, pulseBIndex, NCPLVerification.evecBasis]
      · simp [replaceCoordinate, NCPLVerification.evecBasis, hk]
    · simp [NCPLVerification.evecBasis]
  have hcurve : HasDerivAt
      (fun t : ℝ ↦ (z.1, replaceCoordinate z.2 (pulseBIndex i) t))
      (0, NCPLVerification.evecBasis (pulseBIndex i)) (pulseB z.2 i) :=
    (hasDerivAt_const (pulseB z.2 i) z.1).prodMk hpLine
  have hpoint : (z.1, replaceCoordinate z.2 (pulseBIndex i) (pulseB z.2 i)) = z := by
    apply Prod.ext
    · rfl
    · funext k
      by_cases hk : k = pulseBIndex i
      · subst k
        simp [replaceCoordinate, pulseB, pulseBIndex]
      · simp [replaceCoordinate, hk]
  have hf := (terminalValue_differentiable K
    (InnerFiniteBall.explicitValue_contDiff.differentiable (by simp))) z
      |>.hasFDerivAt
  have hcomp := hf.comp_hasDerivAt_of_eq (pulseB z.2 i) hcurve hpoint.symm
  have hexact := hasDerivAt_explicit_terminal_B K z.1 z.2 i
  unfold actualPulseGradient ambientGradY
  exact hcomp.unique hexact

private theorem outerStateDerivative_le_neg_one_of_frontier {M : Nat}
    (s a b : Fin M → ℝ) (i : Fin M)
    (hlower : -(1 / 10 : ℝ) < s i) (hupper : s i ≤ (1 / 5 : ℝ))
    (hprev : (1 : ℝ) ≤ previousMemory s i)
    (hb : 1 ≤ b i) (hbabs : |b i| ≤ 21)
    (hnextLow : ∀ h : i.val + 1 < M,
      s ⟨i.val + 1, h⟩ ≤ (1 / 5 : ℝ)) :
    outerStateDerivative terminalPhaseScale s a b i ≤ -1 := by
  have habs : |s i| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hC : stateClip (s i) = s i := stateClip_eq_self habs
  have hCd : deriv stateClip (s i) = 1 := stateClip_deriv_eq_one habs
  have hA : frontierSwitch (s i) = 0 :=
    frontierSwitch_eq_zero_of_le_fifth hupper
  have hAd : deriv frontierSwitch (s i) = 0 :=
    frontierSwitch_deriv_eq_zero_of_le_fifth hupper
  have hAp : frontierSwitch (previousMemory s i) = 1 :=
    frontierSwitch_eq_one_of_one_le hprev
  have hPb : pulseClip (b i) = b i := pulseClip_eq_self hbabs
  have hphase := phasePotential_deriv_nonpos terminalPhaseScale_pos (s i)
  by_cases hsucc : i.val + 1 < M
  · have hAj : frontierSwitch (s ⟨i.val + 1, hsucc⟩) = 0 :=
      frontierSwitch_eq_zero_of_le_fifth (hnextLow hsucc)
    unfold outerStateDerivative nextStateContribution nextOrderingStateContribution
      nextEntranceStateContribution nextExitStateContribution
    simp only [hsucc, ↓reduceDIte]
    rw [hA, hAd, hAp, hC, hCd, hPb, hAj]
    norm_num only [zero_mul, mul_zero, sub_zero, sub_self, mul_one,
      add_zero, neg_zero]
    nlinarith
  · unfold outerStateDerivative nextStateContribution nextOrderingStateContribution
      nextEntranceStateContribution nextExitStateContribution
    simp only [hsucc, ↓reduceDIte]
    rw [hA, hAd, hAp, hC, hCd, hPb]
    norm_num only [zero_mul, mul_zero, sub_zero, sub_self, mul_one,
      add_zero, neg_zero]
    nlinarith

theorem explicitValue_terminal_gradientSq_lower {M : Nat} (hM : 1 ≤ M)
    (z : TerminalPrimal M)
    (hterminal : z.1 ⟨M - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    (1 / 4 : ℝ) ^ 2 ≤ actualGradientSq
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.explicitValue : Pulse M → ℝ)) z := by
  let f := terminalValue terminalPhaseScale
    (InnerFiniteBall.explicitValue : Pulse M → ℝ)
  by_contra hnot
  have hsmall : actualGradientSq f z ≤ (1 / 4 : ℝ) ^ 2 :=
    le_of_lt (lt_of_not_ge hnot)
  have hV : Differentiable ℝ
      (InnerFiniteBall.explicitValue : Pulse M → ℝ) :=
    InnerFiniteBall.explicitValue_contDiff.differentiable (by simp)
  have hpulse : vecSq z.2 ≤ 20 ^ 2 := by
    apply smallGradient_pulseSq_le_fourHundred hM hV _ z hsmall hterminal
    intro p
    rw [InnerFiniteBall.explicitValue_fderiv_apply_self]
    exact InnerFiniteBall.explicitValue_radial_lower p
  obtain ⟨j, ⟨hjpos, hfront⟩, _⟩ :=
    smallGradient_unique_frontier hM hV z hsmall hterminal
  let i : Fin M := ⟨j - 1, by have := hfront.1; omega⟩
  have hcurLow : z.1 i ≤ (1 / 5 : ℝ) := by
    have h := hfront.2.2 j le_rfl hfront.1
    have hjlt : j - 1 < M := by have := hfront.1; omega
    have he := extendedState_succ z.1 (j - 1) hjlt
    have hj : j = (j - 1) + 1 := by omega
    rw [hj, he] at h
    exact h
  have hcurLower := smallGradient_excludes_farLeft hV z hsmall i
  have hprevHigh : (1 : ℝ) ≤ previousMemory z.1 i := by
    rw [previousMemory_eq_extendedState]
    apply hfront.2.1
    dsimp [i]
    omega
  have haSq := coordinate_sq_le_vecSq z.2 (pulseAIndex i)
  have hbSq := coordinate_sq_le_vecSq z.2 (pulseBIndex i)
  have haAbs : |pulseA z.2 i| ≤ 20 := by
    change |z.2 (pulseAIndex i)| ≤ 20
    nlinarith [sq_abs (z.2 (pulseAIndex i))]
  have hbAbs : |pulseB z.2 i| ≤ 20 := by
    change |z.2 (pulseBIndex i)| ≤ 20
    nlinarith [sq_abs (z.2 (pulseBIndex i))]
  have hAprev : frontierSwitch (previousMemory z.1 i) = 1 :=
    frontierSwitch_eq_one_of_one_le hprevHigh
  have hAcur : frontierSwitch (z.1 i) = 0 :=
    frontierSwitch_eq_zero_of_le_fifth hcurLow
  have hcurAbs : |z.1 i| ≤ 2 := by rw [abs_le]; constructor <;> linarith
  have hCcur : stateClip (z.1 i) = z.1 i := stateClip_eq_self hcurAbs
  have hPda : deriv pulseClip (pulseA z.2 i) = 1 :=
    pulseClip_deriv_eq_one (haAbs.trans (by norm_num))
  have hPdb : deriv pulseClip (pulseB z.2 i) = 1 :=
    pulseClip_deriv_eq_one (hbAbs.trans (by norm_num))
  let ga := actualPulseGradient f z (pulseAIndex i)
  let gb := actualPulseGradient f z (pulseBIndex i)
  have hga : ga = 2 * pulseA z.2 i - pulseB z.2 i - 4 := by
    dsimp [ga, f]
    rw [actualPulseGradient_explicit_A, explicitPulseGradA,
      hAprev, hAcur, hPda]
    ring
  have hgb : gb = -pulseA z.2 i + 2 * pulseB z.2 i - z.1 i := by
    dsimp [gb, f]
    rw [actualPulseGradient_explicit_B, explicitPulseGradB,
      hAprev, hAcur, hPdb, hCcur]
    ring
  have hgaCoord := coordinate_sq_le_vecSq (actualPulseGradient f z) (pulseAIndex i)
  have hgbCoord := coordinate_sq_le_vecSq (actualPulseGradient f z) (pulseBIndex i)
  have hpGrad : vecSq (actualPulseGradient f z) ≤ actualGradientSq f z := by
    unfold actualGradientSq
    have hs0 : 0 ≤ vecSq (actualStateGradient f z) := by
      unfold vecSq NCPLVerification.vecSq
      positivity
    linarith
  have hgaLower : -(1 / 4 : ℝ) ≤ ga := by
    dsimp [ga] at hgaCoord ⊢
    nlinarith
  have hgbLower : -(1 / 4 : ℝ) ≤ gb := by
    dsimp [gb] at hgbCoord ⊢
    nlinarith
  have hbOne : 1 ≤ pulseB z.2 i := by
    nlinarith
  have hnextLow : ∀ h : i.val + 1 < M,
      z.1 ⟨i.val + 1, h⟩ ≤ (1 / 5 : ℝ) := by
    intro hsucc
    have hjM : j < M := by
      dsimp [i] at hsucc
      omega
    have hafterSeq := hfront.2.2 (j + 1) (by omega) (by omega)
    have hafter : z.1 ⟨j, hjM⟩ ≤ (1 / 5 : ℝ) := by
      simpa only [extendedState_succ z.1 j hjM] using hafterSeq
    have hidx : (⟨i.val + 1, hsucc⟩ : Fin M) = ⟨j, hjM⟩ := by
      apply Fin.ext
      dsimp [i]
      omega
    rw [hidx]
    exact hafter
  have hd := outerStateDerivative_le_neg_one_of_frontier z.1
    (pulseA z.2) (pulseB z.2) i hcurLower hcurLow hprevHigh hbOne
      (hbAbs.trans (by norm_num)) hnextLow
  have hc := stateGradient_coordinate_sq_le f z i
  have hstateEq := actualStateGradient_terminalValue_eq terminalPhaseScale hV z i
  dsimp [f] at hstateEq hc hsmall
  rw [hstateEq] at hc
  nlinarith

theorem unboundedValue_terminal_gradientSq_lower {M N : Nat} (hM : 1 ≤ M)
    (hN10 : 10 ≤ N) (z : TerminalPrimal M)
    (hterminal : z.1 ⟨M - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    (1 / 4 : ℝ) ^ 2 ≤ actualGradientSq
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N))) z := by
  have heq : terminalValue terminalPhaseScale
      (InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N)) =
      terminalValue terminalPhaseScale
        (InnerFiniteBall.explicitValue : Pulse M → ℝ) := by
    funext q
    simp only [terminalValue]
    rw [InnerFiniteBall.unboundedValue_eq_explicitValue hN10]
  rw [heq]
  exact explicitValue_terminal_gradientSq_lower hM z hterminal

def actualGradientNorm {M : Nat} (f : TerminalPrimal M → ℝ)
    (z : TerminalPrimal M) : ℝ := Real.sqrt (actualGradientSq f z)

theorem unboundedValue_terminal_gradientNorm_lower {M N : Nat} (hM : 1 ≤ M)
    (hN10 : 10 ≤ N) (z : TerminalPrimal M)
    (hterminal : z.1 ⟨M - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    (1 / 4 : ℝ) ≤ actualGradientNorm
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N))) z := by
  unfold actualGradientNorm
  have h := unboundedValue_terminal_gradientSq_lower hM hN10 z hterminal
  have hnonneg : 0 ≤ actualGradientSq
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N))) z := by
    unfold actualGradientSq vecSq NCPLVerification.vecSq
    positivity
  nlinarith [Real.sq_sqrt hnonneg,
    Real.sqrt_nonneg (actualGradientSq
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N))) z)]

/-! ## Finite-ball inactivity and the terminal certificate -/

def innerInactiveInterior {M N : Nat} (D : ℝ) : Set (Pulse M) :=
  {p | 8000 * (N : ℝ) ^ 2 * vecSq p < (D / 2) ^ 2}

theorem innerInactiveInterior_isOpen {M N : Nat} (D : ℝ) :
    IsOpen (innerInactiveInterior (M := M) (N := N) D) := by
  apply isOpen_lt
  · apply Continuous.const_mul
    unfold vecSq NCPLVerification.vecSq
    fun_prop
  · fun_prop

private theorem unboundedMaximizer_mem_ball_of_inactive {M N : Nat}
    (hN10 : 10 ≤ N) {D : ℝ} {p : Pulse M}
    (hp : p ∈ innerInactiveInterior (N := N) D) :
    InnerFiniteBall.unboundedMaximizer (M := M) (by omega : 0 < N) p ∈
      diameterBall (M * N) D := by
  change vecSq (InnerFiniteBall.unboundedMaximizer
    (M := M) (by omega : 0 < N) p) ≤ (D / 2) ^ 2
  unfold InnerFiniteBall.unboundedMaximizer
  rw [RestrictedBall.vecSq_flattenBlocks]
  calc
    (∑ i : Fin M, vecSq
      (blockWStar (by omega : 0 < N)
        (InnerFiniteBall.pulseA p) (InnerFiniteBall.pulseB p) i)) ≤
        8000 * (N : ℝ) ^ 2 *
          ∑ i : Fin M,
            ((InnerFiniteBall.pulseA p i) ^ 2 +
              (InnerFiniteBall.pulseB p i) ^ 2) :=
      blockWStar_growth hN10 _ _
    _ = 8000 * (N : ℝ) ^ 2 * vecSq p := by
      rw [InnerFiniteBall.vecSq_pulse]
    _ ≤ (D / 2) ^ 2 := hp.le

theorem finiteValue_eq_unboundedValue_of_inactive {M N : Nat}
    (hN10 : 10 ≤ N) {D : ℝ} {p : Pulse M}
    (hp : p ∈ innerInactiveInterior (N := N) D) :
    InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D p =
      InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N) p := by
  let hN : 0 < N := by omega
  let y := InnerFiniteBall.unboundedMaximizer (M := M) hN p
  have hu := InnerFiniteBall.unboundedMaximizer_spec (M := M) hN p
  have hy : y ∈ diameterBall (M * N) D := by
    exact unboundedMaximizer_mem_ball_of_inactive hN10 hp
  have hb : IsMaximizerOn (diameterBall (M * N) D)
      (InnerFiniteBall.innerObjective hN) p y := by
    refine ⟨hy, ?_⟩
    intro v _hv
    exact hu.2 v (Set.mem_univ v)
  rw [show InnerFiniteBall.finiteValue (M := M) hN D p =
      InnerFiniteBall.innerObjective hN p y by
    exact value_eq_of_isMaximizerOn hb]
  rw [show InnerFiniteBall.unboundedValue (M := M) hN p =
      InnerFiniteBall.innerObjective hN p y by
    exact value_eq_of_isMaximizerOn hu]

theorem finiteValue_eventuallyEq_unboundedValue_of_inactive {M N : Nat}
    (hN10 : 10 ≤ N) {D : ℝ} {p : Pulse M}
    (hp : p ∈ innerInactiveInterior (N := N) D) :
    InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D =ᶠ[nhds p]
      InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N) := by
  filter_upwards [(innerInactiveInterior_isOpen (M := M) (N := N) D).mem_nhds hp]
    with q hq
  exact finiteValue_eq_unboundedValue_of_inactive hN10 hq

theorem terminalValue_fderiv_finite_eq_unbounded_of_inactive {M N : Nat}
    (hN10 : 10 ≤ N) {D : ℝ} {z : TerminalPrimal M}
    (hp : z.2 ∈ innerInactiveInterior (N := N) D) :
    fderiv ℝ (terminalValue terminalPhaseScale
      (InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D)) z =
    fderiv ℝ (terminalValue terminalPhaseScale
      (InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N))) z := by
  have hev := finiteValue_eventuallyEq_unboundedValue_of_inactive hN10 hp
  have hevcomp :
      (fun q : TerminalPrimal M ↦
        InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D q.2) =ᶠ[nhds z]
      (fun q : TerminalPrimal M ↦
        InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N) q.2) :=
    hev.comp_tendsto continuousAt_snd
  have hevfull : terminalValue terminalPhaseScale
      (InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D) =ᶠ[nhds z]
      terminalValue terminalPhaseScale
        (InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N)) := by
    filter_upwards [hevcomp] with q hq
    simp [terminalValue, hq]
  exact hevfull.fderiv_eq

theorem actualGradientSq_finite_eq_unbounded_of_inactive {M N : Nat}
    (hN10 : 10 ≤ N) {D : ℝ} {z : TerminalPrimal M}
    (hp : z.2 ∈ innerInactiveInterior (N := N) D) :
    actualGradientSq
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D)) z =
    actualGradientSq
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N))) z := by
  have hf := terminalValue_fderiv_finite_eq_unbounded_of_inactive hN10 hp
  unfold actualGradientSq actualStateGradient actualPulseGradient
    ambientGradX ambientGradY
  rw [hf]

theorem finiteValue_terminal_gradientSq_lower {M N : Nat} (hM : 1 ≤ M)
    (hN10 : 10 ≤ N) {D : ℝ} (hD : 0 ≤ D)
    (hDmargin : 8000 * (N : ℝ) ^ 2 * 20 ^ 2 < (D / 2) ^ 2)
    (z : TerminalPrimal M)
    (hterminal : z.1 ⟨M - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    (1 / 4 : ℝ) ^ 2 ≤ actualGradientSq
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D)) z := by
  let f := terminalValue terminalPhaseScale
    (InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D)
  by_contra hnot
  have hsmall : actualGradientSq f z ≤ (1 / 4 : ℝ) ^ 2 :=
    le_of_lt (lt_of_not_ge hnot)
  have hpulse := finiteValue_smallGradient_pulseSq_le hM hN10 hD z
    hsmall hterminal
  have hp : z.2 ∈ innerInactiveInterior (N := N) D := by
    unfold innerInactiveInterior
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left hpulse (by positivity)) hDmargin
  have heq := actualGradientSq_finite_eq_unbounded_of_inactive hN10 hp
  have hun := unboundedValue_terminal_gradientSq_lower hM hN10 z hterminal
  dsimp [f] at hsmall
  rw [heq] at hsmall
  nlinarith

theorem finiteValue_terminal_gradientNorm_lower {M N : Nat} (hM : 1 ≤ M)
    (hN10 : 10 ≤ N) {D : ℝ} (hD : 0 ≤ D)
    (hDmargin : 8000 * (N : ℝ) ^ 2 * 20 ^ 2 < (D / 2) ^ 2)
    (z : TerminalPrimal M)
    (hterminal : z.1 ⟨M - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    (1 / 4 : ℝ) ≤ actualGradientNorm
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D)) z := by
  unfold actualGradientNorm
  have h := finiteValue_terminal_gradientSq_lower hM hN10 hD hDmargin z hterminal
  have hnonneg : 0 ≤ actualGradientSq
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D)) z := by
    unfold actualGradientSq vecSq NCPLVerification.vecSq
    positivity
  nlinarith [Real.sq_sqrt hnonneg,
    Real.sqrt_nonneg (actualGradientSq
      (terminalValue terminalPhaseScale
        (InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D)) z)]

end

end TerminalCertificate
end Simplified
end NCCLowerBound
