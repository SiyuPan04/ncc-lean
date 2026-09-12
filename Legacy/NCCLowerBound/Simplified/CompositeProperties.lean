import NCCLowerBound.Simplified.Composite

/-!
# Global certificates for the five-component hard instance

This file packages consequences of the literal construction which are useful
at theorem level: exact dual contraction, a dimension-linear initial-gap
certificate, joint smoothness of the finite-dimensional objective, and the
two-neighbour locality of the memory chain.

The initial-gap argument is made for the *contracted* value function.  This is
important: it is unconditional and does not require the sharp endpoint-ratio
estimate used elsewhere to control the relay correction at the zero dual
vector.
-/

namespace NCCLowerBound
namespace Simplified
namespace CompositeProperties

noncomputable section

open scoped BigOperators
open Set
open InnerRelay
open Composite
open NCCLowerBoundVerification

/-! ## A typed primal value function -/

/-- A primal point, with memory, entrance, and exit blocks kept separate. -/
abbrev PrimalPoint (M : Nat) :=
  (Fin M → ℝ) × ((Fin M → ℝ) × (Fin M → ℝ))

/-- A full saddle point. -/
abbrev SaddlePoint (M N : Nat) :=
  PrimalPoint M × (Fin M → InnerRelay.EVec N)

def primalValue {M : Nat} (K : ℝ) (x : PrimalPoint M) : ℝ :=
  unconstrainedValue K x.1 x.2.1 x.2.2

def primalOrigin (M : Nat) : PrimalPoint M :=
  (0, 0, 0)

def saddleObjective {M N : Nat} (hN : 0 < N) (K : ℝ)
    (z : SaddlePoint M N) : ℝ :=
  hardObjective hN K z.1.1 z.1.2.1 z.1.2.2 z.2

/-! ## Exact maximisation certificates -/

/-- The blockwise Green-kernel point is a maximiser of the whole dual
problem, not merely a point attaining a separately stated formula. -/
theorem blockWStar_isGreatest {M N : Nat} (hN10 : 10 ≤ N)
    (K : ℝ) (s a b : Fin M → ℝ) :
    IsGreatest
      (Set.range (hardObjective (by omega : 0 < N) K s a b))
      (hardObjective (by omega : 0 < N) K s a b
        (blockWStar (by omega : 0 < N) a b)) := by
  rw [hardObjective_at_blockWStar hN10]
  exact unconstrainedValue_isGreatest hN10 K s a b

/-- Exact value of the unconstrained dual supremum, stated without `sSup`
or a choice of a maximiser. -/
theorem dual_maximum_iff {M N : Nat} (hN10 : 10 ≤ N)
    (K : ℝ) (s a b : Fin M → ℝ) (v : ℝ) :
    (v ∈ Set.range (hardObjective (by omega : 0 < N) K s a b) ∧
        ∀ q ∈ Set.range (hardObjective (by omega : 0 < N) K s a b), q ≤ v) ↔
      v = unconstrainedValue K s a b := by
  constructor
  · intro hv
    exact ((unconstrainedValue_isGreatest hN10 K s a b).unique
      ⟨hv.1, hv.2⟩).symm
  · rintro rfl
    exact unconstrainedValue_isGreatest hN10 K s a b

/-! ## Origin and dimension-linear initial gap -/

theorem effectiveLink_nonneg (a b : ℝ) :
    0 ≤ a ^ 2 - a * b + b ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]

@[simp] theorem phaseComponent_origin {M : Nat} (K : ℝ) :
    phaseComponent K (0 : Fin M → ℝ) = 0 := by
  simp [phaseComponent, phasePotential_zero]

@[simp] theorem orderingComponent_origin {M : Nat} :
    orderingComponent (0 : Fin M → ℝ) = 0 := by
  classical
  unfold orderingComponent orderingSummand
  simp [frontierSwitch_zero]

@[simp] theorem entranceComponent_origin {M : Nat} :
    entranceComponent (0 : Fin M → ℝ) (0 : Fin M → ℝ) = 0 := by
  classical
  unfold entranceComponent entranceSummand
  simp [pulseClip_zero]

@[simp] theorem exitComponent_origin {M : Nat} :
    exitComponent (0 : Fin M → ℝ) (0 : Fin M → ℝ) = 0 := by
  classical
  unfold exitComponent exitSummand
  simp [pulseClip_zero]

@[simp] theorem outerComponent_origin {M : Nat} (K : ℝ) :
    outerComponent K (0 : Fin M → ℝ) 0 0 = 0 := by
  simp [outerComponent]

@[simp] theorem unconstrainedValue_origin {M : Nat} (K : ℝ) :
    unconstrainedValue K (0 : Fin M → ℝ) 0 0 = 0 := by
  simp [unconstrainedValue]

@[simp] theorem primalValue_origin {M : Nat} (K : ℝ) :
    primalValue K (primalOrigin M) = 0 := by
  simp [primalValue, primalOrigin]

/-- Every contracted primal value has a lower bound linear in the number of
blocks.  The coefficient is independent of both `M` and the relay dimension
`N`. -/
theorem unconstrainedValue_lower {M : Nat} {K : ℝ} (hK : 0 < K)
    (s a b : Fin M → ℝ) :
    -(M : ℝ) * (154 + |phasePotential K 2|) ≤
      unconstrainedValue K s a b := by
  have hphase := phaseComponent_lower hK s
  have hord := orderingComponent_nonneg s
  have hent : (-88 : ℝ) * M ≤ entranceComponent s a := by
    unfold entranceComponent
    calc
      (-88 : ℝ) * M = ∑ _i : Fin M, (-88 : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
      _ ≤ ∑ i : Fin M, entranceSummand s a i :=
        Finset.sum_le_sum fun i _ ↦ entranceSummand_lower s a i
  have hexit : (-66 : ℝ) * M ≤ exitComponent s b := by
    unfold exitComponent
    calc
      (-66 : ℝ) * M = ∑ _i : Fin M, (-66 : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        ring
      _ ≤ ∑ i : Fin M, exitSummand s b i :=
        Finset.sum_le_sum fun i _ ↦ exitSummand_lower s b i
  have hlinks : 0 ≤ ∑ i : Fin M,
      ((a i) ^ 2 - a i * b i + (b i) ^ 2) :=
    Finset.sum_nonneg fun i _ ↦ effectiveLink_nonneg (a i) (b i)
  have hU : -|phasePotential K 2| ≤ phasePotential K 2 := neg_abs_le _
  have hM : 0 ≤ (M : ℝ) := Nat.cast_nonneg M
  unfold unconstrainedValue outerComponent
  nlinarith

theorem primalValue_bddBelow {M : Nat} {K : ℝ} (hK : 0 < K) :
    BddBelow (Set.range (primalValue (M := M) K)) := by
  refine ⟨-(M : ℝ) * (154 + |phasePotential K 2|), ?_⟩
  rintro _ ⟨x, rfl⟩
  exact unconstrainedValue_lower hK x.1 x.2.1 x.2.2

/-- The actual infimum of the contracted value function. -/
def primalInfimum (M : Nat) (K : ℝ) : ℝ :=
  sInf (Set.range (primalValue (M := M) K))

theorem primalInfimum_lower {M : Nat} {K : ℝ} (hK : 0 < K) :
    -(M : ℝ) * (154 + |phasePotential K 2|) ≤
      primalInfimum M K := by
  rw [primalInfimum, le_csInf_iff (primalValue_bddBelow hK)
    (Set.range_nonempty _)]
  rintro _ ⟨x, rfl⟩
  exact unconstrainedValue_lower hK x.1 x.2.1 x.2.2

theorem primalInfimum_le_zero {M : Nat} {K : ℝ} (hK : 0 < K) :
    primalInfimum M K ≤ 0 := by
  rw [← primalValue_origin (M := M) K]
  exact csInf_le (primalValue_bddBelow hK)
    ⟨primalOrigin M, rfl⟩

/-- Dimension-linear initial gap at the all-zero primal point. -/
theorem origin_gap_le {M : Nat} {K : ℝ} (hK : 0 < K) :
    primalValue K (primalOrigin M) - primalInfimum M K ≤
      (M : ℝ) * (154 + |phasePotential K 2|) := by
  rw [primalValue_origin]
  have h := primalInfimum_lower (M := M) hK
  linarith

/-! ## Joint `C∞` regularity -/

private theorem previousMemory_contDiff {M : Nat} (i : Fin M) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun s : Fin M → ℝ ↦ previousMemory s i) := by
  unfold previousMemory
  split
  · exact contDiff_const
  · exact contDiff_apply ℝ ℝ _

private theorem phaseComponent_contDiff {M : Nat} (K : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (phaseComponent K : (Fin M → ℝ) → ℝ) := by
  unfold phaseComponent
  apply ContDiff.sum
  intro i _
  exact (phasePotential_contDiff K).comp (contDiff_apply ℝ ℝ i)

private theorem orderingComponent_contDiff {M : Nat} :
    ContDiff ℝ (⊤ : ℕ∞) (orderingComponent : (Fin M → ℝ) → ℝ) := by
  unfold orderingComponent
  apply ContDiff.sum
  intro i _
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun s : Fin M → ℝ ↦ s i) :=
    contDiff_apply ℝ ℝ i
  have hp : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : Fin M → ℝ ↦ previousMemory s i) := previousMemory_contDiff i
  change ContDiff ℝ (⊤ : ℕ∞) (fun s : Fin M → ℝ ↦
    24 * frontierSwitch (s i) * (1 - stateClip (previousMemory s i)) *
      (1 - frontierSwitch (previousMemory s i)))
  exact (((contDiff_const.mul (frontierSwitch_contDiff.comp hs)).mul
    (contDiff_const.sub (stateClip_contDiff.comp hp))).mul
      (contDiff_const.sub (frontierSwitch_contDiff.comp hp)))

private theorem primal_state_contDiff {M : Nat} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : PrimalPoint M ↦ x.1) := contDiff_fst

private theorem primal_entrance_contDiff {M : Nat} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : PrimalPoint M ↦ x.2.1) :=
  contDiff_fst.comp contDiff_snd

private theorem primal_exit_contDiff {M : Nat} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : PrimalPoint M ↦ x.2.2) :=
  contDiff_snd.comp contDiff_snd

private theorem primal_state_coord_contDiff {M : Nat} (i : Fin M) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : PrimalPoint M ↦ x.1 i) :=
  (contDiff_apply ℝ ℝ i).comp primal_state_contDiff

private theorem primal_entrance_coord_contDiff {M : Nat} (i : Fin M) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : PrimalPoint M ↦ x.2.1 i) :=
  (contDiff_apply ℝ ℝ i).comp primal_entrance_contDiff

private theorem primal_exit_coord_contDiff {M : Nat} (i : Fin M) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : PrimalPoint M ↦ x.2.2 i) :=
  (contDiff_apply ℝ ℝ i).comp primal_exit_contDiff

private theorem primal_previous_coord_contDiff {M : Nat} (i : Fin M) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : PrimalPoint M ↦ previousMemory x.1 i) :=
  (previousMemory_contDiff i).comp primal_state_contDiff

theorem outerComponent_contDiff {M : Nat} (K : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : PrimalPoint M ↦ outerComponent K x.1 x.2.1 x.2.2) := by
  have hphase : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : PrimalPoint M ↦ phaseComponent K x.1) :=
    (phaseComponent_contDiff K).comp primal_state_contDiff
  have hord : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : PrimalPoint M ↦ orderingComponent x.1) :=
    orderingComponent_contDiff.comp primal_state_contDiff
  have hent : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : PrimalPoint M ↦ entranceComponent x.1 x.2.1) := by
    unfold entranceComponent
    apply ContDiff.sum
    intro i _
    have hs := primal_state_coord_contDiff i
    have hp := primal_previous_coord_contDiff i
    have ha := primal_entrance_coord_contDiff i
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : PrimalPoint M ↦
      -4 * frontierSwitch (previousMemory x.1 i) *
        (1 - frontierSwitch (x.1 i)) * pulseClip (x.2.1 i))
    exact (((contDiff_const.mul (frontierSwitch_contDiff.comp hp)).mul
      (contDiff_const.sub (frontierSwitch_contDiff.comp hs))).mul
        (pulseClip_contDiff.comp ha))
  have hexit : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : PrimalPoint M ↦ exitComponent x.1 x.2.2) := by
    unfold exitComponent
    apply ContDiff.sum
    intro i _
    have hs := primal_state_coord_contDiff i
    have hp := primal_previous_coord_contDiff i
    have hb := primal_exit_coord_contDiff i
    change ContDiff ℝ (⊤ : ℕ∞) (fun x : PrimalPoint M ↦
      -frontierSwitch (previousMemory x.1 i) * stateClip (x.1 i) *
        (1 - frontierSwitch (x.1 i)) * pulseClip (x.2.2 i))
    exact (((((frontierSwitch_contDiff.comp hp).neg).mul
      (stateClip_contDiff.comp hs)).mul
        (contDiff_const.sub (frontierSwitch_contDiff.comp hs))).mul
          (pulseClip_contDiff.comp hb))
  simpa only [outerComponent] using ((hphase.add hord).add hent).add hexit

theorem primalValue_contDiff {M : Nat} (K : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (primalValue (M := M) K) := by
  have houter := outerComponent_contDiff (M := M) K
  have hlinks : ContDiff ℝ (⊤ : ℕ∞) (fun x : PrimalPoint M ↦
      ∑ i : Fin M,
        ((x.2.1 i) ^ 2 - x.2.1 i * x.2.2 i + (x.2.2 i) ^ 2)) := by
    apply ContDiff.sum
    intro i _
    have ha := primal_entrance_coord_contDiff i
    have hb := primal_exit_coord_contDiff i
    exact ((ha.pow 2).sub (ha.mul hb)).add (hb.pow 2)
  exact houter.add hlinks

private theorem vecSq_comp_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : Nat} {w : E → InnerRelay.EVec N}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ vecSq (w x)) := by
  unfold vecSq NCPLVerification.vecSq
  apply ContDiff.sum
  intro i _
  exact ((contDiff_apply ℝ ℝ i).comp hw).pow 2

private theorem pathEnergy_comp_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : Nat} {w : E → InnerRelay.EVec N}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ pathEnergy N (w x)) := by
  cases N with
  | zero => simpa [pathEnergy] using (contDiff_const :
      ContDiff ℝ (⊤ : ℕ∞) (fun _ : E ↦ (0 : ℝ)))
  | succ n =>
      simp only [pathEnergy]
      apply ContDiff.sum
      intro i _
      exact (((contDiff_apply ℝ ℝ i.castSucc).comp hw).sub
        ((contDiff_apply ℝ ℝ i.succ).comp hw)).pow 2

private theorem regularizedPathQuad_comp_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {N : Nat}
    {w : E → InnerRelay.EVec N}
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ regularizedPathQuad N (w x)) := by
  unfold regularizedPathQuad
  exact (contDiff_const.mul (vecSq_comp_contDiff hw)).add
    (pathEnergy_comp_contDiff hw)

private theorem correctedH_comp_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {N : Nat} (hN : 0 < N)
    {a b : E → ℝ} {w : E → InnerRelay.EVec N}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ correctedH hN (a x) (b x) (w x)) := by
  have hwfirst : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ w x (first hN)) :=
    (contDiff_apply ℝ ℝ (first hN)).comp hw
  have hwlast : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ w x (last hN)) :=
    (contDiff_apply ℝ ℝ (last hN)).comp hw
  have hforcing : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ endpointForcing hN (a x) (b x) (w x)) := by
    unfold endpointForcing
    exact (ha.mul hwfirst).sub (hb.mul hwlast)
  have hrelay : ContDiff ℝ (⊤ : ℕ∞)
      (fun x ↦ relayH hN (a x) (b x) (w x)) := by
    unfold relayH
    exact (contDiff_const.mul (regularizedPathQuad_comp_contDiff hw)).add
      (contDiff_const.mul hforcing)
  unfold correctedH
  exact hrelay.add (contDiff_const.mul ((ha.pow 2).add (hb.pow 2)))

/-- The complete saddle objective is jointly `C∞` in all finite-dimensional
primal and dual coordinates. -/
theorem saddleObjective_contDiff {M N : Nat} (hN : 0 < N) (K : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (saddleObjective (M := M) hN K) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : SaddlePoint M N ↦ z.1) := contDiff_fst
  have houter : ContDiff ℝ (⊤ : ℕ∞) (fun z : SaddlePoint M N ↦
      outerComponent K z.1.1 z.1.2.1 z.1.2.2) :=
    (outerComponent_contDiff K).comp hp
  have hinner : ContDiff ℝ (⊤ : ℕ∞) (fun z : SaddlePoint M N ↦
      innerComponent hN z.1.2.1 z.1.2.2 z.2) := by
    unfold innerComponent
    apply ContDiff.sum
    intro i _
    have ha : ContDiff ℝ (⊤ : ℕ∞) (fun z : SaddlePoint M N ↦ z.1.2.1 i) :=
      primal_entrance_coord_contDiff i |>.comp hp
    have hb : ContDiff ℝ (⊤ : ℕ∞) (fun z : SaddlePoint M N ↦ z.1.2.2 i) :=
      primal_exit_coord_contDiff i |>.comp hp
    have hy : ContDiff ℝ (⊤ : ℕ∞) (fun z : SaddlePoint M N ↦ z.2 i) :=
      (contDiff_apply ℝ (InnerRelay.EVec N) i).comp contDiff_snd
    exact correctedH_comp_contDiff hN ha hb hy
  exact houter.add hinner

/-! ## Two-neighbour locality of the chain -/

/-- Two finite vectors agree away from coordinate `j`. -/
def SameExcept {M : Nat} (u v : Fin M → ℝ) (j : Fin M) : Prop :=
  ∀ k, k ≠ j → u k = v k

theorem previousMemory_eq_of_sameExcept {M : Nat} {u v : Fin M → ℝ}
    {j i : Fin M} (huv : SameExcept u v j)
    (hnext : i.val ≠ j.val + 1) :
    previousMemory u i = previousMemory v i := by
  by_cases hi : i.val = 0
  · simp [previousMemory, hi]
  · have hipos : 0 < i.val := Nat.pos_of_ne_zero hi
    rw [previousMemory_succ u i hipos, previousMemory_succ v i hipos]
    apply huv
    intro heq
    have hval : i.val - 1 = j.val := Fin.ext_iff.mp heq
    omega

/-- Changing one memory coordinate can alter an outer summand only in its
own block or the immediately following block.  This bound is independent of
the chain length. -/
theorem outer_summands_two_neighbour_local {M : Nat} {u v : Fin M → ℝ}
    {j i : Fin M} (huv : SameExcept u v j) (hself : i ≠ j)
    (hnext : i.val ≠ j.val + 1) (K : ℝ) (a b : Fin M → ℝ) :
    phasePotential K (u i) = phasePotential K (v i) ∧
      orderingSummand u i = orderingSummand v i ∧
      entranceSummand u a i = entranceSummand v a i ∧
      exitSummand u b i = exitSummand v b i := by
  have hcur := huv i hself
  have hprev := previousMemory_eq_of_sameExcept huv hnext
  simp [orderingSummand, entranceSummand, exitSummand, hcur, hprev]

/-- Entrance-pulse coordinate `a_j` affects only block `j`. -/
theorem entranceSummand_local {M : Nat} (s : Fin M → ℝ)
    {a a' : Fin M → ℝ} {j i : Fin M} (haa' : SameExcept a a' j)
    (hij : i ≠ j) :
    entranceSummand s a i = entranceSummand s a' i := by
  simp [entranceSummand, haa' i hij]

/-- Exit-pulse coordinate `b_j` affects only block `j`. -/
theorem exitSummand_local {M : Nat} (s : Fin M → ℝ)
    {b b' : Fin M → ℝ} {j i : Fin M} (hbb' : SameExcept b b' j)
    (hij : i ≠ j) :
    exitSummand s b i = exitSummand s b' i := by
  simp [exitSummand, hbb' i hij]

end

end CompositeProperties
end Simplified
end NCCLowerBound
