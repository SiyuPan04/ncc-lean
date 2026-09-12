import NCCLowerBound.Simplified.InnerRelay
import NCCLowerBound.Simplified.PhasePotential

/-!
# The five-component hard instance

This file is the literal finite-sum construction in lines 986--1118 of
`NC_C_Lower_Bound_simplified.tex`.  Memory, entrance, exit, and dual-block
coordinates are kept as separate finite functions; this makes every indexing
convention (especially the fixed seed `s₀ = 1`) explicit in the type.
-/

namespace NCCLowerBound
namespace Simplified
namespace Composite

noncomputable section

open scoped BigOperators
open InnerRelay

/-- The manuscript's fixed seed `s₀ = 1`, followed by the stored memories. -/
def previousMemory {M : Nat} (s : Fin M → ℝ) (i : Fin M) : ℝ :=
  if h : i.val = 0 then 1 else s ⟨i.val - 1, by omega⟩

@[simp] theorem previousMemory_first {M : Nat} (s : Fin M → ℝ)
    (i : Fin M) (hi : i.val = 0) : previousMemory s i = 1 := by
  simp [previousMemory, hi]

theorem previousMemory_succ {M : Nat} (s : Fin M → ℝ)
    (i : Fin M) (hi : 0 < i.val) :
    previousMemory s i = s ⟨i.val - 1, by omega⟩ := by
  simp [previousMemory, Nat.ne_of_gt hi]

/-- `f_ph`. -/
def phaseComponent {M : Nat} (K : ℝ) (s : Fin M → ℝ) : ℝ :=
  ∑ i : Fin M, phasePotential K (s i)

/-- One summand of `f_ord`. -/
def orderingSummand {M : Nat} (s : Fin M → ℝ) (i : Fin M) : ℝ :=
  24 * frontierSwitch (s i) *
    (1 - stateClip (previousMemory s i)) *
    (1 - frontierSwitch (previousMemory s i))

/-- `f_ord`. -/
def orderingComponent {M : Nat} (s : Fin M → ℝ) : ℝ :=
  ∑ i : Fin M, orderingSummand s i

/-- One summand of `f_ent`. -/
def entranceSummand {M : Nat} (s : Fin M → ℝ)
    (a : Fin M → ℝ) (i : Fin M) : ℝ :=
  -4 * frontierSwitch (previousMemory s i) *
    (1 - frontierSwitch (s i)) * pulseClip (a i)

/-- `f_ent`. -/
def entranceComponent {M : Nat} (s : Fin M → ℝ)
    (a : Fin M → ℝ) : ℝ :=
  ∑ i : Fin M, entranceSummand s a i

/-- One summand of `f_exit`. -/
def exitSummand {M : Nat} (s : Fin M → ℝ)
    (b : Fin M → ℝ) (i : Fin M) : ℝ :=
  -frontierSwitch (previousMemory s i) * stateClip (s i) *
    (1 - frontierSwitch (s i)) * pulseClip (b i)

/-- `f_exit`. -/
def exitComponent {M : Nat} (s : Fin M → ℝ)
    (b : Fin M → ℝ) : ℝ :=
  ∑ i : Fin M, exitSummand s b i

/-- The four purely primal outer components. -/
def outerComponent {M : Nat} (K : ℝ) (s a b : Fin M → ℝ) : ℝ :=
  phaseComponent K s + orderingComponent s + entranceComponent s a +
    exitComponent s b

/-- The boxed saddle objective `fbar`. -/
def hardObjective {M N : Nat} (hN : 0 < N) (K : ℝ)
    (s a b : Fin M → ℝ) (y : Fin M → EVec N) : ℝ :=
  outerComponent K s a b + innerComponent hN a b y

/-- The explicit unconstrained value after contracting every dual relay. -/
def unconstrainedValue {M : Nat} (K : ℝ)
    (s a b : Fin M → ℝ) : ℝ :=
  outerComponent K s a b +
    ∑ i : Fin M, ((a i) ^ 2 - a i * b i + (b i) ^ 2)

/-! ## Exact contraction of the dual blocks -/

theorem hardObjective_le_unconstrainedValue {M N : Nat} (hN10 : 10 ≤ N)
    (K : ℝ) (s a b : Fin M → ℝ) (y : Fin M → EVec N) :
    hardObjective (by omega : 0 < N) K s a b y ≤
      unconstrainedValue K s a b := by
  have hmax := innerComponent_le_at_blockWStar (by omega : 0 < N) a b y
  rw [innerComponent_blockWStar_value hN10 a b] at hmax
  simpa [hardObjective, unconstrainedValue] using
    add_le_add_left hmax (outerComponent K s a b)

theorem hardObjective_at_blockWStar {M N : Nat} (hN10 : 10 ≤ N)
    (K : ℝ) (s a b : Fin M → ℝ) :
    hardObjective (by omega : 0 < N) K s a b
        (blockWStar (by omega : 0 < N) a b) =
      unconstrainedValue K s a b := by
  rw [hardObjective, unconstrainedValue,
    innerComponent_blockWStar_value hN10]

/-- A choice-free formulation of equation (unconstrained-value): the displayed
value is the greatest element of the range over all dual vectors. -/
theorem unconstrainedValue_isGreatest {M N : Nat} (hN10 : 10 ≤ N)
    (K : ℝ) (s a b : Fin M → ℝ) :
    IsGreatest
      (Set.range (hardObjective (by omega : 0 < N) K s a b))
      (unconstrainedValue K s a b) := by
  constructor
  · exact ⟨blockWStar (by omega : 0 < N) a b,
      hardObjective_at_blockWStar hN10 K s a b⟩
  · rintro _ ⟨y, rfl⟩
    exact hardObjective_le_unconstrainedValue hN10 K s a b y

/-! ## Sign and gap estimates used at initialization -/

theorem one_sub_stateClip_mul_one_sub_switch_nonneg (t : ℝ) :
    0 ≤ (1 - stateClip t) * (1 - frontierSwitch t) := by
  rcases frontierSwitch_mem_unitInterval t with ⟨hA0, hA1⟩
  by_cases hC : stateClip t ≤ 1
  · exact mul_nonneg (sub_nonneg.mpr hC) (sub_nonneg.mpr hA1)
  · have hC1 : 1 ≤ stateClip t := le_of_not_ge hC
    have harg : (1 : ℝ) ≤ (5 * stateClip t - 1) / 4 := by linarith
    have hA : frontierSwitch t = 1 := by
      exact NCCLowerBoundVerification.Lambda1_eq_one_of_one_le harg
    simp [hA]

theorem orderingSummand_nonneg {M : Nat} (s : Fin M → ℝ) (i : Fin M) :
    0 ≤ orderingSummand s i := by
  have hA := (frontierSwitch_mem_unitInterval (s i)).1
  have htail := one_sub_stateClip_mul_one_sub_switch_nonneg
    (previousMemory s i)
  unfold orderingSummand
  simpa [mul_assoc] using
    mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 24) hA) htail

theorem orderingComponent_nonneg {M : Nat} (s : Fin M → ℝ) :
    0 ≤ orderingComponent s := by
  unfold orderingComponent
  exact Finset.sum_nonneg fun i _ ↦ orderingSummand_nonneg s i

theorem entranceSummand_lower {M : Nat} (s : Fin M → ℝ)
    (a : Fin M → ℝ) (i : Fin M) :
    (-88 : ℝ) ≤ entranceSummand s a i := by
  rcases frontierSwitch_mem_unitInterval (previousMemory s i) with ⟨hp0, hp1⟩
  rcases frontierSwitch_mem_unitInterval (s i) with ⟨hc0, hc1⟩
  have hP := pulseClip_abs_le_twentyTwo (a i)
  rw [abs_le] at hP
  unfold entranceSummand
  have hone : 0 ≤ 1 - frontierSwitch (s i) := sub_nonneg.mpr hc1
  have hprod0 : 0 ≤ frontierSwitch (previousMemory s i) *
      (1 - frontierSwitch (s i)) := mul_nonneg hp0 hone
  have hprod1 : frontierSwitch (previousMemory s i) *
      (1 - frontierSwitch (s i)) ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hP.2 hprod0,
    mul_le_mul_of_nonpos_left hP.1 (by linarith :
      (-4 : ℝ) * (frontierSwitch (previousMemory s i) *
        (1 - frontierSwitch (s i))) ≤ 0)]

theorem exitSummand_lower {M : Nat} (s : Fin M → ℝ)
    (b : Fin M → ℝ) (i : Fin M) :
    (-66 : ℝ) ≤ exitSummand s b i := by
  rcases frontierSwitch_mem_unitInterval (previousMemory s i) with ⟨hp0, hp1⟩
  rcases frontierSwitch_mem_unitInterval (s i) with ⟨hc0, hc1⟩
  have hC := stateClip_abs_le_three (s i)
  have hP := pulseClip_abs_le_twentyTwo (b i)
  have hfront : |frontierSwitch (previousMemory s i)| ≤ 1 := by
    rw [abs_of_nonneg hp0]
    exact hp1
  have htail : |1 - frontierSwitch (s i)| ≤ 1 := by
    rw [abs_of_nonneg (sub_nonneg.mpr hc1)]
    linarith
  have habs : |exitSummand s b i| ≤ 66 := by
    unfold exitSummand
    rw [abs_mul, abs_mul, abs_mul, abs_neg]
    calc
      |frontierSwitch (previousMemory s i)| * |stateClip (s i)| *
          |1 - frontierSwitch (s i)| * |pulseClip (b i)|
          ≤ 1 * 3 * 1 * 22 := by gcongr
      _ = 66 := by norm_num
  exact (abs_le.mp habs).1

theorem phaseComponent_lower {M : Nat} {K : ℝ} (hK : 0 < K)
    (s : Fin M → ℝ) :
    (M : ℝ) * phasePotential K 2 ≤ phaseComponent K s := by
  unfold phaseComponent
  calc
    (M : ℝ) * phasePotential K 2 =
        ∑ _i : Fin M, phasePotential K 2 := by simp
    _ ≤ ∑ i : Fin M, phasePotential K (s i) :=
      Finset.sum_le_sum fun i _ ↦ phasePotential_lower_bound hK (s i)

/-- A dimension-linear lower bound for the primal value, hence the initial
gap certificate once the feasible dual origin is substituted. -/
theorem hardObjective_at_zeroDual_lower {M N : Nat} (hN10 : 10 ≤ N)
    {K : ℝ} (hK : 0 < K) (s a b : Fin M → ℝ) :
    -(M : ℝ) * (154 + |phasePotential K 2|) ≤
      hardObjective (by omega : 0 < N) K s a b (fun _ _ ↦ 0) := by
  have hphase := phaseComponent_lower hK s
  have hord := orderingComponent_nonneg s
  have hent : (-88 : ℝ) * M ≤ entranceComponent s a := by
    unfold entranceComponent
    calc
      (-88 : ℝ) * M = ∑ _i : Fin M, (-88 : ℝ) := by simp; ring
      _ ≤ ∑ i : Fin M, entranceSummand s a i :=
        Finset.sum_le_sum fun i _ ↦ entranceSummand_lower s a i
  have hexit : (-66 : ℝ) * M ≤ exitComponent s b := by
    unfold exitComponent
    calc
      (-66 : ℝ) * M = ∑ _i : Fin M, (-66 : ℝ) := by simp; ring
      _ ≤ ∑ i : Fin M, exitSummand s b i :=
        Finset.sum_le_sum fun i _ ↦ exitSummand_lower s b i
  have hinner : 0 ≤ innerComponent (by omega : 0 < N) a b (fun _ _ ↦ 0) := by
    unfold innerComponent
    exact Finset.sum_nonneg fun i _ ↦
      correctedH_zero_dual_nonneg_of_ten hN10 (a i) (b i)
  have hU : -|phasePotential K 2| ≤ phasePotential K 2 := neg_abs_le _
  unfold hardObjective outerComponent
  nlinarith

@[simp] theorem previousMemory_zero {M : Nat} (i : Fin M) :
    previousMemory (fun _ ↦ 0) i = if i.val = 0 then 1 else 0 := by
  unfold previousMemory
  split <;> simp_all

theorem hardObjective_origin {M N : Nat} (hN : 0 < N) (K : ℝ) :
    hardObjective hN K (fun _ : Fin M ↦ 0) (fun _ ↦ 0) (fun _ ↦ 0)
      (fun _ _ ↦ 0) = 0 := by
  classical
  have hinner0 :
      correctedH hN 0 0 (fun _ : Fin N ↦ 0) = 0 := by
    rw [show (fun _ : Fin N ↦ (0 : ℝ)) = (0 : EVec N) from rfl,
      correctedH_zero_dual]
    ring
  unfold hardObjective outerComponent phaseComponent orderingComponent
    entranceComponent exitComponent innerComponent orderingSummand
    entranceSummand exitSummand
  simp [phasePotential_zero, previousMemory, frontierSwitch_zero,
    stateClip_zero, pulseClip_zero, hinner0]

end

end Composite
end Simplified
end NCCLowerBound
