import NCC.Construction.Inner
import NCC.Construction.Outer

/-!
# The literal current hard instance and its constrained value

The objective below is the displayed stage sum in `eq:hard-instance`, on
genuine coordinate vectors of dimensions `3M` and `MN`. Its restricted
value is an actual `ValueOn` of the diameter ball. The equality separating
the outer sum from the constrained inner value is proved by a maximizer,
not postulated. Consequently the phase margins below concern derivatives
of the actual constrained value.
-/

namespace NCC.Construction.Composite

noncomputable section

open scoped BigOperators
open Set
open NCCLowerBoundVerification

abbrev Primal (m : ℕ) := Inner.Vec (m * 3)
abbrev Dual (m n : ℕ) := Inner.Dual m n

def state {m : ℕ} (x : Primal m) (i : Fin m) : ℝ :=
  x (finProdFinEquiv (i, ⟨0, by omega⟩))

def entrance {m : ℕ} (x : Primal m) (i : Fin m) : ℝ :=
  x (finProdFinEquiv (i, ⟨1, by omega⟩))

def exit {m : ℕ} (x : Primal m) (i : Fin m) : ℝ :=
  x (finProdFinEquiv (i, ⟨2, by omega⟩))

def primal {m : ℕ} (s a b : Fin m → ℝ) : Primal m := fun j =>
  let ik := finProdFinEquiv.symm j
  if ik.2.val = 0 then s ik.1 else if ik.2.val = 1 then a ik.1 else b ik.1

@[simp] theorem state_primal {m : ℕ} (s a b : Fin m → ℝ) : state (primal s a b) = s := by
  funext i
  simp [state, primal]

@[simp] theorem entrance_primal {m : ℕ} (s a b : Fin m → ℝ) : entrance (primal s a b) = a := by
  funext i
  simp [entrance, primal]

@[simp] theorem exit_primal {m : ℕ} (s a b : Fin m → ℝ) : exit (primal s a b) = b := by
  funext i
  simp [exit, primal]

def pulsePair {m : ℕ} (a b : Fin m → ℝ) : Inner.Pulse m := fun j =>
  let ik := finProdFinEquiv.symm j
  if ik.2.val = 0 then a ik.1 else b ik.1

def pulse {m : ℕ} (x : Primal m) : Inner.Pulse m := pulsePair (entrance x) (exit x)

@[simp] theorem pulsePair_a {m : ℕ} (a b : Fin m → ℝ) (i : Fin m) :
    pulsePair a b (finProdFinEquiv (i, ⟨0, by omega⟩)) = a i := by
  simp [pulsePair]

@[simp] theorem pulsePair_b {m : ℕ} (a b : Fin m → ℝ) (i : Fin m) :
    pulsePair a b (finProdFinEquiv (i, ⟨1, by omega⟩)) = b i := by
  simp [pulsePair]

@[simp] theorem pulse_primal {m : ℕ} (s a b : Fin m → ℝ) :
    pulse (primal s a b) = pulsePair a b := by
  simp [pulse]

def objective {m n : ℕ} (hn : 0 < n) (x : Primal m) (y : Dual m n) : ℝ :=
  ∑ i : Fin m,
    (Outer.C_en (Outer.previous (state x) i) (entrance x i) (state x i) +
    Inner.H hn (entrance x i) (exit x i) (fun j => y (finProdFinEquiv (i, j))) +
    Outer.C_ex (Outer.previous (state x) i) (exit x i) (state x i) +
    Outer.C_st (Outer.previous (state x) i) (state x i) + R Outer.c_R (state x i))

def value {m n : ℕ} (hn : 0 < n) (D : ℝ) : Primal m → ℝ :=
  ValueOn (Inner.dualBall m n D) (objective hn)

/-- Literal equality of the displayed stage sum with outer plus inner. -/
theorem objective_split {m n : ℕ} (hn : 0 < n) (x : Primal m) (y : Dual m n) :
    objective hn x y = Outer.outerValue (state x) (entrance x) (exit x) +
      Inner.objective hn (pulse x) y := by
  unfold objective Outer.outerValue Inner.objective
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pulse, pulsePair_a, pulsePair_b, Outer.stage, Outer.coupling]
  ring

/-- The already proved unique constrained inner maximizer, for the actual
connector pulse of this primal point. -/
def maximizer {m n : ℕ} (hn : 0 < n) (D : ℝ) (hD : 0 ≤ D) (x : Primal m) : Dual m n :=
  NCCLowerBound.Simplified.InnerFiniteBall.finiteMaximizer hn D hD (pulse x)

theorem inner_maximizer_spec {m n : ℕ} (hn : 0 < n) (D : ℝ) (hD : 0 ≤ D) (x : Primal m) :
    IsMaximizerOn (Inner.dualBall m n D) (Inner.objective hn) (pulse x)
      (maximizer hn D hD x) := by
  rw [Inner.objective_eq_old]
  exact NCCLowerBound.Simplified.InnerFiniteBall.finiteMaximizer_spec hn D hD (pulse x)

theorem maximizer_spec {m n : ℕ} (hn : 0 < n) (D : ℝ) (hD : 0 ≤ D) (x : Primal m) :
    IsMaximizerOn (Inner.dualBall m n D) (objective hn) x (maximizer hn D hD x) := by
  have hi := inner_maximizer_spec hn D hD x
  refine ⟨hi.1, ?_⟩
  intro y hy
  rw [objective_split, objective_split]
  have h := hi.2 y hy
  linarith

/-- Exact separation of the actual constrained supremum. -/
theorem value_split {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D) (x : Primal m) :
    value hn D x = Outer.outerValue (state x) (entrance x) (exit x) +
      Inner.V hn D (pulse x) := by
  rw [show value hn D x = objective hn x (maximizer hn D hD x) from
    value_eq_of_isMaximizerOn (maximizer_spec hn D hD x), objective_split]
  have hi : Inner.V hn D (pulse x) = Inner.objective hn (pulse x) (maximizer hn D hD x) :=
    value_eq_of_isMaximizerOn (inner_maximizer_spec hn D hD x)
  rw [hi]

theorem pulse_contDiff {m : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (pulse : Primal m → Inner.Pulse m) := by
  apply contDiff_pi.2
  intro j
  unfold pulse pulsePair
  dsimp
  split
  · unfold entrance
    fun_prop
  · unfold exit
    fun_prop

theorem outer_flat_contDiff {m : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Primal m => Outer.outerValue (state x) (entrance x) (exit x)) := by
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := q_contDiff
  have hes := e_s_contDiff
  have henu := e_nu_contDiff
  have hr := R_contDiff Outer.c_R
  unfold Outer.outerValue
  apply ContDiff.sum
  intro i _
  have hprev : ContDiff ℝ (⊤ : ℕ∞) (fun x : Primal m => Outer.previous (state x) i) := by
    unfold Outer.previous NCCLowerBound.Simplified.Composite.previousMemory
    split
    · exact contDiff_const
    · unfold state
      fun_prop
  unfold Outer.stage Outer.coupling Outer.C_en Outer.C_ex Outer.C_st
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : Primal m => state x i) := by unfold state; fun_prop
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun x : Primal m => entrance x i) := by unfold entrance; fun_prop
  have hb : ContDiff ℝ (⊤ : ℕ∞) (fun x : Primal m => exit x i) := by unfold exit; fun_prop
  fun_prop

/-- Full Fréchet differentiability of the actual constrained value. -/
theorem value_differentiable {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D) :
    Differentiable ℝ (value (m := m) hn D) := by
  have heq : value (m := m) hn D = fun x =>
      Outer.outerValue (state x) (entrance x) (exit x) + Inner.V hn D (pulse x) := by
    funext x
    exact value_split hn hD x
  rw [heq]
  exact (outer_flat_contDiff.differentiable (by simp)).add
    ((Inner.V_differentiable hn hD).comp (pulse_contDiff.differentiable (by simp)))

def stateCoordinateValue {m n : ℕ} (hn : 0 < n) (D : ℝ)
    (s a b : Fin m → ℝ) (i : Fin m) (t : ℝ) : ℝ :=
  value hn D (primal (Outer.stateLine s i t) a b)

theorem stateCoordinateValue_split {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) (i : Fin m) :
    stateCoordinateValue hn D s a b i =
      fun t => Outer.coordinateValue s a b i t + Inner.V hn D (pulsePair a b) := by
  funext t
  unfold stateCoordinateValue
  rw [value_split hn hD]
  simp only [state_primal, entrance_primal, exit_primal, pulse_primal, Outer.coordinateValue]

/-- The genuine derivative of the constrained value along a state coordinate. -/
theorem stateCoordinateValue_hasDerivAt {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (stateCoordinateValue hn D s a b i)
      (Outer.incoming (Outer.previous s i) (a i) (b i) (s i) + deriv (R Outer.c_R) (s i) +
        Outer.nextContribution s a b i) (s i) := by
  rw [stateCoordinateValue_split hn hD]
  exact (Outer.coordinateValue_hasDerivAt s a b i).add_const _

theorem state_derivative_eq_outer {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) (i : Fin m) :
    deriv (stateCoordinateValue hn D s a b i) (s i) =
      deriv (Outer.coordinateValue s a b i) (s i) := by
  rw [(stateCoordinateValue_hasDerivAt hn hD s a b i).deriv,
    (Outer.coordinateValue_hasDerivAt s a b i).deriv]

/-- The unit coordinate direction of state `s_i` in the `3M`-vector. -/
def stateDirection {m : ℕ} (i : Fin m) : Primal m := primal (Pi.single i 1) 0 0

theorem primal_stateLine_hasDerivAt {m : ℕ} (s a b : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (fun t => primal (Outer.stateLine s i t) a b) (stateDirection i) (s i) := by
  apply hasDerivAt_pi.2
  intro j
  obtain ⟨⟨r, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  fin_cases k
  · by_cases hri : r = i
    · simpa [stateDirection, primal, Outer.stateLine, Pi.single_apply, hri] using
        ((hasDerivAt_id (s i)).smul_const (1 : ℝ))
    · simpa [stateDirection, primal, Outer.stateLine, Pi.single_apply, hri] using
        (hasDerivAt_const (s i) (s r))
  · simpa [stateDirection, primal] using (hasDerivAt_const (s i) (a r))
  · simpa [stateDirection, primal] using (hasDerivAt_const (s i) (b r))

theorem stateLine_self {m : ℕ} (s : Fin m → ℝ) (i : Fin m) :
    Outer.stateLine s i (s i) = s := by
  funext j
  by_cases hj : j = i <;> simp [Outer.stateLine, hj]

/-- The scalar coordinate derivative is the actual Fréchet derivative
applied to the corresponding coordinate direction. -/
theorem state_fderiv_eq_deriv {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) (i : Fin m) :
    (fderiv ℝ (value hn D) (primal s a b)) (stateDirection i) =
      deriv (stateCoordinateValue hn D s a b i) (s i) := by
  have hval := (value_differentiable hn hD (primal s a b)).hasFDerivAt
  have hline := primal_stateLine_hasDerivAt s a b i
  have hcomp := hval.comp_hasDerivAt_of_eq (s i) hline
    (by rw [stateLine_self])
  exact hcomp.deriv.symm

/-- `lem:phase-margins` (i), for the actual finite-ball value. -/
theorem phase_left {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) (i : Fin m) (hi : s i ≤ -(1 / 10)) :
    deriv (stateCoordinateValue hn D s a b i) (s i) ≤ -1 := by
  rw [state_derivative_eq_outer hn hD]
  exact Outer.outer_phase_left s a b i hi

/-- `lem:phase-margins` (ii), for the actual finite-ball value. -/
theorem phase_transition {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) (i : Fin m) (hi0 : 1 / 5 < s i) (hi1 : s i < 1) :
    deriv (stateCoordinateValue hn D s a b i) (s i) ≤ -1 := by
  rw [state_derivative_eq_outer hn hD]
  exact Outer.outer_phase_transition s a b i hi0 hi1

/-- `lem:phase-margins` (iii), with zero-based predecessor index `i`. -/
theorem phase_out_of_order {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) (i : Fin m) (hinext : i.val + 1 < m)
    (hi0 : -(1 / 10) < s i) (hi1 : s i ≤ 1 / 5) (hnext : 1 ≤ s ⟨i.val + 1, hinext⟩) :
    deriv (stateCoordinateValue hn D s a b i) (s i) ≤ -1 := by
  rw [state_derivative_eq_outer hn hD]
  exact Outer.outer_phase_out_of_order s a b i hinext hi0 hi1 hnext

theorem phase_left_fderiv {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) (i : Fin m) (hi : s i ≤ -(1 / 10)) :
    (fderiv ℝ (value hn D) (primal s a b)) (stateDirection i) ≤ -1 := by
  rw [state_fderiv_eq_deriv hn hD]
  exact phase_left hn hD s a b i hi

theorem phase_transition_fderiv {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) (i : Fin m) (hi0 : 1 / 5 < s i) (hi1 : s i < 1) :
    (fderiv ℝ (value hn D) (primal s a b)) (stateDirection i) ≤ -1 := by
  rw [state_fderiv_eq_deriv hn hD]
  exact phase_transition hn hD s a b i hi0 hi1

theorem phase_out_of_order_fderiv {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) (i : Fin m) (hinext : i.val + 1 < m)
    (hi0 : -(1 / 10) < s i) (hi1 : s i ≤ 1 / 5) (hnext : 1 ≤ s ⟨i.val + 1, hinext⟩) :
    (fderiv ℝ (value hn D) (primal s a b)) (stateDirection i) ≤ -1 := by
  rw [state_fderiv_eq_deriv hn hD]
  exact phase_out_of_order hn hD s a b i hinext hi0 hi1 hnext

@[simp] theorem state_zero (m : ℕ) : state (0 : Primal m) = 0 := rfl
@[simp] theorem entrance_zero (m : ℕ) : entrance (0 : Primal m) = 0 := rfl
@[simp] theorem exit_zero (m : ℕ) : exit (0 : Primal m) = 0 := rfl

@[simp] theorem pulse_zero (m : ℕ) : pulse (0 : Primal m) = 0 := by
  funext j
  simp [pulse, pulsePair, entrance, exit]

theorem outerValue_zero (m : ℕ) : Outer.outerValue (0 : Fin m → ℝ) 0 0 = 0 := by
  have hq : q 0 = 0 := q_eq_zero (by norm_num)
  have he : e_nu 0 = 0 := e_nu_eq_self (by norm_num)
  simp [Outer.outerValue, Outer.stage, Outer.coupling, Outer.C_en, Outer.C_ex, Outer.C_st,
    hq, he, R_zero]

theorem inner_zero_zero {m n : ℕ} (hn : 0 < n) :
    Inner.objective (blocks := m) hn 0 0 = 0 := by
  unfold Inner.objective
  apply Finset.sum_eq_zero
  intro i _
  change Inner.H hn 0 0 0 = 0
  rw [Inner.H_eq_old, NCCLowerBound.Simplified.InnerRelay.correctedH_zero_dual]
  ring

theorem inner_origin_nonpos {m n : ℕ} (hn : 0 < n) (y : Dual m n) :
    Inner.objective hn 0 y ≤ 0 := by
  unfold Inner.objective
  apply Finset.sum_nonpos
  intro i _
  change Inner.H hn 0 0 _ ≤ 0
  rw [Inner.H_eq_old]
  exact NCCLowerBound.Simplified.InnerRelay.correctedH_zero_primal_nonpos hn _

theorem zero_mem_dualBall (m n : ℕ) (D : ℝ) : (0 : Dual m n) ∈ Inner.dualBall m n D := by
  change vecSq (0 : Dual m n) ≤ (D / 2) ^ 2
  simp only [vecSq, NCPLVerification.vecSq, Pi.zero_apply, zero_pow (by norm_num : 2 ≠ 0),
    Finset.sum_const_zero]
  positivity

theorem objective_origin_zero {m n : ℕ} (hn : 0 < n) : objective (m := m) hn 0 0 = 0 := by
  rw [objective_split, state_zero, entrance_zero, exit_zero, pulse_zero,
    outerValue_zero, inner_zero_zero, zero_add]

/-- The primal origin has exactly zero constrained value. -/
theorem value_origin {m n : ℕ} (hn : 0 < n) (D : ℝ) : value (m := m) hn D 0 = 0 := by
  have hs : IsMaximizerOn (Inner.dualBall m n D) (objective hn) 0 0 := by
    refine ⟨zero_mem_dualBall m n D, ?_⟩
    intro y _
    rw [objective_origin_zero, objective_split, state_zero, entrance_zero,
      exit_zero, pulse_zero, outerValue_zero, zero_add]
    exact inner_origin_nonpos hn y
  rw [show value hn D (0 : Primal m) = objective hn 0 0 from value_eq_of_isMaximizerOn hs,
    objective_origin_zero]

theorem state_coupling_nonneg (u v : ℝ) : 0 ≤ Outer.C_st u v := by
  by_cases hu : 1 ≤ u
  · simp [Outer.C_st, q_eq_one hu]
  · have heu : e_s u ≤ e_s 1 := by
      rw [e_s_eq_identityExtension]
      exact identityExtension_monotone (by norm_num : (0 : ℝ) ≤ 2) (le_of_not_ge hu)
    rw [e_s_eq_self (by norm_num : |(1 : ℝ)| ≤ 2)] at heu
    unfold Outer.C_st
    have hqv := (q_mem v).1
    have hqu := (q_mem u).2
    positivity

private theorem q_abs_le_one (t : ℝ) : |q t| ≤ 1 := by
  rw [abs_of_nonneg (q_mem t).1]
  exact (q_mem t).2

private theorem one_sub_q_abs_le_one (t : ℝ) : |1 - q t| ≤ 1 := by
  rw [abs_of_nonneg (by linarith [(q_mem t).2])]
  linarith [(q_mem t).1]

theorem entrance_coupling_lower (u a v : ℝ) : -86 ≤ Outer.C_en u a v := by
  have hqu := q_abs_le_one u
  have hqv := one_sub_q_abs_le_one v
  have hea := e_nu_abs_le a
  have h : |Outer.C_en u a v| ≤ 86 := by
    unfold Outer.C_en
    rw [abs_mul, abs_mul, abs_mul]
    norm_num
    calc
      _ ≤ 4 * 1 * 1 * (43 / 2 : ℝ) := by gcongr
      _ = 86 := by ring
  exact (abs_le.mp h).1

theorem exit_coupling_lower (u b v : ℝ) : -(215 / 4) ≤ Outer.C_ex u b v := by
  have hqu := q_abs_le_one u
  have hqv := one_sub_q_abs_le_one v
  have hes := e_s_abs_le v
  have heb := e_nu_abs_le b
  have h : |Outer.C_ex u b v| ≤ 215 / 4 := by
    unfold Outer.C_ex
    rw [abs_mul, abs_mul, abs_mul, abs_neg]
    calc
      _ ≤ 1 * (5 / 2 : ℝ) * 1 * (43 / 2 : ℝ) := by gcongr
      _ = 215 / 4 := by ring
  exact (abs_le.mp h).1

/-- The precise numerical constant in `prop:initial-gap`. -/
def c_Δ : ℝ := (9 / 10) * (Outer.c_R + 1) + 86 + 215 / 4

theorem c_Δ_pos : 0 < c_Δ := by
  unfold c_Δ
  linarith [Outer.c_R_ge_twenty_five]

theorem stage_lower (u a b v : ℝ) : -c_Δ ≤ Outer.stage Outer.c_R u a b v := by
  have hen := entrance_coupling_lower u a v
  have hex := exit_coupling_lower u b v
  have hst := state_coupling_nonneg u v
  have hr := R_lower_bound (by linarith [Outer.c_R_ge_twenty_five] : -1 ≤ Outer.c_R) v
  unfold Outer.stage Outer.coupling c_Δ
  linarith

theorem outerValue_lower {m : ℕ} (s a b : Fin m → ℝ) :
    -c_Δ * (m : ℝ) ≤ Outer.outerValue s a b := by
  calc
    -c_Δ * (m : ℝ) = ∑ _i : Fin m, -c_Δ := by simp; ring
    _ ≤ Outer.outerValue s a b :=
      Finset.sum_le_sum (fun i _ => stage_lower (Outer.previous s i) (a i) (b i) (s i))

theorem inner_zero_nonneg {m n : ℕ} (hn : 10 ≤ n) (p : Inner.Pulse m) :
    0 ≤ Inner.objective (by omega : 0 < n) p 0 := by
  unfold Inner.objective
  apply Finset.sum_nonneg
  intro i _
  exact (Inner.H_origin_signs hn _ _ 0).1

theorem objective_zero_lower {m n : ℕ} (hn : 10 ≤ n) (x : Primal m) :
    -c_Δ * (m : ℝ) ≤ objective (by omega : 0 < n) x 0 := by
  rw [objective_split]
  have ho := outerValue_lower (state x) (entrance x) (exit x)
  have hi := inner_zero_nonneg hn (pulse x)
  linarith

theorem objective_zero_le_value {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (x : Primal m) : objective hn x 0 ≤ value hn D x := by
  have hmax := maximizer_spec hn D hD x
  rw [show value hn D x = objective hn x (maximizer hn D hD x) from
    value_eq_of_isMaximizerOn hmax]
  exact hmax.2 0 (zero_mem_dualBall m n D)

/-- Uniform global lower bound on the actual restricted value. -/
theorem value_lower {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D) (x : Primal m) :
    -c_Δ * (m : ℝ) ≤ value (by omega : 0 < n) D x :=
  (objective_zero_lower hn x).trans (objective_zero_le_value (by omega) hD x)

theorem value_bddBelow {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D) :
    BddBelow (Set.range (value (m := m) (by omega : 0 < n) D)) := by
  refine ⟨-c_Δ * (m : ℝ), ?_⟩
  rintro _ ⟨x, rfl⟩
  exact value_lower hn hD x

/-- `prop:initial-gap`, with a literal infimum of the genuine value. -/
theorem initial_gap {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D) :
    value (m := m) (by omega : 0 < n) D 0 -
      sInf (Set.range (value (m := m) (by omega : 0 < n) D)) ≤ c_Δ * (m : ℝ) := by
  rw [value_origin]
  have hlower : -c_Δ * (m : ℝ) ≤
      sInf (Set.range (value (m := m) (by omega : 0 < n) D)) := by
    apply le_csInf (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    exact value_lower hn hD x
  linarith

end

end NCC.Construction.Composite
