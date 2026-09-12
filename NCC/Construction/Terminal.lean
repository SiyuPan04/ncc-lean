import NCC.Construction.Frontier

/-!
# Actual finite-ball terminal-gradient obstruction

The radius restriction is shown locally inactive using the exact inner
maximizer and the strict connector bound proved for the constrained value.
The remaining derivatives use the current scalar potential `R`, never an
identification with a predecessor manuscript's potential.
-/

namespace NCC.Construction.Terminal

noncomputable section

open scoped BigOperators
open NCCLowerBoundVerification Set Filter
open Composite Frontier

def c_y : ℝ := 20 * Real.sqrt 20
def c_D : ℝ := 1 / (40 * c_y)
def g₀ : ℝ := 1 / 4

theorem c_y_pos : 0 < c_y := by unfold c_y; positivity
theorem c_D_pos : 0 < c_D := by
  unfold c_D
  exact one_div_pos.mpr (mul_pos (by norm_num) c_y_pos)
theorem c_y_sq : c_y ^ 2 = 8000 := by
  unfold c_y
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 20)]
  norm_num

def pA {m : ℕ} (p : Inner.Pulse m) (i : Fin m) : ℝ :=
  p (finProdFinEquiv (i, ⟨0, by omega⟩))

def pB {m : ℕ} (p : Inner.Pulse m) (i : Fin m) : ℝ :=
  p (finProdFinEquiv (i, ⟨1, by omega⟩))

@[simp] theorem pA_pair {m : ℕ} (a b : Fin m → ℝ) : pA (pulsePair a b) = a := by
  funext i
  exact pulsePair_a a b i

@[simp] theorem pB_pair {m : ℕ} (a b : Fin m → ℝ) : pB (pulsePair a b) = b := by
  funext i
  exact pulsePair_b a b i

theorem pulse_vecSq {m : ℕ} (p : Inner.Pulse m) :
    vecSq p = ∑ i : Fin m, ((pA p i) ^ 2 + (pB p i) ^ 2) :=
  NCCLowerBound.Simplified.InnerFiniteBall.vecSq_pulse p

def innerExplicit {m : ℕ} (p : Inner.Pulse m) : ℝ :=
  ∑ i : Fin m, Inner.Q (pA p i) (pB p i)

def freeMaximizer {m n : ℕ} (hn : 0 < n) (p : Inner.Pulse m) : Inner.Dual m n :=
  fun k => let ij := finProdFinEquiv.symm k
    Inner.maximizer hn (pA p ij.1) (pB p ij.1) ij.2

theorem freeMaximizer_growth {m n : ℕ} (hn : 10 ≤ n) (p : Inner.Pulse m) :
    vecSq (freeMaximizer (by omega : 0 < n) p) ≤ 8000 * (n : ℝ) ^ 2 * vecSq p := by
  have heq : vecSq (freeMaximizer (by omega : 0 < n) p) =
      ∑ i : Fin m, vecSq (Inner.maximizer (by omega : 0 < n) (pA p i) (pB p i)) := by
    unfold vecSq NCPLVerification.vecSq
    rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
    simp [freeMaximizer]
  rw [heq, pulse_vecSq, Finset.mul_sum]
  exact Finset.sum_le_sum (fun i _ => Inner.maximizer_growth_squared hn (pA p i) (pB p i))

theorem freeMaximizer_value {m n : ℕ} (hn : 10 ≤ n) (p : Inner.Pulse m) :
    Inner.objective (by omega : 0 < n) p (freeMaximizer (by omega) p) = innerExplicit p := by
  unfold Inner.objective innerExplicit
  apply Finset.sum_congr rfl
  intro i _
  simpa [freeMaximizer, pA, pB] using Inner.H_maximum_value hn (pA p i) (pB p i)

theorem freeMaximizer_maximal {m n : ℕ} (hn : 0 < n) (p : Inner.Pulse m)
    (y : Inner.Dual m n) :
    Inner.objective hn p y ≤ Inner.objective hn p (freeMaximizer hn p) := by
  unfold Inner.objective
  apply Finset.sum_le_sum
  intro i _
  simpa [freeMaximizer, pA, pB] using
    Inner.H_maximum hn (pA p i) (pB p i) (fun k => y (finProdFinEquiv (i, k)))

def inactiveRegion (m n : ℕ) (D : ℝ) : Set (Inner.Pulse m) :=
  {p | 8000 * (n : ℝ) ^ 2 * vecSq p < (D / 2) ^ 2}

theorem inactiveRegion_open (m n : ℕ) (D : ℝ) : IsOpen (inactiveRegion m n D) := by
  apply isOpen_lt
  · unfold vecSq NCPLVerification.vecSq
    fun_prop
  · fun_prop

theorem inactive_of_connector_bound {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 < D)
    (hsize : (n : ℝ) ≤ c_D * D) (p : Inner.Pulse m) (hp : Inner.norm₂ p < 20) :
    p ∈ inactiveRegion m n D := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < 40 * c_y := mul_pos (by norm_num) c_y_pos
  have hnD : (n : ℝ) ≤ D / (40 * c_y) := by
    simpa only [c_D, one_div, div_eq_mul_inv, mul_comm, one_mul] using hsize
  have hproduct := (le_div_iff₀ hden).mp hnD
  have hbound : c_y * (n : ℝ) * 20 ≤ D / 2 := by nlinarith
  have hstrict : c_y * (n : ℝ) * Inner.norm₂ p < D / 2 :=
    (mul_lt_mul_of_pos_left hp (mul_pos c_y_pos hnpos)).trans_le hbound
  have hsq : (c_y * (n : ℝ) * Inner.norm₂ p) ^ 2 < (D / 2) ^ 2 :=
    (sq_lt_sq₀ (mul_nonneg (mul_nonneg c_y_pos.le hnpos.le) (norm₂_nonneg p))
      (by positivity)).mpr hstrict
  change 8000 * (n : ℝ) ^ 2 * vecSq p < (D / 2) ^ 2
  simpa only [mul_pow, c_y_sq, norm₂_sq] using hsq

theorem freeMaximizer_feasible {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} {p : Inner.Pulse m}
    (hp : p ∈ inactiveRegion m n D) :
    freeMaximizer (by omega : 0 < n) p ∈ Inner.dualBall m n D :=
  (freeMaximizer_growth hn p).trans hp.le

theorem inner_value_eq_explicit {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} {p : Inner.Pulse m}
    (hp : p ∈ inactiveRegion m n D) : Inner.V (by omega : 0 < n) D p = innerExplicit p := by
  have hm : IsMaximizerOn (Inner.dualBall m n D) (Inner.objective (by omega : 0 < n)) p
      (freeMaximizer (by omega) p) :=
    ⟨freeMaximizer_feasible hn hp, fun y _ => freeMaximizer_maximal (by omega) p y⟩
  exact (value_eq_of_isMaximizerOn hm).trans (freeMaximizer_value hn p)

theorem inner_eventuallyEq_explicit {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} {p : Inner.Pulse m}
    (hp : p ∈ inactiveRegion m n D) :
    Inner.V (by omega : 0 < n) D =ᶠ[nhds p] innerExplicit := by
  filter_upwards [(inactiveRegion_open m n D).mem_nhds hp] with r hr
  exact inner_value_eq_explicit hn hr

theorem inner_fderiv_eq_explicit {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} {p : Inner.Pulse m}
    (hp : p ∈ inactiveRegion m n D) :
    fderiv ℝ (Inner.V (by omega : 0 < n) D) p = fderiv ℝ innerExplicit p :=
  (inner_eventuallyEq_explicit hn hp).fderiv_eq

def explicitValue {m : ℕ} (x : Primal m) : ℝ :=
  Outer.outerValue (state x) (entrance x) (exit x) + innerExplicit (pulse x)

/-- Local equality with the actual unconstrained contraction; it includes
all state coordinates and preserves the manuscript's current `R`. -/
theorem value_eventuallyEq_explicit {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    {x : Primal m} (hp : pulse x ∈ inactiveRegion m n D) :
    value (by omega : 0 < n) D =ᶠ[nhds x] explicitValue := by
  have hev := (inner_eventuallyEq_explicit hn hp).comp_tendsto
    (pulse_contDiff.continuous.continuousAt : ContinuousAt (pulse : Primal m → Inner.Pulse m) x)
  filter_upwards [hev] with z hz
  change Inner.V (by omega : 0 < n) D (pulse z) = innerExplicit (pulse z) at hz
  rw [value_split (by omega) hD, explicitValue, hz]

theorem value_fderiv_eq_explicit {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    {x : Primal m} (hp : pulse x ∈ inactiveRegion m n D) :
    fderiv ℝ (value (by omega : 0 < n) D) x = fderiv ℝ explicitValue x :=
  (value_eventuallyEq_explicit hn hD hp).fderiv_eq

theorem innerExplicit_contDiff {m : ℕ} :
    ContDiff ℝ (⊤ : ℕ∞) (innerExplicit : Inner.Pulse m → ℝ) := by
  unfold innerExplicit Inner.Q pA pB
  fun_prop

theorem innerExplicit_line_hasDerivAt {m : ℕ} (a b da db : Fin m → ℝ) :
    HasDerivAt (fun t : ℝ => innerExplicit
      (pulsePair (fun i => a i + t * da i) (fun i => b i + t * db i)))
      (∑ i : Fin m, ((2 * a i - b i) * da i + (2 * b i - a i) * db i)) 0 := by
  simp only [innerExplicit, pA_pair, pB_pair]
  apply HasDerivAt.fun_sum
  intro i _
  have ha := ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).mul_const (da i)).const_add (a i)
  have hb := ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).mul_const (db i)).const_add (b i)
  have h := ((ha.pow 2).sub (ha.mul hb)).add (hb.pow 2)
  convert! h using 1
  simp
  ring

theorem innerExplicit_fderiv_pair {m : ℕ} (a b da db : Fin m → ℝ) :
    (fderiv ℝ innerExplicit (pulsePair a b)) (pulsePair da db) =
      ∑ i : Fin m, ((2 * a i - b i) * da i + (2 * b i - a i) * db i) := by
  have hp : HasDerivAt (fun t : ℝ => pulsePair a b + t • pulsePair da db)
      (pulsePair da db) 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (pulsePair da db)).const_add
      (pulsePair a b)
  have hc := (((innerExplicit_contDiff.differentiable (by simp)) (pulsePair a b)).hasFDerivAt).comp_hasDerivAt_of_eq
    0 hp (by simp)
  have he : HasDerivAt (fun t : ℝ => innerExplicit (pulsePair a b + t • pulsePair da db))
      (∑ i : Fin m, ((2 * a i - b i) * da i + (2 * b i - a i) * db i)) 0 := by
    simpa only [pulsePair_line] using innerExplicit_line_hasDerivAt a b da db
  exact hc.unique he

def entranceDirection {m : ℕ} (i : Fin m) : Primal m := primal 0 (Pi.single i 1) 0
def exitDirection {m : ℕ} (i : Fin m) : Primal m := primal 0 0 (Pi.single i 1)

theorem entranceDirection_eq_basis {m : ℕ} (i : Fin m) :
    entranceDirection i = NCPLVerification.evecBasis (finProdFinEquiv (i, ⟨1, by omega⟩)) := by
  funext j
  obtain ⟨⟨r, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  fin_cases k <;> simp [entranceDirection, primal, NCPLVerification.evecBasis, Pi.single_apply]

theorem exitDirection_eq_basis {m : ℕ} (i : Fin m) :
    exitDirection i = NCPLVerification.evecBasis (finProdFinEquiv (i, ⟨2, by omega⟩)) := by
  funext j
  obtain ⟨⟨r, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  fin_cases k <;> simp [exitDirection, primal, NCPLVerification.evecBasis, Pi.single_apply]

theorem entrance_gradient_eq {m n : ℕ} (hn : 0 < n) (D : ℝ)
    (s a b : Fin m → ℝ) (i : Fin m) :
    gradient (value hn D) (primal s a b) (finProdFinEquiv (i, ⟨1, by omega⟩)) =
      (fderiv ℝ (value hn D) (primal s a b)) (entranceDirection i) := by
  rw [entranceDirection_eq_basis]
  rfl

theorem exit_gradient_eq {m n : ℕ} (hn : 0 < n) (D : ℝ)
    (s a b : Fin m → ℝ) (i : Fin m) :
    gradient (value hn D) (primal s a b) (finProdFinEquiv (i, ⟨2, by omega⟩)) =
      (fderiv ℝ (value hn D) (primal s a b)) (exitDirection i) := by
  rw [exitDirection_eq_basis]
  rfl

theorem entrance_fderiv_of_inactive {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) (hp : pulsePair a b ∈ inactiveRegion m n D) (i : Fin m) :
    (fderiv ℝ (value (by omega : 0 < n) D) (primal s a b)) (entranceDirection i) =
      outerGradA s a i + (2 * a i - b i) := by
  rw [entranceDirection, value_fderiv_connectors (by omega) hD,
    inner_fderiv_eq_explicit hn hp, innerExplicit_fderiv_pair,
    outerConnectorGradient, pulsePair_dot]
  simp [Pi.single_apply]

theorem exit_fderiv_of_inactive {m n : ℕ} (hn : 10 ≤ n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) (hp : pulsePair a b ∈ inactiveRegion m n D) (i : Fin m) :
    (fderiv ℝ (value (by omega : 0 < n) D) (primal s a b)) (exitDirection i) =
      outerGradB s b i + (2 * b i - a i) := by
  rw [exitDirection, value_fderiv_connectors (by omega) hD,
    inner_fderiv_eq_explicit hn hp, innerExplicit_fderiv_pair,
    outerConnectorGradient, pulsePair_dot]
  simp [Pi.single_apply]

theorem frontier_previous_high {m : ℕ} (s : Fin m → ℝ) {j : Fin m}
    (hf : IsFrontier s j) : 1 ≤ Outer.previous s j := by
  unfold Outer.previous NCCLowerBound.Simplified.Composite.previousMemory
  split
  · exact le_rfl
  · apply hf.1
    change j.val - 1 < j.val
    omega

theorem frontier_nextContribution_zero {m : ℕ} (s a b : Fin m → ℝ) {j : Fin m}
    (hf : IsFrontier s j) : Outer.nextContribution s a b j = 0 := by
  unfold Outer.nextContribution
  split
  · rename_i hjn
    have hnext : s ⟨j.val + 1, hjn⟩ ≤ 1 / 5 := hf.2 _ (by change j.val ≤ j.val + 1; omega)
    have h := Outer.low_u_identities (hf.2 j le_rfl)
      (a ⟨j.val + 1, hjn⟩) (b ⟨j.val + 1, hjn⟩) (s ⟨j.val + 1, hjn⟩)
    simp only [Outer.outgoing, h.1, h.2.1, h.2.2, q_eq_zero hnext]
    ring
  · rfl

theorem frontier_state_fderiv {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ) {j : Fin m} (hf : IsFrontier s j)
    (hlo : -(1 / 10 : ℝ) < s j) (hb : |b j| ≤ 21) :
    (fderiv ℝ (value hn D) (primal s a b)) (stateDirection j) =
      deriv (R Outer.c_R) (s j) - b j := by
  rw [state_fderiv_eq_deriv hn hD, (stateCoordinateValue_hasDerivAt hn hD s a b j).deriv,
    frontier_nextContribution_zero s a b hf]
  have hlow := hf.2 j le_rfl
  have hv := Outer.low_v_identities hlow (Outer.previous s j) (a j) (b j)
  have hs : |s j| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  simp only [Outer.incoming, hv.1, hv.2.1, hv.2.2,
    q_eq_one (frontier_previous_high s hf), deriv_e_s_eq_one hs, e_nu_eq_self hb]
  ring

theorem small_gradient_inactive {m n : ℕ} (hm : 1 ≤ m) (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 < D) (hsize : (n : ℝ) ≤ c_D * D) (s a b : Fin m → ℝ)
    (hsmall : Inner.norm₂ (gradient (value (by omega : 0 < n) D) (primal s a b)) ≤ 1 / 4)
    (hlast : s ⟨m - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    pulsePair a b ∈ inactiveRegion m n D :=
  inactive_of_connector_bound (by omega) hD hsize (pulsePair a b)
    (connector_norm_lt_twenty hm hn hD.le s a b hsmall hlast)

/-- The actual three frontier coordinates cannot all belong to a gradient
of Euclidean norm at most `1/4`. The finite-ball argument precedes every
use of the effective quadratic connector derivatives. -/
theorem small_gradient_impossible {m n : ℕ} (hm : 1 ≤ m) (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 < D) (hsize : (n : ℝ) ≤ c_D * D) (s a b : Fin m → ℝ)
    (hsmall : Inner.norm₂ (gradient (value (by omega : 0 < n) D) (primal s a b)) ≤ 1 / 4)
    (hlast : s ⟨m - 1, by omega⟩ ≤ (1 / 5 : ℝ)) : False := by
  obtain ⟨j, hf, _⟩ := small_unique_frontier hm (by omega : 0 < n) hD.le s a b hsmall hlast
  have hlo := small_state_lower (by omega : 0 < n) hD.le s a b hsmall j
  have hlow := hf.2 j le_rfl
  have hp := small_gradient_inactive hm hn hD hsize s a b hsmall hlast
  have hnorm := connector_norm_lt_twenty hm hn hD.le s a b hsmall hlast
  have ha : |a j| ≤ 21 := by
    have h := coordinate_abs_le_norm₂ (pulsePair a b) (finProdFinEquiv (j, ⟨0, by omega⟩))
    rw [pulsePair_a] at h
    linarith
  have hb : |b j| ≤ 21 := by
    have h := coordinate_abs_le_norm₂ (pulsePair a b) (finProdFinEquiv (j, ⟨1, by omega⟩))
    rw [pulsePair_b] at h
    linarith
  have hs : |s j| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  let ga := (fderiv ℝ (value (by omega : 0 < n) D) (primal s a b)) (entranceDirection j)
  let gb := (fderiv ℝ (value (by omega : 0 < n) D) (primal s a b)) (exitDirection j)
  have hga : ga = 2 * a j - b j - 4 := by
    have h := entrance_fderiv_of_inactive hn hD.le s a b hp j
    simp only [outerGradA, activation_single s hf j, ite_true, deriv_e_nu_eq_one ha] at h
    dsimp [ga]
    linarith
  have hgb : gb = 2 * b j - a j - s j := by
    have h := exit_fderiv_of_inactive hn hD.le s a b hp j
    simp only [outerGradB, activation_single s hf j, ite_true,
      deriv_e_nu_eq_one hb, e_s_eq_self hs] at h
    dsimp [gb]
    linarith
  have hga_abs : |ga| ≤ 1 / 4 := by
    have h := (coordinate_abs_le_norm₂ (gradient (value (by omega : 0 < n) D) (primal s a b))
      (finProdFinEquiv (j, ⟨1, by omega⟩))).trans hsmall
    rw [entrance_gradient_eq] at h
    exact h
  have hgb_abs : |gb| ≤ 1 / 4 := by
    have h := (coordinate_abs_le_norm₂ (gradient (value (by omega : 0 < n) D) (primal s a b))
      (finProdFinEquiv (j, ⟨2, by omega⟩))).trans hsmall
    rw [exit_gradient_eq] at h
    exact h
  have hbgt : 1 < b j := by
    have hid := NCC.Lower.frontier_connector_identity hga hgb
    have hga_low := (abs_le.mp hga_abs).1
    have hgb_low := (abs_le.mp hgb_abs).1
    linarith
  have hstate := frontier_state_fderiv (by omega : 0 < n) hD.le s a b hf hlo hb
  have hR : deriv (R Outer.c_R) (s j) ≤ 0 :=
    deriv_R_nonpos (by linarith [Outer.c_R_ge_twenty_five]) (s j)
  have hnegative := NCC.Lower.state_derivative_lt_neg_one hbgt hR
  have hc := (coordinate_abs_le_norm₂ (gradient (value (by omega : 0 < n) D) (primal s a b))
    (finProdFinEquiv (j, ⟨0, by omega⟩))).trans hsmall
  rw [state_gradient_eq, hstate] at hc
  have hlower := (abs_le.mp hc).1
  linarith

theorem g₀_pos : 0 < g₀ := by norm_num [g₀]

/-- `prop:terminal-gradient` for the literal, unnormalised hard instance.
The ball has radius `D/2`, `c_y=20√20`, `c_D=1/(40c_y)`, and `g₀=1/4`. -/
theorem terminal_gradient_lower {m n : ℕ} (hm : 1 ≤ m) (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 < D) (hsize : (n : ℝ) ≤ c_D * D) (x : Primal m)
    (hlast : state x ⟨m - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    g₀ ≤ Inner.norm₂ (gradient (value (by omega : 0 < n) D) x) := by
  apply le_of_lt
  apply lt_of_not_ge
  intro hsmall
  have hs : Inner.norm₂ (gradient (value (by omega : 0 < n) D)
      (primal (state x) (entrance x) (exit x))) ≤ 1 / 4 := by
    simpa only [primal_reconstruct, g₀] using hsmall
  exact small_gradient_impossible hm hn hD hsize (state x) (entrance x) (exit x) hs hlast

end

end NCC.Construction.Terminal
