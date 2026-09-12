import NCC.Construction.Composite
import NCC.Lower.TerminalAlgebra

/-!
# The actual constrained gradient and the unique active connector

Coordinates are serialized stage-by-stage as `(s_i,a_i,b_i)`. All norms
in this file are explicitly Euclidean. No inactive-ball assumption is
used: radial coercivity is for the actual finite-ball inner value.
-/

namespace NCC.Construction.Frontier

noncomputable section

open scoped BigOperators
open NCCLowerBoundVerification
open Composite

def gradient {d : ℕ} (f : Inner.Vec d → ℝ) (x : Inner.Vec d) : Inner.Vec d :=
  NCPLVerification.continuousLinearMapCoordinates (fderiv ℝ f x)

/-- The defined vector represents the genuine Fréchet derivative in the
Euclidean coordinate pairing, rather than the product-space sup norm. -/
theorem gradient_represents {d : ℕ} (f : Inner.Vec d → ℝ) (x h : Inner.Vec d) :
    (fderiv ℝ f x) h = ∑ i, gradient f x i * h i :=
  NCPLVerification.continuousLinearMap_apply_eq_coordinates _ _

theorem norm₂_nonneg {d : ℕ} (x : Inner.Vec d) : 0 ≤ Inner.norm₂ x := Real.sqrt_nonneg _

theorem norm₂_sq {d : ℕ} (x : Inner.Vec d) : (Inner.norm₂ x) ^ 2 = vecSq x :=
  Real.sq_sqrt (vecSq_nonneg x)

theorem coordinate_abs_le_norm₂ {d : ℕ} (x : Inner.Vec d) (i : Fin d) :
    |x i| ≤ Inner.norm₂ x := by
  have hi : (x i) ^ 2 ≤ vecSq x := by
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have hs := norm₂_sq x
  have hn := norm₂_nonneg x
  nlinarith [sq_abs (x i)]

theorem fderiv_le_norm₂_mul {d : ℕ} (f : Inner.Vec d → ℝ) (x h : Inner.Vec d) :
    (fderiv ℝ f x) h ≤ Inner.norm₂ (gradient f x) * Inner.norm₂ h := by
  rw [gradient_represents]
  exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (gradient f x) h

theorem stateDirection_eq_basis {m : ℕ} (i : Fin m) :
    stateDirection i = NCPLVerification.evecBasis (finProdFinEquiv (i, ⟨0, by omega⟩)) := by
  funext j
  obtain ⟨⟨r, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  fin_cases k <;> simp [stateDirection, primal, NCPLVerification.evecBasis, Pi.single_apply]

theorem state_gradient_eq {m n : ℕ} (hn : 0 < n) (D : ℝ)
    (s a b : Fin m → ℝ) (i : Fin m) :
    gradient (value hn D) (primal s a b) (finProdFinEquiv (i, ⟨0, by omega⟩)) =
      (fderiv ℝ (value hn D) (primal s a b)) (stateDirection i) := by
  rw [stateDirection_eq_basis]
  rfl

theorem small_state_lower {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ)
    (hsmall : Inner.norm₂ (gradient (value hn D) (primal s a b)) ≤ 1 / 4)
    (i : Fin m) : -(1 / 10 : ℝ) < s i := by
  by_contra hi
  have hd := phase_left_fderiv hn hD s a b i (le_of_not_gt hi)
  have hc := coordinate_abs_le_norm₂ (gradient (value hn D) (primal s a b))
    (finProdFinEquiv (i, ⟨0, by omega⟩))
  rw [state_gradient_eq] at hc
  have hl := (abs_le.mp (hc.trans hsmall)).1
  linarith

theorem small_state_phase {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ)
    (hsmall : Inner.norm₂ (gradient (value hn D) (primal s a b)) ≤ 1 / 4)
    (i : Fin m) : s i ≤ (1 / 5 : ℝ) ∨ 1 ≤ s i := by
  by_cases hi : s i ≤ (1 / 5 : ℝ)
  · exact Or.inl hi
  right
  by_contra hh
  have hd := phase_transition_fderiv hn hD s a b i (lt_of_not_ge hi) (lt_of_not_ge hh)
  have hc := coordinate_abs_le_norm₂ (gradient (value hn D) (primal s a b))
    (finProdFinEquiv (i, ⟨0, by omega⟩))
  rw [state_gradient_eq] at hc
  have hl := (abs_le.mp (hc.trans hsmall)).1
  linarith

theorem small_no_low_high {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b : Fin m → ℝ)
    (hsmall : Inner.norm₂ (gradient (value hn D) (primal s a b)) ≤ 1 / 4)
    (i : Fin m) (hinext : i.val + 1 < m) (hlo : s i ≤ (1 / 5 : ℝ)) :
    ¬ 1 ≤ s ⟨i.val + 1, hinext⟩ := by
  intro hh
  have hd := phase_out_of_order_fderiv hn hD s a b i hinext
    (small_state_lower hn hD s a b hsmall i) hlo hh
  have hc := coordinate_abs_le_norm₂ (gradient (value hn D) (primal s a b))
    (finProdFinEquiv (i, ⟨0, by omega⟩))
  rw [state_gradient_eq] at hc
  have hl := (abs_le.mp (hc.trans hsmall)).1
  linarith

/-- Zero-based first low stored state. The fixed seed is not a coordinate. -/
def IsFrontier {m : ℕ} (s : Fin m → ℝ) (j : Fin m) : Prop :=
  (∀ i, i < j → 1 ≤ s i) ∧ (∀ i, j ≤ i → s i ≤ (1 / 5 : ℝ))

theorem existsUnique_frontier {m : ℕ} (hm : 1 ≤ m) (s : Fin m → ℝ)
    (hphase : ∀ i, s i ≤ (1 / 5 : ℝ) ∨ 1 ≤ s i)
    (hno : ∀ (i : Fin m) (hi : i.val + 1 < m), s i ≤ (1 / 5 : ℝ) →
      ¬ 1 ≤ s ⟨i.val + 1, hi⟩)
    (hlast : s ⟨m - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    ∃! j, IsFrontier s j := by
  let P : ℕ → Prop := fun k => ∃ hk : k < m, s ⟨k, hk⟩ ≤ (1 / 5 : ℝ)
  have hex : ∃ k, P k := ⟨m - 1, ⟨by omega, hlast⟩⟩
  obtain ⟨hjm, hjlow⟩ := Nat.find_spec hex
  let j : Fin m := ⟨Nat.find hex, hjm⟩
  have hbefore : ∀ i : Fin m, i < j → 1 ≤ s i := by
    intro i hi
    rcases hphase i with hlo | hhi
    · exact False.elim (Nat.find_min hex hi ⟨i.isLt, hlo⟩)
    · exact hhi
  have hafterNat : ∀ k (hk : k < m), j.val ≤ k → s ⟨k, hk⟩ ≤ (1 / 5 : ℝ) := by
    intro k
    induction k with
    | zero =>
        intro hk hj
        have heq : Nat.find hex = 0 := by change Nat.find hex ≤ 0 at hj; omega
        simpa only [heq] using hjlow
    | succ k ih =>
        intro hk hj
        by_cases heq : j.val = k + 1
        · have hf : j = ⟨k + 1, hk⟩ := Fin.ext heq
          change s j ≤ (1 / 5 : ℝ) at hjlow
          simpa only [hf] using hjlow
        · have hk' : k < m := by omega
          have hprev := ih hk' (by omega)
          rcases hphase ⟨k + 1, hk⟩ with hlo | hhi
          · exact hlo
          · exact False.elim (hno ⟨k, hk'⟩ hk hprev hhi)
  have hjfront : IsFrontier s j := ⟨hbefore, fun i hi => hafterNat i.val i.isLt hi⟩
  refine ⟨j, hjfront, ?_⟩
  intro k hk
  apply le_antisymm
  · by_contra h
    have hh := hk.1 j (lt_of_not_ge h)
    have hl := hjfront.2 j le_rfl
    linarith
  · by_contra h
    have hh := hjfront.1 k (lt_of_not_ge h)
    have hl := hk.2 k le_rfl
    linarith

theorem small_unique_frontier {m n : ℕ} (hm : 1 ≤ m) (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) (s a b : Fin m → ℝ)
    (hsmall : Inner.norm₂ (gradient (value hn D) (primal s a b)) ≤ 1 / 4)
    (hlast : s ⟨m - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    ∃! j, IsFrontier s j :=
  existsUnique_frontier hm s (small_state_phase hn hD s a b hsmall)
    (small_no_low_high hn hD s a b hsmall) hlast

def activation {m : ℕ} (s : Fin m → ℝ) (i : Fin m) : ℝ :=
  q (Outer.previous s i) * (1 - q (s i))

theorem activation_single {m : ℕ} (s : Fin m → ℝ) {j : Fin m}
    (hf : IsFrontier s j) (i : Fin m) : activation s i = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst i
    have hcur : q (s j) = 0 := q_eq_zero (hf.2 j le_rfl)
    have hprev : q (Outer.previous s j) = 1 := by
      unfold Outer.previous NCCLowerBound.Simplified.Composite.previousMemory
      split
      · exact q_eq_one le_rfl
      · apply q_eq_one
        apply hf.1
        change j.val - 1 < j.val
        omega
    simp [activation, hcur, hprev]
  · have hout : activation s i = 0 := by
      rcases lt_or_gt_of_ne hij with hbefore | hafter
      · simp [activation, q_eq_one (hf.1 i hbefore)]
      · have hprev : q (Outer.previous s i) = 0 := by
          unfold Outer.previous NCCLowerBound.Simplified.Composite.previousMemory
          split
          · omega
          · apply q_eq_zero
            apply hf.2
            change j.val ≤ i.val - 1
            omega
        simp [activation, hprev]
    simp [hij, hout]

def outerGradA {m : ℕ} (s a : Fin m → ℝ) (i : Fin m) : ℝ :=
  -4 * activation s i * deriv e_nu (a i)

def outerGradB {m : ℕ} (s b : Fin m → ℝ) (i : Fin m) : ℝ :=
  -activation s i * e_s (s i) * deriv e_nu (b i)

def outerConnectorGradient {m : ℕ} (s a b : Fin m → ℝ) : Inner.Pulse m :=
  pulsePair (outerGradA s a) (outerGradB s b)

theorem outer_line_hasDerivAt {m : ℕ} (s a b da db : Fin m → ℝ) :
    HasDerivAt (fun t : ℝ => Outer.outerValue s (fun i => a i + t * da i)
      (fun i => b i + t * db i))
      (∑ i : Fin m, (outerGradA s a i * da i + outerGradB s b i * db i)) 0 := by
  unfold Outer.outerValue
  apply HasDerivAt.fun_sum
  intro i _
  have ha : HasDerivAt (fun t : ℝ => e_nu (a i + t * da i))
      (deriv e_nu (a i) * da i) 0 := by
    have he := (e_nu_contDiff.differentiable (by simp) (a i)).hasDerivAt
    have hl := ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).mul_const (da i)).const_add (a i)
    convert! he.comp_of_eq 0 hl (by simp) using 1
    simp
  have hb : HasDerivAt (fun t : ℝ => e_nu (b i + t * db i))
      (deriv e_nu (b i) * db i) 0 := by
    have he := (e_nu_contDiff.differentiable (by simp) (b i)).hasDerivAt
    have hl := ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).mul_const (db i)).const_add (b i)
    convert! he.comp_of_eq 0 hl (by simp) using 1
    simp
  have h := ((ha.const_mul (-4 * q (Outer.previous s i) * (1 - q (s i)))).add
    (hb.const_mul (-q (Outer.previous s i) * e_s (s i) * (1 - q (s i))))).add_const
      (Outer.C_st (Outer.previous s i) (s i) + R Outer.c_R (s i))
  convert! h using 1
  · funext t
    unfold Outer.stage Outer.coupling Outer.C_en Outer.C_ex
    simp only [Pi.add_apply]
    ring
  · unfold outerGradA outerGradB activation
    ring

theorem pulsePair_dot {m : ℕ} (a b da db : Fin m → ℝ) :
    (∑ k, pulsePair a b k * pulsePair da db k) =
      ∑ i : Fin m, (a i * da i + b i * db i) := by
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [Fin.sum_univ_two, pulsePair]

theorem pulsePair_vecSq {m : ℕ} (a b : Fin m → ℝ) :
    vecSq (pulsePair a b) = ∑ i : Fin m, ((a i) ^ 2 + (b i) ^ 2) := by
  simpa only [vecSq, NCPLVerification.vecSq, sq] using pulsePair_dot a b a b

/-- Outside the unique frontier both actual outer connector partials vanish. -/
theorem outerConnectorGradient_support {m : ℕ} (s a b : Fin m → ℝ) {j : Fin m}
    (hf : IsFrontier s j) (i : Fin m) (hi : i ≠ j) :
    outerGradA s a i = 0 ∧ outerGradB s b i = 0 := by
  simp [outerGradA, outerGradB, activation_single s hf i, hi]

theorem outerConnectorGradient_norm_le_seven {m : ℕ} (s a b : Fin m → ℝ) {j : Fin m}
    (hf : IsFrontier s j) : Inner.norm₂ (outerConnectorGradient s a b) ≤ 7 := by
  have hsingle : vecSq (outerConnectorGradient s a b) =
      (outerGradA s a j) ^ 2 + (outerGradB s b j) ^ 2 := by
    unfold outerConnectorGradient
    rw [pulsePair_vecSq, Finset.sum_eq_single j]
    · intro i _ hi
      rcases outerConnectorGradient_support s a b hf i hi with ⟨ha, hb⟩
      simp [ha, hb]
    · simp
  have ha := deriv_e_nu_mem (a j)
  have hb := deriv_e_nu_mem (b j)
  have hs := e_s_abs_le (s j)
  have hga : |outerGradA s a j| ≤ 4 := by
    simp only [outerGradA, activation_single s hf j, ite_true, mul_one, abs_mul,
      abs_of_nonneg ha.1]
    norm_num
    linarith [ha.2]
  have hgb : |outerGradB s b j| ≤ 5 / 2 := by
    simp only [outerGradB, activation_single s hf j, ite_true, neg_mul, one_mul,
      abs_neg, abs_mul, abs_of_nonneg hb.1]
    calc
      _ ≤ (5 / 2 : ℝ) * 1 := mul_le_mul hs hb.2 hb.1 (by norm_num)
      _ = _ := by ring
  have hnorm := norm₂_sq (outerConnectorGradient s a b)
  rw [hsingle] at hnorm
  have hn := norm₂_nonneg (outerConnectorGradient s a b)
  have hga2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)).mpr hga
  have hgb2 := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 5 / 2)).mpr hgb
  rw [sq_abs] at hga2 hgb2
  nlinarith

theorem primal_connectorLine_hasDerivAt {m : ℕ} (s a b da db : Fin m → ℝ) :
    HasDerivAt (fun t : ℝ => primal s (fun i => a i + t * da i)
      (fun i => b i + t * db i)) (primal 0 da db) 0 := by
  apply hasDerivAt_pi.2
  intro j
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  fin_cases k
  · simpa [primal] using (hasDerivAt_const (0 : ℝ) (s i))
  · simpa [primal] using
      (((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).mul_const (da i)).const_add (a i))
  · simpa [primal] using
      (((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).mul_const (db i)).const_add (b i))

theorem outer_fderiv_connectors {m : ℕ} (s a b da db : Fin m → ℝ) :
    (fderiv ℝ (fun x : Primal m => Outer.outerValue (state x) (entrance x) (exit x))
      (primal s a b)) (primal 0 da db) =
      ∑ k, outerConnectorGradient s a b k * pulsePair da db k := by
  have h := ((outer_flat_contDiff.differentiable (by simp)) (primal s a b)).hasFDerivAt
  have hc := h.comp_hasDerivAt_of_eq 0 (primal_connectorLine_hasDerivAt s a b da db)
    (by simp)
  have he := outer_line_hasDerivAt s a b da db
  have hc' : HasDerivAt (fun t : ℝ => Outer.outerValue s (fun i => a i + t * da i)
      (fun i => b i + t * db i))
      ((fderiv ℝ (fun x : Primal m => Outer.outerValue (state x) (entrance x) (exit x))
        (primal s a b)) (primal 0 da db)) 0 := by
    simpa only [Function.comp_def, state_primal, entrance_primal, exit_primal] using hc
  rw [outerConnectorGradient, pulsePair_dot]
  exact hc'.unique he

theorem primal_connector_vecSq {m : ℕ} (a b : Fin m → ℝ) :
    vecSq (primal (0 : Fin m → ℝ) a b) = vecSq (pulsePair a b) := by
  rw [pulsePair_vecSq]
  unfold vecSq NCPLVerification.vecSq
  rw [← Equiv.sum_comp finProdFinEquiv, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [Fin.sum_univ_three, primal]

theorem primal_connector_norm₂ {m : ℕ} (a b : Fin m → ℝ) :
    Inner.norm₂ (primal (0 : Fin m → ℝ) a b) = Inner.norm₂ (pulsePair a b) := by
  unfold Inner.norm₂
  rw [primal_connector_vecSq]

theorem pulsePair_line {m : ℕ} (a b da db : Fin m → ℝ) (t : ℝ) :
    pulsePair (fun i => a i + t * da i) (fun i => b i + t * db i) =
      pulsePair a b + t • pulsePair da db := by
  funext j
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  fin_cases k <;> simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pulsePair]

theorem value_fderiv_connectors {m n : ℕ} (hn : 0 < n) {D : ℝ} (hD : 0 ≤ D)
    (s a b da db : Fin m → ℝ) :
    (fderiv ℝ (value hn D) (primal s a b)) (primal 0 da db) =
      (∑ k, outerConnectorGradient s a b k * pulsePair da db k) +
      (fderiv ℝ (Inner.V hn D) (pulsePair a b)) (pulsePair da db) := by
  have hc := ((value_differentiable hn hD) (primal s a b)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 (primal_connectorLine_hasDerivAt s a b da db) (by simp)
  have hp : HasDerivAt (fun t : ℝ => pulsePair a b + t • pulsePair da db)
      (pulsePair da db) 0 := by
    simpa using ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const (pulsePair da db)).const_add
      (pulsePair a b)
  have hi := ((Inner.V_differentiable hn hD) (pulsePair a b)).hasFDerivAt.comp_hasDerivAt_of_eq
    0 hp (by simp)
  have he := (outer_line_hasDerivAt s a b da db).add hi
  have he' : HasDerivAt (fun t : ℝ => value hn D
      (primal s (fun i => a i + t * da i) (fun i => b i + t * db i)))
      ((∑ i : Fin m, (outerGradA s a i * da i + outerGradB s b i * db i)) +
        (fderiv ℝ (Inner.V hn D) (pulsePair a b)) (pulsePair da db)) 0 := by
    have heq : (fun t : ℝ => value hn D
        (primal s (fun i => a i + t * da i) (fun i => b i + t * db i))) =
        (fun t : ℝ => Outer.outerValue s (fun i => a i + t * da i)
          (fun i => b i + t * db i) + Inner.V hn D (pulsePair a b + t • pulsePair da db)) := by
      funext t
      rw [value_split hn hD]
      simp only [state_primal, entrance_primal, exit_primal, pulse_primal, pulsePair_line]
    rw [heq]
    exact he
  rw [outerConnectorGradient, pulsePair_dot]
  exact hc.unique he'

/-- Cauchy-Schwarz for the single active outer connector. -/
theorem outer_radial_lower {m : ℕ} (s a b : Fin m → ℝ) {j : Fin m}
    (hf : IsFrontier s j) :
    -7 * Inner.norm₂ (pulsePair a b) ≤
      ∑ k, outerConnectorGradient s a b k * pulsePair a b k := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
    (fun k => -outerConnectorGradient s a b k) (pulsePair a b)
  have hsq : (∑ k, (-outerConnectorGradient s a b k) ^ 2) =
      vecSq (outerConnectorGradient s a b) := by
    simp [vecSq, NCPLVerification.vecSq]
  rw [hsq] at h
  have hnorm := outerConnectorGradient_norm_le_seven s a b hf
  have hn := norm₂_nonneg (pulsePair a b)
  have hp := mul_le_mul_of_nonneg_right hnorm hn
  have hneg : (∑ k, -outerConnectorGradient s a b k * pulsePair a b k) =
      -(∑ k, outerConnectorGradient s a b k * pulsePair a b k) := by
    simp only [neg_mul, Finset.sum_neg_distrib]
  rw [hneg] at h
  change -(∑ k, outerConnectorGradient s a b k * pulsePair a b k) ≤
    Inner.norm₂ (outerConnectorGradient s a b) * Inner.norm₂ (pulsePair a b) at h
  linarith

/-- The key radial estimate is derived from the actual constrained value
and the actual Euclidean gradient. In particular, it does not presuppose
that the unconstrained inner maximizer fits in the ball. -/
theorem connector_radial_budget {m n : ℕ} (hm : 1 ≤ m) (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) (s a b : Fin m → ℝ)
    (hsmall : Inner.norm₂ (gradient (value (by omega : 0 < n) D) (primal s a b)) ≤ 1 / 4)
    (hlast : s ⟨m - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    (2 / 5 : ℝ) * (Inner.norm₂ (pulsePair a b)) ^ 2 -
      7 * Inner.norm₂ (pulsePair a b) ≤ (1 / 4 : ℝ) * Inner.norm₂ (pulsePair a b) := by
  obtain ⟨j, hf, _⟩ := small_unique_frontier hm (by omega : 0 < n) hD s a b hsmall hlast
  have hout := outer_radial_lower s a b hf
  have hin := Inner.V_radial_lower hn hD (pulsePair a b)
  have heq := value_fderiv_connectors (by omega : 0 < n) hD s a b a b
  have hcs := fderiv_le_norm₂_mul (value (by omega : 0 < n) D) (primal s a b) (primal 0 a b)
  rw [primal_connector_norm₂] at hcs
  have hprod := mul_le_mul_of_nonneg_right hsmall (norm₂_nonneg (pulsePair a b))
  rw [norm₂_sq]
  linarith

theorem connector_norm_le {m n : ℕ} (hm : 1 ≤ m) (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) (s a b : Fin m → ℝ)
    (hsmall : Inner.norm₂ (gradient (value (by omega : 0 < n) D) (primal s a b)) ≤ 1 / 4)
    (hlast : s ⟨m - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    Inner.norm₂ (pulsePair a b) ≤ (145 / 8 : ℝ) :=
  NCC.Lower.connector_norm_le (norm₂_nonneg _) (connector_radial_budget hm hn hD s a b hsmall hlast)

theorem connector_norm_lt_twenty {m n : ℕ} (hm : 1 ≤ m) (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) (s a b : Fin m → ℝ)
    (hsmall : Inner.norm₂ (gradient (value (by omega : 0 < n) D) (primal s a b)) ≤ 1 / 4)
    (hlast : s ⟨m - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    Inner.norm₂ (pulsePair a b) < 20 :=
  (connector_norm_le hm hn hD s a b hsmall hlast).trans_lt
    NCC.Lower.connector_bound_constant_lt_twenty

theorem primal_reconstruct {m : ℕ} (x : Primal m) :
    primal (state x) (entrance x) (exit x) = x := by
  funext j
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective j
  fin_cases k <;> simp [primal, state, entrance, exit]

/-- `lem:bounded-connector`, on an arbitrary point of the literal `3M`
primal space, with the sharper quantitative bound `145/8 < 20`. -/
theorem bounded_connector {m n : ℕ} (hm : 1 ≤ m) (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) (x : Primal m)
    (hsmall : Inner.norm₂ (gradient (value (by omega : 0 < n) D) x) ≤ 1 / 4)
    (hlast : state x ⟨m - 1, by omega⟩ ≤ (1 / 5 : ℝ)) :
    (∀ i, -(1 / 10 : ℝ) < state x i) ∧
    (∃! j, IsFrontier (state x) j) ∧
    Inner.norm₂ (pulse x) ≤ (145 / 8 : ℝ) := by
  have hs : Inner.norm₂ (gradient (value (by omega : 0 < n) D)
      (primal (state x) (entrance x) (exit x))) ≤ 1 / 4 := by
    simpa only [primal_reconstruct] using hsmall
  exact ⟨small_state_lower (by omega) hD (state x) (entrance x) (exit x) hs,
    small_unique_frontier hm (by omega) hD (state x) (entrance x) (exit x) hs hlast,
    connector_norm_le hm hn hD (state x) (entrance x) (exit x) hs hlast⟩

end

end NCC.Construction.Frontier
