import NCC.Construction.Scalar.Bounds
import NCCLowerBound.Simplified.Composite

/-!
# Exact current outer couplings

All couplings use the current scalar formulas. Equality with the three old
couplings is proved by equality of the scalar functions; the phase
regularizer is deliberately the current `R`, with no old-phase substitution.
-/

namespace NCC.Construction.Outer

noncomputable section

open Set
open scoped BigOperators

def C_en (u a v : ℝ) : ℝ := -4 * q u * (1 - q v) * e_nu a
def C_ex (u b v : ℝ) : ℝ := -q u * e_s v * (1 - q v) * e_nu b
def C_st (u v : ℝ) : ℝ := 24 * q v * (1 - e_s u) * (1 - q u)

/-- Sum of the three couplings of a single stage. -/
def coupling (u a b v : ℝ) : ℝ := C_en u a v + C_ex u b v + C_st u v

/-- The stage uses the manuscript's current `R(c_R,·)`. -/
def stage (c u a b v : ℝ) : ℝ := coupling u a b v + R c v

theorem identityExtension_eq_saturation {r : ℝ} (hr : 0 ≤ r) :
    identityExtension r = NCCLowerBoundVerification.saturationTemplate r 1 := by
  let f := identityExtension r
  let g := NCCLowerBoundVerification.saturationTemplate r 1
  have hf : Differentiable ℝ f := fun t => (hasDerivAt_identityExtension r t).differentiableAt
  have hg : Differentiable ℝ g := NCCLowerBoundVerification.differentiable_saturationTemplate r 1
  have hderiv : ∀ t, deriv f t = deriv g t := by
    intro t
    rw [show deriv f t = deriv (identityExtension r) t by rfl,
      show deriv g t = deriv (NCCLowerBoundVerification.saturationTemplate r 1) t by rfl,
      deriv_identityExtension, NCCLowerBoundVerification.deriv_saturationTemplate,
      NCCLowerBoundVerification.clipIntegrand_eq_smooth hr (by norm_num)]
    simp only [NCCLowerBoundVerification.smoothClipIntegrand, div_one,
      NCCLowerBoundVerification.Lambda1_eq_smoothTransition]
    have hs := step_symmetry (t + (r + 1))
    rw [show 1 - (t + (r + 1)) = -t - r by ring] at hs
    change step (t + (r + 1)) - step (t - r) = 1 - step (t - r) - step (-t - r)
    linarith
  have hz : ∀ t, deriv (fun x => f x - g x) t = 0 := by
    intro t
    change deriv (f - g) t = 0
    rw [deriv_sub (hf t) (hg t), hderiv]
    ring
  have hconst := is_const_of_deriv_eq_zero (hf.sub hg) hz
  funext t
  have h := hconst t 0
  have hf0 : f 0 = 0 := identityExtension_eq_self (by linarith) hr
  have hg0 : g 0 = 0 := NCCLowerBoundVerification.saturationTemplate_zero r 1
  change f t - g t = f 0 - g 0 at h
  rw [hf0, hg0] at h
  linarith

theorem e_s_eq_old : e_s = NCCLowerBound.Simplified.stateClip := by
  rw [e_s_eq_identityExtension, identityExtension_eq_saturation (by norm_num)]
  rfl

theorem e_nu_eq_old : e_nu = NCCLowerBound.Simplified.pulseClip := by
  rw [e_nu_eq_identityExtension, identityExtension_eq_saturation (by norm_num)]
  rfl

theorem q_eq_old : q = NCCLowerBound.Simplified.frontierSwitch := by
  funext t
  by_cases hlo : t ≤ 1 / 5
  · rw [q_eq_zero hlo, NCCLowerBound.Simplified.frontierSwitch_eq_zero_of_le_fifth hlo]
  by_cases hhi : 1 ≤ t
  · rw [q_eq_one hhi, NCCLowerBound.Simplified.frontierSwitch_eq_one_of_one_le hhi]
  have habs : |t| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [NCCLowerBound.Simplified.frontierSwitch,
    NCCLowerBound.Simplified.stateClip_eq_self habs, q_eq_step]
  exact congrFun NCCLowerBoundVerification.Lambda1_eq_smoothTransition _ |>.symm

theorem C_en_eq_old {m : ℕ} (s a : Fin m → ℝ) (i : Fin m) :
    C_en (NCCLowerBound.Simplified.Composite.previousMemory s i) (a i) (s i) =
      NCCLowerBound.Simplified.Composite.entranceSummand s a i := by
  simp only [C_en, q_eq_old, e_nu_eq_old,
    NCCLowerBound.Simplified.Composite.entranceSummand]

theorem C_ex_eq_old {m : ℕ} (s b : Fin m → ℝ) (i : Fin m) :
    C_ex (NCCLowerBound.Simplified.Composite.previousMemory s i) (b i) (s i) =
      NCCLowerBound.Simplified.Composite.exitSummand s b i := by
  simp only [C_ex, q_eq_old, e_nu_eq_old, e_s_eq_old,
    NCCLowerBound.Simplified.Composite.exitSummand]

theorem C_st_eq_old {m : ℕ} (s : Fin m → ℝ) (i : Fin m) :
    C_st (NCCLowerBound.Simplified.Composite.previousMemory s i) (s i) =
      NCCLowerBound.Simplified.Composite.orderingSummand s i := by
  simp only [C_st, q_eq_old, e_s_eq_old,
    NCCLowerBound.Simplified.Composite.orderingSummand]

private theorem q_differentiable : Differentiable ℝ q :=
  (q_contDiff (k := (1 : ℕ∞))).differentiable (by norm_num)

private theorem es_differentiable : Differentiable ℝ e_s :=
  e_s_contDiff.differentiable (by simp)

private theorem enu_differentiable : Differentiable ℝ e_nu :=
  e_nu_contDiff.differentiable (by simp)

theorem deriv_C_en_u (u a v : ℝ) :
    deriv (fun t => C_en t a v) u = -4 * deriv q u * (1 - q v) * e_nu a := by
  exact ((((q_differentiable u).hasDerivAt.const_mul (-4)).mul_const (1 - q v)).mul_const
    (e_nu a)).deriv

theorem deriv_C_en_v (u a v : ℝ) :
    deriv (C_en u a) v = 4 * q u * deriv q v * e_nu a := by
  unfold C_en
  have h := ((((q_differentiable v).hasDerivAt.const_sub 1).const_mul (-4 * q u)).mul_const
    (e_nu a))
  convert! h.deriv using 1
  ring

theorem deriv_C_ex_u (u b v : ℝ) :
    deriv (fun t => C_ex t b v) u = -deriv q u * e_s v * (1 - q v) * e_nu b := by
  exact (((((q_differentiable u).hasDerivAt.neg).mul_const (e_s v)).mul_const (1 - q v)).mul_const
    (e_nu b)).deriv

theorem deriv_C_ex_v (u b v : ℝ) :
    deriv (C_ex u b) v =
      -q u * (deriv e_s v * (1 - q v) - e_s v * deriv q v) * e_nu b := by
  unfold C_ex
  have h0 := ((es_differentiable v).hasDerivAt.const_mul (-q u)).mul
    ((q_differentiable v).hasDerivAt.const_sub 1)
  have h := h0.mul_const (e_nu b)
  convert! h.deriv using 1
  ring

theorem deriv_C_st_u (u v : ℝ) :
    deriv (fun t => C_st t v) u =
      -24 * q v * (deriv e_s u * (1 - q u) + (1 - e_s u) * deriv q u) := by
  have h := (((es_differentiable u).hasDerivAt.const_sub 1).const_mul (24 * q v)).mul
    ((q_differentiable u).hasDerivAt.const_sub 1)
  convert! h.deriv using 1
  ring

theorem deriv_C_st_v (u v : ℝ) :
    deriv (C_st u) v = 24 * deriv q v * (1 - e_s u) * (1 - q u) := by
  exact ((((q_differentiable v).hasDerivAt.const_mul 24).mul_const (1 - e_s u)).mul_const
    (1 - q u)).deriv

theorem low_v_identities {v : ℝ} (hv : v ≤ 1 / 5) (u a b : ℝ) :
    deriv (C_st u) v = 0 ∧ deriv (C_en u a) v = 0 ∧
      deriv (C_ex u b) v = -q u * deriv e_s v * e_nu b := by
  rw [deriv_C_st_v, deriv_C_en_v, deriv_C_ex_v,
    q_eq_zero hv, deriv_q_eq_zero_left hv]
  constructor
  · ring
  constructor <;> ring

theorem low_u_identities {u : ℝ} (hu : u ≤ 1 / 5) (a b v : ℝ) :
    deriv (fun t => C_en t a v) u = 0 ∧ deriv (fun t => C_ex t b v) u = 0 ∧
      deriv (fun t => C_st t v) u = -24 * q v * deriv e_s u := by
  rw [deriv_C_st_u, deriv_C_en_u, deriv_C_ex_u,
    q_eq_zero hu, deriv_q_eq_zero_left hu]
  constructor
  · ring
  constructor <;> ring

theorem low_v_exit_bound {v : ℝ} (hv : v ≤ 1 / 5) (u b : ℝ) :
    deriv (C_ex u b) v ≤ 43 / 2 := by
  rw [(low_v_identities hv u 0 b).2.2]
  have hq := q_mem u
  have he := deriv_e_s_mem v
  have hb := e_nu_abs_le b
  have habs : |-q u * deriv e_s v * e_nu b| ≤ 43 / 2 := by
    rw [abs_mul, abs_mul, abs_neg, abs_of_nonneg hq.1, abs_of_nonneg he.1]
    calc
      q u * deriv e_s v * |e_nu b| ≤ 1 * 1 * (43 / 2 : ℝ) := by
        gcongr <;> linarith [hq.1, hq.2, he.1, he.2]
      _ = 43 / 2 := by ring
  exact (le_abs_self _).trans habs

theorem low_u_state_nonpos {u : ℝ} (hu : u ≤ 1 / 5) (v : ℝ) :
    deriv (fun t => C_st t v) u ≤ 0 := by
  rw [(low_u_identities hu 0 0 v).2.2]
  have hp := mul_nonneg (q_mem v).1 (deriv_e_s_mem u).1
  nlinarith

theorem low_high_state_exact {u v : ℝ} (hu0 : -(1 / 10) < u)
    (hu1 : u ≤ 1 / 5) (hv : 1 ≤ v) :
    deriv (fun t => C_st t v) u = -24 := by
  rw [(low_u_identities hu1 0 0 v).2.2, q_eq_one hv,
    deriv_e_s_eq_one (abs_le.mpr ⟨by linarith, by linarith⟩)]
  ring

private theorem q_abs_le_one (t : ℝ) : |q t| ≤ 1 := by
  rw [abs_of_nonneg (q_mem t).1]
  exact (q_mem t).2

private theorem one_sub_q_abs_le_one (t : ℝ) : |1 - q t| ≤ 1 := by
  rw [abs_of_nonneg (by linarith [(q_mem t).2])]
  linarith [(q_mem t).1]

private theorem deriv_es_abs_le_one (t : ℝ) : |deriv e_s t| ≤ 1 := by
  rw [abs_of_nonneg (deriv_e_s_mem t).1]
  exact (deriv_e_s_mem t).2

private theorem one_sub_es_abs_le (t : ℝ) : |1 - e_s t| ≤ 7 / 2 := by
  have h := abs_sub (1 : ℝ) (e_s t)
  norm_num at h
  linarith [e_s_abs_le t]

/-- Boundedness is proved for the six actual partial derivatives. -/
theorem six_partials_bounded : ∃ C : ℝ, 0 ≤ C ∧ ∀ u a v : ℝ,
    |deriv (fun t => C_st t v) u| ≤ C ∧ |deriv (C_st u) v| ≤ C ∧
    |deriv (fun t => C_en t a v) u| ≤ C ∧ |deriv (C_en u a) v| ≤ C ∧
    |deriv (fun t => C_ex t a v) u| ≤ C ∧ |deriv (C_ex u a) v| ≤ C := by
  obtain ⟨A, hA0, hA⟩ := q_iteratedDeriv_bounded (k := 1) (by norm_num)
  have hA' : ∀ t, |deriv q t| ≤ A := by simpa using hA
  refine ⟨1000 * (A + 1), by positivity, ?_⟩
  intro u a v
  have hqu := q_abs_le_one u
  have hqv := q_abs_le_one v
  have h1u := one_sub_q_abs_le_one u
  have h1v := one_sub_q_abs_le_one v
  have hesv := e_s_abs_le v
  have henu := e_nu_abs_le a
  have hdeu := deriv_es_abs_le_one u
  have hdev := deriv_es_abs_le_one v
  have h1eu := one_sub_es_abs_le u
  have hdu := hA' u
  have hdv := hA' v
  have hen_u : |deriv (fun t => C_en t a v) u| ≤ 86 * A := by
    rw [deriv_C_en_u, abs_mul, abs_mul, abs_mul]
    norm_num
    calc
      _ ≤ 4 * A * 1 * (43 / 2 : ℝ) := by gcongr
      _ = 86 * A := by ring
  have hen_v : |deriv (C_en u a) v| ≤ 86 * A := by
    rw [deriv_C_en_v, abs_mul, abs_mul, abs_mul]
    norm_num
    calc
      _ ≤ 4 * 1 * A * (43 / 2 : ℝ) := by gcongr
      _ = 86 * A := by ring
  have hex_u : |deriv (fun t => C_ex t a v) u| ≤ (215 / 4 : ℝ) * A := by
    rw [deriv_C_ex_u, abs_mul, abs_mul, abs_mul, abs_neg]
    calc
      _ ≤ A * (5 / 2 : ℝ) * 1 * (43 / 2 : ℝ) := by gcongr
      _ = (215 / 4 : ℝ) * A := by ring
  have hinnerEx : |deriv e_s v * (1 - q v) - e_s v * deriv q v| ≤
      1 + (5 / 2 : ℝ) * A := by
    calc
      _ ≤ |deriv e_s v * (1 - q v)| + |e_s v * deriv q v| := abs_sub _ _
      _ ≤ 1 * 1 + (5 / 2 : ℝ) * A := by rw [abs_mul, abs_mul]; gcongr
      _ = _ := by ring
  have hex_v : |deriv (C_ex u a) v| ≤ (43 / 2 : ℝ) * (1 + (5 / 2 : ℝ) * A) := by
    rw [deriv_C_ex_v, abs_mul, abs_mul, abs_neg]
    calc
      _ ≤ 1 * (1 + (5 / 2 : ℝ) * A) * (43 / 2 : ℝ) := by gcongr
      _ = _ := by ring
  have hinnerSt : |deriv e_s u * (1 - q u) + (1 - e_s u) * deriv q u| ≤
      1 + (7 / 2 : ℝ) * A := by
    calc
      _ ≤ |deriv e_s u * (1 - q u)| + |(1 - e_s u) * deriv q u| := abs_add_le _ _
      _ ≤ 1 * 1 + (7 / 2 : ℝ) * A := by rw [abs_mul, abs_mul]; gcongr
      _ = _ := by ring
  have hst_u : |deriv (fun t => C_st t v) u| ≤ 24 * (1 + (7 / 2 : ℝ) * A) := by
    rw [deriv_C_st_u, abs_mul, abs_mul]
    norm_num
    calc
      _ ≤ 24 * 1 * (1 + (7 / 2 : ℝ) * A) := by gcongr
      _ = _ := by ring
  have hst_v : |deriv (C_st u) v| ≤ 84 * A := by
    rw [deriv_C_st_v, abs_mul, abs_mul, abs_mul]
    norm_num
    calc
      _ ≤ 24 * A * (7 / 2 : ℝ) * 1 := by gcongr
      _ = _ := by ring
  exact ⟨by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith⟩

/-- The six state partials, in exactly the order of the definition of `c_R`. -/
def statePartial (j : Fin 6) (z : ℝ × ℝ × ℝ) : ℝ :=
  ![deriv (fun t => C_st t z.2.2) z.1,
    deriv (C_st z.1) z.2.2,
    deriv (fun t => C_en t z.2.1 z.2.2) z.1,
    deriv (C_en z.1 z.2.1) z.2.2,
    deriv (fun t => C_ex t z.2.1 z.2.2) z.1,
    deriv (C_ex z.1 z.2.1) z.2.2] j

theorem partial_bddAbove (j : Fin 6) : BddAbove (Set.range (fun z => |statePartial j z|)) := by
  obtain ⟨C, _, hC⟩ := six_partials_bounded
  refine ⟨C, ?_⟩
  rintro _ ⟨⟨u, a, v⟩, rfl⟩
  have h := hC u a v
  fin_cases j <;> simp only [statePartial] <;> tauto

def partialNorm (j : Fin 6) : ℝ := sSup (Set.range (fun z => |statePartial j z|))

theorem partial_le_norm (j : Fin 6) (z : ℝ × ℝ × ℝ) : |statePartial j z| ≤ partialNorm j :=
  le_csSup (partial_bddAbove j) (Set.mem_range_self z)

theorem partialNorm_nonneg (j : Fin 6) : 0 ≤ partialNorm j :=
  (abs_nonneg (statePartial j (0, 0, 0))).trans (partial_le_norm j (0, 0, 0))

/-- The literal finite constant prescribed in the current paper. -/
def c_R : ℝ := 25 + ∑ j : Fin 6, partialNorm j

theorem c_R_ge_twenty_five : 25 ≤ c_R := by
  have hs : 0 ≤ ∑ j : Fin 6, partialNorm j :=
    Finset.sum_nonneg (fun j _ => partialNorm_nonneg j)
  unfold c_R
  linarith

def incoming (u a b v : ℝ) : ℝ :=
  deriv (C_en u a) v + deriv (C_ex u b) v + deriv (C_st u) v

def outgoing (u a b v : ℝ) : ℝ :=
  deriv (fun t => C_en t a v) u + deriv (fun t => C_ex t b v) u +
    deriv (fun t => C_st t v) u

theorem incoming_outgoing_bound (u a b t a' b' v : ℝ) :
    |incoming u a b t + outgoing t a' b' v| ≤ c_R := by
  have h0 := partial_le_norm 0 (t, 0, v)
  have h1 := partial_le_norm 1 (u, 0, t)
  have h2 := partial_le_norm 2 (t, a', v)
  have h3 := partial_le_norm 3 (u, a, t)
  have h4 := partial_le_norm 4 (t, b', v)
  have h5 := partial_le_norm 5 (u, b, t)
  change |deriv (fun x => C_st x v) t| ≤ partialNorm 0 at h0
  change |deriv (C_st u) t| ≤ partialNorm 1 at h1
  change |deriv (fun x => C_en x a' v) t| ≤ partialNorm 2 at h2
  change |deriv (C_en u a) t| ≤ partialNorm 3 at h3
  change |deriv (fun x => C_ex x b' v) t| ≤ partialNorm 4 at h4
  change |deriv (C_ex u b) t| ≤ partialNorm 5 at h5
  have hab : |incoming u a b t + outgoing t a' b' v| ≤
      |deriv (C_en u a) t| + |deriv (C_ex u b) t| + |deriv (C_st u) t| +
      (|deriv (fun x => C_en x a' v) t| + |deriv (fun x => C_ex x b' v) t| +
        |deriv (fun x => C_st x v) t|) := by
    unfold incoming outgoing
    calc
      _ ≤ |deriv (C_en u a) t + deriv (C_ex u b) t + deriv (C_st u) t| +
          |deriv (fun x => C_en x a' v) t + deriv (fun x => C_ex x b' v) t +
            deriv (fun x => C_st x v) t| := abs_add_le _ _
      _ ≤ _ := by gcongr <;> exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
  unfold c_R
  simp only [Fin.sum_univ_succ]
  norm_num
  change |incoming u a b t + outgoing t a' b' v| ≤
    25 + (partialNorm 0 + (partialNorm 1 +
      (partialNorm 2 + (partialNorm 3 + (partialNorm 4 + partialNorm 5)))))
  linarith

attribute [local fun_prop] q_differentiable es_differentiable enu_differentiable

theorem coupling_hasDerivAt_v (u a b v : ℝ) :
    HasDerivAt (coupling u a b) (incoming u a b v) v := by
  have hen : Differentiable ℝ (C_en u a) := by unfold C_en; fun_prop
  have hex : Differentiable ℝ (C_ex u b) := by unfold C_ex; fun_prop
  have hst : Differentiable ℝ (C_st u) := by unfold C_st; fun_prop
  exact ((hen v).hasDerivAt.add (hex v).hasDerivAt).add (hst v).hasDerivAt

theorem coupling_hasDerivAt_u (u a b v : ℝ) :
    HasDerivAt (fun t => coupling t a b v) (outgoing u a b v) u := by
  have hen : Differentiable ℝ (fun t => C_en t a v) := by unfold C_en; fun_prop
  have hex : Differentiable ℝ (fun t => C_ex t b v) := by unfold C_ex; fun_prop
  have hst : Differentiable ℝ (fun t => C_st t v) := by unfold C_st; fun_prop
  exact ((hen u).hasDerivAt.add (hex u).hasDerivAt).add (hst u).hasDerivAt

/-- The entire dependence on a state shared by two consecutive stages.
The outgoing stage's own regularizer is constant in this coordinate. -/
def adjacentSlice (u a b a' b' v t : ℝ) : ℝ :=
  stage c_R u a b t + coupling t a' b' v

theorem adjacentSlice_hasDerivAt (u a b a' b' v t : ℝ) :
    HasDerivAt (adjacentSlice u a b a' b' v)
      (incoming u a b t + deriv (R c_R) t + outgoing t a' b' v) t := by
  have hR := ((R_contDiff c_R).differentiable (by simp) t).hasDerivAt
  exact ((coupling_hasDerivAt_v u a b t).add hR).add (coupling_hasDerivAt_u t a' b' v)

theorem incoming_low_bound {t : ℝ} (ht : t ≤ 1 / 5) (u a b : ℝ) :
    incoming u a b t ≤ 43 / 2 := by
  unfold incoming
  rw [(low_v_identities ht u a b).1, (low_v_identities ht u a b).2.1]
  simpa only [zero_add, add_zero] using low_v_exit_bound ht u b

theorem outgoing_low_nonpos {t : ℝ} (ht : t ≤ 1 / 5) (a b v : ℝ) :
    outgoing t a b v ≤ 0 := by
  unfold outgoing
  rw [(low_u_identities ht a b v).1, (low_u_identities ht a b v).2.1]
  simpa only [zero_add, add_zero] using low_u_state_nonpos ht v

theorem outgoing_low_high_exact {t v : ℝ} (ht0 : -(1 / 10) < t)
    (ht1 : t ≤ 1 / 5) (hv : 1 ≤ v) (a b : ℝ) : outgoing t a b v = -24 := by
  unfold outgoing
  rw [(low_u_identities ht1 a b v).1, (low_u_identities ht1 a b v).2.1]
  simpa only [zero_add, add_zero] using low_high_state_exact ht0 ht1 hv

/-- Phase margin (i) for the actual adjacent-stage objective. -/
theorem adjacent_phase_left (u a b a' b' v : ℝ) {t : ℝ} (ht : t ≤ -(1 / 10)) :
    deriv (adjacentSlice u a b a' b' v) t ≤ -1 := by
  rw [(adjacentSlice_hasDerivAt u a b a' b' v t).deriv, deriv_R_left ht]
  have hin := incoming_low_bound (by linarith : t ≤ 1 / 5) u a b
  have hout := outgoing_low_nonpos (by linarith : t ≤ 1 / 5) a' b' v
  linarith

/-- Phase margin (ii), using the finite constant defined by the actual six
supremum norms, rather than assuming a bound on state derivatives. -/
theorem adjacent_phase_transition (u a b a' b' v : ℝ) {t : ℝ}
    (ht0 : 1 / 5 < t) (ht1 : t < 1) :
    deriv (adjacentSlice u a b a' b' v) t ≤ -1 := by
  rw [(adjacentSlice_hasDerivAt u a b a' b' v t).deriv,
    deriv_R_transition ht0.le ht1.le]
  have hbound := incoming_outgoing_bound u a b t a' b' v
  have hle := (abs_le.mp hbound).2
  linarith

/-- Phase margin (iii) for the actual adjacent-stage objective. -/
theorem adjacent_phase_out_of_order (u a b a' b' : ℝ) {t v : ℝ}
    (ht0 : -(1 / 10) < t) (ht1 : t ≤ 1 / 5) (hv : 1 ≤ v) :
    deriv (adjacentSlice u a b a' b' v) t ≤ -1 := by
  rw [(adjacentSlice_hasDerivAt u a b a' b' v t).deriv,
    outgoing_low_high_exact ht0 ht1 hv a' b']
  have hin := incoming_low_bound ht1 u a b
  have hR := deriv_R_nonpos (by linarith [c_R_ge_twenty_five] : -1 ≤ c_R) t
  linarith

/-- Literal fixed seed and finite stage sum from the current construction. -/
abbrev previous {m : ℕ} (s : Fin m → ℝ) (i : Fin m) : ℝ :=
  NCCLowerBound.Simplified.Composite.previousMemory s i

def outerValue {m : ℕ} (s a b : Fin m → ℝ) : ℝ :=
  ∑ j : Fin m, stage c_R (previous s j) (a j) (b j) (s j)

def stateLine {m : ℕ} (s : Fin m → ℝ) (i : Fin m) (t : ℝ) : Fin m → ℝ :=
  fun j => if j = i then t else s j

def coordinateValue {m : ℕ} (s a b : Fin m → ℝ) (i : Fin m) (t : ℝ) : ℝ :=
  outerValue (stateLine s i t) a b

private theorem previous_stateLine_fixed {m : ℕ} (s : Fin m → ℝ) (i j : Fin m)
    (t : ℝ) (hj : j.val ≠ i.val + 1) :
    previous (stateLine s i t) j = previous s j := by
  unfold previous NCCLowerBound.Simplified.Composite.previousMemory
  split
  · rfl
  · rename_i h0
    have hne : (⟨j.val - 1, by omega⟩ : Fin m) ≠ i := by
      intro heq
      have hval := congrArg Fin.val heq
      simp only at hval
      omega
    simp only [stateLine, if_neg hne]

private theorem previous_stateLine_next {m : ℕ} (s : Fin m → ℝ) (i j : Fin m)
    (t : ℝ) (hj : j.val = i.val + 1) : previous (stateLine s i t) j = t := by
  have h0 : j.val ≠ 0 := by omega
  have hp : (⟨j.val - 1, by omega⟩ : Fin m) = i := by
    apply Fin.ext
    simp only
    omega
  simp [previous, NCCLowerBound.Simplified.Composite.previousMemory, h0, hp, stateLine]

def nextContribution {m : ℕ} (s a b : Fin m → ℝ) (i : Fin m) : ℝ :=
  if hi : i.val + 1 < m then
    outgoing (s i) (a ⟨i.val + 1, hi⟩) (b ⟨i.val + 1, hi⟩) (s ⟨i.val + 1, hi⟩)
  else 0

private theorem sum_nextContribution {m : ℕ} (s a b : Fin m → ℝ) (i : Fin m) :
    (∑ j : Fin m, if j.val = i.val + 1 then outgoing (s i) (a j) (b j) (s j) else 0) =
      nextContribution s a b i := by
  classical
  unfold nextContribution
  split
  · rename_i hi
    let j : Fin m := ⟨i.val + 1, hi⟩
    rw [Finset.sum_eq_single j]
    · simp [j]
    · intro k _ hkj
      have hv : k.val ≠ i.val + 1 := by
        intro heq
        exact hkj (Fin.ext heq)
      simp only [if_neg hv]
    · simp
  · rename_i hi
    apply Finset.sum_eq_zero
    intro j _
    have hne : j.val ≠ i.val + 1 := by omega
    simp only [if_neg hne]

/-- Exact differentiation of the complete finite sum along any state
coordinate. Boundary stages are included, with no extra state premises. -/
theorem coordinateValue_hasDerivAt {m : ℕ} (s a b : Fin m → ℝ) (i : Fin m) :
    HasDerivAt (coordinateValue s a b i)
      (incoming (previous s i) (a i) (b i) (s i) + deriv (R c_R) (s i) +
        nextContribution s a b i) (s i) := by
  let inc := incoming (previous s i) (a i) (b i) (s i) + deriv (R c_R) (s i)
  have hterm : ∀ j : Fin m, HasDerivAt
      (fun t => stage c_R (previous (stateLine s i t) j) (a j) (b j) (stateLine s i t j))
      ((if j = i then inc else 0) +
        (if j.val = i.val + 1 then outgoing (s i) (a j) (b j) (s j) else 0)) (s i) := by
    intro j
    by_cases hji : j = i
    · subst j
      have hn : i.val ≠ i.val + 1 := by omega
      simp only [if_neg hn, add_zero, ite_true]
      have heq :
          (fun t => stage c_R (previous (stateLine s i t) i) (a i) (b i) (stateLine s i t i)) =
          fun t => stage c_R (previous s i) (a i) (b i) t := by
        funext t
        rw [previous_stateLine_fixed s i i t hn]
        simp [stateLine]
      rw [heq]
      exact (coupling_hasDerivAt_v (previous s i) (a i) (b i) (s i)).add
        ((R_contDiff c_R).differentiable (by simp) (s i)).hasDerivAt
    · by_cases hjn : j.val = i.val + 1
      · simp only [if_neg hji, if_pos hjn, zero_add]
        have heq :
            (fun t => stage c_R (previous (stateLine s i t) j) (a j) (b j) (stateLine s i t j)) =
            fun t => coupling t (a j) (b j) (s j) + R c_R (s j) := by
          funext t
          rw [previous_stateLine_next s i j t hjn]
          simp only [stateLine, if_neg hji, stage]
        rw [heq]
        exact (coupling_hasDerivAt_u (s i) (a j) (b j) (s j)).add_const _
      · simp only [if_neg hji, if_neg hjn, zero_add]
        have heq :
            (fun t => stage c_R (previous (stateLine s i t) j) (a j) (b j) (stateLine s i t j)) =
            fun _ => stage c_R (previous s j) (a j) (b j) (s j) := by
          funext t
          rw [previous_stateLine_fixed s i j t hjn]
          simp only [stateLine, if_neg hji]
        rw [heq]
        exact hasDerivAt_const (s i) _
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun j _ => hterm j)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    sum_nextContribution] at hsum
  exact hsum

theorem outgoing_zero (u : ℝ) : outgoing u 0 0 0 = 0 := by
  have he : e_nu 0 = 0 := e_nu_eq_self (by norm_num)
  have hq : q 0 = 0 := q_eq_zero (by norm_num)
  simp only [outgoing, deriv_C_en_u, deriv_C_ex_u, deriv_C_st_u, he, hq]
  ring

/-- The complete state derivative equals that of its literal adjacent-stage
slice, including a zero outgoing slice at the final coordinate. -/
theorem coordinate_derivative_eq_slice {m : ℕ} (s a b : Fin m → ℝ) (i : Fin m) :
    deriv (coordinateValue s a b i) (s i) =
      if hi : i.val + 1 < m then
        deriv (adjacentSlice (previous s i) (a i) (b i)
          (a ⟨i.val + 1, hi⟩) (b ⟨i.val + 1, hi⟩) (s ⟨i.val + 1, hi⟩)) (s i)
      else deriv (adjacentSlice (previous s i) (a i) (b i) 0 0 0) (s i) := by
  rw [(coordinateValue_hasDerivAt s a b i).deriv]
  unfold nextContribution
  split
  · rw [(adjacentSlice_hasDerivAt _ _ _ _ _ _ _).deriv]
  · rw [(adjacentSlice_hasDerivAt _ _ _ _ _ _ _).deriv, outgoing_zero]

/-- Phase margin (i) for the complete current finite stage sum. -/
theorem outer_phase_left {m : ℕ} (s a b : Fin m → ℝ) (i : Fin m)
    (hi : s i ≤ -(1 / 10)) : deriv (coordinateValue s a b i) (s i) ≤ -1 := by
  rw [coordinate_derivative_eq_slice]
  split <;> exact adjacent_phase_left _ _ _ _ _ _ hi

/-- Phase margin (ii) for the complete current finite stage sum. -/
theorem outer_phase_transition {m : ℕ} (s a b : Fin m → ℝ) (i : Fin m)
    (hi0 : 1 / 5 < s i) (hi1 : s i < 1) :
    deriv (coordinateValue s a b i) (s i) ≤ -1 := by
  rw [coordinate_derivative_eq_slice]
  split <;> exact adjacent_phase_transition _ _ _ _ _ _ hi0 hi1

/-- Phase margin (iii) for the complete current finite stage sum. The
zero-based `i` and `i+1` encode the paper's predecessor/current pair. -/
theorem outer_phase_out_of_order {m : ℕ} (s a b : Fin m → ℝ) (i : Fin m)
    (hinext : i.val + 1 < m) (hi0 : -(1 / 10) < s i) (hi1 : s i ≤ 1 / 5)
    (hnext : 1 ≤ s ⟨i.val + 1, hinext⟩) :
    deriv (coordinateValue s a b i) (s i) ≤ -1 := by
  rw [coordinate_derivative_eq_slice, dif_pos hinext]
  exact adjacent_phase_out_of_order _ _ _ _ _ hi0 hi1 hnext

end

end NCC.Construction.Outer
