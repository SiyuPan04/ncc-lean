import NCPLVerification.ResidualKernelSmoothness
import NCPLVerification.CarmonActivation
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Residual perspectives and their outer-gate compositions
-/

namespace NCPLVerification

noncomputable section

def twoConeGradient (g : ℝ → ℝ → ℝ) (rho u v : ℝ) : ℝ :=
  if 0 < rho then rho * g (u / rho) (v / rho) else 0

private theorem twoConeGradient_abs_sub_le_ordered
    (g : ℝ → ℝ → ℝ) (C L S K : ℝ)
    (hC0 : 0 ≤ C) (hL0 : 0 ≤ L) (hS0 : 0 ≤ S) (hK0 : 0 ≤ K)
    (hLK : L ≤ K) (hCSK : C + S ≤ K)
    (habs : ∀ u v, |g u v| ≤ C)
    (hlip : ∀ u v u' v',
      |g u v - g u' v'| ≤ L * (|u - u'| + |v - v'|))
    (hscale : ∀ {r s u v : ℝ}, 0 < r → r ≤ s →
      r * |g (u / r) (v / r) - g (u / s) (v / s)| ≤ S * (s - r))
    {r s u v u' v' : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) :
    |twoConeGradient g r u v - twoConeGradient g s u' v'| ≤
      K * (|r - s| + |u - u'| + |v - v'|) := by
  have hs : 0 ≤ s := hr.trans hrs
  have hCK : C ≤ K := by linarith
  rcases hr.eq_or_lt with rfl | hrpos
  · by_cases hspos : 0 < s
    · simp only [twoConeGradient, lt_self_iff_false, if_false, if_pos hspos,
        zero_sub, abs_neg, abs_mul, abs_of_pos hspos]
      have hg := habs (u' / s) (v' / s)
      have hmain : s * |g (u' / s) (v' / s)| ≤ K * s := by
        calc
          s * |g (u' / s) (v' / s)| ≤ s * C :=
            mul_le_mul_of_nonneg_left hg hspos.le
          _ = C * s := by ring
          _ ≤ K * s := mul_le_mul_of_nonneg_right hCK hspos.le
      nlinarith [abs_nonneg (u - u'), abs_nonneg (v - v')]
    · have hseq : s = 0 := le_antisymm (le_of_not_gt hspos) hs
      subst s
      simp only [twoConeGradient, lt_self_iff_false, if_false, sub_self,
        abs_zero, zero_add]
      exact mul_nonneg hK0 (add_nonneg (abs_nonneg _) (abs_nonneg _))
  · have hspos : 0 < s := hrpos.trans_le hrs
    simp only [twoConeGradient, if_pos hrpos, if_pos hspos]
    have hu : |u / r - u' / r| = |u - u'| / r := by
      rw [show u / r - u' / r = (u - u') / r by ring,
        abs_div, abs_of_pos hrpos]
    have hv : |v / r - v' / r| = |v - v'| / r := by
      rw [show v / r - v' / r = (v - v') / r by ring,
        abs_div, abs_of_pos hrpos]
    have hsame0 := hlip (u / r) (v / r) (u' / r) (v' / r)
    rw [hu, hv] at hsame0
    have hsame :
        r * |g (u / r) (v / r) - g (u' / r) (v' / r)| ≤
          L * (|u - u'| + |v - v'|) := by
      calc
        r * |g (u / r) (v / r) - g (u' / r) (v' / r)| ≤
            r * (L * (|u - u'| / r + |v - v'| / r)) :=
          mul_le_mul_of_nonneg_left hsame0 hrpos.le
        _ = L * (|u - u'| + |v - v'|) := by
          field_simp [hrpos.ne']
    have hrad := hscale hrpos hrs (u := u') (v := v')
    have hsplit := abs_add_le
      (g (u / r) (v / r) - g (u' / r) (v' / r))
      (g (u' / r) (v' / r) - g (u' / s) (v' / s))
    have heq :
        g (u / r) (v / r) - g (u' / s) (v' / s) =
          (g (u / r) (v / r) - g (u' / r) (v' / r)) +
            (g (u' / r) (v' / r) - g (u' / s) (v' / s)) := by ring
    have hfirst :
        r * |g (u / r) (v / r) - g (u' / s) (v' / s)| ≤
          L * (|u - u'| + |v - v'|) + S * (s - r) := by
      rw [heq]
      calc
        r * |(g (u / r) (v / r) - g (u' / r) (v' / r)) +
            (g (u' / r) (v' / r) - g (u' / s) (v' / s))| ≤
            r * (|g (u / r) (v / r) - g (u' / r) (v' / r)| +
              |g (u' / r) (v' / r) - g (u' / s) (v' / s)|) :=
          mul_le_mul_of_nonneg_left hsplit hrpos.le
        _ = r * |g (u / r) (v / r) - g (u' / r) (v' / r)| +
            r * |g (u' / r) (v' / r) - g (u' / s) (v' / s)| := by ring
        _ ≤ L * (|u - u'| + |v - v'|) + S * (s - r) :=
          add_le_add hsame hrad
    have hdecomp :
        r * g (u / r) (v / r) - s * g (u' / s) (v' / s) =
          r * (g (u / r) (v / r) - g (u' / s) (v' / s)) +
            (r - s) * g (u' / s) (v' / s) := by ring
    rw [hdecomp]
    have htri := abs_add_le
      (r * (g (u / r) (v / r) - g (u' / s) (v' / s)))
      ((r - s) * g (u' / s) (v' / s))
    rw [abs_mul, abs_of_pos hrpos, abs_mul,
      abs_of_nonpos (sub_nonpos.mpr hrs), neg_sub] at htri
    have hg := habs (u' / s) (v' / s)
    have hsecond : (s - r) * |g (u' / s) (v' / s)| ≤ C * (s - r) := by
      calc
        (s - r) * |g (u' / s) (v' / s)| ≤ (s - r) * C :=
          mul_le_mul_of_nonneg_left hg (sub_nonneg.mpr hrs)
        _ = C * (s - r) := by ring
    rw [abs_of_nonpos (sub_nonpos.mpr hrs), neg_sub]
    have hq0 : 0 ≤ |u - u'| + |v - v'| := by positivity
    have hd0 : 0 ≤ s - r := sub_nonneg.mpr hrs
    nlinarith

theorem twoConeGradient_abs_sub_le
    (g : ℝ → ℝ → ℝ) (C L S K : ℝ)
    (hC0 : 0 ≤ C) (hL0 : 0 ≤ L) (hS0 : 0 ≤ S) (hK0 : 0 ≤ K)
    (hLK : L ≤ K) (hCSK : C + S ≤ K)
    (habs : ∀ u v, |g u v| ≤ C)
    (hlip : ∀ u v u' v',
      |g u v - g u' v'| ≤ L * (|u - u'| + |v - v'|))
    (hscale : ∀ {r s u v : ℝ}, 0 < r → r ≤ s →
      r * |g (u / r) (v / r) - g (u / s) (v / s)| ≤ S * (s - r))
    {r s u v u' v' : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |twoConeGradient g r u v - twoConeGradient g s u' v'| ≤
      K * (|r - s| + |u - u'| + |v - v'|) := by
  by_cases hrs : r ≤ s
  · exact twoConeGradient_abs_sub_le_ordered g C L S K hC0 hL0 hS0 hK0
      hLK hCSK habs hlip hscale hr hrs
  · have h := twoConeGradient_abs_sub_le_ordered g C L S K hC0 hL0 hS0 hK0
      hLK hCSK habs hlip hscale hs (le_of_not_ge hrs)
      (u := u') (v := v') (u' := u) (v' := v)
    simpa [abs_sub_comm, add_comm, add_left_comm, add_assoc] using h

def residualConeValue (rho u v : ℝ) : ℝ :=
  if 0 < rho then rho ^ 2 * residualSqKernel (u / rho) (v / rho) else 0

def residualConeGradU (rho u v : ℝ) : ℝ :=
  twoConeGradient residualGradS rho u v

def residualConeGradV (rho u v : ℝ) : ℝ :=
  twoConeGradient residualGradT rho u v

def residualConeGradRho (rho u v : ℝ) : ℝ :=
  twoConeGradient residualRadialField rho u v

theorem hasDerivAt_residualConeValue_u {rho u v : ℝ} (hrho : 0 ≤ rho) :
    HasDerivAt (fun q ↦ residualConeValue rho q v)
      (residualConeGradU rho u v) u := by
  rcases hrho.eq_or_lt with rfl | hpos
  · simpa only [residualConeValue, lt_self_iff_false, if_false,
      residualConeGradU, twoConeGradient] using hasDerivAt_const u 0
  · have hratio : HasDerivAt (fun q : ℝ ↦ q / rho) (1 / rho) u :=
      (hasDerivAt_id u).div_const rho
    have hk := (hasDerivAt_residualSqKernel_left (u / rho) (v / rho)).comp
      u hratio
    have hmul := (hasDerivAt_const u (rho ^ 2)).mul hk
    have hfun :
        (fun q : ℝ ↦ residualConeValue rho q v) =
          (fun _ : ℝ ↦ rho ^ 2) *
            ((fun s : ℝ ↦ residualSqKernel s (v / rho)) ∘
              fun q : ℝ ↦ q / rho) := by
      funext q
      change residualConeValue rho q v =
        rho ^ 2 * residualSqKernel (q / rho) (v / rho)
      rw [residualConeValue, if_pos hpos]
    have hderiv :
        residualConeGradU rho u v =
          0 * residualSqKernel (u / rho) (v / rho) +
            rho ^ 2 * (residualGradS (u / rho) (v / rho) * (1 / rho)) := by
      unfold residualConeGradU twoConeGradient
      rw [if_pos hpos]
      field_simp [hpos.ne']
      ring
    rw [hfun, hderiv]
    exact hmul

theorem hasDerivAt_residualConeValue_v {rho u v : ℝ} (hrho : 0 ≤ rho) :
    HasDerivAt (fun q ↦ residualConeValue rho u q)
      (residualConeGradV rho u v) v := by
  rcases hrho.eq_or_lt with rfl | hpos
  · simpa only [residualConeValue, lt_self_iff_false, if_false,
      residualConeGradV, twoConeGradient] using hasDerivAt_const v 0
  · have hratio : HasDerivAt (fun q : ℝ ↦ q / rho) (1 / rho) v :=
      (hasDerivAt_id v).div_const rho
    have hk := (hasDerivAt_residualSqKernel_right (u / rho) (v / rho)).comp
      v hratio
    have hmul := (hasDerivAt_const v (rho ^ 2)).mul hk
    have hfun :
        (fun q : ℝ ↦ residualConeValue rho u q) =
          (fun _ : ℝ ↦ rho ^ 2) *
            ((fun t : ℝ ↦ residualSqKernel (u / rho) t) ∘
              fun q : ℝ ↦ q / rho) := by
      funext q
      change residualConeValue rho u q =
        rho ^ 2 * residualSqKernel (u / rho) (q / rho)
      rw [residualConeValue, if_pos hpos]
    have hderiv :
        residualConeGradV rho u v =
          0 * residualSqKernel (u / rho) (v / rho) +
            rho ^ 2 * (residualGradT (u / rho) (v / rho) * (1 / rho)) := by
      unfold residualConeGradV twoConeGradient
      rw [if_pos hpos]
      field_simp [hpos.ne']
      ring
    rw [hfun, hderiv]
    exact hmul

private theorem residualConeValue_abs_le_all (rho u v : ℝ) :
    |residualConeValue rho u v| ≤ 4 * rho ^ 2 := by
  by_cases h : 0 ≤ rho
  · rcases h.eq_or_lt with rfl | hpos
    · simp [residualConeValue]
    · rw [residualConeValue, if_pos hpos, abs_mul,
        abs_of_nonneg (sq_nonneg rho)]
      simpa [mul_comm] using
        mul_le_mul_of_nonneg_left
          (residualSqKernel_abs_le_four (u / rho) (v / rho)) (sq_nonneg rho)
  · have hn : ¬0 < rho := not_lt_of_ge (le_of_not_ge h)
    simpa [residualConeValue, hn] using
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg rho)

theorem hasDerivAt_residualConeValue_rho_zero (u v : ℝ) :
    HasDerivAt (fun q ↦ residualConeValue q u v) 0 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hpow : (fun q : ℝ ↦ q ^ 2) =o[nhds 0] fun q ↦ q :=
    Asymptotics.isLittleO_pow_id (by norm_num)
  refine (Asymptotics.IsBigO.of_bound 4 ?_).trans_isLittleO hpow
  filter_upwards [] with q
  have h := residualConeValue_abs_le_all q u v
  have hz : residualConeValue 0 u v = 0 := by simp [residualConeValue]
  simpa only [hz, zero_add, smul_zero, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg q)] using h

private theorem hasDerivAt_residualSqKernel_comp
    {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun q ↦ residualSqKernel (f q) (g q))
      (residualGradS (f x) (g x) * f' +
        residualGradT (f x) (g x) * g') x := by
  have hs := (hasDerivAt_sigma (f x)).comp x hf
  have hb := (hasDerivAt_beta (g x)).comp x hg
  have hi := (hasDerivAt_const x (1 : ℝ)).sub (hs.mul hb)
  have ho := (hasDerivAt_posPart_sq
    (1 - sigma (f x) * beta (g x))).comp x hi
  change HasDerivAt (fun q ↦ residualSqKernel (f q) (g q)) _ x at ho
  apply ho.congr_deriv
  simp only [residualGradS, residualGradT, gateResidual,
    Function.comp_apply]
  ring

theorem hasDerivAt_residualConeValue_rho {rho u v : ℝ} (hrho : 0 ≤ rho) :
    HasDerivAt (fun q ↦ residualConeValue q u v)
      (residualConeGradRho rho u v) rho := by
  rcases hrho.eq_or_lt with rfl | hpos
  · simpa [residualConeGradRho, twoConeGradient] using
      hasDerivAt_residualConeValue_rho_zero u v
  · have hsq := (hasDerivAt_id rho).mul (hasDerivAt_id rho)
    have hru :=
      (hasDerivAt_const rho u).div (hasDerivAt_id rho) hpos.ne'
    change HasDerivAt (fun q : ℝ ↦ u / q)
      ((0 * rho - u * 1) / rho ^ 2) rho at hru
    have hru' : HasDerivAt (fun q : ℝ ↦ u / q) (-u / rho ^ 2) rho := by
      convert hru using 1
      ring
    have hrv :=
      (hasDerivAt_const rho v).div (hasDerivAt_id rho) hpos.ne'
    change HasDerivAt (fun q : ℝ ↦ v / q)
      ((0 * rho - v * 1) / rho ^ 2) rho at hrv
    have hrv' : HasDerivAt (fun q : ℝ ↦ v / q) (-v / rho ^ 2) rho := by
      convert hrv using 1
      ring
    have hk := hasDerivAt_residualSqKernel_comp hru' hrv'
    have hmul := hsq.mul hk
    have hgrad :
        residualConeGradRho rho u v =
          (1 * rho + rho * 1) * residualSqKernel (u / rho) (v / rho) +
            (rho * rho) *
              (residualGradS (u / rho) (v / rho) * (-u / rho ^ 2) +
                residualGradT (u / rho) (v / rho) * (-v / rho ^ 2)) := by
      unfold residualConeGradRho twoConeGradient residualRadialField
      rw [if_pos hpos]
      unfold residualGradS residualGradT
      unfold residualWeightedGradS residualWeightedGradT
      unfold sigmaWeightedDeriv betaWeightedDeriv
      field_simp [hpos.ne']
      ring
    rw [hgrad]
    apply hmul.congr_of_eventuallyEq
    filter_upwards [(isOpen_Ioi.mem_nhds hpos)] with q hq
    change residualConeValue q u v =
      (q * q) * residualSqKernel (u / q) (v / q)
    have hq' : 0 < q := hq
    simp [residualConeValue, hq', pow_two]

def residualFirstConeValue (rho v : ℝ) : ℝ :=
  residualConeValue rho rho v

def residualFirstConeGradRho (rho v : ℝ) : ℝ :=
  residualConeGradRho rho rho v + residualConeGradU rho rho v

theorem hasDerivAt_residualFirstConeValue {rho v : ℝ} (hrho : 0 ≤ rho) :
    HasDerivAt (fun q ↦ residualFirstConeValue q v)
      (residualFirstConeGradRho rho v) rho := by
  rcases hrho.eq_or_lt with rfl | hpos
  · rw [hasDerivAt_iff_isLittleO_nhds_zero]
    have hpow : (fun q : ℝ ↦ q ^ 2) =o[nhds 0] fun q ↦ q :=
      Asymptotics.isLittleO_pow_id (by norm_num)
    refine (Asymptotics.IsBigO.of_bound 4 ?_).trans_isLittleO hpow
    filter_upwards [] with q
    have h := residualConeValue_abs_le_all q q v
    have hz : residualFirstConeValue 0 v = 0 := by
      simp [residualFirstConeValue, residualConeValue]
    have hz' : residualConeValue 0 0 v = 0 := by
      simp [residualConeValue]
    have hgz : residualFirstConeGradRho 0 v = 0 := by
      simp [residualFirstConeGradRho, residualConeGradRho,
        residualConeGradU, twoConeGradient]
    simpa only [residualFirstConeValue, hz, hz', hgz, zero_add, smul_zero,
      sub_zero, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q)] using h
  · have hsq := (hasDerivAt_id rho).mul (hasDerivAt_id rho)
    have hrv :=
      (hasDerivAt_const rho v).div (hasDerivAt_id rho) hpos.ne'
    change HasDerivAt (fun q : ℝ ↦ v / q)
      ((0 * rho - v * 1) / rho ^ 2) rho at hrv
    have hrv' : HasDerivAt (fun q : ℝ ↦ v / q) (-v / rho ^ 2) rho := by
      convert hrv using 1
      ring
    have hk := hasDerivAt_residualSqKernel_comp
      (hasDerivAt_const rho (1 : ℝ)) hrv'
    have hmul := hsq.mul hk
    have hgrad :
        residualFirstConeGradRho rho v =
          (1 * rho + rho * 1) * residualSqKernel 1 (v / rho) +
            (rho * rho) *
              (residualGradS 1 (v / rho) * 0 +
                residualGradT 1 (v / rho) * (-v / rho ^ 2)) := by
      unfold residualFirstConeGradRho residualConeGradRho
        residualConeGradU twoConeGradient residualRadialField
      simp only [if_pos hpos]
      unfold residualGradS residualGradT
      unfold residualWeightedGradS residualWeightedGradT
      unfold sigmaWeightedDeriv betaWeightedDeriv
      field_simp [hpos.ne']
      ring
    rw [hgrad]
    apply hmul.congr_of_eventuallyEq
    filter_upwards [(isOpen_Ioi.mem_nhds hpos)] with q hq
    change residualFirstConeValue q v =
      (q * q) * residualSqKernel 1 (v / q)
    have hq' : 0 < q := hq
    rw [residualFirstConeValue, residualConeValue, if_pos hq',
      div_self hq'.ne']
    ring

theorem residualConeValue_abs_le {rho u v : ℝ} (hrho : 0 ≤ rho) :
    |residualConeValue rho u v| ≤ 4 * rho ^ 2 := by
  rcases hrho.eq_or_lt with rfl | hpos
  · simp [residualConeValue]
  · rw [residualConeValue, if_pos hpos, abs_mul,
      abs_of_nonneg (sq_nonneg rho)]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left
        (residualSqKernel_abs_le_four (u / rho) (v / rho)) (sq_nonneg rho)

theorem residualConeGradU_abs_le {rho u v : ℝ} (hrho : 0 ≤ rho) :
    |residualConeGradU rho u v| ≤ 16 * rho := by
  rcases hrho.eq_or_lt with rfl | hpos
  · simp [residualConeGradU, twoConeGradient]
  · rw [residualConeGradU, twoConeGradient, if_pos hpos, abs_mul,
      abs_of_pos hpos]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left
        (residualGradS_abs_le_sixteen (u / rho) (v / rho)) hpos.le

theorem residualConeGradV_abs_le {rho u v : ℝ} (hrho : 0 ≤ rho) :
    |residualConeGradV rho u v| ≤ 8 * rho := by
  rcases hrho.eq_or_lt with rfl | hpos
  · simp [residualConeGradV, twoConeGradient]
  · rw [residualConeGradV, twoConeGradient, if_pos hpos, abs_mul,
      abs_of_pos hpos]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left
        (residualGradT_abs_le_eight (u / rho) (v / rho)) hpos.le

theorem residualConeGradRho_abs_le {rho u v : ℝ} (hrho : 0 ≤ rho) :
    |residualConeGradRho rho u v| ≤ 40 * rho := by
  rcases hrho.eq_or_lt with rfl | hpos
  · simp [residualConeGradRho, twoConeGradient]
  · rw [residualConeGradRho, twoConeGradient, if_pos hpos, abs_mul,
      abs_of_pos hpos]
    simpa [mul_comm] using
      mul_le_mul_of_nonneg_left
        (residualRadialField_abs_le_forty (u / rho) (v / rho)) hpos.le

theorem residualConeGradU_abs_sub_le {r s u v u' v' : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |residualConeGradU r u v - residualConeGradU s u' v'| ≤
      400 * (|r - s| + |u - u'| + |v - v'|) := by
  unfold residualConeGradU
  exact twoConeGradient_abs_sub_le residualGradS 16 200 300 400
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) residualGradS_abs_le_sixteen
    residualGradS_abs_sub_le residualGradS_scale_abs_sub_le hr hs

theorem residualConeGradV_abs_sub_le {r s u v u' v' : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |residualConeGradV r u v - residualConeGradV s u' v'| ≤
      400 * (|r - s| + |u - u'| + |v - v'|) := by
  unfold residualConeGradV
  exact twoConeGradient_abs_sub_le residualGradT 8 200 300 400
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) residualGradT_abs_le_eight
    residualGradT_abs_sub_le residualGradT_scale_abs_sub_le hr hs

theorem residualConeGradRho_abs_sub_le {r s u v u' v' : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |residualConeGradRho r u v - residualConeGradRho s u' v'| ≤
      1600 * (|r - s| + |u - u'| + |v - v'|) := by
  unfold residualConeGradRho
  exact twoConeGradient_abs_sub_le residualRadialField 40 1000 1500 1600
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) residualRadialField_abs_le_forty
    residualRadialField_abs_sub_le residualRadialField_scale_abs_sub_le hr hs

theorem deriv_carmonRhoProfile (t : ℝ) :
    deriv carmonRhoProfile t = carmonRhoProfileDeriv t :=
  (hasDerivAt_carmonRhoProfile t).deriv

theorem differentiable_carmonRhoProfile : Differentiable ℝ carmonRhoProfile :=
  fun t ↦ (hasDerivAt_carmonRhoProfile t).differentiableAt

theorem deriv_carmonRhoProfileDeriv (t : ℝ) :
    deriv carmonRhoProfileDeriv t = carmonRhoProfileSecond t :=
  (hasDerivAt_carmonRhoProfileDeriv t).deriv

theorem differentiable_carmonRhoProfileDeriv :
    Differentiable ℝ carmonRhoProfileDeriv :=
  fun t ↦ (hasDerivAt_carmonRhoProfileDeriv t).differentiableAt

theorem carmonRhoProfile_lipschitz :
    LipschitzWith (64 : NNReal) carmonRhoProfile := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_carmonRhoProfile
  intro t
  rw [deriv_carmonRhoProfile, ← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using abs_carmonRhoProfileDeriv_le_sixtyFour t

theorem carmonRhoProfile_abs_sub_le (s t : ℝ) :
    |carmonRhoProfile s - carmonRhoProfile t| ≤ 64 * |s - t| := by
  simpa [Real.norm_eq_abs] using carmonRhoProfile_lipschitz.norm_sub_le s t

theorem carmonRhoProfileDeriv_lipschitz :
    LipschitzWith (1152 : NNReal) carmonRhoProfileDeriv := by
  apply lipschitzWith_of_nnnorm_deriv_le differentiable_carmonRhoProfileDeriv
  intro t
  rw [deriv_carmonRhoProfileDeriv, ← NNReal.coe_le_coe]
  simpa [Real.norm_eq_abs] using abs_carmonRhoProfileSecond_le_elevenFiftyTwo t

theorem carmonRhoProfileDeriv_abs_sub_le (s t : ℝ) :
    |carmonRhoProfileDeriv s - carmonRhoProfileDeriv t| ≤
      1152 * |s - t| := by
  simpa [Real.norm_eq_abs] using
    carmonRhoProfileDeriv_lipschitz.norm_sub_le s t

def residualProfileGradP (p u v : ℝ) : ℝ :=
  carmonRhoProfileDeriv p *
    residualConeGradRho (carmonRhoProfile p) u v

def residualProfileGradU (p u v : ℝ) : ℝ :=
  residualConeGradU (carmonRhoProfile p) u v

def residualProfileGradV (p u v : ℝ) : ℝ :=
  residualConeGradV (carmonRhoProfile p) u v

def residualProfileValue (p u v : ℝ) : ℝ :=
  residualConeValue (carmonRhoProfile p) u v

def residualFirstProfileValue (p v : ℝ) : ℝ :=
  residualFirstConeValue (carmonRhoProfile p) v

def residualFirstProfileGradP (p v : ℝ) : ℝ :=
  carmonRhoProfileDeriv p *
    residualFirstConeGradRho (carmonRhoProfile p) v

theorem hasDerivAt_residualProfileValue_p (p u v : ℝ) :
    HasDerivAt (fun s ↦ residualProfileValue s u v)
      (residualProfileGradP p u v) p := by
  have h := (hasDerivAt_residualConeValue_rho
    (u := u) (v := v) (carmonRhoProfile_nonneg p)).comp
      p (hasDerivAt_carmonRhoProfile p)
  change HasDerivAt (fun s : ℝ ↦ residualProfileValue s u v) _ p at h
  apply h.congr_deriv
  simp [residualProfileGradP]
  ring

theorem hasDerivAt_residualProfileValue_u (p u v : ℝ) :
    HasDerivAt (fun s ↦ residualProfileValue p s v)
      (residualProfileGradU p u v) u := by
  have h := hasDerivAt_residualConeValue_u
    (u := u) (v := v) (carmonRhoProfile_nonneg p)
  change HasDerivAt (fun s : ℝ ↦ residualProfileValue p s v) _ u at h
  exact h

theorem hasDerivAt_residualProfileValue_v (p u v : ℝ) :
    HasDerivAt (fun s ↦ residualProfileValue p u s)
      (residualProfileGradV p u v) v := by
  have h := hasDerivAt_residualConeValue_v
    (u := u) (v := v) (carmonRhoProfile_nonneg p)
  change HasDerivAt (fun s : ℝ ↦ residualProfileValue p u s) _ v at h
  exact h

theorem hasDerivAt_residualFirstProfileValue_p (p v : ℝ) :
    HasDerivAt (fun s ↦ residualFirstProfileValue s v)
      (residualFirstProfileGradP p v) p := by
  have h := (hasDerivAt_residualFirstConeValue
    (v := v) (carmonRhoProfile_nonneg p)).comp
      p (hasDerivAt_carmonRhoProfile p)
  change HasDerivAt (fun s : ℝ ↦ residualFirstProfileValue s v) _ p at h
  apply h.congr_deriv
  simp [residualFirstProfileGradP]
  ring

def residualProfileSmoothC : ℝ := 7000000

theorem residualProfileSmoothC_nonneg : 0 ≤ residualProfileSmoothC := by
  norm_num [residualProfileSmoothC]

theorem residualFirstConeGradRho_abs_le {rho v : ℝ} (hrho : 0 ≤ rho) :
    |residualFirstConeGradRho rho v| ≤ 56 * rho := by
  unfold residualFirstConeGradRho
  have hr := residualConeGradRho_abs_le (u := rho) (v := v) hrho
  have hu := residualConeGradU_abs_le (u := rho) (v := v) hrho
  exact (abs_add_le _ _).trans (by linarith)

theorem residualFirstConeGradRho_abs_sub_le
    {r s v v' : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |residualFirstConeGradRho r v - residualFirstConeGradRho s v'| ≤
      4000 * (|r - s| + |v - v'|) := by
  unfold residualFirstConeGradRho
  have hR := residualConeGradRho_abs_sub_le hr hs
    (u := r) (v := v) (u' := s) (v' := v')
  have hU := residualConeGradU_abs_sub_le hr hs
    (u := r) (v := v) (u' := s) (v' := v')
  have htri := abs_add_le
    (residualConeGradRho r r v - residualConeGradRho s s v')
    (residualConeGradU r r v - residualConeGradU s s v')
  have heq :
      residualConeGradRho r r v + residualConeGradU r r v -
        (residualConeGradRho s s v' + residualConeGradU s s v') =
      (residualConeGradRho r r v - residualConeGradRho s s v') +
        (residualConeGradU r r v - residualConeGradU s s v') := by ring
  rw [heq]
  nlinarith [abs_nonneg (r - s), abs_nonneg (v - v')]

theorem residualFirstProfileGradP_abs_sub_le (p v p' v' : ℝ) :
    |residualFirstProfileGradP p v - residualFirstProfileGradP p' v'| ≤
      4 * residualProfileSmoothC * (|p - p'| + |v - v'|) := by
  unfold residualFirstProfileGradP
  let G := residualFirstConeGradRho
  have heq :
      carmonRhoProfileDeriv p * G (carmonRhoProfile p) v -
        carmonRhoProfileDeriv p' * G (carmonRhoProfile p') v' =
      (carmonRhoProfileDeriv p - carmonRhoProfileDeriv p') *
          G (carmonRhoProfile p) v +
        carmonRhoProfileDeriv p' *
          (G (carmonRhoProfile p) v - G (carmonRhoProfile p') v') := by
    ring
  rw [heq]
  have htri := abs_add_le
    ((carmonRhoProfileDeriv p - carmonRhoProfileDeriv p') *
      G (carmonRhoProfile p) v)
    (carmonRhoProfileDeriv p' *
      (G (carmonRhoProfile p) v - G (carmonRhoProfile p') v'))
  repeat' rw [abs_mul] at htri
  have hdp := carmonRhoProfileDeriv_abs_sub_le p p'
  have hG0 := residualFirstConeGradRho_abs_le
    (v := v) (carmonRhoProfile_nonneg p)
  have hG112 : |G (carmonRhoProfile p) v| ≤ 112 := by
    dsimp [G]
    nlinarith [carmonRhoProfile_le_two p]
  have hd' := abs_carmonRhoProfileDeriv_le_sixtyFour p'
  have hG := residualFirstConeGradRho_abs_sub_le
    (v := v) (v' := v') (carmonRhoProfile_nonneg p)
      (carmonRhoProfile_nonneg p')
  have hr := carmonRhoProfile_abs_sub_le p p'
  have hG' :
      |G (carmonRhoProfile p) v - G (carmonRhoProfile p') v'| ≤
        4000 * (64 * |p - p'| + |v - v'|) := by
    dsimp [G] at hG ⊢
    nlinarith [abs_nonneg (p - p'), abs_nonneg (v - v')]
  have h1 :
      |carmonRhoProfileDeriv p - carmonRhoProfileDeriv p'| *
          |G (carmonRhoProfile p) v| ≤
        (1152 * |p - p'|) * 112 := by gcongr
  have h2 :
      |carmonRhoProfileDeriv p'| *
          |G (carmonRhoProfile p) v - G (carmonRhoProfile p') v'| ≤
        64 * (4000 * (64 * |p - p'| + |v - v'|)) := by gcongr
  calc
    _ ≤ |carmonRhoProfileDeriv p - carmonRhoProfileDeriv p'| *
          |G (carmonRhoProfile p) v| +
        |carmonRhoProfileDeriv p'| *
          |G (carmonRhoProfile p) v - G (carmonRhoProfile p') v'| := htri
    _ ≤ (1152 * |p - p'|) * 112 +
        64 * (4000 * (64 * |p - p'| + |v - v'|)) :=
      add_le_add h1 h2
    _ ≤ 4 * residualProfileSmoothC * (|p - p'| + |v - v'|) := by
      unfold residualProfileSmoothC
      nlinarith [abs_nonneg (p - p'), abs_nonneg (v - v')]

theorem residualProfileGradP_abs_sub_le (p u v p' u' v' : ℝ) :
    |residualProfileGradP p u v - residualProfileGradP p' u' v'| ≤
      residualProfileSmoothC * (|p - p'| + |u - u'| + |v - v'|) := by
  unfold residualProfileGradP
  have heq :
      carmonRhoProfileDeriv p *
          residualConeGradRho (carmonRhoProfile p) u v -
        carmonRhoProfileDeriv p' *
          residualConeGradRho (carmonRhoProfile p') u' v' =
      (carmonRhoProfileDeriv p - carmonRhoProfileDeriv p') *
          residualConeGradRho (carmonRhoProfile p') u' v' +
        carmonRhoProfileDeriv p *
          (residualConeGradRho (carmonRhoProfile p) u v -
            residualConeGradRho (carmonRhoProfile p') u' v') := by ring
  rw [heq]
  have htri := abs_add_le
    ((carmonRhoProfileDeriv p - carmonRhoProfileDeriv p') *
      residualConeGradRho (carmonRhoProfile p') u' v')
    (carmonRhoProfileDeriv p *
      (residualConeGradRho (carmonRhoProfile p) u v -
        residualConeGradRho (carmonRhoProfile p') u' v'))
  repeat' rw [abs_mul] at htri
  have hdd := carmonRhoProfileDeriv_abs_sub_le p p'
  have hdp := abs_carmonRhoProfileDeriv_le_sixtyFour p
  have hr := carmonRhoProfile_abs_sub_le p p'
  have hg := residualConeGradRho_abs_sub_le
    (carmonRhoProfile_nonneg p) (carmonRhoProfile_nonneg p')
    (u := u) (v := v) (u' := u') (v' := v')
  have hgv0 := residualConeGradRho_abs_le (carmonRhoProfile_nonneg p')
    (u := u') (v := v')
  have hrle := carmonRhoProfile_le_two p'
  have hgv : |residualConeGradRho (carmonRhoProfile p') u' v'| ≤ 80 := by
    nlinarith
  have h1 :
      |carmonRhoProfileDeriv p - carmonRhoProfileDeriv p'| *
          |residualConeGradRho (carmonRhoProfile p') u' v'| ≤
        (1152 * |p - p'|) * 80 := by gcongr
  have h2 :
      |carmonRhoProfileDeriv p| *
          |residualConeGradRho (carmonRhoProfile p) u v -
            residualConeGradRho (carmonRhoProfile p') u' v'| ≤
        64 * (1600 * (64 * |p - p'| + |u - u'| + |v - v'|)) := by
    calc
      _ ≤ 64 * (1600 *
          (|carmonRhoProfile p - carmonRhoProfile p'| +
            |u - u'| + |v - v'|)) := by gcongr
      _ ≤ 64 * (1600 *
          (64 * |p - p'| + |u - u'| + |v - v'|)) := by gcongr
  unfold residualProfileSmoothC
  nlinarith [abs_nonneg (p - p'), abs_nonneg (u - u'), abs_nonneg (v - v')]

theorem residualProfileGradU_abs_sub_le (p u v p' u' v' : ℝ) :
    |residualProfileGradU p u v - residualProfileGradU p' u' v'| ≤
      residualProfileSmoothC * (|p - p'| + |u - u'| + |v - v'|) := by
  unfold residualProfileGradU
  have hg := residualConeGradU_abs_sub_le
    (carmonRhoProfile_nonneg p) (carmonRhoProfile_nonneg p')
    (u := u) (v := v) (u' := u') (v' := v')
  have hr := carmonRhoProfile_abs_sub_le p p'
  unfold residualProfileSmoothC
  nlinarith [abs_nonneg (p - p'), abs_nonneg (u - u'), abs_nonneg (v - v')]

theorem residualProfileGradV_abs_sub_le (p u v p' u' v' : ℝ) :
    |residualProfileGradV p u v - residualProfileGradV p' u' v'| ≤
      residualProfileSmoothC * (|p - p'| + |u - u'| + |v - v'|) := by
  unfold residualProfileGradV
  have hg := residualConeGradV_abs_sub_le
    (carmonRhoProfile_nonneg p) (carmonRhoProfile_nonneg p')
    (u := u) (v := v) (u' := u') (v' := v')
  have hr := carmonRhoProfile_abs_sub_le p p'
  unfold residualProfileSmoothC
  nlinarith [abs_nonneg (p - p'), abs_nonneg (u - u'), abs_nonneg (v - v')]

end

end NCPLVerification
