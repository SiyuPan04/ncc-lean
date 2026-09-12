import NCCLowerBoundVerification.Lower.ClipSoftHinge
import NCCLowerBoundVerification.Lower.NumericalHierarchy
import NCPLVerification.InnerDifferentiability
import NCPLVerification.OrthogonalFrames

/-!
# The radial budget

This file verifies the radial block in `lem:radial-properties` of
`Upper+Lower_unified_lower.tex`.  The Hessian is represented without choosing
a matrix basis: `radialHessianApply p h` is its action on a direction `h`.
-/

namespace NCCLowerBoundVerification

noncomputable section

open Set MeasureTheory

/-- Euclidean dot product on the paper's coordinate vectors. -/
def radialDot {d : Nat} (x y : EVec d) : ℝ :=
  ∑ i : Fin d, x i * y i

/-- Equation `eq:radial-composition`. -/
def radialBudget {d : Nat} (P0 P1 K : ℝ) (p : EVec d) : ℝ :=
  Sigma3 P0 P1 K (vecSq p)

/-- The coordinate gradient claimed in `lem:radial-properties`. -/
def radialGradient {d : Nat} (P0 P1 K : ℝ) (p : EVec d) : EVec d :=
  fun i ↦ 2 * Sigma3Deriv P0 P1 K (vecSq p) * p i

/-- The basis-free action of
`2 Σ3'(‖p‖²) I + 4 Σ3''(‖p‖²) p pᵀ`. -/
def radialHessianApply {d : Nat} (P0 P1 K : ℝ)
    (p h : EVec d) : EVec d :=
  fun i ↦
    2 * Sigma3Deriv P0 P1 K (vecSq p) * h i +
      4 * Sigma3Second P0 P1 K (vecSq p) * radialDot p h * p i

/-- The Hessian quadratic form. -/
def radialHessianQuad {d : Nat} (P0 P1 K : ℝ)
    (p h : EVec d) : ℝ :=
  radialDot h (radialHessianApply P0 P1 K p h)

theorem vecSq_nonneg {d : Nat} (p : EVec d) : 0 ≤ vecSq p := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.sum_nonneg (fun i _ ↦ sq_nonneg (p i))

theorem radialDot_self {d : Nat} (p : EVec d) :
    radialDot p p = vecSq p := by
  unfold radialDot vecSq NCPLVerification.vecSq
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Finite-dimensional Cauchy--Schwarz in the exact squared-norm notation of
the paper. -/
theorem radialDot_sq_le {d : Nat} (p h : EVec d) :
    radialDot p h ^ 2 ≤ vecSq p * vecSq h := by
  simpa [radialDot, vecSq, NCPLVerification.vecSq] using
    (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ p h)

theorem hasEVecFDerivAt_vecSq {d : Nat} (p : EVec d) :
    NCPLVerification.HasEVecFDerivAt (fun q : EVec d ↦ vecSq q)
      (NCPLVerification.evecDot (fun i ↦ 2 * p i)) p := by
  letI : AddCommGroup (EVec d) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec d) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec d) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold NCPLVerification.HasEVecFDerivAt
  have hs : HasFDerivAt
      (fun q : EVec d ↦ ∑ i : Fin d, q i ^ 2)
      (∑ i : Fin d, (2 * p i) • NCPLVerification.evecProj i) p := by
    apply HasFDerivAt.fun_sum
    intro i _
    have hi : HasFDerivAt (fun q : EVec d ↦ q i)
        (NCPLVerification.evecProj i) p :=
      (NCPLVerification.evecProj i).hasFDerivAt
    have hmul := hi.mul hi
    convert hmul using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    · funext q
      simp [pow_two]
    · apply ContinuousLinearMap.ext
      intro h
      simp only [add_apply, smul_apply,
        NCPLVerification.evecProj_apply]
      ring
  have heq :
      (∑ i : Fin d, (2 * p i) • NCPLVerification.evecProj i) =
        NCPLVerification.evecDot (fun i ↦ 2 * p i) := by
    apply ContinuousLinearMap.ext
    intro h
    simp only [sum_apply,
      smul_apply, NCPLVerification.evecProj_apply,
      NCPLVerification.evecDot_apply,
      smul_eq_mul]
  rw [heq] at hs
  simpa [vecSq, NCPLVerification.vecSq] using hs

/-- The displayed vector really represents the Fréchet derivative of
`F_rad`; this is the formal gradient claim, including splice points. -/
theorem hasEVecFDerivAt_radialBudget {d : Nat}
    (P0 P1 K : ℝ) (p : EVec d) :
    NCPLVerification.HasEVecFDerivAt (radialBudget P0 P1 K)
      (NCPLVerification.evecDot (radialGradient P0 P1 K p)) p := by
  letI : AddCommGroup (EVec d) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec d) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec d) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ ℝ := RCLike.toInnerProductSpaceReal.toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold NCPLVerification.HasEVecFDerivAt
  have hs : HasFDerivAt (fun q : EVec d ↦ vecSq q)
      (NCPLVerification.evecDot (fun i ↦ 2 * p i)) p := by
    simpa only [NCPLVerification.HasEVecFDerivAt] using hasEVecFDerivAt_vecSq p
  have hcomp := (hasDerivAt_Sigma3 P0 P1 K (vecSq p)).hasFDerivAt.comp p hs
  convert hcomp using 1
  · rfl
  · apply ContinuousLinearMap.ext
    intro h
    simp only [ContinuousLinearMap.comp_apply,
      NCPLVerification.evecDot_apply, radialGradient,
      ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The radial composition is genuinely smooth on the finite-dimensional
coordinate space. -/
theorem radialBudget_contDiff {d : Nat} (P0 P1 K : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (radialBudget P0 P1 K : EVec d → ℝ) := by
  have hsq : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun p : EVec d ↦ ∑ i : Fin d, p i ^ 2) := by
    apply ContDiff.sum
    intro i _
    exact (contDiff_apply ℝ ℝ i).pow 2
  have hsq' : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun p : EVec d ↦ vecSq p) := by
    change ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun p : EVec d ↦ ∑ i : Fin d, p i ^ 2)
    exact hsq
  exact (Sigma3_contDiff P0 P1 K).comp hsq'

/-! ## Value, support, and radial-force properties -/

theorem radialBudget_nonneg {d : Nat} {P0 P1 K : ℝ}
    (hP : P0 ^ 2 < P1 ^ 2) (hK : 0 ≤ K) (p : EVec d) :
    0 ≤ radialBudget P0 P1 K p := by
  exact Sigma3_nonneg hP hK (vecSq p)

theorem radialBudget_eq_zero_of_core {d : Nat} {P0 P1 K : ℝ}
    (hP : P0 ^ 2 < P1 ^ 2) {p : EVec d}
    (hp : vecSq p ≤ P0 ^ 2) : radialBudget P0 P1 K p = 0 := by
  exact Sigma3_eq_zero hP hp

theorem radialGradient_eq_zero_of_core {d : Nat} {P0 P1 K : ℝ}
    (hP : P0 ^ 2 < P1 ^ 2) {p : EVec d}
    (hp : vecSq p ≤ P0 ^ 2) : radialGradient P0 P1 K p = 0 := by
  have hz := Sigma3Deriv_eq_zero (K := K) hP hp
  funext i
  simp [radialGradient, hz]

/-- The radial block cannot reveal a coordinate which was zero before the
oracle query. -/
theorem radialGradient_support {d : Nat} (P0 P1 K : ℝ) (p : EVec d)
    (i : Fin d) (hi : p i = 0) : radialGradient P0 P1 K p i = 0 := by
  simp [radialGradient, hi]

theorem radialGradient_nonnegative_multiple {d : Nat}
    {P0 P1 K : ℝ} (hK : 0 ≤ K) (p : EVec d) :
    ∃ a : ℝ, 0 ≤ a ∧ radialGradient P0 P1 K p = a • p := by
  refine ⟨2 * Sigma3Deriv P0 P1 K (vecSq p), ?_, ?_⟩
  · exact mul_nonneg (by norm_num) (Sigma3Deriv_mem hK).1
  · funext i
    simp [radialGradient]

theorem radial_inner_gradient {d : Nat} (P0 P1 K : ℝ) (p : EVec d) :
    radialDot p (radialGradient P0 P1 K p) =
      2 * Sigma3Deriv P0 P1 K (vecSq p) * vecSq p := by
  unfold radialDot radialGradient
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem radial_inner_gradient_nonneg {d : Nat} {P0 P1 K : ℝ}
    (hK : 0 ≤ K) (p : EVec d) :
    0 ≤ radialDot p (radialGradient P0 P1 K p) := by
  rw [radial_inner_gradient]
  exact mul_nonneg (mul_nonneg (by norm_num) (Sigma3Deriv_mem hK).1)
    (vecSq_nonneg p)

theorem radial_inner_gradient_tail {d : Nat} {P0 P1 K : ℝ}
    (hP : P0 ^ 2 < P1 ^ 2) {p : EVec d}
    (hp : P1 ^ 2 ≤ vecSq p) :
    radialDot p (radialGradient P0 P1 K p) = 2 * K * vecSq p := by
  rw [radial_inner_gradient, Sigma3Deriv_eq_K hP hp]

/-- On the affine tail the gradient is exactly `2 K p`. -/
theorem radialGradient_eq_tail {d : Nat} {P0 P1 K : ℝ}
    (hP : P0 ^ 2 < P1 ^ 2) {p : EVec d}
    (hp : P1 ^ 2 ≤ vecSq p) :
    radialGradient P0 P1 K p = (2 * K) • p := by
  have hk := Sigma3Deriv_eq_K (K := K) hP hp
  funext i
  simp [radialGradient, hk]

/-! ## Hessian formula and its uniform Euclidean bound -/

theorem radialHessianQuad_eq {d : Nat} (P0 P1 K : ℝ)
    (p h : EVec d) :
    radialHessianQuad P0 P1 K p h =
      2 * Sigma3Deriv P0 P1 K (vecSq p) * vecSq h +
        4 * Sigma3Second P0 P1 K (vecSq p) * (radialDot p h) ^ 2 := by
  unfold radialHessianQuad radialHessianApply radialDot
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  unfold vecSq NCPLVerification.vecSq
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · calc
      (∑ i, h i *
          (4 * Sigma3Second P0 P1 K (∑ j, p j ^ 2) *
            (∑ j, p j * h j) * p i)) =
          ∑ i, (p i * h i) *
            (4 * Sigma3Second P0 P1 K (∑ j, p j ^ 2) *
              (∑ j, p j * h j)) := by
              apply Finset.sum_congr rfl
              intro i _
              ring
      _ = (∑ i, p i * h i) *
            (4 * Sigma3Second P0 P1 K (∑ j, p j ^ 2) *
              (∑ j, p j * h j)) := by rw [Finset.sum_mul]
      _ = 4 * Sigma3Second P0 P1 K (∑ j, p j ^ 2) *
            (∑ j, p j * h j) ^ 2 := by ring

theorem radialHessian_uniform_quadratic_bound {d : Nat}
    {P0 P1 K : ℝ} (hP : P0 ^ 2 < P1 ^ 2) (hK : 0 ≤ K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ p h : EVec d,
      |radialHessianQuad P0 P1 K p h| ≤ L * vecSq h := by
  obtain ⟨C, hC, hweighted⟩ := Sigma3_weightedSecond_bounded (K := K) hP
  refine ⟨2 * K + 4 * C, by positivity, ?_⟩
  intro p h
  let r := vecSq p
  let q := vecSq h
  let s := Sigma3Deriv P0 P1 K r
  let t := Sigma3Second P0 P1 K r
  have hr : 0 ≤ r := vecSq_nonneg p
  have hq : 0 ≤ q := vecSq_nonneg h
  have hs0 : 0 ≤ s := (Sigma3Deriv_mem (r := r) hK).1
  have hsK : s ≤ K := (Sigma3Deriv_mem (r := r) hK).2
  have hdot := radialDot_sq_le p h
  have hweighted' : |r * t| ≤ C := hweighted r
  have ht_nonneg : 0 ≤ |t| := abs_nonneg t
  have hmul : |t| * radialDot p h ^ 2 ≤ C * q := by
    calc
      |t| * radialDot p h ^ 2 ≤ |t| * (r * q) :=
        mul_le_mul_of_nonneg_left (by simpa [r, q] using hdot) ht_nonneg
      _ = |r * t| * q := by rw [abs_mul, abs_of_nonneg hr]; ring
      _ ≤ C * q := mul_le_mul_of_nonneg_right hweighted' hq
  rw [radialHessianQuad_eq]
  calc
    |2 * s * q + 4 * t * radialDot p h ^ 2| ≤
        |2 * s * q| + |4 * t * radialDot p h ^ 2| := abs_add_le _ _
    _ = 2 * s * q + 4 * (|t| * radialDot p h ^ 2) := by
      rw [abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs0) hq)]
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
        abs_of_nonneg (sq_nonneg (radialDot p h))]
      ring
    _ ≤ 2 * K * q + 4 * (C * q) := by nlinarith
    _ = (2 * K + 4 * C) * vecSq h := by simp [q]; ring

/-! The next statements certify that the displayed Hessian is an actual
second derivative, rather than merely a matrix suggested by algebra. -/

def radialLine {d : Nat} (p h : EVec d) (t : ℝ) : EVec d :=
  fun i ↦ p i + t * h i

theorem hasDerivAt_vecSq_radialLine {d : Nat} (p h : EVec d) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ vecSq (radialLine p h s))
      (2 * radialDot (radialLine p h t) h) t := by
  unfold vecSq NCPLVerification.vecSq
  have hsum : HasDerivAt
      (fun s : ℝ ↦ ∑ i : Fin d, (radialLine p h s i) ^ 2)
      (∑ i : Fin d, 2 * radialLine p h t i * h i) t := by
    apply HasDerivAt.fun_sum
    intro i _
    have hlin : HasDerivAt (fun s : ℝ ↦ p i + s * h i) (h i) t := by
      convert (hasDerivAt_const t (p i)).add ((hasDerivAt_id t).mul_const (h i)) using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      · funext s
        rfl
      · ring
    convert hlin.pow 2 using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    · funext s
      simp [radialLine]
    · simp [radialLine]
  apply hsum.congr_deriv
  unfold radialDot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem hasDerivAt_radialBudget_line {d : Nat} (P0 P1 K : ℝ)
    (p h : EVec d) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ radialBudget P0 P1 K (radialLine p h s))
      (2 * Sigma3Deriv P0 P1 K (vecSq (radialLine p h t)) *
        radialDot (radialLine p h t) h) t := by
  have hcomp := (hasDerivAt_Sigma3 P0 P1 K (vecSq (radialLine p h t))).comp t
    (hasDerivAt_vecSq_radialLine p h t)
  convert hcomp using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · rfl
  · ring

theorem hasDerivAt_radial_firstDerivative_line {d : Nat} (P0 P1 K : ℝ)
    (p h : EVec d) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        2 * Sigma3Deriv P0 P1 K (vecSq (radialLine p h s)) *
          radialDot (radialLine p h s) h)
      (radialHessianQuad P0 P1 K (radialLine p h t) h) t := by
  have hsq := hasDerivAt_vecSq_radialLine p h t
  have hsigma :=
    (hasDerivAt_Sigma3Deriv P0 P1 K (vecSq (radialLine p h t))).comp t hsq
  have hdot : HasDerivAt (fun s : ℝ ↦ radialDot (radialLine p h s) h)
      (vecSq h) t := by
    unfold radialDot vecSq NCPLVerification.vecSq
    have hsum : HasDerivAt
        (fun s : ℝ ↦ ∑ i : Fin d, radialLine p h s i * h i)
        (∑ i : Fin d, h i ^ 2) t := by
      apply HasDerivAt.fun_sum
      intro i _
      have hlin : HasDerivAt (fun s : ℝ ↦ p i + s * h i) (h i) t := by
        convert (hasDerivAt_const t (p i)).add
          ((hasDerivAt_id t).mul_const (h i)) using 1
        all_goals try { apply AddCommGroup.ext <;> rfl }
        all_goals try { apply Module.ext <;> rfl }
        · funext s
          rfl
        · ring
      convert hlin.mul_const (h i) using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      · funext s
        simp [radialLine]
      · ring
    exact hsum
  have hprod := (hsigma.const_mul 2).mul hdot
  convert hprod using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · rfl
  · rw [radialHessianQuad_eq]
    simp only [Function.comp_apply]
    ring

/-- At `t = 0`, the genuine second directional derivative is precisely the
quadratic form of `radialHessianApply`. -/
theorem hasSecondDirectionalDerivative_radialBudget {d : Nat}
    (P0 P1 K : ℝ) (p h : EVec d) :
    HasDerivAt
      (fun t : ℝ ↦
        2 * Sigma3Deriv P0 P1 K (vecSq (radialLine p h t)) *
          radialDot (radialLine p h t) h)
      (radialHessianQuad P0 P1 K p h) 0 := by
  have hzero : radialLine p h 0 = p := by
    funext i
    simp [radialLine]
  simpa only [hzero] using
    hasDerivAt_radial_firstDerivative_line P0 P1 K p h 0

/-! ## Affine-tail lower bound used by the assembled objective -/

theorem rightHinge_ge_sub_right {a b t : ℝ} (hab : a < b) (hbt : b ≤ t) :
    t - b ≤ rightHinge a b t := by
  have hc := rightHingeIntegrand_continuous a b
  have hhead : 0 ≤ ∫ u in a..b, rightHingeIntegrand a b u := by
    apply intervalIntegral.integral_nonneg hab.le
    intro u _
    exact Lambda1_nonneg _
  have htail : (∫ u in b..t, rightHingeIntegrand a b u) = t - b := by
    calc
      (∫ u in b..t, rightHingeIntegrand a b u) =
          ∫ _u in b..t, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        have hu' : u ∈ Set.Icc b t := by
          simpa [uIcc_of_le hbt] using hu
        have hden : 0 < b - a := sub_pos.mpr hab
        have harg : 1 ≤ (u - a) / (b - a) := by
          rw [le_div_iff₀ hden]
          linarith [hu'.1]
        exact Lambda1_eq_one_of_one_le harg
      _ = t - b := by simp
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable a b) (hc.intervalIntegrable b t)
  unfold rightHinge
  rw [← hadd, htail]
  linarith

theorem Sigma3_ge_affine_tail {P0 P1 K r : ℝ}
    (hP : P0 ^ 2 < P1 ^ 2) (hK : 0 ≤ K) (hr : P1 ^ 2 ≤ r) :
    K * (r - P1 ^ 2) ≤ Sigma3 P0 P1 K r := by
  unfold Sigma3
  exact mul_le_mul_of_nonneg_left (rightHinge_ge_sub_right hP hr) hK

/-- The exact last inequality of `lem:radial-properties`. -/
theorem radialBudget_sub_quadratic_lower {d : Nat}
    {P0 P1 K cq : ℝ} (hP : P0 ^ 2 < P1 ^ 2)
    (hcq : 0 ≤ cq) (hKcq : cq < K) (p : EVec d) :
    -cq * P1 ^ 2 ≤ radialBudget P0 P1 K p - cq * vecSq p := by
  have hK : 0 ≤ K := by linarith
  by_cases hp : vecSq p ≤ P1 ^ 2
  · have hnonneg := radialBudget_nonneg (d := d) hP hK p
    have hmul := mul_le_mul_of_nonneg_left hp hcq
    linarith
  · have hp' : P1 ^ 2 ≤ vecSq p := le_of_not_ge hp
    have htail := Sigma3_ge_affine_tail hP hK hp'
    have hdiff : 0 ≤ (K - cq) * (vecSq p - P1 ^ 2) :=
      mul_nonneg (by linarith) (sub_nonneg.mpr hp')
    unfold radialBudget
    nlinarith

/-- Instantiation of the preceding interface with the constants selected by
`RadialTransitionConstants`. -/
theorem radialBudget_selected_constants_lower {d : Nat}
    {gamma cp cq cs psi0 deltaS Bs : ℝ}
    (C : RadialTransitionConstants gamma cp cq cs psi0 deltaS Bs)
    (hcq : 0 ≤ cq) (p : EVec d) :
    -cq * C.P1 ^ 2 ≤
      radialBudget C.P0 C.P1 C.K p - cq * vecSq p := by
  have hP0 : 0 < C.P0 := by linarith [C.P0_gt_one]
  have hP1 : 0 < C.P1 := hP0.trans C.P0_lt_P1
  have hdiff : 0 < C.P1 - C.P0 := sub_pos.mpr C.P0_lt_P1
  have hsum : 0 < C.P1 + C.P0 := by linarith
  have hprod : 0 < (C.P1 - C.P0) * (C.P1 + C.P0) := mul_pos hdiff hsum
  have hsq : C.P0 ^ 2 < C.P1 ^ 2 := by nlinarith
  exact radialBudget_sub_quadratic_lower hsq hcq (by linarith [C.K_gt]) p

end

end NCCLowerBoundVerification
