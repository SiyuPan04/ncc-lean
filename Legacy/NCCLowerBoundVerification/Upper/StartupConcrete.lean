import NCCLowerBoundVerification.Upper.TrackingConcrete
import NCCLowerBoundVerification.Upper.ScaledOperator

/-!
# Concrete startup residual analysis

This file discharges the two raw inequalities consumed by
`TrackingAnalytic.startup_energy_from_residual`.  They are derived from a
genuine strong subgradient inequality and the anisotropic residual norm.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace StartupConcrete

noncomputable section

open PointwiseConjugate TrackingAnalytic

def dualPairSq {m n : Nat} (mu r : ℝ)
    (q : EVec m) (y : EVec n) : ℝ :=
  mu * vecSq q + 1 / r * vecSq y

def plainPairDot {m n : Nat}
    (q q' : EVec m) (y y' : EVec n) : ℝ :=
  dot q q' + dot y y'

def dualScaled {m n : Nat} (mu r : ℝ)
    (q : EVec m) (y : EVec n) : ScaledOperator.Pair m n :=
  ScaledOperator.pack (Real.sqrt mu • q) ((Real.sqrt r)⁻¹ • y)

def primalScaled {m n : Nat} (mu r : ℝ)
    (q : EVec m) (y : EVec n) : ScaledOperator.Pair m n :=
  ScaledOperator.pack ((Real.sqrt mu)⁻¹ • q) (Real.sqrt r • y)

theorem dot_smul_right {d : Nat} (c : ℝ) (x y : EVec d) :
    dot x (c • y) = c * dot x y := by
  rw [dot_comm, dot_smul_left, dot_comm]

theorem dot_smul_smul {d : Nat} (a b : ℝ) (x y : EVec d) :
    dot (a • x) (b • y) = a * b * dot x y := by
  rw [dot_smul_left, dot_smul_right]
  ring

theorem dualScaled_dot_primalScaled {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r)
    (eq : EVec m) (ey : EVec n) (aq : EVec m) (ay : EVec n) :
    dot (dualScaled mu r eq ey) (primalScaled mu r aq ay) =
      plainPairDot eq aq ey ay := by
  have hpack := ScaledOperator.vecDot_pack
    (Real.sqrt mu • eq) ((Real.sqrt mu)⁻¹ • aq)
    ((Real.sqrt r)⁻¹ • ey) (Real.sqrt r • ay)
  change dot (ScaledOperator.pack (Real.sqrt mu • eq) ((Real.sqrt r)⁻¹ • ey))
      (ScaledOperator.pack ((Real.sqrt mu)⁻¹ • aq) (Real.sqrt r • ay)) =
        dot (Real.sqrt mu • eq) ((Real.sqrt mu)⁻¹ • aq) +
          dot ((Real.sqrt r)⁻¹ • ey) (Real.sqrt r • ay) at hpack
  have hsmu : Real.sqrt mu ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hmu)
  have hsr : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
  unfold dualScaled primalScaled plainPairDot
  rw [hpack, dot_smul_smul, dot_smul_smul]
  field_simp [hsmu, hsr]

theorem vecSq_dualScaled {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (q : EVec m) (y : EVec n) :
    vecSq (dualScaled mu r q y) = dualPairSq mu r q y := by
  unfold dualScaled dualPairSq
  rw [ScaledOperator.vecSq_pack, vecSq_smul,
    vecSq_smul, Real.sq_sqrt hmu.le]
  have hinv : (Real.sqrt r)⁻¹ ^ 2 = 1 / r := by
    rw [inv_pow, Real.sq_sqrt hr.le]
    simp [div_eq_mul_inv]
  rw [hinv]

theorem vecSq_primalScaled {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (q : EVec m) (y : EVec n) :
    vecSq (primalScaled mu r q y) = pairSq mu r q y := by
  unfold primalScaled pairSq
  rw [ScaledOperator.vecSq_pack, vecSq_smul,
    vecSq_smul, Real.sq_sqrt hr.le]
  have hinv : (Real.sqrt mu)⁻¹ ^ 2 = 1 / mu := by
    rw [inv_pow, Real.sq_sqrt hmu.le]
    simp [div_eq_mul_inv]
  rw [hinv]

/-- Cauchy--Schwarz between the primal metric and its dual metric. -/
theorem plainPairDot_le_mul {m n : Nat} {mu r A B : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {eq : EVec m} {ey : EVec n} {aq : EVec m} {ay : EVec n}
    (he : dualPairSq mu r eq ey ≤ B ^ 2)
    (ha : pairSq mu r aq ay = A ^ 2) :
    plainPairDot eq aq ey ay ≤ A * B := by
  have he0 : 0 ≤ dualPairSq mu r eq ey := by
    unfold dualPairSq
    exact add_nonneg
      (mul_nonneg hmu.le (Tracking.vecSq_nonneg _))
      (mul_nonneg (by positivity) (Tracking.vecSq_nonneg _))
  have hp0 : 0 ≤ pairSq mu r aq ay := pairSq_nonneg hmu hr.le _ _
  have hcs : dot (dualScaled mu r eq ey) (primalScaled mu r aq ay) ≤
      Real.sqrt (vecSq (dualScaled mu r eq ey)) *
        Real.sqrt (vecSq (primalScaled mu r aq ay)) := by
    exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
      (dualScaled mu r eq ey) (primalScaled mu r aq ay)
  rw [dualScaled_dot_primalScaled hmu hr,
    vecSq_dualScaled hmu hr, vecSq_primalScaled hmu hr, ha] at hcs
  have hsqrtA : Real.sqrt (A ^ 2) = A := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hA]
  rw [hsqrtA] at hcs
  have hsqrtE0 := Real.sqrt_nonneg (dualPairSq mu r eq ey)
  have hsqrtE2 := Real.sq_sqrt he0
  have hsqrtEle : Real.sqrt (dualPairSq mu r eq ey) ≤ B := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hsqrtEle hA
  nlinarith

theorem pairDot_le_mul {m n : Nat} {mu r A B : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {bq aq : EVec m} {byv ay : EVec n}
    (hb : pairSq mu r bq byv = B ^ 2)
    (ha : pairSq mu r aq ay = A ^ 2) :
    pairDot mu r bq aq byv ay ≤ A * B := by
  let eq : EVec m := mu⁻¹ • bq
  let ey : EVec n := r • byv
  have hdual : dualPairSq mu r eq ey = pairSq mu r bq byv := by
    unfold dualPairSq pairSq eq ey
    rw [vecSq_smul, vecSq_smul]
    field_simp [ne_of_gt hmu, ne_of_gt hr]
  have hdot : plainPairDot eq aq ey ay = pairDot mu r bq aq byv ay := by
    unfold plainPairDot pairDot eq ey
    rw [dot_smul_left, dot_smul_left]
    field_simp [ne_of_gt hmu]
  rw [← hdot]
  apply plainPairDot_le_mul hmu hr hA hB
  · rw [hdual, hb]
  · exact ha

theorem neg_pairDot_le_mul {m n : Nat} {mu r A B : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {bq aq : EVec m} {byv ay : EVec n}
    (hb : pairSq mu r bq byv = B ^ 2)
    (ha : pairSq mu r aq ay = A ^ 2) :
    -pairDot mu r bq aq byv ay ≤ A * B := by
  have hbneg : pairSq mu r (-bq) (-byv) = B ^ 2 := by
    rw [show pairSq mu r (-bq) (-byv) = pairSq mu r bq byv by
      unfold pairSq
      rw [Tracking.vecSq_neg, Tracking.vecSq_neg]]
    exact hb
  have h := pairDot_le_mul hmu hr hA hB hbneg ha
  have hneg : pairDot mu r (-bq) aq (-byv) ay =
      -pairDot mu r bq aq byv ay := by
    unfold pairDot dot
    simp_rw [Pi.neg_apply, neg_mul]
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    ring
  rw [hneg] at h
  exact h

theorem pairSq_sub_expand {m n : Nat} (mu r : ℝ)
    (aq bq : EVec m) (ay byv : EVec n) :
    pairSq mu r (aq - bq) (ay - byv) =
      pairSq mu r aq ay + pairSq mu r bq byv -
        2 * pairDot mu r bq aq byv ay := by
  unfold pairSq pairDot
  rw [PointwiseConjugate.vecSq_sub_expand,
    PointwiseConjugate.vecSq_sub_expand]
  ring

def coincidentState {m n : Nat} (q : EVec m) (y : EVec n) :
    RelativeFOAM.State m n where
  q := q
  y := y
  qFast := q
  yFast := y

def startupOutput {m n : Nat} (xFast qFast : EVec m)
    (yFast wFast : EVec n) : RelativeFOAM.MicroOutput m n where
  xFast := xFast
  yFastNext := yFast
  qFastNext := qFast
  wFastNext := wFast

def startupErrorX {m n : Nat} (mu : ℝ)
    (q0 : EVec m) (y0 : EVec n) (xFast qFast : EVec m)
    (yFast wFast : EVec n) : EVec m :=
  (2 / mu) • RelativeFOAM.residualX mu (mu / 8)
    (coincidentState q0 y0) (startupOutput xFast qFast yFast wFast)

def startupErrorY {m n : Nat} (mu : ℝ)
    (q0 : EVec m) (y0 : EVec n) (xFast qFast : EVec m)
    (yFast wFast : EVec n) : EVec n :=
  RelativeFOAM.residualY mu (mu / 8)
    (coincidentState q0 y0) (startupOutput xFast qFast yFast wFast)

theorem vecSq_sub_two_smul_le {d : Nat} (a b : EVec d) :
    vecSq (a - (2 : ℝ) • b) ≤ 2 * vecSq a + 8 * vecSq b := by
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  change (a i - 2 * b i) ^ 2 ≤ 2 * a i ^ 2 + 8 * b i ^ 2
  nlinarith [sq_nonneg (a i + 2 * b i)]

/-- At the startup curvature `r₀ = μ/8`, the actual relative micro-residual
implies the anisotropic dual-norm estimate used in the startup proof.  The
error vectors here are exactly `e_q = 2 Δ_x / μ` and `e_y = Δ_y`; no
proximal-map or residual estimate is assumed separately. -/
theorem startup_relative_residual_dual_bound {m n : Nat} {mu : ℝ}
    (hmu : 0 < mu)
    {q0 xFast qFast : EVec m} {y0 yFast wFast : EVec n}
    (hres : RelativeFOAM.RelativeResidual mu (mu / 8)
      (coincidentState q0 y0) (startupOutput xFast qFast yFast wFast)) :
    dualPairSq mu (mu / 8)
        (startupErrorX mu q0 y0 xFast qFast yFast wFast)
        (startupErrorY mu q0 y0 xFast qFast yFast wFast) ≤
      pairSq mu (mu / 8) (qFast - q0) (yFast - y0) := by
  let eq := startupErrorX mu q0 y0 xFast qFast yFast wFast
  let ey := startupErrorY mu q0 y0 xFast qFast yFast wFast
  let bq := mu⁻¹ • (qFast - q0)
  have hr : 0 < mu / 8 := by positivity
  have htheta : RelativeFOAM.theta mu = 8 / mu := rfl
  have hqCenter : RelativeFOAM.qCenter mu (mu / 8)
      (coincidentState q0 y0) = q0 := by
    unfold RelativeFOAM.qCenter coincidentState
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hyCenter : RelativeFOAM.yCenter mu (mu / 8)
      (coincidentState q0 y0) = y0 := by
    unfold RelativeFOAM.yCenter coincidentState
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have heq : eq - (2 : ℝ) • bq = xFast + mu⁻¹ • q0 := by
    dsimp [eq, bq, startupErrorX]
    unfold RelativeFOAM.residualX startupOutput
    rw [hqCenter]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [inv_eq_one_div]
    field_simp [ne_of_gt hmu]
    ring
  have hbound := vecSq_sub_two_smul_le eq bq
  rw [heq] at hbound
  have heqSq : vecSq eq = (4 / mu ^ 2) *
      vecSq (RelativeFOAM.residualX mu (mu / 8)
        (coincidentState q0 y0) (startupOutput xFast qFast yFast wFast)) := by
    dsimp [eq, startupErrorX]
    rw [vecSq_smul]
    congr 1
    field_simp [ne_of_gt hmu]
    ring
  have hbqSq : vecSq bq = (1 / mu ^ 2) * vecSq (qFast - q0) := by
    dsimp [bq]
    rw [vecSq_smul]
    congr 1
    simp [div_eq_mul_inv]
  have hres' := hres
  unfold RelativeFOAM.RelativeResidual at hres'
  rw [hqCenter, hyCenter, htheta] at hres'
  have h8Inv : (8 / mu)⁻¹ = mu / 8 := by
    field_simp [ne_of_gt hmu]
  rw [h8Inv] at hres'
  dsimp [startupOutput] at hres'
  have hdx0 : 0 ≤ vecSq (RelativeFOAM.residualX mu (mu / 8)
      (coincidentState q0 y0) (startupOutput xFast qFast yFast wFast)) :=
    Tracking.vecSq_nonneg _
  have hdy0 : 0 ≤ vecSq ey := Tracking.vecSq_nonneg _
  have hb0 : 0 ≤ vecSq (qFast - q0) := Tracking.vecSq_nonneg _
  have hy0 : 0 ≤ vecSq (yFast - y0) := Tracking.vecSq_nonneg _
  change 8 / mu * vecSq (RelativeFOAM.residualX mu (mu / 8)
      (coincidentState q0 y0) (startupOutput xFast qFast yFast wFast)) +
      8 / mu * vecSq ey ≤
        mu / 8 * vecSq (xFast + mu⁻¹ • q0) +
          mu / 8 * vecSq (yFast - y0) at hres'
  rw [heqSq, hbqSq] at hbound
  change mu * vecSq eq + 1 / (mu / 8) * vecSq ey ≤
    1 / mu * vecSq (qFast - q0) +
      mu / 8 * vecSq (yFast - y0)
  rw [heqSq]
  field_simp [ne_of_gt hmu] at hres' hbound ⊢
  nlinarith

/-- The exact startup master inequality and fast-gap estimate, now derived
from the residual, strong monotonicity, and strong support. -/
theorem startup_master_and_gap {m n : Nat} {mu r A B R gap : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {qStar qf q0 : EVec m} {yStar yf y0 : EVec n}
    {gq eq : EVec m} {gy ey : EVec n}
    (hAmetric : pairSq mu r (qf - qStar) (yf - yStar) = A ^ 2)
    (hBmetric : pairSq mu r (qf - q0) (yf - y0) = B ^ 2)
    (hRmetric : pairSq mu r (q0 - qStar) (y0 - yStar) = R ^ 2)
    (hresidual : dualPairSq mu r eq ey ≤ B ^ 2)
    (hgq : gq = eq - mu⁻¹ • (qf - q0))
    (hgy : gy = ey - r • (yf - y0))
    (hmonotone : pairSq mu r (qf - qStar) (yf - yStar) ≤
      plainPairDot gq (qf - qStar) gy (yf - yStar))
    (hsupport : gap ≤ plainPairDot gq (qf - qStar) gy (yf - yStar) -
      (1 / 2 : ℝ) * pairSq mu r (qf - qStar) (yf - yStar)) :
    3 * A ^ 2 - 2 * A * B + B ^ 2 ≤ R ^ 2 ∧
      gap ≤ 2 * A * B := by
  let aq := qf - qStar
  let ay := yf - yStar
  let bq := qf - q0
  let byv := yf - y0
  have hEA : plainPairDot eq aq ey ay ≤ A * B := by
    apply plainPairDot_le_mul hmu hr hA hB hresidual
    simpa [aq, ay] using hAmetric
  have hBA : pairDot mu r bq aq byv ay ≤ A * B := by
    apply pairDot_le_mul hmu hr hA hB
    · simpa [bq, byv] using hBmetric
    · simpa [aq, ay] using hAmetric
  have hnegBA : -pairDot mu r bq aq byv ay ≤ A * B := by
    apply neg_pairDot_le_mul hmu hr hA hB
    · simpa [bq, byv] using hBmetric
    · simpa [aq, ay] using hAmetric
  have hgeom : R ^ 2 = A ^ 2 + B ^ 2 -
      2 * pairDot mu r bq aq byv ay := by
    have hsubq : q0 - qStar = aq - bq := by dsimp [aq, bq]; abel
    have hsuby : y0 - yStar = ay - byv := by dsimp [ay, byv]; abel
    rw [hsubq, hsuby, pairSq_sub_expand, hAmetric, hBmetric] at hRmetric
    exact hRmetric.symm
  have hgrad : plainPairDot gq aq gy ay =
      plainPairDot eq aq ey ay - pairDot mu r bq aq byv ay := by
    rw [hgq, hgy]
    unfold plainPairDot pairDot
    rw [dot_sub_left, dot_sub_left, dot_smul_left, dot_smul_left]
    dsimp [bq, byv]
    have hmuinv : mu⁻¹ = 1 / mu := by simp [div_eq_mul_inv]
    rw [hmuinv]
    ring
  have hmono : A ^ 2 ≤
      plainPairDot eq aq ey ay - pairDot mu r bq aq byv ay := by
    rw [← hgrad]
    simpa [aq, ay, hAmetric] using hmonotone
  constructor
  · nlinarith
  · have hgradUpper : plainPairDot gq aq gy ay ≤ 2 * A * B := by
      rw [hgrad]
      nlinarith
    have hmetric0 := pairSq_nonneg hmu hr.le aq ay
    change gap ≤ plainPairDot gq aq gy ay -
      (1 / 2 : ℝ) * pairSq mu r aq ay at hsupport
    nlinarith

/-- Startup energy on the actual constrained fast domain.  This is the
subtype-correct counterpart of `TrackingAnalytic.startup_energy_from_residual`.
-/
theorem constrained_startup_energy_from_master {m n : Nat}
    {Y : Set (EVec n)} {mu r A B R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    {P : EVec m → Y → ℝ} {qStar qFast : EVec m}
    {yStar yFast : Y}
    (halpha : RelativeFOAM.alpha mu r = 1)
    (hmetric : pairSq mu r (qFast - qStar)
      (yFast.1 - yStar.1) = A ^ 2)
    (hmaster : 3 * A ^ 2 - 2 * A * B + B ^ 2 ≤ R ^ 2)
    (hgap : P qFast yFast - P qStar yStar ≤ 2 * A * B) :
    TrackingConcrete.constrainedEnergy mu r qStar yStar P (P qStar yStar)
        (coincidentState qFast yFast.1) yFast.2 ≤
      (1 + 2 * Real.sqrt 3) * R ^ 2 := by
  have hfast := startup_fast_gap_bound hA hB hmaster hgap
  have hdist := (startup_distance_bounds hmaster).1
  unfold TrackingConcrete.constrainedEnergy coincidentState
  dsimp
  have hslow :
      2 * RelativeFOAM.alpha mu r / mu * vecSq (qFast - qStar) +
          2 * r * vecSq (yFast.1 - yStar.1) = 2 * A ^ 2 := by
    rw [halpha]
    unfold pairSq at hmetric
    linear_combination 2 * hmetric
  linarith

/-- The complete startup quadratic and fast-gap estimates for the genuine
constrained pointwise-conjugate objective.  The only residual premise is the
micro-solver's displayed `RelativeResidual`; the subgradient at the fast pair
is the one produced by its normal relations, and the starred subgradient is
stationary. -/
theorem startup_pzr_master_and_gap {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu A B R : ℝ}
    (hmu : 0 < mu) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {qStar q0 qFast xStar xFast : EVec m}
    {yStar yFast : Y} {y0 wStar wFast : EVec n}
    (hsubgradFast : IsGammaSubgradient X Y H qFast yFast xFast wFast)
    (hsubgradStar : IsGammaSubgradient X Y H qStar yStar xStar wStar)
    (hstationQ : xStar + mu⁻¹ • qStar = 0)
    (hstationY : wStar + (mu / 8) • yStar.1 = 0)
    (hres : RelativeFOAM.RelativeResidual mu (mu / 8)
      (coincidentState q0 y0)
      (startupOutput xFast qFast yFast.1 wFast))
    (hAmetric : pairSq mu (mu / 8) (qFast - qStar)
      (yFast.1 - yStar.1) = A ^ 2)
    (hBmetric : pairSq mu (mu / 8) (qFast - q0)
      (yFast.1 - y0) = B ^ 2)
    (hRmetric : pairSq mu (mu / 8) (q0 - qStar)
      (y0 - yStar.1) = R ^ 2) :
    3 * A ^ 2 - 2 * A * B + B ^ 2 ≤ R ^ 2 ∧
      Pzr X Y H mu (mu / 8) qFast yFast -
        Pzr X Y H mu (mu / 8) qStar yStar ≤ 2 * A * B := by
  let r : ℝ := mu / 8
  let eq := startupErrorX mu q0 y0 xFast qFast yFast.1 wFast
  let ey := startupErrorY mu q0 y0 xFast qFast yFast.1 wFast
  let gq := xFast + mu⁻¹ • qFast
  let gy := wFast + r • yFast.1
  have hr : 0 < r := by dsimp [r]; positivity
  have hresidual : dualPairSq mu r eq ey ≤
      pairSq mu r (qFast - q0) (yFast.1 - y0) := by
    dsimp [r, eq, ey]
    exact startup_relative_residual_dual_bound hmu hres
  have hqCenter : RelativeFOAM.qCenter mu r
      (coincidentState q0 y0) = q0 := by
    unfold RelativeFOAM.qCenter coincidentState
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hyCenter : RelativeFOAM.yCenter mu r
      (coincidentState q0 y0) = y0 := by
    unfold RelativeFOAM.yCenter coincidentState
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hgq : gq = eq - mu⁻¹ • (qFast - q0) := by
    dsimp [gq, eq, startupErrorX, r]
    unfold RelativeFOAM.residualX startupOutput
    rw [hqCenter]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      inv_eq_one_div]
    field_simp [ne_of_gt hmu]
    ring
  have hthetaInv : (RelativeFOAM.theta mu)⁻¹ = r := by
    dsimp [r]
    unfold RelativeFOAM.theta
    field_simp [ne_of_gt hmu]
  have hgy : gy = ey - r • (yFast.1 - y0) := by
    dsimp [gy, ey, startupErrorY]
    unfold RelativeFOAM.residualY startupOutput
    rw [hyCenter, hthetaInv]
    funext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hfast := Pzr_strongSupport (r := r) hmu hsubgradFast qStar yStar
  change Pzr X Y H mu r qFast yFast +
      dot gq (qStar - qFast) + dot gy (yStar.1 - yFast.1) +
      1 / (2 * mu) * vecSq (qStar - qFast) +
      r / 2 * vecSq (yStar.1 - yFast.1) ≤
        Pzr X Y H mu r qStar yStar at hfast
  have hdotQ : dot gq (qStar - qFast) =
      -dot gq (qFast - qStar) := by
    rw [dot_sub_right, dot_sub_right]
    ring
  have hdotY : dot gy (yStar.1 - yFast.1) =
      -dot gy (yFast.1 - yStar.1) := by
    rw [dot_sub_right, dot_sub_right]
    ring
  have hquad : 1 / (2 * mu) * vecSq (qStar - qFast) +
      r / 2 * vecSq (yStar.1 - yFast.1) =
        (1 / 2 : ℝ) * pairSq mu r (qFast - qStar)
          (yFast.1 - yStar.1) := by
    unfold pairSq
    rw [vecSq_sub_comm qStar qFast,
      vecSq_sub_comm yStar.1 yFast.1]
    field_simp [ne_of_gt hmu]
  have hsupport : Pzr X Y H mu r qFast yFast -
      Pzr X Y H mu r qStar yStar ≤
        plainPairDot gq (qFast - qStar) gy (yFast.1 - yStar.1) -
          (1 / 2 : ℝ) * pairSq mu r (qFast - qStar)
            (yFast.1 - yStar.1) := by
    unfold plainPairDot
    nlinarith [hfast, hdotQ, hdotY, hquad]
  have hstar := Pzr_strongMinimizer hmu hr hsubgradStar
    hstationQ (by simpa [r] using hstationY) qFast yFast
  have hstarQuad : 1 / (2 * mu) * vecSq (qFast - qStar) +
      r / 2 * vecSq (yFast.1 - yStar.1) =
        (1 / 2 : ℝ) * pairSq mu r (qFast - qStar)
          (yFast.1 - yStar.1) := by
    unfold pairSq
    field_simp [ne_of_gt hmu]
  have hgapLower : (1 / 2 : ℝ) * pairSq mu r
      (qFast - qStar) (yFast.1 - yStar.1) ≤
        Pzr X Y H mu r qFast yFast - Pzr X Y H mu r qStar yStar := by
    nlinarith [hstar, hstarQuad]
  have hmonotone : pairSq mu r (qFast - qStar)
      (yFast.1 - yStar.1) ≤
        plainPairDot gq (qFast - qStar) gy (yFast.1 - yStar.1) := by
    nlinarith [hsupport, hgapLower]
  have hresidualB : dualPairSq mu r eq ey ≤ B ^ 2 := by
    calc
      dualPairSq mu r eq ey ≤
          pairSq mu r (qFast - q0) (yFast.1 - y0) := hresidual
      _ = B ^ 2 := by simpa [r] using hBmetric
  apply startup_master_and_gap hmu hr hA hB
      (hAmetric := by simpa [r] using hAmetric)
      (hBmetric := by simpa [r] using hBmetric)
      (hRmetric := by simpa [r] using hRmetric)
      (hresidual := hresidualB) (hgq := hgq) (hgy := hgy)
      (hmonotone := hmonotone)
  simpa [r] using hsupport

/-- The paper's startup-via-radius energy estimate, with every analytic input
traced to the real micro residual and real `Pzr` subgradients. -/
theorem startup_pzr_energy_bound {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu A B R : ℝ}
    (hmu : 0 < mu) (hA : 0 ≤ A) (hB : 0 ≤ B)
    {qStar q0 qFast xStar xFast : EVec m}
    {yStar yFast : Y} {y0 wStar wFast : EVec n}
    (hsubgradFast : IsGammaSubgradient X Y H qFast yFast xFast wFast)
    (hsubgradStar : IsGammaSubgradient X Y H qStar yStar xStar wStar)
    (hstationQ : xStar + mu⁻¹ • qStar = 0)
    (hstationY : wStar + (mu / 8) • yStar.1 = 0)
    (hres : RelativeFOAM.RelativeResidual mu (mu / 8)
      (coincidentState q0 y0)
      (startupOutput xFast qFast yFast.1 wFast))
    (hAmetric : pairSq mu (mu / 8) (qFast - qStar)
      (yFast.1 - yStar.1) = A ^ 2)
    (hBmetric : pairSq mu (mu / 8) (qFast - q0)
      (yFast.1 - y0) = B ^ 2)
    (hRmetric : pairSq mu (mu / 8) (q0 - qStar)
      (y0 - yStar.1) = R ^ 2) :
    TrackingConcrete.constrainedEnergy mu (mu / 8) qStar yStar
        (Pzr X Y H mu (mu / 8))
        (Pzr X Y H mu (mu / 8) qStar yStar)
        (coincidentState qFast yFast.1) yFast.2 ≤
      (1 + 2 * Real.sqrt 3) * R ^ 2 := by
  have hcore := startup_pzr_master_and_gap hmu hA hB
    hsubgradFast hsubgradStar hstationQ hstationY hres
    hAmetric hBmetric hRmetric
  have halpha : RelativeFOAM.alpha mu (mu / 8) = 1 := by
    unfold RelativeFOAM.alpha RelativeFOAM.theta
    have harg : 8 / mu * (mu / 8) = 1 := by
      field_simp [ne_of_gt hmu]
    rw [harg, Real.sqrt_one]
  exact constrained_startup_energy_from_master hA hB halpha hAmetric
    hcore.1 hcore.2

/-- Witness-free startup estimate: `A`, `B`, and `R` are constructed as the
square roots of their genuine metric squares rather than supplied by the
caller. -/
theorem startup_pzr_energy_bound_metric {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu : ℝ}
    (hmu : 0 < mu)
    {qStar q0 qFast xStar xFast : EVec m}
    {yStar yFast : Y} {y0 wStar wFast : EVec n}
    (hsubgradFast : IsGammaSubgradient X Y H qFast yFast xFast wFast)
    (hsubgradStar : IsGammaSubgradient X Y H qStar yStar xStar wStar)
    (hstationQ : xStar + mu⁻¹ • qStar = 0)
    (hstationY : wStar + (mu / 8) • yStar.1 = 0)
    (hres : RelativeFOAM.RelativeResidual mu (mu / 8)
      (coincidentState q0 y0)
      (startupOutput xFast qFast yFast.1 wFast)) :
    TrackingConcrete.constrainedEnergy mu (mu / 8) qStar yStar
        (Pzr X Y H mu (mu / 8))
        (Pzr X Y H mu (mu / 8) qStar yStar)
        (coincidentState qFast yFast.1) yFast.2 ≤
      (1 + 2 * Real.sqrt 3) *
        pairSq mu (mu / 8) (q0 - qStar) (y0 - yStar.1) := by
  let A := Real.sqrt (pairSq mu (mu / 8) (qFast - qStar)
    (yFast.1 - yStar.1))
  let B := Real.sqrt (pairSq mu (mu / 8) (qFast - q0)
    (yFast.1 - y0))
  let R := Real.sqrt (pairSq mu (mu / 8) (q0 - qStar)
    (y0 - yStar.1))
  have hr : 0 < mu / 8 := by positivity
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hAmetric : pairSq mu (mu / 8) (qFast - qStar)
      (yFast.1 - yStar.1) = A ^ 2 := by
    symm
    exact Real.sq_sqrt (pairSq_nonneg hmu hr.le _ _)
  have hBmetric : pairSq mu (mu / 8) (qFast - q0)
      (yFast.1 - y0) = B ^ 2 := by
    symm
    exact Real.sq_sqrt (pairSq_nonneg hmu hr.le _ _)
  have hRmetric : pairSq mu (mu / 8) (q0 - qStar)
      (y0 - yStar.1) = R ^ 2 := by
    symm
    exact Real.sq_sqrt (pairSq_nonneg hmu hr.le _ _)
  have henergy := startup_pzr_energy_bound hmu hA0 hB0
    hsubgradFast hsubgradStar hstationQ hstationY hres
    hAmetric hBmetric hRmetric
  rw [← hRmetric] at henergy
  exact henergy

theorem sqrt_three_lt_two : Real.sqrt 3 < 2 := by
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith

/-- Scalar finalization of the paper's startup proposition and its computable
majorant `B⁽⁰⁾ = 8(Δ+r₀D²)`. -/
theorem startup_energy_to_computable_majorant
    {E R2 Delta r D2 : ℝ}
    (hE : E ≤ (1 + 2 * Real.sqrt 3) * R2)
    (hR : R2 ≤ Delta + (3 / 2 : ℝ) * r * D2)
    (hR20 : 0 ≤ R2) (hDelta : 0 ≤ Delta)
    (hr : 0 ≤ r) (hD2 : 0 ≤ D2) :
    E ≤ 5 * (Delta + (3 / 2 : ℝ) * r * D2) ∧
      E ≤ 8 * (Delta + r * D2) := by
  have hs := sqrt_three_lt_two
  have hcoef : 1 + 2 * Real.sqrt 3 < 5 := by nlinarith
  have hbase0 : 0 ≤ Delta + (3 / 2 : ℝ) * r * D2 := by positivity
  have hfive : E ≤ 5 * (Delta + (3 / 2 : ℝ) * r * D2) := by
    have hcoefR := mul_le_mul_of_nonneg_right hcoef.le hR20
    have hRscaled := mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 5)
    nlinarith
  constructor
  · exact hfive
  · nlinarith [mul_nonneg hr hD2]

/-- Fully assembled startup proposition at `q₀=-μz`, `y₀=0`.  The remaining
radius premise is the genuine proximal displacement estimate from the primal
initial gap; all micro-residual and conjugate estimates are proved above. -/
theorem startup_pzr_computable_majorant {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu Delta D2 : ℝ}
    (hmu : 0 < mu) (hDelta : 0 ≤ Delta) (hD2 : 0 ≤ D2)
    {z qStar qFast xStar xFast : EVec m}
    {yStar yFast : Y} {wStar wFast : EVec n}
    (hsubgradFast : IsGammaSubgradient X Y H qFast yFast xFast wFast)
    (hsubgradStar : IsGammaSubgradient X Y H qStar yStar xStar wStar)
    (hstationQ : xStar + mu⁻¹ • qStar = 0)
    (hstationY : wStar + (mu / 8) • yStar.1 = 0)
    (hres : RelativeFOAM.RelativeResidual mu (mu / 8)
      (coincidentState ((-mu) • z) 0)
      (startupOutput xFast qFast yFast.1 wFast))
    (hprimal : mu * vecSq (z - xStar) ≤
      Delta + (mu / 8) / 2 * D2)
    (hyStar : vecSq yStar.1 ≤ D2) :
    let E := TrackingConcrete.constrainedEnergy mu (mu / 8) qStar yStar
      (Pzr X Y H mu (mu / 8))
      (Pzr X Y H mu (mu / 8) qStar yStar)
      (coincidentState qFast yFast.1) yFast.2
    E ≤ 5 * (Delta + (3 / 2 : ℝ) * (mu / 8) * D2) ∧
      E ≤ 8 * (Delta + (mu / 8) * D2) := by
  dsimp
  have hr : 0 ≤ mu / 8 := by positivity
  have hqStar : qStar = (-mu) • xStar :=
    q_eq_neg_mu_smul_of_stationary hmu hstationQ
  have henergy := startup_pzr_energy_bound_metric hmu hsubgradFast
    hsubgradStar hstationQ hstationY hres
  have hR := startup_radius_bound hmu hr hprimal hyStar
  rw [← hqStar] at hR
  have hR20 := pairSq_nonneg hmu hr
    (((-mu) • z) - qStar) (0 - yStar.1)
  exact startup_energy_to_computable_majorant henergy hR hR20 hDelta hr hD2

end

end StartupConcrete
end Upper
end NCCLowerBoundVerification
