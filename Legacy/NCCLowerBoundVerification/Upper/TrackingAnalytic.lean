import NCCLowerBoundVerification.Upper.Tracking
import NCCLowerBoundVerification.Upper.PointwiseConjugate

/-!
# Analytic discharge of the tracking interfaces

This file pushes the local inputs of `Upper.Tracking` down to the already
formalized Moreau remainder estimate and to strong-minimizer inequalities for
the concrete pointwise-conjugate objective.  In particular, no tracking,
startup, curvature-transfer, or outer-descent conclusion is assumed here.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace TrackingAnalytic

noncomputable section

open PointwiseConjugate

/-! ## The actual Moreau descent lemma -/

/-- The quadratic remainder theorem in `MoreauEnvelope` directly supplies
the precise `SmoothDescentAt` instance used by `Tracking.outer_descent`. -/
theorem moreau_smoothDescentAt {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) (z d : EVec m) :
    Tracking.SmoothDescentAt (moreauEnvelope phi ell hexists) ell z d
      (residualGradient hexists z) := by
  unfold Tracking.SmoothDescentAt
  have hrem := moreauEnvelope_remainder_abs_le hell hweak hexists z d
  rw [residualCLM_apply] at hrem
  have hle := (le_abs_self
    (moreauEnvelope phi ell hexists (z + d) -
      moreauEnvelope phi ell hexists z -
      eDot (residualGradient hexists z) d)).trans hrem
  linarith

/-- The derivative field of the Moreau envelope is literally the residual
gradient represented as a continuous linear functional. -/
theorem moreau_fderiv_is_residual {m : Nat} {X : Set (EVec m)}
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 < ell)
    (hweak : IsWeaklyConvexOn ell X phi)
    (hexists : HasProxEverywhere X phi ell) :
    ∀ z, fderiv ℝ (moreauEnvelope phi ell hexists) z =
      residualCLM (residualGradient hexists z) :=
  fun z => fderiv_moreauEnvelope_eq hell hweak hexists z

/-! ## Weighted product geometry -/

def pairSq {m n : Nat} (mu r : ℝ)
    (q : EVec m) (y : EVec n) : ℝ :=
  1 / mu * vecSq q + r * vecSq y

def pairDot {m n : Nat} (mu r : ℝ)
    (q q' : EVec m) (y y' : EVec n) : ℝ :=
  1 / mu * dot q q' + r * dot y y'

theorem dot_self {d : Nat} (x : EVec d) : dot x x = vecSq x := by
  unfold dot vecSq NCPLVerification.vecSq
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot_add_left {d : Nat} (x y z : EVec d) :
    dot (x + y) z = dot x z + dot y z := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

theorem two_dot_le_sq_add_sq {d : Nat} (x y : EVec d) :
    2 * dot x y ≤ vecSq x + vecSq y := by
  unfold dot vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  nlinarith [sq_nonneg (x i - y i)]

theorem pairSq_nonneg {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r) (q : EVec m) (y : EVec n) :
    0 ≤ pairSq mu r q y := by
  unfold pairSq
  exact add_nonneg
    (mul_nonneg (by positivity) (Tracking.vecSq_nonneg q))
    (mul_nonneg hr (Tracking.vecSq_nonneg y))

theorem pair_young {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r)
    (q q' : EVec m) (y y' : EVec n) :
    2 * pairDot mu r q q' y y' ≤
      pairSq mu r q y + pairSq mu r q' y' := by
  have hq := two_dot_le_sq_add_sq q q'
  have hy := two_dot_le_sq_add_sq y y'
  unfold pairDot pairSq
  have hq' := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ 1 / mu)
  have hy' := mul_le_mul_of_nonneg_left hy hr
  nlinarith

theorem vecSq_sub_triangle_two {d : Nat} (x y z : EVec d) :
    vecSq (x - z) ≤ 2 * vecSq (x - y) + 2 * vecSq (y - z) := by
  have h := Tracking.vecSq_neg_add_le_two (x - y) (z - y)
  have hid : -(x - y) + (z - y) = z - x := by abel
  rw [hid, vecSq_sub_comm z x, vecSq_sub_comm z y] at h
  exact h

theorem vecSq_sub_triangle_four_thirds {d : Nat} (x y z : EVec d) :
    vecSq (x - z) ≤ 4 * vecSq (x - y) + (4 / 3 : ℝ) * vecSq (y - z) := by
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (3 * (x i - y i) - (y i - z i))]

/-! ## Strong minimizers of `Pzr` and exact parameter changes -/

/-- Convenient strong-minimizer predicate in the paper's product metric. -/
def IsPairStrongMinimizer {m n : Nat} (P : EVec m → EVec n → ℝ)
    (mu r : ℝ) (qStar : EVec m) (yStar : EVec n) : Prop :=
  ∀ q y, P qStar yStar + (1 / 2 : ℝ) *
      pairSq mu r (q - qStar) (y - yStar) ≤ P q y

/-- `PointwiseConjugate.Pzr_strongMinimizer` in the non-subtype coordinates
used by `RelativeFOAM.energy`. -/
theorem Pzr_isPairStrongMinimizer {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) {q : EVec m} {y : Y}
    {x : EVec m} {w : EVec n}
    (hsubgrad : IsGammaSubgradient X Y H q y x w)
    (hstationQ : x + mu⁻¹ • q = 0)
    (hstationY : w + r • y.1 = 0) :
    ∀ q' (y' : Y),
      Pzr X Y H mu r q y + (1 / 2 : ℝ) *
          pairSq mu r (q' - q) (y'.1 - y.1) ≤
        Pzr X Y H mu r q' y' := by
  intro q' y'
  have h := Pzr_strongMinimizer hmu hr hsubgrad hstationQ hstationY q' y'
  unfold pairSq
  convert h using 1 <;> ring

theorem Pzr_curvature_identity {m n : Nat}
    (X : Set (EVec m)) (Y : Set (EVec n))
    (H : EVec m → EVec n → ℝ) (mu r : ℝ)
    (q : EVec m) (y : Y) :
    Pzr X Y H mu (r / 4) q y =
      Pzr X Y H mu r q y - (3 * r / 8) * vecSq y.1 := by
  unfold Pzr
  ring

theorem alpha_quarter {mu r : ℝ} (hmu : 0 < mu) (hr : 0 ≤ r) :
    RelativeFOAM.alpha mu (r / 4) = RelativeFOAM.alpha mu r / 2 := by
  have ht : 0 < RelativeFOAM.theta mu := RelativeFOAM.theta_pos hmu
  have ha0 : 0 ≤ RelativeFOAM.alpha mu r := Real.sqrt_nonneg _
  have hb0 : 0 ≤ RelativeFOAM.alpha mu (r / 4) := Real.sqrt_nonneg _
  have ha2 : RelativeFOAM.alpha mu r ^ 2 =
      RelativeFOAM.theta mu * r := Real.sq_sqrt (mul_nonneg ht.le hr)
  have hb2 : RelativeFOAM.alpha mu (r / 4) ^ 2 =
      RelativeFOAM.theta mu * (r / 4) :=
    Real.sq_sqrt (mul_nonneg ht.le (div_nonneg hr (by norm_num)))
  nlinarith

/-! ## Anchor tilt: drift, slow part, and fast gap -/

/-- Strong minimizers of an objective and of its linear tilt move by at most
the dual metric length of the tilt. -/
theorem tilt_minimizer_drift {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r)
    {P PT : EVec m → EVec n → ℝ} {delta : EVec m}
    {qStar qTilt : EVec m} {yStar yTilt : EVec n}
    (hP : IsPairStrongMinimizer P mu r qStar yStar)
    (hPT : IsPairStrongMinimizer PT mu r qTilt yTilt)
    (htilt : ∀ q y, PT q y = P q y - 1 / mu * dot delta q) :
    pairSq mu r (qTilt - qStar) (yTilt - yStar) ≤
      1 / mu * vecSq delta := by
  have h1 := hP qTilt yTilt
  have h2 := hPT qStar yStar
  rw [htilt, htilt] at h2
  unfold pairSq at h1 h2 ⊢
  rw [vecSq_sub_comm qStar qTilt, vecSq_sub_comm yStar yTilt] at h2
  have hy := two_dot_le_sq_add_sq delta (qTilt - qStar)
  have hqnonneg : 0 ≤ 1 / mu * vecSq (qTilt - qStar) :=
    mul_nonneg (div_nonneg zero_le_one hmu.le) (Tracking.vecSq_nonneg _)
  have hynonneg : 0 ≤ r * vecSq (yTilt - yStar) := by
    exact mul_nonneg hr (Tracking.vecSq_nonneg _)
  have hdot : dot delta qTilt - dot delta qStar =
      dot delta (qTilt - qStar) := by
    exact (dot_sub_right delta qTilt qStar).symm
  rw [← hdot] at hy
  have hmuinv : 0 ≤ 1 / mu := div_nonneg zero_le_one hmu.le
  have hscaled := mul_le_mul_of_nonneg_left hy hmuinv
  nlinarith

/-- Full anchor-energy estimate from the two concrete strong-minimizer
inequalities and the exact linear-tilt identity. -/
theorem anchor_energy_tilt_bound {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r)
    {P PT : EVec m → EVec n → ℝ} {delta : EVec m}
    {qStar qTilt : EVec m} {yStar yTilt : EVec n}
    (hP : IsPairStrongMinimizer P mu r qStar yStar)
    (hPT : IsPairStrongMinimizer PT mu r qTilt yTilt)
    (htilt : ∀ q y, PT q y = P q y - 1 / mu * dot delta q)
    (S : RelativeFOAM.State m n)
    (halpha0 : 0 ≤ RelativeFOAM.alpha mu r)
    (halpha1 : RelativeFOAM.alpha mu r ≤ 1) :
    RelativeFOAM.energy mu r qTilt yTilt PT (PT qTilt yTilt) S ≤
      2 * RelativeFOAM.energy mu r qStar yStar P (P qStar yStar) S +
        6 * (1 / mu * vecSq delta) := by
  let D2 := pairSq mu r (qTilt - qStar) (yTilt - yStar)
  have hdrift : D2 ≤ 1 / mu * vecSq delta :=
    tilt_minimizer_drift hmu hr hP hPT htilt
  have hslowQ := vecSq_sub_triangle_two S.q qStar qTilt
  have hslowY := vecSq_sub_triangle_two S.y yStar yTilt
  have hfastStrong := hP S.qFast S.yFast
  have hyDelta := two_dot_le_sq_add_sq delta (S.qFast - qStar)
  have htiltFast := htilt S.qFast S.yFast
  have htiltStar := htilt qTilt yTilt
  have hPAtTilt := hP qTilt yTilt
  have hdotFast : dot delta S.qFast - dot delta qStar =
      dot delta (S.qFast - qStar) := by rw [dot_sub_right]
  have hmu0 : 0 ≤ 1 / mu := div_nonneg zero_le_one hmu.le
  have hqscale := mul_le_mul_of_nonneg_left hyDelta hmu0
  have hyDeltaNeg := two_dot_le_sq_add_sq (-delta) (S.qFast - qStar)
  have hdotNeg : dot (-delta) (S.qFast - qStar) =
      -dot delta (S.qFast - qStar) := by
    unfold dot
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.neg_apply]
    ring
  rw [hdotNeg, Tracking.vecSq_neg] at hyDeltaNeg
  have hqscaleNeg := mul_le_mul_of_nonneg_left hyDeltaNeg hmu0
  have hyTilt := two_dot_le_sq_add_sq delta (qTilt - qStar)
  have hqscaleTilt := mul_le_mul_of_nonneg_left hyTilt hmu0
  have hdotTilt : dot delta qTilt - dot delta qStar =
      dot delta (qTilt - qStar) := by rw [dot_sub_right]
  have hlowerTilt :
      P qStar yStar - 1 / mu * dot delta qStar -
          1 / 2 * (1 / mu * vecSq delta) ≤ PT qTilt yTilt := by
    rw [htiltStar]
    unfold pairSq at hPAtTilt
    rw [← hdotTilt] at hqscaleTilt
    have hyMetric : 0 ≤ r * vecSq (yTilt - yStar) :=
      mul_nonneg hr (Tracking.vecSq_nonneg _)
    nlinarith
  have hqYoungFast :
      -(1 / mu) * dot delta (S.qFast - qStar) ≤
        1 / 2 * (1 / mu * vecSq delta) +
          1 / 2 * (1 / mu * vecSq (S.qFast - qStar)) := by
    nlinarith
  have hfast :
      PT S.qFast S.yFast - PT qTilt yTilt ≤
        2 * (P S.qFast S.yFast - P qStar yStar) +
          1 / mu * vecSq delta := by
    rw [htiltFast]
    unfold pairSq at hfastStrong
    rw [← hdotFast] at hqscale
    have hfastMetricNonneg :
        0 ≤ r * vecSq (S.yFast - yStar) :=
      mul_nonneg hr (Tracking.vecSq_nonneg _)
    nlinarith
  unfold RelativeFOAM.energy
  dsimp [D2, pairSq] at hdrift
  have hcoefQ : 0 ≤ 2 * RelativeFOAM.alpha mu r / mu := by positivity
  have hcoefY : 0 ≤ 2 * r := by positivity
  have hslowQscaled := mul_le_mul_of_nonneg_left hslowQ hcoefQ
  have hslowYscaled := mul_le_mul_of_nonneg_left hslowY hcoefY
  rw [vecSq_sub_comm qStar qTilt] at hslowQscaled
  rw [vecSq_sub_comm yStar yTilt] at hslowYscaled
  have hAlphaDrift :
      RelativeFOAM.alpha mu r / mu * vecSq (qTilt - qStar) +
        r * vecSq (yTilt - yStar) ≤
          1 / mu * vecSq (qTilt - qStar) +
            r * vecSq (yTilt - yStar) := by
    have hq0 := Tracking.vecSq_nonneg (qTilt - qStar)
    have := mul_le_mul_of_nonneg_right halpha1 hq0
    have hmuinv : 0 ≤ 1 / mu := div_nonneg zero_le_one hmu.le
    have hscaled := mul_le_mul_of_nonneg_left this hmuinv
    calc
      RelativeFOAM.alpha mu r / mu * vecSq (qTilt - qStar) +
          r * vecSq (yTilt - yStar) =
        (1 / mu) * (RelativeFOAM.alpha mu r * vecSq (qTilt - qStar)) +
          r * vecSq (yTilt - yStar) := by ring
      _ ≤ (1 / mu) * (1 * vecSq (qTilt - qStar)) +
          r * vecSq (yTilt - yStar) := by linarith
      _ = 1 / mu * vecSq (qTilt - qStar) +
          r * vecSq (yTilt - yStar) := by ring
  have hDriftCost :
      4 * (RelativeFOAM.alpha mu r / mu * vecSq (qTilt - qStar) +
        r * vecSq (yTilt - yStar)) ≤ 4 * (1 / mu * vecSq delta) := by
    nlinarith
  have hslow :
      2 * RelativeFOAM.alpha mu r / mu * vecSq (S.q - qTilt) +
          2 * r * vecSq (S.y - yTilt) ≤
        2 * (2 * RelativeFOAM.alpha mu r / mu * vecSq (S.q - qStar) +
          2 * r * vecSq (S.y - yStar)) +
          4 * (1 / mu * vecSq delta) := by
    calc
      2 * RelativeFOAM.alpha mu r / mu * vecSq (S.q - qTilt) +
          2 * r * vecSq (S.y - yTilt) ≤
        2 * RelativeFOAM.alpha mu r / mu *
            (2 * vecSq (S.q - qStar) + 2 * vecSq (qTilt - qStar)) +
          2 * r * (2 * vecSq (S.y - yStar) +
            2 * vecSq (yTilt - yStar)) :=
        add_le_add hslowQscaled hslowYscaled
      _ = 2 * (2 * RelativeFOAM.alpha mu r / mu * vecSq (S.q - qStar) +
            2 * r * vecSq (S.y - yStar)) +
          4 * (RelativeFOAM.alpha mu r / mu * vecSq (qTilt - qStar) +
            r * vecSq (yTilt - yStar)) := by ring
      _ ≤ 2 * (2 * RelativeFOAM.alpha mu r / mu * vecSq (S.q - qStar) +
            2 * r * vecSq (S.y - yStar)) +
          4 * (1 / mu * vecSq delta) :=
        by
          simpa only [add_comm] using add_le_add_left hDriftCost
            (2 * (2 * RelativeFOAM.alpha mu r / mu * vecSq (S.q - qStar) +
              2 * r * vecSq (S.y - yStar)))
  have hfast2 := mul_le_mul_of_nonneg_left hfast (by norm_num : (0 : ℝ) ≤ 2)
  linarith only [hslow, hfast2]

/-! ## Curvature transfer from the concrete objective identity -/

theorem curvature_energy_bound {m n : Nat} {mu r D2 : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hD2 : 0 ≤ D2)
    {P P' : EVec m → EVec n → ℝ}
    {qStar qNew : EVec m} {yStar yNew : EVec n}
    (hPmin : ∀ q y, P qStar yStar ≤ P q y)
    (hPNew : IsPairStrongMinimizer P' mu (r / 4) qNew yNew)
    (hcurv : ∀ q y, P' q y = P q y - (3 * r / 8) * vecSq y)
    (hyNew : vecSq yNew ≤ D2)
    (S : RelativeFOAM.State m n)
    (halpha1 : RelativeFOAM.alpha mu r ≤ 1) :
    RelativeFOAM.energy mu (r / 4) qNew yNew P' (P' qNew yNew) S ≤
      RelativeFOAM.energy mu r qStar yStar P (P qStar yStar) S +
        (27 / 4 : ℝ) * r * D2 := by
  have hdriftRaw := hPNew qStar yStar
  rw [hcurv, hcurv] at hdriftRaw
  have hmin := hPmin qNew yNew
  have hyStar0 := Tracking.vecSq_nonneg yStar
  have hdrift : pairSq mu (r / 4) (qStar - qNew) (yStar - yNew) ≤
      (3 * r / 4) * D2 := by
    unfold pairSq at hdriftRaw ⊢
    have hc : 0 ≤ 3 * r / 8 := by positivity
    have hyNewScaled := mul_le_mul_of_nonneg_left hyNew hc
    have hyStarScaled : 0 ≤ (3 * r / 8) * vecSq yStar :=
      mul_nonneg hc hyStar0
    nlinarith
  have hqtri := vecSq_sub_triangle_two S.q qStar qNew
  have hytri := vecSq_sub_triangle_four_thirds S.y yStar yNew
  have hfast :
      P' S.qFast S.yFast - P' qNew yNew ≤
        P S.qFast S.yFast - P qStar yStar + (3 * r / 8) * D2 := by
    rw [hcurv, hcurv]
    have hyf0 := Tracking.vecSq_nonneg S.yFast
    have hc : 0 ≤ 3 * r / 8 := by positivity
    have hyNewScaled := mul_le_mul_of_nonneg_left hyNew hc
    have hyfScaled : 0 ≤ (3 * r / 8) * vecSq S.yFast :=
      mul_nonneg hc hyf0
    nlinarith
  have haeq := alpha_quarter hmu hr.le
  have haNew0 : 0 ≤ RelativeFOAM.alpha mu (r / 4) := Real.sqrt_nonneg _
  have hcoefQ : 0 ≤ 2 * RelativeFOAM.alpha mu (r / 4) / mu :=
    div_nonneg (mul_nonneg (by norm_num) haNew0) hmu.le
  have hcoefY : 0 ≤ 2 * (r / 4) := by positivity
  have hqscaled := mul_le_mul_of_nonneg_left hqtri hcoefQ
  have hyscaled := mul_le_mul_of_nonneg_left hytri hcoefY
  unfold RelativeFOAM.energy
  rw [haeq]
  rw [haeq] at hqscaled
  unfold pairSq at hdrift
  have hqdrift0 := Tracking.vecSq_nonneg (qStar - qNew)
  have hydrift0 := Tracking.vecSq_nonneg (yStar - yNew)
  have hcoeff :
      2 * (RelativeFOAM.alpha mu r / 2) / mu *
          (2 * vecSq (qStar - qNew)) +
        2 * (r / 4) * ((4 / 3 : ℝ) * vecSq (yStar - yNew)) ≤
          (8 / 3 : ℝ) *
            (1 / mu * vecSq (qStar - qNew) +
              r / 4 * vecSq (yStar - yNew)) := by
    have hqalpha := mul_le_mul_of_nonneg_right halpha1 hqdrift0
    have hmuinv : 0 ≤ 1 / mu := div_nonneg zero_le_one hmu.le
    have hqbound := mul_le_mul_of_nonneg_left hqalpha hmuinv
    have hqnonneg : 0 ≤ 1 / mu * vecSq (qStar - qNew) :=
      mul_nonneg hmuinv hqdrift0
    calc
      2 * (RelativeFOAM.alpha mu r / 2) / mu *
            (2 * vecSq (qStar - qNew)) +
          2 * (r / 4) * ((4 / 3 : ℝ) * vecSq (yStar - yNew)) =
        2 * (1 / mu) *
            (RelativeFOAM.alpha mu r * vecSq (qStar - qNew)) +
          (2 * r / 3) * vecSq (yStar - yNew) := by ring
      _ ≤ 2 * (1 / mu) * (1 * vecSq (qStar - qNew)) +
          (2 * r / 3) * vecSq (yStar - yNew) := by nlinarith
      _ ≤ (8 / 3 : ℝ) *
          (1 / mu * vecSq (qStar - qNew) +
            r / 4 * vecSq (yStar - yNew)) := by nlinarith
  have hDriftCost :
      2 * (RelativeFOAM.alpha mu r / 2) / mu *
            (2 * vecSq (qStar - qNew)) +
          2 * (r / 4) * ((4 / 3 : ℝ) * vecSq (yStar - yNew)) ≤
        2 * r * D2 := by
    nlinarith
  have hslow :
      2 * (RelativeFOAM.alpha mu r / 2) / mu * vecSq (S.q - qNew) +
          2 * (r / 4) * vecSq (S.y - yNew) ≤
        2 * RelativeFOAM.alpha mu r / mu * vecSq (S.q - qStar) +
          2 * r * vecSq (S.y - yStar) + 2 * r * D2 := by
    calc
      2 * (RelativeFOAM.alpha mu r / 2) / mu * vecSq (S.q - qNew) +
          2 * (r / 4) * vecSq (S.y - yNew) ≤
        2 * (RelativeFOAM.alpha mu r / 2) / mu *
            (2 * vecSq (S.q - qStar) + 2 * vecSq (qStar - qNew)) +
          2 * (r / 4) * (4 * vecSq (S.y - yStar) +
            (4 / 3 : ℝ) * vecSq (yStar - yNew)) :=
        add_le_add hqscaled hyscaled
      _ = 2 * RelativeFOAM.alpha mu r / mu * vecSq (S.q - qStar) +
          2 * r * vecSq (S.y - yStar) +
          (2 * (RelativeFOAM.alpha mu r / 2) / mu *
              (2 * vecSq (qStar - qNew)) +
            2 * (r / 4) * ((4 / 3 : ℝ) * vecSq (yStar - yNew))) := by ring
      _ ≤ 2 * RelativeFOAM.alpha mu r / mu * vecSq (S.q - qStar) +
          2 * r * vecSq (S.y - yStar) + 2 * r * D2 :=
        by
          simpa only [add_comm] using add_le_add_left hDriftCost
            (2 * RelativeFOAM.alpha mu r / mu * vecSq (S.q - qStar) +
              2 * r * vecSq (S.y - yStar))
  have hfast2 := mul_le_mul_of_nonneg_left hfast (by norm_num : (0 : ℝ) ≤ 2)
  have hrD : 0 ≤ r * D2 := mul_nonneg hr.le hD2
  linarith only [hslow, hfast2, hrD]

/-! ## Startup: residual arithmetic and the initial radius -/

/-- The exact quadratic inequality obtained from strong monotonicity and the
startup relative residual gives both distance estimates used in the TeX. -/
theorem startup_distance_bounds {A B R : ℝ}
    (hmaster : 3 * A ^ 2 - 2 * A * B + B ^ 2 ≤ R ^ 2) :
    A ^ 2 ≤ R ^ 2 / 2 ∧ B ^ 2 ≤ (3 / 2 : ℝ) * R ^ 2 := by
  constructor
  · nlinarith [sq_nonneg (B - A)]
  · nlinarith [sq_nonneg (3 * A - B)]

theorem startup_fast_gap_bound {A B R gap : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hmaster : 3 * A ^ 2 - 2 * A * B + B ^ 2 ≤ R ^ 2)
    (hgap : gap ≤ 2 * A * B) :
    gap ≤ Real.sqrt 3 * R ^ 2 := by
  rcases startup_distance_bounds hmaster with ⟨hA2, hB2⟩
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hAB0 : 0 ≤ 2 * A * B := by positivity
  have hR2 : 0 ≤ R ^ 2 := sq_nonneg _
  have hprod : A ^ 2 * B ^ 2 ≤ (3 / 4 : ℝ) * R ^ 4 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hA2) (sq_nonneg B),
      mul_nonneg (sub_nonneg.2 hB2) (sq_nonneg A)]
  have hsq : (2 * A * B) ^ 2 ≤ (Real.sqrt 3 * R ^ 2) ^ 2 := by
    calc
      (2 * A * B) ^ 2 = 4 * (A ^ 2 * B ^ 2) := by ring
      _ ≤ 3 * R ^ 4 := by nlinarith
      _ = (Real.sqrt 3 * R ^ 2) ^ 2 := by rw [mul_pow, hs2]; ring
  have hright0 : 0 ≤ Real.sqrt 3 * R ^ 2 := mul_nonneg hs0 hR2
  exact hgap.trans ((sq_le_sq₀ hAB0 hright0).1 hsq)

/-- Startup energy with coincident slow/fast states, derived from the raw
strong-monotonicity/residual quadratic and fast-gap inequality. -/
theorem startup_energy_from_residual {m n : Nat} {mu r A B R : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    {P : EVec m → EVec n → ℝ} {qStar qf : EVec m}
    {yStar yf : EVec n}
    (halpha : RelativeFOAM.alpha mu r = 1)
    (hmetric : pairSq mu r (qf - qStar) (yf - yStar) = A ^ 2)
    (hmaster : 3 * A ^ 2 - 2 * A * B + B ^ 2 ≤ R ^ 2)
    (hgap : P qf yf - P qStar yStar ≤ 2 * A * B) :
    RelativeFOAM.energy mu r qStar yStar P (P qStar yStar)
        { q := qf, y := yf, qFast := qf, yFast := yf } ≤
      (1 + 2 * Real.sqrt 3) * R ^ 2 := by
  have hfast := startup_fast_gap_bound hA hB hmaster hgap
  have hdist := (startup_distance_bounds hmaster).1
  unfold pairSq at hmetric
  unfold RelativeFOAM.energy
  dsimp
  have hslow :
      2 * RelativeFOAM.alpha mu r / mu * vecSq (qf - qStar) +
          2 * r * vecSq (yf - yStar) = 2 * A ^ 2 := by
    rw [halpha]
    linear_combination 2 * hmetric
  linarith

/-- A genuine proximal minimizer and an initial value gap control its squared
displacement; no startup-radius estimate is assumed. -/
theorem prox_displacement_from_initial_gap {m : Nat}
    {X : Set (EVec m)} {phi : EVec m → ℝ} {mu lower gap : ℝ}
    {z xStar : EVec m} (hz : z ∈ X)
    (hprox : IsProxPoint X phi mu z xStar)
    (hlower : lower ≤ phi xStar)
    (hgap : phi z - lower ≤ gap) :
    mu * vecSq (z - xStar) ≤ gap := by
  have hmin := hprox.2 z hz
  rw [vecSq_sub_comm xStar z] at hmin
  have hzero : vecSq (z - z) = 0 := by
    simp [vecSq, NCPLVerification.vecSq]
  rw [hzero] at hmin
  linarith

/-- The concrete conjugate/primal relation and dual-radius bound yield the
paper's startup metric radius. -/
theorem startup_radius_bound {m n : Nat} {mu r Delta D2 : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r)
    {z xStar : EVec m} {yStar : EVec n}
    (hprimal : mu * vecSq (z - xStar) ≤ Delta + r / 2 * D2)
    (hy : vecSq yStar ≤ D2) :
    pairSq mu r (((-mu) • z) - ((-mu) • xStar)) (0 - yStar) ≤
      Delta + (3 / 2 : ℝ) * r * D2 := by
  have hscale :
      vecSq (((-mu) • z) - ((-mu) • xStar)) =
        mu ^ 2 * vecSq (z - xStar) := by
    unfold vecSq NCPLVerification.vecSq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hy0 : vecSq (0 - yStar) = vecSq yStar := by
    rw [zero_sub, Tracking.vecSq_neg]
  unfold pairSq
  rw [hscale, hy0]
  have hyr := mul_le_mul_of_nonneg_left hy hr
  field_simp [ne_of_gt hmu]
  nlinarith

end

end TrackingAnalytic
end Upper
end NCCLowerBoundVerification
