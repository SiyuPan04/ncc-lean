import NCCLowerBoundVerification.Upper.PointwiseConjugate
import NCCLowerBoundVerification.Upper.ProjectionGeometry

/-!
# Relative FOAM one-step contraction

This module proves the Lyapunov contraction in TeX 1764--1895 directly from
the two macro updates, the single combined relative-residual test, and the
strong-support inequality for the pointwise-conjugate objective.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace RelativeFOAMContraction

noncomputable section

set_option maxHeartbeats 800000

open RelativeFOAM
open PointwiseConjugate

private theorem scalar_q_update_bound
    {mu a q qf qg qp x qs : ℝ} (hmu : 0 < mu) (ha : 0 < a)
    (hale : a ≤ 1)
    (hqg : qg = a * q + (1 - a) * qf) :
    2 / mu *
        (q + mu / 2 * ((qp - q) / mu) -
          mu / 2 * (x + qp / mu) - qs) ^ 2 ≤
      1 / mu * (q - qs) ^ 2 + 1 / mu * (qp - qs) ^ 2 +
      2 / a * (x + qp / mu) * ((1 - a) * qf + a * qs - qp) +
      1 / a *
        (8 / mu * (qp + mu / 2 * (x - qg / mu)) ^ 2 -
          mu / 8 * (x + qg / mu) ^ 2) := by
  subst qg
  let p := 4 * a ^ 2 + 9 * a - 18
  let z₁ :=
    -(4 * a * q - 3 * a * qf - a * qp + 3 * qf - 6 * qp - 3 * (mu * x)) /
      (a + 6)
  let z₂ :=
    (13 * a ^ 2 * q - 9 * a ^ 2 * qf + 4 * a ^ 2 * (mu * x) -
      18 * a * q + 27 * a * qf + 9 * a * (mu * x) -
      18 * qf - 18 * (mu * x)) / p
  have ha2 : a ^ 2 ≤ a := by
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hale)]
  have hp : p < 0 := by
    dsimp [p]
    nlinarith
  have hd₁ : 0 ≤ (a + 6) / a := by positivity
  have hd₂ : 0 ≤ -p / (8 * a * (a + 6)) := by
    exact div_nonneg (by linarith) (by positivity)
  have hd₃ : 0 ≤ 3 * (a - 1) ^ 2 * (5 * a - 6) / (2 * p) := by
    have hn : 3 * (a - 1) ^ 2 * (5 * a - 6) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (by norm_num) (sq_nonneg (a - 1))) (by linarith)
    have hd : 2 * p ≤ 0 := by linarith
    rw [show 3 * (a - 1) ^ 2 * (5 * a - 6) / (2 * p) =
      (-(3 * (a - 1) ^ 2 * (5 * a - 6))) / (-(2 * p)) by ring]
    exact div_nonneg (neg_nonneg.mpr hn) (neg_nonneg.mpr hd)
  have hsos :
      0 ≤ (a + 6) / a * z₁ ^ 2 +
        (-p / (8 * a * (a + 6))) * z₂ ^ 2 +
        (3 * (a - 1) ^ 2 * (5 * a - 6) / (2 * p)) * (q - qf) ^ 2 := by
    positivity
  have hid :
      (1 / mu * (q - qs) ^ 2 + 1 / mu * (qp - qs) ^ 2 +
        2 / a * (x + qp / mu) * ((1 - a) * qf + a * qs - qp) +
        1 / a *
          (8 / mu * (qp + mu / 2 * (x - (a * q + (1 - a) * qf) / mu)) ^ 2 -
            mu / 8 * (x + (a * q + (1 - a) * qf) / mu) ^ 2) -
        2 / mu *
          (q + mu / 2 * ((qp - q) / mu) -
            mu / 2 * (x + qp / mu) - qs) ^ 2) =
      1 / mu * ((a + 6) / a * z₁ ^ 2 +
        (-p / (8 * a * (a + 6))) * z₂ ^ 2 +
        (3 * (a - 1) ^ 2 * (5 * a - 6) / (2 * p)) * (q - qf) ^ 2) := by
    dsimp [z₁, z₂]
    field_simp [ne_of_gt hmu, ne_of_gt ha, ne_of_lt hp]
    ring
  have hmuinv : 0 ≤ 1 / mu := by positivity
  have := mul_nonneg hmuinv hsos
  nlinarith

private theorem scalar_y_update_bound
    {mu a y yf yg yp w ys : ℝ} (hmu : 0 < mu) (ha : 0 < a)
    (hale : a ≤ 1) (hyg : yg = a * y + (1 - a) * yf) :
    (a * mu / 4) *
        (y + (4 / (a * mu)) * ((a ^ 2 * mu / 8) * (yp - y)) -
          (4 / (a * mu)) * (w + (a ^ 2 * mu / 8) * yp) - ys) ^ 2 ≤
      (a * mu / 4 - a ^ 2 * mu / 8) * (y - ys) ^ 2 +
      (a ^ 2 * mu / 8) * (yp - ys) ^ 2 +
      2 / a * (w + (a ^ 2 * mu / 8) * yp) *
        ((1 - a) * yf + a * ys - yp) +
      1 / a *
        (8 / mu *
            (w + (a ^ 2 * mu / 8) * yp +
              mu / 8 * (yp - yg)) ^ 2 -
          mu / 8 * (yp - yg) ^ 2) := by
  subst yg
  let z := a ^ 2 * mu * y - 2 * a ^ 2 * mu * yp - 8 * w
  have hc : 0 ≤ a ^ 2 * mu * (1 - a) / 8 := by positivity
  have hsos :
      0 ≤ z ^ 2 / (16 * a * mu) +
        (a ^ 2 * mu * (1 - a) / 8) * (y - yp) ^ 2 := by
    positivity
  have hid :
      ((a * mu / 4 - a ^ 2 * mu / 8) * (y - ys) ^ 2 +
        (a ^ 2 * mu / 8) * (yp - ys) ^ 2 +
        2 / a * (w + (a ^ 2 * mu / 8) * yp) *
          ((1 - a) * yf + a * ys - yp) +
        1 / a *
          (8 / mu *
              (w + (a ^ 2 * mu / 8) * yp +
                mu / 8 * (yp - (a * y + (1 - a) * yf))) ^ 2 -
            mu / 8 * (yp - (a * y + (1 - a) * yf)) ^ 2) -
        (a * mu / 4) *
          (y + (4 / (a * mu)) * ((a ^ 2 * mu / 8) * (yp - y)) -
            (4 / (a * mu)) * (w + (a ^ 2 * mu / 8) * yp) - ys) ^ 2) =
      z ^ 2 / (16 * a * mu) +
        (a ^ 2 * mu * (1 - a) / 8) * (y - yp) ^ 2 := by
    dsimp [z]
    field_simp [ne_of_gt hmu, ne_of_gt ha]
    ring
  nlinarith

theorem alpha_sq_eq {mu r : ℝ} (hmu : 0 < mu) (hr : 0 ≤ r) :
    alpha mu r ^ 2 = theta mu * r := by
  unfold alpha
  exact Real.sq_sqrt (mul_nonneg (theta_pos hmu).le hr)

theorem r_eq_alpha_sq {mu r : ℝ} (hmu : 0 < mu) (hr : 0 ≤ r) :
    r = alpha mu r ^ 2 * mu / 8 := by
  have h := alpha_sq_eq hmu hr
  unfold theta at h
  field_simp [ne_of_gt hmu] at h ⊢
  nlinarith

theorem etaY_eq {mu r : ℝ} (hmu : 0 < mu) (hr : 0 < r) :
    etaY mu r = 4 / (alpha mu r * mu) := by
  unfold etaY theta
  field_simp [ne_of_gt hmu, ne_of_gt (alpha_pos hmu hr)]
  norm_num

private theorem q_macro_bound {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hrmu : r ≤ mu / 8)
    (S : State m n) (O : MicroOutput m n) (qStar : EVec m) :
    2 / mu * vecSq (slowQNext mu r S O - qStar) ≤
      1 / mu * vecSq (S.q - qStar) +
      1 / mu * vecSq (O.qFastNext - qStar) +
      2 / alpha mu r *
        dot (O.xFast + mu⁻¹ • O.qFastNext)
          ((1 - alpha mu r) • S.qFast + alpha mu r • qStar -
            O.qFastNext) +
      1 / alpha mu r *
        (8 / mu * vecSq (residualX mu r S O) -
          mu / 8 * vecSq (O.xFast + mu⁻¹ • qCenter mu r S)) := by
  have ha := alpha_pos hmu hr
  have hale := alpha_le_one hmu hr.le hrmu
  have hcoord : ∀ i : Fin m,
      2 / mu * (slowQNext mu r S O i - qStar i) ^ 2 ≤
        1 / mu * (S.q i - qStar i) ^ 2 +
        1 / mu * (O.qFastNext i - qStar i) ^ 2 +
        2 / alpha mu r *
          (O.xFast i + O.qFastNext i / mu) *
            ((1 - alpha mu r) * S.qFast i + alpha mu r * qStar i -
              O.qFastNext i) +
        1 / alpha mu r *
          (8 / mu * residualX mu r S O i ^ 2 -
            mu / 8 * (O.xFast i + qCenter mu r S i / mu) ^ 2) := by
    intro i
    have hs := scalar_q_update_bound
        (mu := mu) (a := alpha mu r) (q := S.q i) (qf := S.qFast i)
        (qg := qCenter mu r S i) (qp := O.qFastNext i)
        (x := O.xFast i) (qs := qStar i) hmu ha hale (by simp [qCenter])
    simp only [qCenter, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs
    unfold slowQNext residualX qCenter etaQ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    convert hs using 1 <;> field_simp [ne_of_gt hmu, ne_of_gt ha]
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ (Finset.univ : Finset (Fin m))) =>
    hcoord i
  simp [vecSq, NCPLVerification.vecSq, dot, slowQNext, residualX,
    qCenter, etaQ, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, div_eq_mul_inv, mul_add, mul_sub, mul_assoc, mul_left_comm,
    mul_comm] at hsum ⊢
  exact hsum

private theorem y_macro_bound {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hrmu : r ≤ mu / 8)
    (S : State m n) (O : MicroOutput m n) (yStar : EVec n) :
    (etaY mu r)⁻¹ * vecSq (slowYNext mu r S O - yStar) ≤
      ((etaY mu r)⁻¹ - r) * vecSq (S.y - yStar) +
      r * vecSq (O.yFastNext - yStar) +
      2 / alpha mu r *
        dot (O.wFastNext + r • O.yFastNext)
          ((1 - alpha mu r) • S.yFast + alpha mu r • yStar -
            O.yFastNext) +
      1 / alpha mu r *
        (theta mu * vecSq (residualY mu r S O) -
          (theta mu)⁻¹ * vecSq (O.yFastNext - yCenter mu r S)) := by
  let a := alpha mu r
  have ha : 0 < a := by simpa [a] using alpha_pos hmu hr
  have hale : a ≤ 1 := by simpa [a] using alpha_le_one hmu hr.le hrmu
  have hrid : r = a ^ 2 * mu / 8 := by
    simpa [a] using r_eq_alpha_sq hmu hr.le
  have heta : etaY mu r = 4 / (a * mu) := by
    simpa [a] using etaY_eq hmu hr
  have htheta : theta mu = 8 / mu := rfl
  have hcoord : ∀ i : Fin n,
      (etaY mu r)⁻¹ * (slowYNext mu r S O i - yStar i) ^ 2 ≤
        ((etaY mu r)⁻¹ - r) * (S.y i - yStar i) ^ 2 +
        r * (O.yFastNext i - yStar i) ^ 2 +
        2 / a *
          (O.wFastNext i + r * O.yFastNext i) *
            ((1 - a) * S.yFast i + a * yStar i -
              O.yFastNext i) +
        1 / a *
          (theta mu * residualY mu r S O i ^ 2 -
            (theta mu)⁻¹ * (O.yFastNext i - yCenter mu r S i) ^ 2) := by
    intro i
    have hs := scalar_y_update_bound
      (mu := mu) (a := a) (y := S.y i) (yf := S.yFast i)
      (yg := yCenter mu r S i) (yp := O.yFastNext i)
      (w := O.wFastNext i) (ys := yStar i) hmu ha hale (by simp [yCenter, a])
    simp only [yCenter, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hs
    unfold slowYNext residualY yCenter
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [show alpha mu r = a by rfl] at hs ⊢
    rw [heta, hrid, htheta]
    convert hs using 1 <;> field_simp [ne_of_gt hmu, ne_of_gt ha]
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ (Finset.univ : Finset (Fin n))) =>
    hcoord i
  simp [vecSq, NCPLVerification.vecSq, dot, slowYNext, residualY,
    yCenter, Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, div_eq_mul_inv, mul_add, mul_sub, mul_assoc,
    mul_left_comm, mul_comm, a] at hsum ⊢
  exact hsum

theorem alpha_mul_etaY_inv {mu r : ℝ} (hmu : 0 < mu) (hr : 0 < r) :
    alpha mu r * (etaY mu r)⁻¹ = 2 * r := by
  rw [etaY_eq hmu hr]
  have ha := ne_of_gt (alpha_pos hmu hr)
  have hs := alpha_sq_eq hmu hr.le
  unfold theta at hs
  field_simp [ha, ne_of_gt hmu] at hs ⊢
  nlinarith

/-- The two macro-update estimates after they are added and the *single*
combined relative residual is applied. -/
theorem combined_macro_bound {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hrmu : r ≤ mu / 8)
    (S : State m n) (O : MicroOutput m n)
    (qStar : EVec m) (yStar : EVec n)
    (hres : RelativeResidual mu r S O) :
    2 * alpha mu r / mu * vecSq (slowQNext mu r S O - qStar) +
        2 * r * vecSq (slowYNext mu r S O - yStar) ≤
      alpha mu r / mu * vecSq (S.q - qStar) +
      (2 * r - alpha mu r * r) * vecSq (S.y - yStar) +
      alpha mu r / mu * vecSq (O.qFastNext - qStar) +
      alpha mu r * r * vecSq (O.yFastNext - yStar) +
      2 * dot (O.xFast + mu⁻¹ • O.qFastNext)
        ((1 - alpha mu r) • S.qFast + alpha mu r • qStar - O.qFastNext) +
      2 * dot (O.wFastNext + r • O.yFastNext)
        ((1 - alpha mu r) • S.yFast + alpha mu r • yStar - O.yFastNext) := by
  have ha := alpha_pos hmu hr
  have hq := q_macro_bound hmu hr hrmu S O qStar
  have hy := y_macro_bound hmu hr hrmu S O yStar
  have hsum := add_le_add hq hy
  have hmul := mul_le_mul_of_nonneg_left hsum ha.le
  have heta := alpha_mul_etaY_inv hmu hr
  have ha0 : alpha mu r ≠ 0 := ne_of_gt ha
  have hclean :
      2 * alpha mu r / mu * vecSq (slowQNext mu r S O - qStar) +
          2 * r * vecSq (slowYNext mu r S O - yStar) ≤
        alpha mu r / mu * vecSq (S.q - qStar) +
        (2 * r - alpha mu r * r) * vecSq (S.y - yStar) +
        alpha mu r / mu * vecSq (O.qFastNext - qStar) +
        alpha mu r * r * vecSq (O.yFastNext - yStar) +
        2 * dot (O.xFast + mu⁻¹ • O.qFastNext)
          ((1 - alpha mu r) • S.qFast + alpha mu r • qStar - O.qFastNext) +
        2 * dot (O.wFastNext + r • O.yFastNext)
          ((1 - alpha mu r) • S.yFast + alpha mu r • yStar - O.yFastNext) +
        (8 / mu * vecSq (residualX mu r S O) -
          mu / 8 * vecSq (O.xFast + mu⁻¹ • qCenter mu r S)) +
        (theta mu * vecSq (residualY mu r S O) -
          (theta mu)⁻¹ * vecSq (O.yFastNext - yCenter mu r S)) := by
    calc
      2 * alpha mu r / mu * vecSq (slowQNext mu r S O - qStar) +
          2 * r * vecSq (slowYNext mu r S O - yStar) =
        alpha mu r *
          (2 / mu * vecSq (slowQNext mu r S O - qStar) +
            (etaY mu r)⁻¹ * vecSq (slowYNext mu r S O - yStar)) := by
              rw [← heta]
              ring
      _ ≤ alpha mu r *
          (1 / mu * vecSq (S.q - qStar) +
            1 / mu * vecSq (O.qFastNext - qStar) +
            2 / alpha mu r *
              dot (O.xFast + mu⁻¹ • O.qFastNext)
                ((1 - alpha mu r) • S.qFast + alpha mu r • qStar -
                  O.qFastNext) +
            1 / alpha mu r *
              (8 / mu * vecSq (residualX mu r S O) -
                mu / 8 * vecSq (O.xFast + mu⁻¹ • qCenter mu r S)) +
            (((etaY mu r)⁻¹ - r) * vecSq (S.y - yStar) +
              r * vecSq (O.yFastNext - yStar) +
              2 / alpha mu r *
                dot (O.wFastNext + r • O.yFastNext)
                  ((1 - alpha mu r) • S.yFast + alpha mu r • yStar -
                    O.yFastNext) +
              1 / alpha mu r *
                (theta mu * vecSq (residualY mu r S O) -
                  (theta mu)⁻¹ *
                    vecSq (O.yFastNext - yCenter mu r S)))) := hmul
      _ = _ := by
        rw [← heta]
        field_simp [ha0, ne_of_gt hmu]
        ring
  have herr :
      (8 / mu * vecSq (residualX mu r S O) -
          mu / 8 * vecSq (O.xFast + mu⁻¹ • qCenter mu r S)) +
        (theta mu * vecSq (residualY mu r S O) -
          (theta mu)⁻¹ * vecSq (O.yFastNext - yCenter mu r S)) ≤ 0 := by
    unfold RelativeResidual at hres
    linarith
  linarith

def PzrTotal {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (H : EVec m → EVec n → ℝ) (mu r : ℝ) (q : EVec m) (y : EVec n) : ℝ :=
  by
    classical
    exact if hy : y ∈ Y then Pzr X Y H mu r q ⟨y, hy⟩ else 0

@[simp] theorem PzrTotal_of_mem {m n : Nat}
    (X : Set (EVec m)) (Y : Set (EVec n))
    (H : EVec m → EVec n → ℝ) (mu r : ℝ)
    (q : EVec m) {y : EVec n} (hy : y ∈ Y) :
    PzrTotal X Y H mu r q y = Pzr X Y H mu r q ⟨y, hy⟩ := by
  classical
  simp [PzrTotal, hy]

private theorem dot_affine {d : Nat} (g u v w : EVec d) (a : ℝ) :
    dot g ((1 - a) • u + a • v - w) =
      (1 - a) * dot g (u - w) + a * dot g (v - w) := by
  unfold dot
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

private theorem vecSq_sub_comm_local {d : Nat} (u v : EVec d) :
    vecSq (u - v) = vecSq (v - u) := by
  unfold vecSq NCPLVerification.vecSq
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

/-- TeX `ub:eq:one-step-contraction`, derived from the concrete update and
the actual strong-support theorem for `Pzr`. -/
theorem oneStep_energy_contraction {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hrmu : r ≤ mu / 8)
    (S : State m n) (O : MicroOutput m n)
    (hyFast : S.yFast ∈ Y) (hyNext : O.yFastNext ∈ Y)
    (qStar : EVec m) (yStar : Y)
    (hmin : ∀ q (y : Y),
      Pzr X Y H mu r qStar yStar ≤ Pzr X Y H mu r q y)
    (hsubgrad : IsGammaSubgradient X Y H O.qFastNext
      ⟨O.yFastNext, hyNext⟩ O.xFast O.wFastNext)
    (hres : RelativeResidual mu r S O) :
    energy mu r qStar yStar.1 (PzrTotal X Y H mu r)
        (Pzr X Y H mu r qStar yStar) (update mu r S O) ≤
      (1 - alpha mu r / 2) *
        energy mu r qStar yStar.1 (PzrTotal X Y H mu r)
          (Pzr X Y H mu r qStar yStar) S := by
  classical
  let a := alpha mu r
  let Pp := Pzr X Y H mu r O.qFastNext ⟨O.yFastNext, hyNext⟩
  let Pf := Pzr X Y H mu r S.qFast ⟨S.yFast, hyFast⟩
  let Ps := Pzr X Y H mu r qStar yStar
  let gq := O.xFast + mu⁻¹ • O.qFastNext
  let gy := O.wFastNext + r • O.yFastNext
  have ha : 0 < a := by simpa [a] using alpha_pos hmu hr
  have hale : a ≤ 1 := by simpa [a] using alpha_le_one hmu hr.le hrmu
  have hsOld := Pzr_strongSupport (r := r) hmu hsubgrad
    S.qFast ⟨S.yFast, hyFast⟩
  have hsStar := Pzr_strongSupport (r := r) hmu hsubgrad qStar yStar
  have hqnonneg := ProjectionGeometry.vecSq_nonneg (S.qFast - O.qFastNext)
  have hynonneg := ProjectionGeometry.vecSq_nonneg (S.yFast - O.yFastNext)
  have hold :
      dot gq (S.qFast - O.qFastNext) +
          dot gy (S.yFast - O.yFastNext) ≤ Pf - Pp := by
    dsimp [gq, gy, Pf, Pp] at hsOld ⊢
    have hcq : 0 ≤ 1 / (2 * mu) := by positivity
    have hcy : 0 ≤ r / 2 := by positivity
    nlinarith [mul_nonneg hcq hqnonneg, mul_nonneg hcy hynonneg]
  have hstar :
      Pp + dot gq (qStar - O.qFastNext) +
          dot gy (yStar.1 - O.yFastNext) +
          1 / (2 * mu) * vecSq (qStar - O.qFastNext) +
          r / 2 * vecSq (yStar.1 - O.yFastNext) ≤ Ps := by
    simpa [gq, gy, Pp, Ps] using hsStar
  have holdScaled := mul_le_mul_of_nonneg_left hold (sub_nonneg.mpr hale)
  have hstarScaled := mul_le_mul_of_nonneg_left hstar ha.le
  have hsupport :
      2 * dot gq ((1 - a) • S.qFast + a • qStar - O.qFastNext) +
          2 * dot gy ((1 - a) • S.yFast + a • yStar.1 - O.yFastNext) +
          a / mu * vecSq (O.qFastNext - qStar) +
          a * r * vecSq (O.yFastNext - yStar.1) ≤
        2 * (1 - a) * (Pf - Pp) + 2 * a * (Ps - Pp) := by
    rw [dot_affine, dot_affine]
    rw [vecSq_sub_comm_local O.qFastNext qStar,
      vecSq_sub_comm_local O.yFastNext yStar.1]
    have hmucoeff : 2 * a * (1 / (2 * mu)) = a / mu := by
      field_simp [ne_of_gt hmu]
    have hrcoeff : 2 * a * (r / 2) = a * r := by ring
    rw [← hmucoeff, ← hrcoeff]
    nlinarith
  have hmacro := combined_macro_bound hmu hr hrmu S O qStar yStar.1 hres
  unfold energy
  dsimp only [update]
  rw [PzrTotal_of_mem X Y H mu r O.qFastNext hyNext,
    PzrTotal_of_mem X Y H mu r S.qFast hyFast]
  change
    2 * a / mu * vecSq (slowQNext mu r S O - qStar) +
        2 * r * vecSq (slowYNext mu r S O - yStar.1) + 2 * (Pp - Ps) ≤
      (1 - a / 2) *
        (2 * a / mu * vecSq (S.q - qStar) +
          2 * r * vecSq (S.y - yStar.1) + 2 * (Pf - Ps))
  have hgap : 0 ≤ Pf - Ps := by
    dsimp [Pf, Ps]
    linarith [hmin S.qFast ⟨S.yFast, hyFast⟩]
  have hqslow := ProjectionGeometry.vecSq_nonneg (S.q - qStar)
  have hyslow := ProjectionGeometry.vecSq_nonneg (S.y - yStar.1)
  have hmid :
      2 * a / mu * vecSq (slowQNext mu r S O - qStar) +
          2 * r * vecSq (slowYNext mu r S O - yStar.1) + 2 * (Pp - Ps) ≤
        a / mu * vecSq (S.q - qStar) +
          (2 * r - a * r) * vecSq (S.y - yStar.1) +
          2 * (1 - a) * (Pf - Ps) := by
    nlinarith
  have hqextra :
      0 ≤ a * (1 - a) / mu * vecSq (S.q - qStar) := by positivity
  have hfextra : 0 ≤ a * (Pf - Ps) := mul_nonneg ha.le hgap
  have hcoeff :
      a / mu * vecSq (S.q - qStar) +
          (2 * r - a * r) * vecSq (S.y - yStar.1) +
          2 * (1 - a) * (Pf - Ps) ≤
        (1 - a / 2) *
          (2 * a / mu * vecSq (S.q - qStar) +
            2 * r * vecSq (S.y - yStar.1) + 2 * (Pf - Ps)) := by
    have hid :
        (1 - a / 2) *
            (2 * a / mu * vecSq (S.q - qStar) +
              2 * r * vecSq (S.y - yStar.1) + 2 * (Pf - Ps)) -
          (a / mu * vecSq (S.q - qStar) +
            (2 * r - a * r) * vecSq (S.y - yStar.1) +
            2 * (1 - a) * (Pf - Ps)) =
          a * (1 - a) / mu * vecSq (S.q - qStar) + a * (Pf - Ps) := by
      field_simp [ne_of_gt hmu]
      ring
    nlinarith
  exact hmid.trans hcoeff

/-- A version whose gamma-subgradient input is obtained from the actual micro
normal relations and the primal/dual support inequalities. -/
theorem oneStep_energy_contraction_of_microRelations {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hrmu : r ≤ mu / 8)
    (S : State m n) (O : MicroOutput m n)
    (hyFast : S.yFast ∈ Y) (hyNext : O.yFastNext ∈ Y)
    (qStar : EVec m) (yStar : Y)
    (hmin : ∀ q (y : Y),
      Pzr X Y H mu r qStar yStar ≤ Pzr X Y H mu r q y)
    (gradX : EVec m) (gradY : EVec n)
    (hbounded : GammaBddAbove X Y H)
    (hx : O.xFast ∈ X)
    (hsupportX : ConvexSupportX X H gradX O.xFast O.yFastNext)
    (hsupportY : ConcaveSupportY Y H gradY O.xFast O.yFastNext)
    (hnormalX : IsEuclideanNormal X O.xFast (O.qFastNext - gradX))
    (hnormalY : IsEuclideanNormal Y O.yFastNext (O.wFastNext + gradY))
    (hres : RelativeResidual mu r S O) :
    energy mu r qStar yStar.1 (PzrTotal X Y H mu r)
        (Pzr X Y H mu r qStar yStar) (update mu r S O) ≤
      (1 - alpha mu r / 2) *
        energy mu r qStar yStar.1 (PzrTotal X Y H mu r)
          (Pzr X Y H mu r qStar yStar) S := by
  have hgamma : IsGammaSubgradient X Y H O.qFastNext
      ⟨O.yFastNext, hyNext⟩ O.xFast O.wFastNext :=
    gamma_subgradient hbounded hx hsupportX hsupportY hnormalX hnormalY
  exact oneStep_energy_contraction hmu hr hrmu S O hyFast hyNext qStar yStar
    hmin hgamma hres

abbrev ValidState {m n : Nat} (Y : Set (EVec n)) :=
  {S : State m n // S.yFast ∈ Y}

def foamStep {m n : Nat} {Y : Set (EVec n)} (mu r : ℝ)
    (oracle : ValidState (m := m) Y → MicroOutput m n)
    (hyNext : ∀ S, (oracle S).yFastNext ∈ Y)
    (S : ValidState (m := m) Y) : ValidState (m := m) Y :=
  ⟨update mu r S.1 (oracle S), hyNext S⟩

/-- Block specialization obtained by iterating the concrete update.  No
macrostep contraction is accepted as a premise. -/
theorem block_energy_contraction {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r rho : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hrmu : r ≤ mu / 8)
    (qStar : EVec m) (yStar : Y)
    (hmin : ∀ q (y : Y),
      Pzr X Y H mu r qStar yStar ≤ Pzr X Y H mu r q y)
    (oracle : ValidState (m := m) Y → MicroOutput m n)
    (hyNext : ∀ S, (oracle S).yFastNext ∈ Y)
    (hsubgrad : ∀ S, IsGammaSubgradient X Y H (oracle S).qFastNext
      ⟨(oracle S).yFastNext, hyNext S⟩ (oracle S).xFast (oracle S).wFastNext)
    (hres : ∀ S, RelativeResidual mu r S.1 (oracle S))
    (S0 : ValidState (m := m) Y)
    (hrho : 0 < rho) (hrho1 : rho < 1) :
    energy mu r qStar yStar.1 (PzrTotal X Y H mu r)
        (Pzr X Y H mu r qStar yStar)
        (((foamStep mu r oracle hyNext)^[blockIterations (alpha mu r) rho] S0).1) ≤
      rho * energy mu r qStar yStar.1 (PzrTotal X Y H mu r)
        (Pzr X Y H mu r qStar yStar) S0.1 := by
  let step := foamStep mu r oracle hyNext
  let E : ValidState (m := m) Y → ℝ := fun S =>
    energy mu r qStar yStar.1 (PzrTotal X Y H mu r)
      (Pzr X Y H mu r qStar yStar) S.1
  have hone : ∀ S, E (step S) ≤ (1 - alpha mu r / 2) * E S := by
    intro S
    exact oneStep_energy_contraction hmu hr hrmu S.1 (oracle S) S.2
      (hyNext S) qStar yStar hmin (hsubgrad S) (hres S)
  have hE0 : 0 ≤ E S0 := by
    have hgap := hmin S0.1.qFast ⟨S0.1.yFast, S0.2⟩
    have hq := ProjectionGeometry.vecSq_nonneg (S0.1.q - qStar)
    have hy := ProjectionGeometry.vecSq_nonneg (S0.1.y - yStar.1)
    have hcq : 0 ≤ 2 * alpha mu r / mu :=
      div_nonneg (mul_nonneg (by norm_num) (alpha_pos hmu hr).le) hmu.le
    dsimp [E]
    unfold energy
    rw [PzrTotal_of_mem X Y H mu r S0.1.qFast S0.2]
    nlinarith [mul_nonneg hcq hq, mul_nonneg (by positivity : 0 ≤ 2 * r) hy]
  have hgeo :
      (1 - alpha mu r / 2) ^ blockIterations (alpha mu r) rho ≤ rho :=
    blockIterations_geometric (alpha_pos hmu hr)
      (by linarith [alpha_le_one hmu hr.le hrmu]) hrho hrho1
  exact block_energy_le step E
    (alpha mu r) rho (blockIterations (alpha mu r) rho) S0
    (by linarith [alpha_le_one hmu hr.le hrmu]) hE0 hone hgeo

end

end RelativeFOAMContraction
end Upper
end NCCLowerBoundVerification
