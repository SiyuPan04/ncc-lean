import NCCLowerBoundVerification.Upper.MoreauEnvelope
import NCCLowerBoundVerification.Upper.RelativeFOAM
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Moving-anchor tracking and the outer descent calculation

This file formalizes TeX 1213--1521 and 1618--2050.  It deliberately separates
three local analytic inputs (the anchor-shift, startup, and curvature-transfer
estimates) from the ensuing, completely algebraic bookkeeping.  Thus none of
the tracking, descent, stopping, or complexity conclusions is hidden in an
algorithmic state.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace Tracking

noncomputable section

open scoped BigOperators

/-! ## Moving the anchor -/

/-- Co-translation of both slow and fast primal dual variables when the anchor
moves by `d`; this is TeX's `q,q^f \mapsto q,q^f-2 ell d`. -/
def coTranslate {m n : Nat} (ell : ℝ) (d : EVec m)
    (S : RelativeFOAM.State m n) : RelativeFOAM.State m n where
  q := S.q - (2 * ell) • d
  y := S.y
  qFast := S.qFast - (2 * ell) • d
  yFast := S.yFast

/-- Scalar form of the relative energy: a slow quadratic part plus twice the
fast primal-dual gap. -/
def splitEnergy (slow fastGap : ℝ) : ℝ := slow + 2 * fastGap

/-- The two local estimates in the moving-anchor proof combine to the factor
`2` and the additive constant `6 A²`.  These premises are the precise local
analytic bridge, rather than the final anchor-shift statement itself. -/
theorem anchor_shift_from_parts {oldSlow oldFast newSlow newFast A2 : ℝ}
    (hslow : newSlow ≤ 2 * oldSlow + 4 * A2)
    (hfast : 2 * newFast ≤ 4 * oldFast + 2 * A2) :
    splitEnergy newSlow newFast ≤ 2 * splitEnergy oldSlow oldFast + 6 * A2 := by
  unfold splitEnergy
  linarith

/-- Substitution `A² = 4 ell ‖d‖²` gives TeX's `24 ell ‖d‖²`. -/
theorem anchor_shift_constant {oldEnergy newEnergy ell d2 : ℝ}
    (h : newEnergy ≤ 2 * oldEnergy + 6 * (4 * ell * d2)) :
    newEnergy ≤ 2 * oldEnergy + 24 * ell * d2 := by
  nlinarith

/-- Majorant passed to the next contracted block. -/
def nextMajorant (rho ell d2 B : ℝ) : ℝ :=
  rho * (2 * B + 24 * ell * d2)

theorem tracked_block_majorant {rho ell d2 B Eshift Enew : ℝ}
    (hshift : Eshift ≤ 2 * B + 24 * ell * d2)
    (hrho : 0 ≤ rho)
    (hblock : Enew ≤ rho * Eshift) :
    Enew ≤ nextMajorant rho ell d2 B := by
  unfold nextMajorant
  nlinarith

/-! ## Startup and homotopy -/

/-- The startup local solver and the radius estimate imply the advertised
constant `5`; the irrational coefficient is discharged here, not assumed. -/
theorem startup_energy_bound {E R2 Delta r0 D2 : ℝ}
    (hE : E ≤ (1 + 2 * Real.sqrt 3) * R2)
    (hR : R2 ≤ Delta + (3 / 2 : ℝ) * r0 * D2)
    (hR0 : 0 ≤ R2) :
    E ≤ 5 * (Delta + (3 / 2 : ℝ) * r0 * D2) := by
  have hs0 : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hs2 : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc : 1 + 2 * Real.sqrt 3 ≤ 5 := by nlinarith
  have htarget : 0 ≤ Delta + (3 / 2 : ℝ) * r0 * D2 := le_trans hR0 hR
  nlinarith

/-- The paper's chosen initial majorant dominates the startup estimate. -/
theorem startup_majorized {E Delta r0 D2 : ℝ}
    (hE : E ≤ 5 * (Delta + (3 / 2 : ℝ) * r0 * D2))
    (hDelta : 0 ≤ Delta) (hrD : 0 ≤ r0 * D2) :
    E ≤ 8 * (Delta + r0 * D2) := by
  nlinarith

/-- At fixed state, the slow and fast curvature-change estimates give
`E_{r/4} ≤ E_r + 27 r D² / 4`. -/
theorem curvature_transfer_from_parts
    {oldSlow oldFast newSlow newFast r D2 : ℝ}
    (hslow : newSlow ≤ oldSlow + 6 * r * D2)
    (hfast : 2 * newFast ≤ 2 * oldFast + (3 / 4 : ℝ) * r * D2) :
    splitEnergy newSlow newFast ≤
      splitEnergy oldSlow oldFast + (27 / 4 : ℝ) * r * D2 := by
  unfold splitEnergy
  linarith

/-- Curvature schedule `r_j=r_0/4^j`. -/
def curvature (r0 : ℝ) (j : ℕ) : ℝ := r0 / (4 : ℝ) ^ j

/-- The contracted majorant after one curvature reduction. -/
def homotopyMajorant (r0 D2 B0 : ℝ) : ℕ → ℝ
  | 0 => B0
  | j + 1 =>
      (homotopyMajorant r0 D2 B0 j +
        (27 / 4 : ℝ) * curvature r0 j * D2) / 8

/-- A recurrence stated with its curvature explicitly.  This is easier to use
than hiding the problem radius inside a recursively defined program. -/
def HomotopyRecurrence (r B : ℕ → ℝ) (D2 : ℝ) : Prop :=
  ∀ j, r (j + 1) = r j / 4 ∧
    B (j + 1) = (B j + (27 / 4 : ℝ) * r j * D2) / 8

theorem curvature_succ (r0 : ℝ) (j : ℕ) :
    curvature r0 (j + 1) = curvature r0 j / 4 := by
  unfold curvature
  rw [pow_succ]
  ring

theorem homotopyMajorant_recurrence (r0 D2 B0 : ℝ) :
    HomotopyRecurrence (curvature r0) (homotopyMajorant r0 D2 B0) D2 := by
  intro j
  exact ⟨curvature_succ r0 j, rfl⟩

/-- The sharper one-line induction used in the manuscript. -/
theorem homotopy_geometric_bound {r B : ℕ → ℝ} {D2 : ℝ}
    (hrec : HomotopyRecurrence r B D2) (j : ℕ)
    (hr : ∀ k, 0 ≤ r k) (hD2 : 0 ≤ D2) :
    B j ≤ B 0 / (8 : ℝ) ^ j + (27 / 4 : ℝ) * r j * D2 := by
  induction j with
  | zero =>
      simp only [pow_zero, div_one]
      exact le_add_of_nonneg_right (mul_nonneg (mul_nonneg (by norm_num) (hr 0)) hD2)
  | succ j ih =>
      rcases hrec j with ⟨hrstep, hB⟩
      rw [hB, hrstep, pow_succ]
      calc
        (B j + (27 / 4 : ℝ) * r j * D2) / 8 ≤
            (B 0 / 8 ^ j + (27 / 4 : ℝ) * r j * D2 +
              (27 / 4 : ℝ) * r j * D2) / 8 := by
                gcongr
        _ = B 0 / (8 ^ j * 8) + (27 / 4 : ℝ) * (r j / 4) * D2 := by ring

theorem div_pow_le_self {x c : ℝ} (hx : 0 ≤ x) (hc : 1 ≤ c) (j : ℕ) :
    x / c ^ j ≤ x := by
  have hpow : 1 ≤ c ^ j := one_le_pow₀ hc
  have hp : 0 < c ^ j := lt_of_lt_of_le zero_lt_one hpow
  apply (div_le_iff₀ hp).2
  nlinarith [mul_nonneg hx (sub_nonneg.2 hpow)]

theorem eight_pow_term_le_four_pow_term {x : ℝ} (hx : 0 ≤ x) (j : ℕ) :
    x / (8 : ℝ) ^ j ≤ x / (4 : ℝ) ^ j := by
  have h4 : 0 < (4 : ℝ) ^ j := pow_pos (by norm_num) _
  have h8 : 0 < (8 : ℝ) ^ j := pow_pos (by norm_num) _
  have hp : (4 : ℝ) ^ j ≤ (8 : ℝ) ^ j :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) j
  exact div_le_div_of_nonneg_left hx h4 hp

/-- The initial contribution after `j` homotopy contractions is at most the
`8(Delta+r_j D²)` term used in the paper. -/
theorem startup_term_after_homotopy {Delta r0 D2 : ℝ} (j : ℕ)
    (hDelta : 0 ≤ Delta) (hrD : 0 ≤ r0 * D2) :
    8 * (Delta + r0 * D2) / (8 : ℝ) ^ j ≤
      8 * (Delta + curvature r0 j * D2) := by
  have hDeltaDiv := div_pow_le_self hDelta (by norm_num : (1 : ℝ) ≤ 8) j
  have hrDiv := eight_pow_term_le_four_pow_term hrD j
  unfold curvature
  have h4ne : (4 : ℝ) ^ j ≠ 0 := ne_of_gt (pow_pos (by norm_num) _)
  have hsplit :
      8 * (Delta + r0 * D2) / (8 : ℝ) ^ j =
        8 * (Delta / 8 ^ j + (r0 * D2) / 8 ^ j) := by ring
  rw [hsplit]
  have hreassoc : r0 / (4 : ℝ) ^ j * D2 = (r0 * D2) / 4 ^ j := by
    field_simp
  rw [hreassoc]
  nlinarith

/-- Combining startup, geometric contraction, and curvature transfer gives the
uniform homotopy majorant `15(Delta+r_j D²)`. -/
theorem homotopy_uniform_majorant {r0 D2 Delta : ℝ} (j : ℕ)
    (hDelta : 0 ≤ Delta) (hr0 : 0 ≤ r0) (hD2 : 0 ≤ D2) :
    homotopyMajorant r0 D2 (8 * (Delta + r0 * D2)) j ≤
      15 * (Delta + curvature r0 j * D2) := by
  have hr : ∀ k, 0 ≤ curvature r0 k := by
    intro k
    exact div_nonneg hr0 (by positivity)
  have hgeo := homotopy_geometric_bound
    (homotopyMajorant_recurrence r0 D2 (8 * (Delta + r0 * D2))) j hr hD2
  have hstart := startup_term_after_homotopy j hDelta (mul_nonneg hr0 hD2)
  have hcurvD : 0 ≤ curvature r0 j * D2 := mul_nonneg (hr j) hD2
  dsimp [homotopyMajorant] at hgeo
  nlinarith

/-! ## One outer iteration -/

theorem vecSq_neg_add_le_two {m : Nat} (a e : EVec m) :
    vecSq (-a + e) ≤ 2 * vecSq a + 2 * vecSq e := by
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.add_apply, Pi.neg_apply]
  nlinarith [sq_nonneg (a i + e i)]

theorem vecSq_nonneg {m : Nat} (x : EVec m) : 0 ≤ vecSq x := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

theorem vecSq_neg {m : Nat} (x : EVec m) : vecSq (-x) = vecSq x := by
  unfold vecSq NCPLVerification.vecSq
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.neg_apply]
  ring

/-- Triangle inequality for the Euclidean length represented by `sqrt vecSq`.
It is proved directly from finite-dimensional Cauchy--Schwarz. -/
theorem sqrt_vecSq_add_le {m : Nat} (x y : EVec m) :
    Real.sqrt (vecSq (x + y)) ≤
      Real.sqrt (vecSq x) + Real.sqrt (vecSq y) := by
  have hx0 := vecSq_nonneg x
  have hy0 := vecSq_nonneg y
  have hxy0 := vecSq_nonneg (x + y)
  have hcs : eDot x y ≤ Real.sqrt (vecSq x) * Real.sqrt (vecSq y) := by
    exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ x y
  have hx2 := Real.sq_sqrt hx0
  have hy2 := Real.sq_sqrt hy0
  have hxy2 := Real.sq_sqrt hxy0
  have hs0 := Real.sqrt_nonneg (vecSq (x + y))
  have hr0 : 0 ≤ Real.sqrt (vecSq x) + Real.sqrt (vecSq y) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsum : vecSq (x + y) ≤
      (Real.sqrt (vecSq x) + Real.sqrt (vecSq y)) ^ 2 := by
    rw [vecSq_add_expand]
    nlinarith
  nlinarith

/-- Exact cancellation behind the outer descent step. -/
theorem descent_identity {m : Nat} (ell : ℝ) (a e : EVec m) :
    2 * ell * eDot a (-a + e) + ell * vecSq (-a + e) =
      -ell * vecSq a + ell * vecSq e := by
  unfold eDot vecSq NCPLVerification.vecSq
  conv_lhs =>
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  conv_rhs =>
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, Pi.neg_apply]
  ring

/-- Minimal smoothness interface used by the outer step.  The derivative and
Lipschitz-gradient facts for the actual Moreau envelope are proved in
`MoreauEnvelope.lean`; this predicate records their standard descent-lemma
consequence at the two iterates. -/
def SmoothDescentAt {m : Nat} (p : EVec m → ℝ) (ell : ℝ)
    (z d grad : EVec m) : Prop :=
  p (z + d) - p z ≤ eDot grad d + ell * vecSq d

/-- Version without the definitional-gradient witness, convenient for applying
the descent calculation to any smooth envelope. -/
theorem outer_descent {m : Nat} {p : EVec m → ℝ} {ell B : ℝ}
    {z a e : EVec m}
    (hsmooth : SmoothDescentAt p ell z (-a + e) ((2 * ell) • a))
    (hread : ell * vecSq e ≤ B) :
    p (z + (-a + e)) - p z ≤ -ell * vecSq a + B := by
  unfold SmoothDescentAt at hsmooth
  have hdot : eDot ((2 * ell) • a) (-a + e) =
      2 * ell * eDot a (-a + e) := by
    unfold eDot
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [hdot, descent_identity] at hsmooth
  linarith

theorem next_majorant_bound {rho ell a2 e2 B d2 : ℝ}
    (hell : 0 ≤ ell) (hrho : 0 ≤ rho)
    (hd : d2 ≤ 2 * a2 + 2 * e2)
    (hread : ell * e2 ≤ B) :
    nextMajorant rho ell d2 B ≤
      48 * rho * ell * a2 + 50 * rho * B := by
  unfold nextMajorant
  nlinarith [mul_nonneg hrho (mul_nonneg hell (sub_nonneg.2 hd))]

/-- Joint potential `W_t=p_r(z_t)+2B_t`. -/
def jointPotential (p B : ℝ) : ℝ := p + 2 * B

/-- With `rho=1/400`, the function decrease and tracking recurrence yield the
paper's stronger `3/4` joint-potential decrease. -/
theorem joint_potential_descent {p pNext B BNext ell a2 : ℝ}
    (houter : pNext - p ≤ -ell * a2 + B)
    (hA : 0 ≤ ell * a2)
    (htrack : BNext ≤ (48 / 400 : ℝ) * ell * a2 + (50 / 400 : ℝ) * B) :
    jointPotential pNext BNext - jointPotential p B ≤
      -(3 / 4 : ℝ) * (ell * a2 + B) := by
  unfold jointPotential
  linarith

/-! ## Termination certificate and telescoping -/

/-- TeX's computable certificate `C_t`; `d2` stands for `‖d_t‖²`. -/
def certificate (ell d2 B : ℝ) : ℝ :=
  2 * ell * Real.sqrt d2 + 2 * Real.sqrt (ell * B)

theorem certificate_sq_bound {ell d2 a2 e2 B : ℝ}
    (hell : 0 ≤ ell) (hd2 : 0 ≤ d2) (ha2 : 0 ≤ a2) (hB : 0 ≤ B)
    (hd : d2 ≤ 2 * a2 + 2 * e2)
    (hread : ell * e2 ≤ B) :
    certificate ell d2 B ^ 2 ≤ 24 * ell * (ell * a2 + B) := by
  have heB : 0 ≤ ell * B := mul_nonneg hell hB
  have hsqd : (Real.sqrt d2) ^ 2 = d2 := Real.sq_sqrt hd2
  have hsqB : (Real.sqrt (ell * B)) ^ 2 = ell * B := Real.sq_sqrt heB
  have hcross :
      2 * (2 * ell * Real.sqrt d2) * (2 * Real.sqrt (ell * B)) ≤
        (2 * ell * Real.sqrt d2) ^ 2 +
          (2 * Real.sqrt (ell * B)) ^ 2 := by
    nlinarith [sq_nonneg
      (2 * ell * Real.sqrt d2 - 2 * Real.sqrt (ell * B))]
  have hscaled : ell ^ 2 * e2 ≤ ell * B := by
    nlinarith [mul_nonneg hell (sub_nonneg.2 hread)]
  unfold certificate
  nlinarith [mul_nonneg (sq_nonneg ell) (sub_nonneg.2 hd)]

/-- The certificate really dominates the squared norm of the Moreau gradient:
`a=e-d`, `grad p_r=2 ell a`, and the readout gives `ell ‖e‖²≤B`. -/
theorem gradient_sq_le_certificate_sq {m : Nat} {ell B : ℝ}
    (d e : EVec m) (hell : 0 ≤ ell) (hB : 0 ≤ B)
    (hread : ell * vecSq e ≤ B) :
    (2 * ell * Real.sqrt (vecSq (e - d))) ^ 2 ≤
      certificate ell (vecSq d) B ^ 2 := by
  have hd0 := vecSq_nonneg d
  have he0 := vecSq_nonneg e
  have htri0 := sqrt_vecSq_add_le e (-d)
  have htri : Real.sqrt (vecSq (e - d)) ≤
      Real.sqrt (vecSq d) + Real.sqrt (vecSq e) := by
    simpa only [sub_eq_add_neg, vecSq_neg, add_comm] using htri0
  have heB : 0 ≤ ell * B := mul_nonneg hell hB
  have hsE2 := Real.sq_sqrt he0
  have hsB2 := Real.sq_sqrt heB
  have hscaled : ell * Real.sqrt (vecSq e) ≤ Real.sqrt (ell * B) := by
    have hm : ell ^ 2 * vecSq e ≤ ell * B := by
      nlinarith [mul_nonneg hell (sub_nonneg.2 hread)]
    have hl0 : 0 ≤ ell * Real.sqrt (vecSq e) :=
      mul_nonneg hell (Real.sqrt_nonneg _)
    have hr0 := Real.sqrt_nonneg (ell * B)
    nlinarith
  have hnorm :
      2 * ell * Real.sqrt (vecSq (e - d)) ≤ certificate ell (vecSq d) B := by
    unfold certificate
    nlinarith [mul_nonneg hell (sub_nonneg.2 htri)]
  have hl0 : 0 ≤ 2 * ell * Real.sqrt (vecSq (e - d)) := by positivity
  have hc0 : 0 ≤ certificate ell (vecSq d) B := by
    unfold certificate
    positivity
  nlinarith

theorem telescoping_energy {T : ℕ} (W A B : ℕ → ℝ)
    (hstep : ∀ t, W (t + 1) - W t ≤ -(3 / 4 : ℝ) * (A t + B t)) :
    W T + (3 / 4 : ℝ) * (∑ t ∈ Finset.range T, (A t + B t)) ≤ W 0 := by
  induction T with
  | zero => simp
  | succ T ih =>
      rw [Finset.sum_range_succ]
      have hs := hstep T
      nlinarith

theorem certificate_sum_bound {T : ℕ} {ell lower : ℝ}
    (W A B C : ℕ → ℝ) (hell : 0 ≤ ell)
    (hstep : ∀ t, W (t + 1) - W t ≤ -(3 / 4 : ℝ) * (A t + B t))
    (hcert : ∀ t, C t ^ 2 ≤ 24 * ell * (A t + B t))
    (hlower : lower ≤ W T) :
    (∑ t ∈ Finset.range T, C t ^ 2) ≤ 32 * ell * (W 0 - lower) := by
  have htel := telescoping_energy (T := T) W A B hstep
  have hsum : (∑ t ∈ Finset.range T, C t ^ 2) ≤
      ∑ t ∈ Finset.range T, 24 * ell * (A t + B t) := by
    exact Finset.sum_le_sum fun t _ => hcert t
  rw [← Finset.mul_sum] at hsum
  nlinarith [mul_nonneg hell (sub_nonneg.2 hlower)]

theorem exists_small_certificate {T : ℕ} {ell lower : ℝ}
    (W A B C : ℕ → ℝ) (hT : 0 < T) (hell : 0 ≤ ell)
    (hstep : ∀ t, W (t + 1) - W t ≤ -(3 / 4 : ℝ) * (A t + B t))
    (hcert : ∀ t, C t ^ 2 ≤ 24 * ell * (A t + B t))
    (hlower : lower ≤ W T) :
    ∃ t < T, C t ^ 2 ≤ (32 * ell / T) * (W 0 - lower) := by
  have hsum := certificate_sum_bound W A B C hell hstep hcert hlower
  have hne : (Finset.range T).Nonempty := ⟨0, Finset.mem_range.2 hT⟩
  have havg : Finset.expect (Finset.range T) (fun t => C t ^ 2) ≤
      (32 * ell / T) * (W 0 - lower) := by
    rw [Finset.expect_eq_sum_div_card]
    simp only [Finset.card_range]
    have hTc : (0 : ℝ) < T := by exact_mod_cast hT
    apply (div_le_iff₀ hTc).2
    calc
      (∑ x ∈ Finset.range T, C x ^ 2) ≤ 32 * ell * (W 0 - lower) := hsum
      _ = (32 * ell / T) * (W 0 - lower) * T := by field_simp
  obtain ⟨t, ht, hsmall⟩ := Finset.exists_le_of_expect_le hne havg
  exact ⟨t, Finset.mem_range.1 ht, hsmall⟩

/-! ## Final numerical constants and headline arithmetic -/

/-- Outer horizon used in the manuscript. -/
def outerIterations (ell gap eps : ℝ) : ℕ :=
  Nat.ceil (4000 * ell * gap / eps ^ 2)

theorem outerIterations_sandwich {ell gap eps : ℝ}
    (harg : 0 ≤ 4000 * ell * gap / eps ^ 2) :
    4000 * ell * gap / eps ^ 2 ≤ outerIterations ell gap eps ∧
      (outerIterations ell gap eps : ℝ) <
        4000 * ell * gap / eps ^ 2 + 1 := by
  constructor
  · exact Nat.le_ceil _
  · exact Nat.ceil_lt_add_one harg

/-- Exact nested-loop accounting: every one of `T` outer iterations runs a
`K`-step block, and each step uses `N+1` oracle/projection calls. -/
def totalOracleCalls (T K N : ℕ) : ℕ := T * K * (N + 1)

@[simp] theorem totalOracleCalls_eq (T K N : ℕ) :
    totalOracleCalls T K N = T * K * (N + 1) := rfl

theorem totalOracleCalls_cast (T K N : ℕ) :
    (totalOracleCalls T K N : ℝ) =
      (T : ℝ) * K * (N + 1) := by
  norm_num [totalOracleCalls]

theorem certificate_gap_constant {ell gap T C2 : ℝ}
    (h : C2 ≤ (32 * ell / T) * (31 * gap)) :
    C2 ≤ 992 * ell * gap / T := by
  calc
    C2 ≤ (32 * ell / T) * (31 * gap) := h
    _ = 992 * ell * gap / T := by ring

theorem final_certificate_arithmetic {ell Delta rD2 T eps : ℝ}
    (heps : 0 < eps) (hT : 4000 * ell * (Delta + rD2) / eps ^ 2 ≤ T)
    (hTpos : 0 < T) :
    992 * ell * (Delta + rD2) / T < eps ^ 2 / 4 := by
  have heps2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hK : 4000 * ell * (Delta + rD2) ≤ T * eps ^ 2 :=
    (div_le_iff₀ heps2).1 hT
  have hratio : 992 * ell * (Delta + rD2) / T ≤
      (992 / 4000 : ℝ) * eps ^ 2 := by
    apply (div_le_iff₀ hTpos).2
    nlinarith
  have hc : (992 / 4000 : ℝ) < 1 / 4 := by norm_num
  nlinarith

theorem regularization_bias_arithmetic {ell r D2 eps : ℝ}
    (harg : 0 ≤ 2 * ell * r * D2) (heps : 0 ≤ eps)
    (h : 2 * ell * r * D2 ≤ eps ^ 2 / 4) :
    Real.sqrt (2 * ell * r * D2) ≤ eps / 2 := by
  have hs0 := Real.sqrt_nonneg (2 * ell * r * D2)
  have hs2 := Real.sq_sqrt harg
  nlinarith

/-- The smoothed certificate and regularization bias each spend half of the
final squared-gradient budget. -/
theorem stationarity_from_smoothed_and_bias {trueSq smoothSq biasSq eps : ℝ}
    (hcompare : trueSq ≤ 2 * smoothSq + 2 * biasSq)
    (hsmooth : smoothSq ≤ eps ^ 2 / 4)
    (hbias : biasSq ≤ eps ^ 2 / 4) :
    trueSq ≤ eps ^ 2 := by
  linarith

/-- The product of the outer iteration scale and the moving-anchor block scale
is exactly the headline gradient-evaluation scale. -/
theorem iteration_gradient_product {ell Delta D eps : ℝ} (heps : eps ≠ 0) :
    (ell * Delta / eps ^ 2) * (ell * D / eps) =
      ell ^ 2 * D * Delta / eps ^ 3 := by
  field_simp

theorem headline_complexity_identity {ell Delta D eps : ℝ} (heps : eps ≠ 0) :
    (ell * Delta / eps ^ 2) * (ell * D / eps) =
      ell ^ 2 * D * Delta / eps ^ 3 := by
  field_simp

end

end Tracking
end Upper
end NCCLowerBoundVerification
