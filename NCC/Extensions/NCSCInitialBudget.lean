import NCC.Extensions.NCSCAuxiliary
import NCC.Extensions.NCSCSystem
import NCC.Upper.AdaptiveMicroProgram
import NCCLowerBoundVerification.Upper.SharedOracle

/-!
# Observable NC-SC initialization, including the fast pair

One feasible query at the origin determines a finite FOAM energy budget.
This budget uses the two observed gradients, not an unproved bound on the
initial dual error by the primal value-gap parameter. The estimate is for
the genuine auxiliary conjugate, at `r = mu` and `L = 8 * (ell + mu)`.
-/

namespace NCC.Extensions.NCSCInitialBudget

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open PointwiseConjugate RelativeFOAM RelativeFOAMContraction
open TrackingConcrete OuterTrajectoryConcrete SharedOracle Oracle
open NCC.Extensions.NCSC

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ} {ell mu Delta : ℝ} {P : NCCInstance m n}

private theorem square_zero (d : ℕ) : vecSq (0 : EVec d) = 0 := by
  simp [vecSq, NCPLVerification.vecSq]

/-- Observable upper bound on the initial conjugate objective gap. -/
def gapBudget (ell mu : ℝ) (gx : EVec m) (gy : EVec n) : ℝ :=
  (1 / (2 * (internalSmoothness ell mu - ell))) * vecSq gx +
    (1 / (2 * mu)) * vecSq gy

/-- Includes both slow-coordinate errors and the fast-pair gap. -/
def budget (ell mu : ℝ) (gx : EVec m) (gy : EVec n) : ℝ :=
  6 * gapBudget ell mu gx gy

theorem curvature_slack_pos (h : NCSCClass ell mu Delta P) :
    0 < internalSmoothness ell mu - ell := by
  unfold internalSmoothness
  linarith [h.ell_pos, h.mu_pos]

theorem budget_nonneg (h : NCSCClass ell mu Delta P)
    (gx : EVec m) (gy : EVec n) : 0 ≤ budget ell mu gx gy := by
  unfold budget gapBudget
  exact mul_nonneg (by norm_num)
    (add_nonneg
      (mul_nonneg (by positivity [curvature_slack_pos h]) (vecSq_nonneg gx))
      (mul_nonneg (by positivity [h.mu_pos]) (vecSq_nonneg gy)))

/-- A direct supremum bound from the primal weak support inequality. -/
theorem gamma_origin_upper (h : NCSCClass ell mu Delta P) :
    gamma P.X P.Y
        (decurved (auxiliary P mu).f (internalSmoothness ell mu) mu 0)
        0 ⟨0, h.dual_origin⟩ ≤
      -P.f 0 0 + (1 / (2 * (internalSmoothness ell mu - ell))) *
        vecSq (P.gradX 0 0) := by
  unfold gamma ValueOn
  apply csSup_le (Set.Nonempty.image _ ⟨0, h.primal_origin⟩)
  rintro _ ⟨x, hx, rfl⟩
  have hs := primal_support_at_origin h hx h.dual_origin
  have ha : 0 < 2 * (internalSmoothness ell mu - ell) :=
    mul_pos (by norm_num) (curvature_slack_pos h)
  have hy := dot_le_quadratic ha (-P.gradX 0 0) x
  have hneg : dot (-P.gradX 0 0) x = -dot (P.gradX 0 0) x := by
    simp [dot, Finset.sum_neg_distrib]
  rw [hneg, Tracking.vecSq_neg] at hy
  have hb : -(P.f x 0 + internalSmoothness ell mu / 2 * vecSq x) ≤
      -P.f 0 0 + (1 / (2 * (internalSmoothness ell mu - ell))) *
        vecSq (P.gradX 0 0) := by
    nlinarith
  simpa only [decurved_eq, auxiliary, quadraticCorrection, square_zero,
    dot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero, sub_zero,
    mul_zero, zero_sub] using hb

/-- Strong dual support bounds the initial dual optimization error using
the dual gradient observed at the feasible origin. -/
theorem dual_origin_upper (h : NCSCClass ell mu Delta P)
    {y : EVec n} (hy : y ∈ P.Y) :
    P.f 0 y ≤ P.f 0 0 + (1 / (2 * mu)) * vecSq (P.gradY 0 0) := by
  have hs := dual_strong_support h h.primal_origin h.dual_origin hy
  have hq := dot_le_quadratic
    (mul_pos (by norm_num : (0 : ℝ) < 2) h.mu_pos) (P.gradY 0 0) y
  simp only [sub_zero] at hs
  change P.f 0 y ≤ P.f 0 0 + dot (P.gradY 0 0) y - mu / 2 * vecSq y at hs
  nlinarith

/-- Evaluate the defining conjugate supremum at primal zero. This proves
a global lower bound without assuming a saddle-value identity. -/
theorem conjugate_origin_lower (h : NCSCClass ell mu Delta P)
    (q : EVec m) (y : P.Y) :
    -P.f 0 0 - (1 / (2 * mu)) * vecSq (P.gradY 0 0) ≤
      Pzr P.X P.Y
        (decurved (auxiliary P mu).f (internalSmoothness ell mu) mu 0)
        (internalSmoothness ell mu) mu q y := by
  have hsup := le_csSup (auxiliary_gamma_bounded h 0 q y)
    (Set.mem_image_of_mem (fun x => dot q x -
      decurved (auxiliary P mu).f (internalSmoothness ell mu) mu 0 x y.1)
      h.primal_origin)
  have hg : -P.f 0 y.1 - mu / 2 * vecSq y.1 ≤
      gamma P.X P.Y
        (decurved (auxiliary P mu).f (internalSmoothness ell mu) mu 0) q y := by
    simpa only [gamma, ValueOn, decurved_eq, auxiliary, quadraticCorrection,
      square_zero, dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      zero_mul, add_zero, sub_zero, zero_sub, neg_add_rev, sub_eq_add_neg,
      add_comm, neg_zero, zero_add] using hsup
  have hy := dual_origin_upper h y.2
  have hq : 0 ≤ (1 / (2 * internalSmoothness ell mu)) * vecSq q :=
    mul_nonneg (by positivity [internalSmoothness_pos h]) (vecSq_nonneg q)
  unfold Pzr
  linarith

/-- Actual initial objective gap, uniform in every feasible comparison
pair and hence applicable to the genuine stationary minimizer. -/
theorem conjugate_gap_le (h : NCSCClass ell mu Delta P)
    (q : EVec m) (y : P.Y) :
    Pzr P.X P.Y
        (decurved (auxiliary P mu).f (internalSmoothness ell mu) mu 0)
        (internalSmoothness ell mu) mu 0 ⟨0, h.dual_origin⟩ -
      Pzr P.X P.Y
        (decurved (auxiliary P mu).f (internalSmoothness ell mu) mu 0)
        (internalSmoothness ell mu) mu q y ≤
      gapBudget ell mu (P.gradX 0 0) (P.gradY 0 0) := by
  have hupper := gamma_origin_upper h
  have hlower := conjugate_origin_lower h q y
  simp only [Pzr, square_zero, mul_zero, zero_add] at *
  unfold gapBudget
  linarith

/-- The explicit initial state has coincident slow and fast origin pairs. -/
def originState {Y : Set (EVec n)} (hy : (0 : EVec n) ∈ Y) :
    ValidState (m := m) Y :=
  ⟨StartupConcrete.coincidentState 0 0, hy⟩

/-- Strong minimization controls both slow errors by four times the gap;
the fast-pair term contributes another twice the same gap. -/
theorem origin_energy_le_six_gap {Y : Set (EVec n)}
    {L r : ℝ} (hL : 0 < L) (hr : 0 ≤ r) (hrL : r ≤ L / 8)
    (hy : (0 : EVec n) ∈ Y) {F : EVec m → Y → ℝ}
    {qStar : EVec m} {yStar : Y}
    (hstrong : IsSubtypePairStrongMinimizer F L r qStar yStar) :
    constrainedEnergy L r qStar yStar F (F qStar yStar)
        (originState (m := m) hy).1 (originState (m := m) hy).2 ≤
      6 * (F 0 ⟨0, hy⟩ - F qStar yStar) := by
  have hs := hstrong 0 ⟨0, hy⟩
  have ha := alpha_le_one hL hr hrL
  have hc : 2 * alpha L r / L ≤ 2 / L :=
    div_le_div_of_nonneg_right (by linarith) hL.le
  have hq := mul_le_mul_of_nonneg_right hc (vecSq_nonneg (0 - qStar))
  unfold TrackingAnalytic.pairSq at hs
  change 2 * alpha L r / L * vecSq (0 - qStar) +
    2 * r * vecSq (0 - yStar.1) + 2 * (F 0 ⟨0, hy⟩ - F qStar yStar) ≤ _
  have hid : 2 / L = 2 * (1 / L) := by ring
  rw [hid] at hq
  nlinarith

/-- Initial snapshot with its genuinely observable energy majorant. -/
def initialSnapshot {X : Set (EVec m)} {Y : Set (EVec n)}
    (hx : (0 : EVec m) ∈ X) (hy : (0 : EVec n) ∈ Y)
    (ell mu : ℝ) (gx : EVec m) (gy : EVec n) : FeasibleSnapshot X Y :=
  ⟨{ z := 0, state := originState hy, B := budget ell mu gx gy }, hx⟩

theorem initial_energy_bound (h : NCSCClass ell mu Delta P)
    {hexists : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y (auxiliary P mu).f mu) (internalSmoothness ell mu)}
    (sys : OuterSystem P.X P.Y (auxiliary P mu).f
      (internalSmoothness ell mu) mu hexists) :
    snapshotEnergy sys
      (initialSnapshot h.primal_origin h.dual_origin ell mu (P.gradX 0 0) (P.gradY 0 0)).1 ≤
      budget ell mu (P.gradX 0 0) (P.gradY 0 0) := by
  have hstrong := Pzr_isSubtypePairStrongMinimizer (internalSmoothness_pos h)
    h.mu_pos (sys.stationary 0).subgradient (sys.stationary 0).stationQ
    (sys.stationary 0).stationY
  have he := origin_energy_le_six_gap (internalSmoothness_pos h) h.mu_pos.le
    (intrinsic_parameter_le h) h.dual_origin hstrong
  have hg := conjugate_gap_le h (sys.stationary 0).qStar (sys.stationary 0).yStar
  exact he.trans (mul_le_mul_of_nonneg_left hg (by norm_num))

/-- One actual origin query supplies every objective-dependent datum in
the initialized snapshot. No unobserved value, conjugate, or minimizer is
used to construct its budget. -/
def initialProgram {X : Set (EVec m)} {Y : Set (EVec n)}
    (hx : (0 : EVec m) ∈ X) (hy : (0 : EVec n) ∈ Y)
    (ell mu : ℝ) : Program X Y (FeasibleSnapshot X Y) :=
  .query (0, 0) ⟨hx, hy⟩ fun reply =>
    .pure (initialSnapshot hx hy ell mu reply.gradX reply.gradY)

theorem initialProgram_exactDepth {X : Set (EVec m)} {Y : Set (EVec n)}
    (hx : (0 : EVec m) ∈ X) (hy : (0 : EVec n) ∈ Y) (ell mu : ℝ) :
    ExactDepth (initialProgram hx hy ell mu) 1 :=
  ExactDepth.query _ _ _ 0 (fun _ => ExactDepth.pure _)

theorem initialProgram_eval (h : NCSCClass ell mu Delta P) :
    Program.eval P (initialProgram h.primal_origin h.dual_origin ell mu) =
      initialSnapshot h.primal_origin h.dual_origin ell mu (P.gradX 0 0) (P.gradY 0 0) := rfl

/-- Closed initialization certificate for the constructed intrinsic NC-SC
system, with no assumed conjugate, stationary-point, or energy premises. -/
theorem evaluated_initial_energy (h : NCSCClass ell mu Delta P) :
    snapshotEnergy (NCSCSystem.system h)
      (Program.eval P (initialProgram h.primal_origin h.dual_origin ell mu)).1 ≤
      (Program.eval P (initialProgram h.primal_origin h.dual_origin ell mu)).1.B :=
  initial_energy_bound h (NCSCSystem.system h)

theorem initialProgram_queryTrace (h : NCSCClass ell mu Delta P) :
    NCC.Upper.AdaptiveMicroProgram.queryTrace P
      (initialProgram h.primal_origin h.dual_origin ell mu) = [(0, 0)] := rfl

theorem evaluated_budget_nonneg (h : NCSCClass ell mu Delta P) :
    0 ≤ (Program.eval P (initialProgram h.primal_origin h.dual_origin ell mu)).1.B :=
  budget_nonneg h _ _

/-- The primal gap gives the correct global envelope lower bound. It
does not by itself supply the extra initial-energy contribution. -/
theorem intrinsic_envelope_lower (h : NCSCClass ell mu Delta P) (z : EVec m) :
    ValueOn P.Y P.f 0 - Delta ≤
      regularizedEnvelope P.X P.Y (auxiliary P mu).f
        (internalSmoothness ell mu) mu (NCSCSystem.intrinsicProx h) z := by
  have hp := selectedProx_spec (NCSCSystem.intrinsicProx h) z
  have hg := h.initial_gap_pointwise _ hp.1
  have hsq : 0 ≤ internalSmoothness ell mu *
      vecSq (selectedProx (NCSCSystem.intrinsicProx h) z - z) :=
    mul_nonneg (internalSmoothness_pos h).le (vecSq_nonneg _)
  unfold regularizedEnvelope moreauEnvelope proxObjective
  rw [congrFun (auxiliary_regularized_value P mu)
    (selectedProx (NCSCSystem.intrinsicProx h) z)]
  linarith

/-- The exact initial potential gap is at most `Delta + 2 * Binit`.
This is the budget to pass to the actual outer selection theorem. -/
theorem initial_potential_gap (h : NCSCClass ell mu Delta P) :
    snapshotPotential (NCSCSystem.system h)
        (Program.eval P (initialProgram h.primal_origin h.dual_origin ell mu)).1 -
      (ValueOn P.Y P.f 0 - Delta) ≤
      Delta + 2 * budget ell mu (P.gradX 0 0) (P.gradY 0 0) := by
  have hp := (selectedProx_spec (NCSCSystem.intrinsicProx h) 0).2 0 h.primal_origin
  have he : regularizedEnvelope P.X P.Y (auxiliary P mu).f
      (internalSmoothness ell mu) mu (NCSCSystem.intrinsicProx h) 0 ≤
      ValueOn P.Y P.f 0 := by
    simpa only [regularizedEnvelope, moreauEnvelope, proxObjective,
      auxiliary_regularized_value, sub_self, square_zero, mul_zero, add_zero] using hp
  change regularizedEnvelope P.X P.Y (auxiliary P mu).f
      (internalSmoothness ell mu) mu (NCSCSystem.intrinsicProx h) 0 +
        2 * budget ell mu (P.gradX 0 0) (P.gradY 0 0) -
        (ValueOn P.Y P.f 0 - Delta) ≤ _
  linarith

end

end NCC.Extensions.NCSCInitialBudget
