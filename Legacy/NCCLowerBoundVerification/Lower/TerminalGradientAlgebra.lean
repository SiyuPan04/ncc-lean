import NCCLowerBoundVerification.Lower.NumericalHierarchy
import NCCLowerBoundVerification.Lower.Activation

/-!
# Terminal pulse-gradient case split

This is the numerical three-range argument in `lem:terminal-gradient`.  It is
stated for the concrete activation `Psi2` and its concrete derivative; the
only input from the surrounding chain is the frontier range of the current
and next states.
-/

namespace NCCLowerBoundVerification

noncomputable section

def terminalGa {theta : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (current a b : ℝ) : ℝ :=
  -C.alpha * Psi2 current + 12 * (a - b / 2) + 2 * C.gamma * a

def terminalGb {theta : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (current next a b : ℝ) : ℝ :=
  -6 * (a - b / 2) + 2 * C.gamma * b -
    C.beta * Psi2 current * Psi2Deriv b * next

theorem concrete_activation_bounds (current b : ℝ) :
    0 ≤ Psi2 current ∧ Psi2 current ≤ Real.exp 1 ∧
      0 ≤ Psi2Deriv b ∧ Psi2Deriv b ≤ 24 := by
  refine ⟨Psi2_nonneg _, Psi2_le_exp_one _, Psi2Deriv_nonneg _, ?_⟩
  have h := abs_Psi2Deriv_le_twentyFour b
  exact (le_abs_self _).trans h

theorem exit_error_upper
    {beta psi psi' next xi1 xi2 delta : ℝ}
    (hbeta : 0 ≤ beta) (hpsi0 : 0 ≤ psi) (hpsi : psi ≤ xi1)
    (hpsi'0 : 0 ≤ psi') (hpsi' : psi' ≤ xi2)
    (hdelta : 0 ≤ delta) (hnext : -delta ≤ next) :
    -beta * psi * psi' * next ≤ beta * xi1 * xi2 * delta := by
  have hprod0 : 0 ≤ psi * psi' := mul_nonneg hpsi0 hpsi'0
  have hxi10 : 0 ≤ xi1 := hpsi0.trans hpsi
  have hxi20 : 0 ≤ xi2 := hpsi'0.trans hpsi'
  have hprod : psi * psi' ≤ xi1 * xi2 :=
    mul_le_mul hpsi hpsi' hpsi'0 hxi10
  have hneg : -next ≤ delta := by linarith
  calc
    -beta * psi * psi' * next = (beta * (psi * psi')) * (-next) := by ring
    _ ≤ (beta * (psi * psi')) * delta :=
      mul_le_mul_of_nonneg_left hneg (mul_nonneg hbeta hprod0)
    _ ≤ (beta * (xi1 * xi2)) * delta := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hprod hbeta) hdelta
    _ = beta * xi1 * xi2 * delta := by ring

theorem terminalGa_add_two_terminalGb_le {theta current next a b : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (_htheta : 0 < theta) (hcurrent : 1 + theta ≤ current)
    (hnext : -C.deltaS ≤ next) (ha : a ≤ 1)
    (hb : b < 1 + theta) :
    terminalGa C current a b + 2 * terminalGb C current next a b ≤ -1 / 2 := by
  have hbounds := concrete_activation_bounds current b
  have hpsi0 := hbounds.1
  have hpsiUpper := hbounds.2.1
  have hderiv0 := hbounds.2.2.1
  have hderivUpper := hbounds.2.2.2
  have hpsiLower : xi0 theta ≤ Psi2 current := xi0_le_Psi2 hcurrent
  have hentrance : -C.alpha * Psi2 current ≤ -C.alpha * xi0 theta := by
    have h := mul_le_mul_of_nonneg_left hpsiLower C.alpha_pos.le
    linarith
  have hga : 2 * C.gamma * a ≤ 2 * C.gamma := by
    nlinarith [C.gamma_pos]
  have hgb : 4 * C.gamma * b ≤ 4 * C.gamma * (1 + theta) := by
    have hcoef : 0 ≤ 4 * C.gamma :=
      mul_nonneg (by norm_num) C.gamma_pos.le
    have h := mul_le_mul_of_nonneg_left hb.le hcoef
    nlinarith
  have herr := exit_error_upper C.beta_pos.le hpsi0 hpsiUpper hderiv0
    hderivUpper C.deltaS_pos.le hnext
  have herr2 : -2 * C.beta * Psi2 current * Psi2Deriv b * next ≤
      2 * C.beta * Real.exp 1 * 24 * C.deltaS := by
    nlinarith
  have hmarg := C.entrance_margin
  have hclip := C.clip_width_margin
  unfold terminalGa terminalGb
  nlinarith

theorem terminalGa_ge_one {theta current a b : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (ha : C.abar ≤ a) (hb : b < 1 + theta) :
    1 ≤ terminalGa C current a b := by
  have hpsi := (concrete_activation_bounds current b).2.1
  have halpha : -C.alpha * Psi2 current ≤ 0 := by
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr C.alpha_pos.le)
      (Psi2_nonneg current)
  have hpsiLower : -C.alpha * Real.exp 1 ≤ -C.alpha * Psi2 current := by
    have h := mul_le_mul_of_nonneg_left hpsi C.alpha_pos.le
    linarith
  have hcoef : 0 ≤ 12 + 2 * C.gamma := by nlinarith [C.gamma_pos]
  have haScaled := mul_le_mul_of_nonneg_left ha hcoef
  have hbScaled : -6 * b ≥ -6 * (1 + theta) := by linarith
  have hmarg := C.threshold_margin
  unfold terminalGa
  nlinarith

theorem terminalGb_le_neg_half {theta current next a b : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (_htheta : 0 < theta) (hnext : -C.deltaS ≤ next)
    (ha : 1 < a) (hb : b < 1 + theta) :
    terminalGb C current next a b ≤ -1 / 2 := by
  have hbounds := concrete_activation_bounds current b
  have hpsi0 := hbounds.1
  have hpsiUpper := hbounds.2.1
  have hderiv0 := hbounds.2.2.1
  have hderivUpper := hbounds.2.2.2
  have hlink : -6 * (a - b / 2) ≤ -3 * (1 - theta) := by
    linarith
  have hgamma : 2 * C.gamma * b ≤ 2 * C.gamma * (1 + theta) := by
    have hcoef : 0 ≤ 2 * C.gamma :=
      mul_nonneg (by norm_num) C.gamma_pos.le
    have h := mul_le_mul_of_nonneg_left hb.le hcoef
    nlinarith
  have herr := exit_error_upper C.beta_pos.le hpsi0 hpsiUpper hderiv0
    hderivUpper C.deltaS_pos.le hnext
  have hclip : C.beta * Real.exp 1 * 24 * C.deltaS ≤ 1 / 4 := by
    nlinarith [C.clip_width_margin]
  have hgate := C.gate_curvature
  unfold terminalGb
  nlinarith

theorem linear_combination_sq_le_five (ga gb : ℝ) :
    (ga + 2 * gb) ^ 2 ≤ 5 * (ga ^ 2 + gb ^ 2) := by
  nlinarith [sq_nonneg (2 * ga - gb)]

/-- The current pulse-gradient block has a uniform squared norm. -/
theorem terminal_pulse_gradient_sq_lower {theta current next a b : ℝ}
    (C : GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24)
    (htheta : 0 < theta) (hcurrent : 1 + theta ≤ current)
    (hnext : -C.deltaS ≤ next) (hb : b < 1 + theta) :
    (1 / 20 : ℝ) ≤
      terminalGa C current a b ^ 2 + terminalGb C current next a b ^ 2 := by
  by_cases haLow : a ≤ 1
  · have hsum := terminalGa_add_two_terminalGb_le C htheta hcurrent hnext haLow hb
    have hcs := linear_combination_sq_le_five
      (terminalGa C current a b) (terminalGb C current next a b)
    have hsumSq : (1 / 4 : ℝ) ≤
        (terminalGa C current a b + 2 * terminalGb C current next a b) ^ 2 := by
      nlinarith [sq_nonneg
        (terminalGa C current a b + 2 * terminalGb C current next a b)]
    nlinarith
  · by_cases haHigh : C.abar ≤ a
    · have hga := terminalGa_ge_one (current := current) C haHigh hb
      nlinarith [sq_nonneg (terminalGb C current next a b),
        sq_nonneg (terminalGa C current a b - 1)]
    · have hgb := terminalGb_le_neg_half
        (current := current) (next := next) C htheta hnext
        (lt_of_not_ge haLow) hb
      nlinarith [sq_nonneg (terminalGa C current a b),
        sq_nonneg (terminalGb C current next a b + 1 / 2)]

/-- The compatible concrete gate hierarchy used by the terminal proof exists. -/
theorem concreteGateThresholdConstants_nonempty {theta : ℝ}
    (htheta0 : 0 < theta) (htheta1 : theta < 1 / 10) :
    Nonempty (GateThresholdConstants theta (xi0 theta) (Real.exp 1) 24) := by
  apply gateThresholdConstants_nonempty htheta0 htheta1
  · exact xi0_pos htheta0
  · exact Real.exp_pos 1
  · norm_num

end

end NCCLowerBoundVerification
