import NCCLowerBoundVerification.Lower.Activation
import NCCLowerBoundVerification.Lower.ClipSoftHinge
import NCCLowerBoundVerification.Lower.SmoothStep

/-!
# Entrance, exit, and radial component interfaces

This file proves the scalar differential identities behind
`lem:entrance-properties` and `lem:exit-properties` from the concrete
functions, rather than recording those identities as assumptions.
-/

namespace NCCLowerBoundVerification

noncomputable section

/-- The entrance pulse of one hard-instance block. -/
def entrancePulse (alpha theta P0 current next a : ℝ) : ℝ :=
  -alpha * Psi2 current * Lambda2 theta next * pi2 P0 a

def entrancePulseDerivA (alpha theta P0 current next a : ℝ) : ℝ :=
  -alpha * Psi2 current * Lambda2 theta next * pi2Deriv P0 a

theorem hasDerivAt_entrancePulse_a
    (alpha theta P0 current next a : ℝ) :
    HasDerivAt (entrancePulse alpha theta P0 current next)
      (entrancePulseDerivA alpha theta P0 current next a) a := by
  unfold entrancePulse entrancePulseDerivA
  convert (hasDerivAt_pi2 P0 a).const_mul
    (-alpha * Psi2 current * Lambda2 theta next) using 1

theorem entrancePulse_at_zero (alpha theta P0 current next : ℝ) :
    entrancePulse alpha theta P0 current next 0 = 0 := by
  simp [entrancePulse, pi2_zero]

theorem entrancePulseDerivA_at_zero {alpha theta P0 current next : ℝ}
    (hP0 : 1 < P0) :
    entrancePulseDerivA alpha theta P0 current next 0 =
      -alpha * Psi2 current * Lambda2 theta next := by
  simp [entrancePulseDerivA, pi2Deriv_zero hP0]

theorem entrancePulse_frontier_deriv_le {alpha theta P0 current next : ℝ}
    (halpha : 0 ≤ alpha) (htheta : 0 < theta) (hP0 : 1 < P0)
    (hcurrent : 1 + theta ≤ current) (hnext : next ≤ 1) :
    entrancePulseDerivA alpha theta P0 current next 0 ≤
      -alpha * xi0 theta := by
  rw [entrancePulseDerivA_at_zero hP0,
    Lambda2_eq_one_of_le_one htheta hnext, mul_one]
  have hpsi : xi0 theta ≤ Psi2 current := xi0_le_Psi2 hcurrent
  have hscaled := mul_le_mul_of_nonneg_left hpsi halpha
  linarith

theorem entrancePulseDerivA_eq_zero_of_current_low
    {alpha theta P0 current next : ℝ} (hcurrent : current ≤ 1) :
    entrancePulseDerivA alpha theta P0 current next 0 = 0 := by
  simp [entrancePulseDerivA, Psi2_eq_zero_of_le_one hcurrent]

theorem entrancePulseDerivA_eq_zero_of_next_high
    {alpha theta P0 current next : ℝ} (htheta : 0 < theta)
    (hnext : 1 + theta ≤ next) :
    entrancePulseDerivA alpha theta P0 current next 0 = 0 := by
  simp [entrancePulseDerivA,
    Lambda2_eq_zero_of_one_add_le htheta hnext]

/-- Low-regime relay appearing in the exit pulse. -/
def exitRelay (theta t : ℝ) : ℝ := t * Lambda2 theta t

def exitRelayDeriv (theta t : ℝ) : ℝ :=
  Lambda2 theta t + t * deriv (Lambda2 theta) t

theorem hasDerivAt_exitRelay (theta t : ℝ) :
    HasDerivAt (exitRelay theta) (exitRelayDeriv theta t) t := by
  have hLambda : HasDerivAt (Lambda2 theta) (deriv (Lambda2 theta) t) t :=
    ((@Lambda2_contDiff theta 1).differentiable (by norm_num)).differentiableAt.hasDerivAt
  have hid : HasDerivAt (fun s : ℝ ↦ s) 1 t := hasDerivAt_id t
  have hmul : HasDerivAt (fun s : ℝ ↦ s * Lambda2 theta s)
      (1 * Lambda2 theta t + t * deriv (Lambda2 theta) t) t :=
    hid.mul hLambda
  change HasDerivAt (fun s : ℝ ↦ s * Lambda2 theta s)
    (Lambda2 theta t + t * deriv (Lambda2 theta) t) t
  simpa only [one_mul] using hmul

theorem exitRelay_eq_self_of_le_one {theta t : ℝ} (htheta : 0 < theta)
    (ht : t ≤ 1) : exitRelay theta t = t := by
  simp [exitRelay, Lambda2_eq_one_of_le_one htheta ht]

theorem exitRelayDeriv_eq_one_of_le_one {theta t : ℝ}
    (htheta : 0 < theta) (ht : t ≤ 1) :
    exitRelayDeriv theta t = 1 := by
  rw [exitRelayDeriv, Lambda2_eq_one_of_le_one htheta ht,
    Lambda2_deriv_eq_zero_of_le_one htheta ht]
  ring

theorem exitRelay_eq_zero_of_high {theta t : ℝ} (htheta : 0 < theta)
    (ht : 1 + theta ≤ t) : exitRelay theta t = 0 := by
  simp [exitRelay, Lambda2_eq_zero_of_one_add_le htheta ht]

/-- The exit pulse of one hard-instance block. -/
def exitPulse (beta theta current b next : ℝ) : ℝ :=
  -beta * Psi2 current * Psi2 b * exitRelay theta next

def exitPulseDerivNext (beta theta current b next : ℝ) : ℝ :=
  -beta * Psi2 current * Psi2 b * exitRelayDeriv theta next

theorem hasDerivAt_exitPulse_next (beta theta current b next : ℝ) :
    HasDerivAt (exitPulse beta theta current b)
      (exitPulseDerivNext beta theta current b next) next := by
  unfold exitPulse exitPulseDerivNext
  convert (hasDerivAt_exitRelay theta next).const_mul
    (-beta * Psi2 current * Psi2 b) using 1

def exitPulseDerivB (beta theta current b next : ℝ) : ℝ :=
  -beta * Psi2 current * Psi2Deriv b * exitRelay theta next

theorem hasDerivAt_exitPulse_b (beta theta current b next : ℝ) :
    HasDerivAt (fun q => exitPulse beta theta current q next)
      (exitPulseDerivB beta theta current b next) b := by
  simpa [exitPulse, exitPulseDerivB, mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_Psi2 b).const_mul
      (-beta * Psi2 current * exitRelay theta next)

theorem exitPulse_eq_zero_at_unrevealed
    (beta theta current next : ℝ) :
    exitPulse beta theta current 0 next = 0 := by
  simp [exitPulse, Psi2_zero]

theorem exitPulseDerivB_eq_zero_at_unrevealed
    (beta theta current next : ℝ) :
    exitPulseDerivB beta theta current 0 next = 0 := by
  simp [exitPulseDerivB, Psi2Deriv_zero]

theorem exitPulse_frontier_deriv_le
    {beta theta current b next : ℝ}
    (hbeta : 0 ≤ beta) (htheta : 0 < theta)
    (hcurrent : 1 + theta ≤ current) (hb : 1 + theta ≤ b)
    (hnext : next ≤ 1) :
    exitPulseDerivNext beta theta current b next ≤
      -beta * (xi0 theta) ^ 2 := by
  rw [exitPulseDerivNext, exitRelayDeriv_eq_one_of_le_one htheta hnext, mul_one]
  have hcur : xi0 theta ≤ Psi2 current := xi0_le_Psi2 hcurrent
  have hb' : xi0 theta ≤ Psi2 b := xi0_le_Psi2 hb
  have hxi : 0 ≤ xi0 theta := (xi0_pos htheta).le
  have hprod : (xi0 theta) ^ 2 ≤ Psi2 current * Psi2 b := by
    calc
      (xi0 theta) ^ 2 = xi0 theta * xi0 theta := by ring
      _ ≤ Psi2 current * xi0 theta :=
        mul_le_mul_of_nonneg_right hcur hxi
      _ ≤ Psi2 current * Psi2 b :=
        mul_le_mul_of_nonneg_left hb' (Psi2_nonneg current)
  have hscaled := mul_le_mul_of_nonneg_left hprod hbeta
  linarith

end

end NCCLowerBoundVerification
