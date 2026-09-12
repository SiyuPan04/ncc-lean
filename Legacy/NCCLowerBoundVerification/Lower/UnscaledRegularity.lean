import NCCLowerBoundVerification.Lower.UnscaledSerialization
import NCCLowerBoundVerification.Lower.ScaledObjective
import NCCLowerBoundVerification.Lower.NumericalHierarchy
import NCCLowerBoundVerification.DiameterBall

/-!
# Regularity data for the unscaled lower-bound objective

This file uses the literal domains from lines 2322--2336 of
`Upper+Lower_unified_lower.tex`: the primal domain is the whole Euclidean
space and the dual domain is the diameter-normalized Euclidean ball.

It also makes the dependency-order choice in Lemma `lem:constants`
concrete.  In particular, the spatial witnesses `(P₀,K,P₁)` are selected
before `c_s`; the latter is then obtained from a proved bound for the literal
memory-remainder expression, and only afterwards is `eta` selected.
-/

namespace NCCLowerBoundVerification

noncomputable section

open Set

def concreteTheta : ℝ := 1 / 20

theorem concreteTheta_pos : 0 < concreteTheta := by
  norm_num [concreteTheta]

theorem concreteTheta_lt_tenth : concreteTheta < 1 / 10 := by
  norm_num [concreteTheta]

def concreteXiOne : ℝ := Real.exp 1

def concreteXiTwo : ℝ := 24

theorem concreteXiOne_pos : 0 < concreteXiOne := by
  exact Real.exp_pos 1

theorem concreteXiTwo_pos : 0 < concreteXiTwo := by
  norm_num [concreteXiTwo]

/-- The first dependency group of `lem:constants`, selected by the proved
closed-form constructor in `NumericalHierarchy.lean`. -/
def concreteGateThreshold :
    GateThresholdConstants concreteTheta (xi0 concreteTheta)
      concreteXiOne concreteXiTwo :=
  Classical.choice <| gateThresholdConstants_nonempty concreteTheta_pos
    concreteTheta_lt_tenth (xi0_pos concreteTheta_pos)
      concreteXiOne_pos concreteXiTwo_pos

/-- The explicit `c_q` supplied by the verified Green-matrix coefficient
bounds `|c₁,n| ≤ 2400` and `|c₂,n| ≤ 600`. -/
def concreteCq : ℝ := 2400 + concreteGateThreshold.gamma

theorem concreteCq_pos : 0 < concreteCq := by
  unfold concreteCq
  linarith [concreteGateThreshold.gamma_pos]

/-- An explicit coefficient bound for the two radial pulse derivatives in
`eq:Ccur`. -/
def concreteCp : ℝ :=
  concreteGateThreshold.alpha * Real.exp 1 +
    concreteGateThreshold.beta * Real.exp 1 * 24 + 1

theorem concreteCp_pos : 0 < concreteCp := by
  unfold concreteCp
  have h1 : 0 < concreteGateThreshold.alpha * Real.exp 1 :=
    mul_pos concreteGateThreshold.alpha_pos (Real.exp_pos 1)
  have h2 : 0 < concreteGateThreshold.beta * Real.exp 1 * 24 := by
    exact mul_pos
      (mul_pos concreteGateThreshold.beta_pos (Real.exp_pos 1)) (by norm_num)
  linarith

/-- The genuinely earlier spatial part of group (iii). -/
def concreteSpatial :
    RadialSpatialConstants concreteGateThreshold.gamma concreteCp concreteCq
      concreteGateThreshold.deltaS concreteGateThreshold.Bs :=
  Classical.choice <| radialSpatialConstants_nonempty
    concreteGateThreshold.gamma_pos concreteCp_pos concreteCq_pos
      concreteGateThreshold.deltaS_pos concreteGateThreshold.Bs_gt_three

/-- A finite global bound for the first derivative of the detector. -/
def concreteLambdaDerivBound : ℝ :=
  Classical.choose (Lambda2_iteratedDeriv_bounded concreteTheta_pos 1)

theorem concreteLambdaDerivBound_nonneg : 0 ≤ concreteLambdaDerivBound :=
  (Classical.choose_spec
    (Lambda2_iteratedDeriv_bounded concreteTheta_pos 1)).1

theorem deriv_Lambda2_concrete_bound (t : ℝ) :
    |deriv (Lambda2 concreteTheta) t| ≤ concreteLambdaDerivBound := by
  have h := (Classical.choose_spec
    (Lambda2_iteratedDeriv_bounded concreteTheta_pos 1)).2 t
  unfold concreteLambdaDerivBound
  simpa using h

/-- A parameter record used only to state the actual memory remainder before
`eta` is chosen.  That remainder is definitionally independent of `eta`. -/
def concretePreParameters : UnscaledParameters where
  theta := concreteTheta
  delta := concreteGateThreshold.deltaS
  P0 := concreteSpatial.P0
  tauS := tauS concreteGateThreshold.deltaS
  alpha := concreteGateThreshold.alpha
  beta := concreteGateThreshold.beta
  gamma := concreteGateThreshold.gamma
  mu := concreteGateThreshold.mu
  eta := 1
  P1 := concreteSpatial.P1
  K := concreteSpatial.K
  theta_pos := concreteTheta_pos
  delta_pos := concreteGateThreshold.deltaS_pos
  P0_gt_one := concreteSpatial.P0_gt_one
  tauS_pos := by
    unfold tauS
    exact div_pos concreteGateThreshold.deltaS_pos (by norm_num)

theorem concreteCq_dominates_quadratic_correction {n : Nat} (hn : 10 ≤ n)
    (a b : ℝ) :
    -2 * concreteCq * (a ^ 2 + b ^ 2) ≤
      2 * (innerC1 (by omega : 0 < n) + concreteGateThreshold.gamma) * a ^ 2 +
      2 * (innerC2 (by omega : 0 < n) + concreteGateThreshold.gamma) * b ^ 2 := by
  have h1 := innerC1_uniform_bound hn
  have h2small := innerC2_uniform_bound hn
  have h2 : |innerC2 (by omega : 0 < n)| ≤ (2400 : ℝ) :=
    h2small.trans (by norm_num)
  simpa only [concreteCq] using
    (quadraticCorrection_remainder_bound
      (C := (2400 : ℝ)) (gamma := concreteGateThreshold.gamma)
      (a := a) (b := b) (by norm_num) concreteGateThreshold.gamma_pos.le h1 h2)

theorem concreteCp_dominates_pulse_remainder
    (P0 : ℝ) {current next a b : ℝ}
    (hnextLower : -concreteGateThreshold.deltaS ≤ next)
    (hnextUpper : next ≤ 1) :
    |a * entrancePulseDerivA concreteGateThreshold.alpha concreteTheta
          P0 current next a +
        b * exitPulseDerivB concreteGateThreshold.beta concreteTheta
          current b next| ≤
      concreteCp * Real.sqrt (a ^ 2 + b ^ 2) := by
  let alpha := concreteGateThreshold.alpha
  let beta := concreteGateThreshold.beta
  let E := Real.exp 1
  have halpha : 0 ≤ alpha := concreteGateThreshold.alpha_pos.le
  have hbeta : 0 ≤ beta := concreteGateThreshold.beta_pos.le
  have hE : 0 ≤ E := (Real.exp_pos 1).le
  have hpsi := Psi2_mem_range current
  have hpi : pi2Deriv P0 a ∈ Set.Icc (0 : ℝ) 1 := by
    exact ⟨clipIntegrand_nonneg _ _ _, clipIntegrand_le_one _ _ _⟩
  have hentrance :
      |entrancePulseDerivA alpha concreteTheta
          P0 current next a| ≤ alpha * E := by
    rw [entrancePulseDerivA,
      Lambda2_eq_one_of_le_one concreteTheta_pos hnextUpper]
    simp only [mul_one, abs_neg, abs_mul, abs_of_nonneg halpha,
      abs_of_nonneg hpsi.1, abs_of_nonneg hpi.1]
    calc
      alpha * Psi2 current * pi2Deriv P0 a ≤
          alpha * Psi2 current * 1 := by
        exact mul_le_mul_of_nonneg_left hpi.2 (mul_nonneg halpha hpsi.1)
      _ ≤ alpha * E := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hpsi.2 halpha
  have hdeltaOne : concreteGateThreshold.deltaS ≤ 1 :=
    concreteGateThreshold.deltaS_lt_one.le
  have hnextAbs : |next| ≤ 1 := (abs_le).2 ⟨by linarith, hnextUpper⟩
  have hexit :
      |exitPulseDerivB beta concreteTheta current b next| ≤
        beta * E * 24 := by
    rw [exitPulseDerivB, exitRelay_eq_self_of_le_one concreteTheta_pos hnextUpper]
    simp only [abs_neg, abs_mul, abs_of_nonneg hbeta, abs_of_nonneg hpsi.1]
    have hd := abs_Psi2Deriv_le_twentyFour b
    calc
      beta * Psi2 current * |Psi2Deriv b| * |next| ≤
          beta * Psi2 current * |Psi2Deriv b| * 1 := by
        exact mul_le_mul_of_nonneg_left hnextAbs
          (mul_nonneg (mul_nonneg hbeta hpsi.1) (abs_nonneg _))
      _ ≤ beta * Psi2 current * 24 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hd
          (mul_nonneg hbeta hpsi.1)
      _ ≤ beta * E * 24 := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpsi.2 hbeta) (by norm_num)
  let R := Real.sqrt (a ^ 2 + b ^ 2)
  have hsumSq : 0 ≤ a ^ 2 + b ^ 2 := add_nonneg (sq_nonneg a) (sq_nonneg b)
  have hRsq : R ^ 2 = a ^ 2 + b ^ 2 := by
    exact Real.sq_sqrt hsumSq
  have hR : 0 ≤ R := Real.sqrt_nonneg _
  have haR : |a| ≤ R := by
    have haSq : |a| ^ 2 ≤ R ^ 2 := by
      rw [hRsq, sq_abs]
      exact le_add_of_nonneg_right (sq_nonneg b)
    nlinarith [abs_nonneg a]
  have hbR : |b| ≤ R := by
    have hbSq : |b| ^ 2 ≤ R ^ 2 := by
      rw [hRsq, sq_abs]
      exact le_add_of_nonneg_left (sq_nonneg a)
    nlinarith [abs_nonneg b]
  have hcoef1 : 0 ≤ alpha * E := mul_nonneg halpha hE
  have hcoef2 : 0 ≤ beta * E * 24 := by positivity
  calc
    |a * entrancePulseDerivA alpha concreteTheta P0
          current next a + b * exitPulseDerivB beta concreteTheta current b next| ≤
        |a * entrancePulseDerivA alpha concreteTheta P0
          current next a| + |b * exitPulseDerivB beta concreteTheta current b next| :=
      abs_add_le _ _
    _ = |a| * |entrancePulseDerivA alpha concreteTheta
          P0 current next a| +
        |b| * |exitPulseDerivB beta concreteTheta current b next| := by
      rw [abs_mul, abs_mul]
    _ ≤ |a| * (alpha * E) + |b| * (beta * E * 24) :=
      add_le_add (mul_le_mul_of_nonneg_left hentrance (abs_nonneg a))
        (mul_le_mul_of_nonneg_left hexit (abs_nonneg b))
    _ ≤ R * (alpha * E) + R * (beta * E * 24) :=
      add_le_add (mul_le_mul_of_nonneg_right haR hcoef1)
        (mul_le_mul_of_nonneg_right hbR hcoef2)
    _ ≤ concreteCp * R := by
      dsimp [concreteCp, alpha, beta, E]
      nlinarith

/-- The `eta`-independent part of the literal serialized state derivative in
`UnscaledObjective.lean`. -/
def serializedMemoryRemainder {T n : Nat} (P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) : ℝ :=
  let raw := serializedState q i
  let cur := serializedClippedCurrent P q i
  let nxt := serializedClippedNext P q i
  let cd := pi1Deriv P.delta P.P0 raw
  Sigma2Deriv P.tauS raw +
    P.mu * Psi2Deriv nxt * cd * Sigma1 P.theta cur -
    P.alpha * Psi2 cur * deriv (Lambda2 P.theta) nxt * cd *
      pi2 P.P0 (serializedA q i) +
    exitPulseDerivNext P.beta P.theta cur (serializedB q i) nxt * cd +
    serializedNextStateContribution P q i

theorem serializedGradState_eq_eta_term_add_memory {T n : Nat}
    (P : UnscaledParameters) (q : SerializedSpace T n) (i : Fin (T - 1)) :
    serializedGradState P q i =
      -P.eta * Psi1Deriv (serializedClippedNext P q i) *
          pi1Deriv P.delta P.P0 (serializedState q i) +
        serializedMemoryRemainder P q i := by
  simp only [serializedGradState, serializedMemoryRemainder]
  ring

theorem concretePi1_mem (t : ℝ) :
    pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t ∈
      Set.Icc (-concreteGateThreshold.deltaS) concreteGateThreshold.Bs := by
  apply (pi1_range_subset concreteGateThreshold.deltaS_pos
    concreteSpatial.P0_gt_one ?_)
  · exact ⟨_, rfl⟩
  · convert concreteSpatial.clip_range using 1 <;>
      simp [stateExcess, stateHalfWidth, stateUpper, stateLower, pulseRadius] <;>
      ring

theorem concretePi1_abs_le_Bs (t : ℝ) :
    |pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t| ≤
      concreteGateThreshold.Bs := by
  have h := concretePi1_mem t
  rcases h with ⟨hl, hu⟩
  rw [abs_le]
  constructor
  · linarith [concreteGateThreshold.deltaS_pos,
      concreteGateThreshold.deltaS_lt_one,
      concreteGateThreshold.Bs_gt_three]
  · exact hu

/-- The largest value needed for `Sigma₁` on the clipped state range. -/
def concreteSigmaBound : ℝ :=
  Sigma1 concreteTheta (-concreteGateThreshold.deltaS)

theorem concreteSigmaBound_nonneg : 0 ≤ concreteSigmaBound := by
  exact Sigma1_nonneg concreteTheta_pos _

theorem concreteSigma1_le (t : ℝ)
    (ht : t ∈ Set.Icc (-concreteGateThreshold.deltaS)
      concreteGateThreshold.Bs) :
    Sigma1 concreteTheta t ≤ concreteSigmaBound := by
  exact Sigma1_antitone concreteTheta ht.1

private theorem abs_Sigma1Deriv_le_one (t : ℝ) :
    |Sigma1Deriv concreteTheta t| ≤ 1 := by
  have h := leftHingeDeriv_mem 1 (1 + concreteTheta) t
  unfold Sigma1Deriv
  rw [abs_le]
  exact ⟨by linarith [h.1], h.2.trans (by norm_num)⟩

private theorem abs_Sigma2Deriv_le_one (tau t : ℝ) :
    |Sigma2Deriv tau t| ≤ 1 := by
  have h := leftHingeDeriv_mem (-tau) 0 t
  unfold Sigma2Deriv
  rw [abs_le]
  exact ⟨by linarith [h.1], h.2.trans (by norm_num)⟩

private theorem abs_concretePi1Deriv_le_one (t : ℝ) :
    |pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0 t| ≤ 1 := by
  have h := pi1Deriv_mem_unitInterval
    concreteGateThreshold.deltaS concreteSpatial.P0 t
  rw [abs_of_nonneg h.1]
  exact h.2

private theorem abs_Lambda2_le_one (t : ℝ) :
    |Lambda2 concreteTheta t| ≤ 1 := by
  have h := Lambda2_mem_unitInterval concreteTheta t
  rw [abs_of_nonneg h.1]
  exact h.2

private theorem concreteExitRelay_abs_le (t : ℝ) :
    |exitRelay concreteTheta
        (pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t)| ≤
      concreteGateThreshold.Bs := by
  rw [exitRelay, abs_mul]
  calc
    |pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t| *
        |Lambda2 concreteTheta
          (pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t)| ≤
        concreteGateThreshold.Bs * 1 := by
      exact mul_le_mul (concretePi1_abs_le_Bs t)
        (abs_Lambda2_le_one _) (abs_nonneg _)
        (by linarith [concreteGateThreshold.Bs_gt_three])
    _ = concreteGateThreshold.Bs := mul_one _

/-- The bound for the optional successor block in the memory remainder. -/
def concreteSuccessorBound : ℝ :=
  concreteGateThreshold.mu * Real.exp 1 +
    concreteGateThreshold.alpha * 24 * (concreteSpatial.P0 + 5 / 2) +
    concreteGateThreshold.beta * 24 * Real.exp 1 * concreteGateThreshold.Bs

private theorem concreteNextStateContribution_bound {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    |serializedNextStateContribution concretePreParameters q i| ≤
      concreteSuccessorBound := by
  unfold serializedNextStateContribution
  split_ifs with h
  · let j : Fin (T - 1) := ⟨i.val + 1, h⟩
    change |concreteGateThreshold.mu *
          Psi2 (serializedClippedNext concretePreParameters q j) *
          Sigma1Deriv concreteTheta
            (serializedClippedNext concretePreParameters q i) *
          pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
            (serializedState q i) -
        concreteGateThreshold.alpha *
          Psi2Deriv (serializedClippedNext concretePreParameters q i) *
          pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
            (serializedState q i) *
          Lambda2 concreteTheta
            (serializedClippedNext concretePreParameters q j) *
          pi2 concreteSpatial.P0 (serializedA q j) -
        concreteGateThreshold.beta *
          Psi2Deriv (serializedClippedNext concretePreParameters q i) *
          pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
            (serializedState q i) *
          Psi2 (serializedB q j) *
          exitRelay concreteTheta
            (serializedClippedNext concretePreParameters q j)| ≤ _
    have hmu : 0 ≤ concreteGateThreshold.mu :=
      concreteGateThreshold.mu_pos.le
    have halpha : 0 ≤ concreteGateThreshold.alpha :=
      concreteGateThreshold.alpha_pos.le
    have hbeta : 0 ≤ concreteGateThreshold.beta :=
      concreteGateThreshold.beta_pos.le
    have hP : 0 ≤ concreteSpatial.P0 + 5 / 2 := by
      linarith [concreteSpatial.P0_gt_one]
    have hBs : 0 ≤ concreteGateThreshold.Bs := by
      linarith [concreteGateThreshold.Bs_gt_three]
    have hterm1 :
        |concreteGateThreshold.mu *
          Psi2 (serializedClippedNext concretePreParameters q j) *
          Sigma1Deriv concreteTheta
            (serializedClippedNext concretePreParameters q i) *
          pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
            (serializedState q i)| ≤
          concreteGateThreshold.mu * Real.exp 1 := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hmu]
      have hp := Psi2_mem_range
        (serializedClippedNext concretePreParameters q j)
      rw [abs_of_nonneg hp.1]
      calc
        concreteGateThreshold.mu *
              Psi2 (serializedClippedNext concretePreParameters q j) *
              |Sigma1Deriv concreteTheta
                (serializedClippedNext concretePreParameters q i)| *
              |pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
                (serializedState q i)| ≤
            concreteGateThreshold.mu * Real.exp 1 * 1 * 1 := by
          gcongr
          · exact hp.2
          · exact abs_Sigma1Deriv_le_one _
          · exact abs_concretePi1Deriv_le_one _
        _ = concreteGateThreshold.mu * Real.exp 1 := by ring
    have hterm2 :
        |concreteGateThreshold.alpha *
          Psi2Deriv (serializedClippedNext concretePreParameters q i) *
          pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
            (serializedState q i) *
          Lambda2 concreteTheta
            (serializedClippedNext concretePreParameters q j) *
          pi2 concreteSpatial.P0 (serializedA q j)| ≤
        concreteGateThreshold.alpha * 24 *
          (concreteSpatial.P0 + 5 / 2) := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg halpha]
      calc
        concreteGateThreshold.alpha *
              |Psi2Deriv (serializedClippedNext concretePreParameters q i)| *
              |pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
                (serializedState q i)| *
              |Lambda2 concreteTheta
                (serializedClippedNext concretePreParameters q j)| *
              |pi2 concreteSpatial.P0 (serializedA q j)| ≤
            concreteGateThreshold.alpha * 24 * 1 * 1 *
              (concreteSpatial.P0 + 5 / 2) := by
          gcongr
          · exact abs_Psi2Deriv_le_twentyFour _
          · exact abs_concretePi1Deriv_le_one _
          · exact abs_Lambda2_le_one _
          · exact pi2_abs_le concreteSpatial.P0_gt_one
        _ = concreteGateThreshold.alpha * 24 *
              (concreteSpatial.P0 + 5 / 2) := by ring
    have hterm3 :
        |concreteGateThreshold.beta *
          Psi2Deriv (serializedClippedNext concretePreParameters q i) *
          pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
            (serializedState q i) *
          Psi2 (serializedB q j) *
          exitRelay concreteTheta
            (serializedClippedNext concretePreParameters q j)| ≤
        concreteGateThreshold.beta * 24 * Real.exp 1 *
          concreteGateThreshold.Bs := by
      rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hbeta]
      have hp := Psi2_mem_range (serializedB q j)
      rw [abs_of_nonneg hp.1]
      have hrelay :
          |exitRelay concreteTheta
            (serializedClippedNext concretePreParameters q j)| ≤
            concreteGateThreshold.Bs := by
        exact concreteExitRelay_abs_le (serializedState q j)
      calc
        concreteGateThreshold.beta *
              |Psi2Deriv (serializedClippedNext concretePreParameters q i)| *
              |pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
                (serializedState q i)| * Psi2 (serializedB q j) *
              |exitRelay concreteTheta
                (serializedClippedNext concretePreParameters q j)| ≤
            concreteGateThreshold.beta * 24 * 1 * Real.exp 1 *
              concreteGateThreshold.Bs := by
          gcongr
          · exact hp.1
          · exact abs_Psi2Deriv_le_twentyFour _
          · exact abs_concretePi1Deriv_le_one _
          · exact hp.2
        _ = concreteGateThreshold.beta * 24 * Real.exp 1 *
              concreteGateThreshold.Bs := by ring
    calc
      |_ - _ - _| ≤ |concreteGateThreshold.mu *
            Psi2 (serializedClippedNext concretePreParameters q j) *
            Sigma1Deriv concreteTheta
              (serializedClippedNext concretePreParameters q i) *
            pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
              (serializedState q i)| +
          |concreteGateThreshold.alpha *
            Psi2Deriv (serializedClippedNext concretePreParameters q i) *
            pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
              (serializedState q i) *
            Lambda2 concreteTheta
              (serializedClippedNext concretePreParameters q j) *
            pi2 concreteSpatial.P0 (serializedA q j)| +
          |concreteGateThreshold.beta *
            Psi2Deriv (serializedClippedNext concretePreParameters q i) *
            pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
              (serializedState q i) * Psi2 (serializedB q j) *
            exitRelay concreteTheta
              (serializedClippedNext concretePreParameters q j)| := by
        let a := concreteGateThreshold.mu *
          Psi2 (serializedClippedNext concretePreParameters q j) *
          Sigma1Deriv concreteTheta
            (serializedClippedNext concretePreParameters q i) *
          pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
            (serializedState q i)
        let b := concreteGateThreshold.alpha *
          Psi2Deriv (serializedClippedNext concretePreParameters q i) *
          pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
            (serializedState q i) *
          Lambda2 concreteTheta
            (serializedClippedNext concretePreParameters q j) *
          pi2 concreteSpatial.P0 (serializedA q j)
        let c := concreteGateThreshold.beta *
          Psi2Deriv (serializedClippedNext concretePreParameters q i) *
          pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0
            (serializedState q i) * Psi2 (serializedB q j) *
          exitRelay concreteTheta
            (serializedClippedNext concretePreParameters q j)
        change |a - b - c| ≤ |a| + |b| + |c|
        calc
          |a - b - c| = |(a + -b) + -c| := by ring
          _ ≤ |a + -b| + |-c| := abs_add_le _ _
          _ ≤ (|a| + |-b|) + |-c| :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                (add_le_add_right (abs_add_le a (-b)) |-c|)
          _ = |a| + |b| + |c| := by rw [abs_neg, abs_neg]
      _ ≤ concreteSuccessorBound := by
        unfold concreteSuccessorBound
        linarith
  · rw [abs_zero]
    unfold concreteSuccessorBound
    have hP : 0 ≤ concreteSpatial.P0 + 5 / 2 := by
      linarith [concreteSpatial.P0_gt_one]
    have hBs : 0 ≤ concreteGateThreshold.Bs := by
      linarith [concreteGateThreshold.Bs_gt_three]
    have hmu : 0 ≤ concreteGateThreshold.mu * Real.exp 1 :=
      mul_nonneg concreteGateThreshold.mu_pos.le (Real.exp_pos 1).le
    have ha : 0 ≤ concreteGateThreshold.alpha * 24 *
        (concreteSpatial.P0 + 5 / 2) :=
      mul_nonneg (mul_nonneg concreteGateThreshold.alpha_pos.le (by norm_num)) hP
    have hb : 0 ≤ concreteGateThreshold.beta * 24 * Real.exp 1 *
        concreteGateThreshold.Bs :=
      mul_nonneg
        (mul_nonneg (mul_nonneg concreteGateThreshold.beta_pos.le (by norm_num))
          (Real.exp_pos 1).le) hBs
    linarith

private theorem concreteExitRelayDeriv_bound (t : ℝ) :
    |exitRelayDeriv concreteTheta
        (pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t)| ≤
      1 + concreteGateThreshold.Bs * concreteLambdaDerivBound := by
  unfold exitRelayDeriv
  calc
    |Lambda2 concreteTheta
          (pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t) +
        pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t *
          deriv (Lambda2 concreteTheta)
            (pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t)| ≤
        |Lambda2 concreteTheta
          (pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t)| +
        |pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t *
          deriv (Lambda2 concreteTheta)
            (pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t)| :=
      abs_add_le _ _
    _ ≤ 1 + concreteGateThreshold.Bs * concreteLambdaDerivBound := by
      rw [abs_mul]
      exact add_le_add (abs_Lambda2_le_one _)
        (mul_le_mul (concretePi1_abs_le_Bs t)
          (deriv_Lambda2_concrete_bound _) (abs_nonneg _)
          (by linarith [concreteGateThreshold.Bs_gt_three]))

private theorem abs_five_memory_terms (a b c d e : ℝ) :
    |a + b - c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le a b
  have h2 := abs_add_le (a + b) (-c)
  have h3 := abs_add_le ((a + b) + (-c)) d
  have h4 := abs_add_le (((a + b) + (-c)) + d) e
  rw [abs_neg] at h2
  have heq : a + b - c + d + e = (((a + b) + (-c)) + d) + e := by ring
  rw [heq]
  linarith

/-- The explicit sum of the proved bounds for every summand of the literal
memory remainder. -/
def concreteCs : ℝ :=
  1 +
    concreteGateThreshold.mu * 24 * concreteSigmaBound +
    concreteGateThreshold.alpha * Real.exp 1 * concreteLambdaDerivBound *
      (concreteSpatial.P0 + 5 / 2) +
    concreteGateThreshold.beta * Real.exp 1 * Real.exp 1 *
      (1 + concreteGateThreshold.Bs * concreteLambdaDerivBound) +
    concreteSuccessorBound

/-- The actual uniform `c_s` estimate used in the TeX hierarchy.  It is a
bound for the literal eta-independent summands of `serializedGradState`, for
every dimension, horizon, point, and state coordinate. -/
theorem concreteCs_dominates_memory_remainder {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    |serializedMemoryRemainder concretePreParameters q i| ≤ concreteCs := by
  let raw := serializedState q i
  let cur := serializedClippedCurrent concretePreParameters q i
  let nxt := serializedClippedNext concretePreParameters q i
  let cd := pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0 raw
  have hmu : 0 ≤ concreteGateThreshold.mu := concreteGateThreshold.mu_pos.le
  have halpha : 0 ≤ concreteGateThreshold.alpha :=
    concreteGateThreshold.alpha_pos.le
  have hbeta : 0 ≤ concreteGateThreshold.beta :=
    concreteGateThreshold.beta_pos.le
  have hP : 0 ≤ concreteSpatial.P0 + 5 / 2 := by
    linarith [concreteSpatial.P0_gt_one]
  have hBs : 0 ≤ concreteGateThreshold.Bs := by
    linarith [concreteGateThreshold.Bs_gt_three]
  have hL : 0 ≤ concreteLambdaDerivBound :=
    concreteLambdaDerivBound_nonneg
  have hS : 0 ≤ concreteSigmaBound := concreteSigmaBound_nonneg
  have hwall : |Sigma2Deriv concretePreParameters.tauS raw| ≤ 1 :=
    abs_Sigma2Deriv_le_one _ _
  have hmemory :
      |concreteGateThreshold.mu * Psi2Deriv nxt * cd *
        Sigma1 concreteTheta cur| ≤
      concreteGateThreshold.mu * 24 * concreteSigmaBound := by
    have hcur : cur ∈ Set.Icc (-concreteGateThreshold.deltaS)
        concreteGateThreshold.Bs := by
      exact concretePi1_mem (serializedCurrentState q i)
    have hs0 : 0 ≤ Sigma1 concreteTheta cur :=
      Sigma1_nonneg concreteTheta_pos _
    have hs1 : Sigma1 concreteTheta cur ≤ concreteSigmaBound :=
      concreteSigma1_le cur hcur
    rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hmu,
      abs_of_nonneg hs0]
    calc
      concreteGateThreshold.mu * |Psi2Deriv nxt| * |cd| *
          Sigma1 concreteTheta cur ≤
        concreteGateThreshold.mu * 24 * 1 * concreteSigmaBound := by
          gcongr
          · exact abs_Psi2Deriv_le_twentyFour _
          · exact abs_concretePi1Deriv_le_one raw
      _ = concreteGateThreshold.mu * 24 * concreteSigmaBound := by ring
  have hentrance :
      |concreteGateThreshold.alpha * Psi2 cur *
        deriv (Lambda2 concreteTheta) nxt * cd *
        pi2 concreteSpatial.P0 (serializedA q i)| ≤
      concreteGateThreshold.alpha * Real.exp 1 *
        concreteLambdaDerivBound * (concreteSpatial.P0 + 5 / 2) := by
    have hp := Psi2_mem_range cur
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg halpha,
      abs_of_nonneg hp.1]
    calc
      concreteGateThreshold.alpha * Psi2 cur *
          |deriv (Lambda2 concreteTheta) nxt| * |cd| *
          |pi2 concreteSpatial.P0 (serializedA q i)| ≤
        concreteGateThreshold.alpha * Real.exp 1 *
          concreteLambdaDerivBound * 1 *
          (concreteSpatial.P0 + 5 / 2) := by
            gcongr
            · exact hp.2
            · exact deriv_Lambda2_concrete_bound _
            · exact abs_concretePi1Deriv_le_one raw
            · exact pi2_abs_le concreteSpatial.P0_gt_one
      _ = concreteGateThreshold.alpha * Real.exp 1 *
          concreteLambdaDerivBound * (concreteSpatial.P0 + 5 / 2) := by ring
  have hexit :
      |exitPulseDerivNext concreteGateThreshold.beta concreteTheta cur
          (serializedB q i) nxt * cd| ≤
      concreteGateThreshold.beta * Real.exp 1 * Real.exp 1 *
        (1 + concreteGateThreshold.Bs * concreteLambdaDerivBound) := by
    have hcurPsi := Psi2_mem_range cur
    have hbPsi := Psi2_mem_range (serializedB q i)
    have hrelay : |exitRelayDeriv concreteTheta nxt| ≤
        1 + concreteGateThreshold.Bs * concreteLambdaDerivBound := by
      exact concreteExitRelayDeriv_bound raw
    unfold exitPulseDerivNext
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_neg,
      abs_of_nonneg hbeta, abs_of_nonneg hcurPsi.1,
      abs_of_nonneg hbPsi.1]
    calc
      concreteGateThreshold.beta * Psi2 cur * Psi2 (serializedB q i) *
          |exitRelayDeriv concreteTheta nxt| * |cd| ≤
        concreteGateThreshold.beta * Real.exp 1 * Real.exp 1 *
          (1 + concreteGateThreshold.Bs * concreteLambdaDerivBound) * 1 := by
            gcongr
            · exact hbPsi.1
            · exact hcurPsi.2
            · exact hbPsi.2
            · exact abs_concretePi1Deriv_le_one raw
      _ = concreteGateThreshold.beta * Real.exp 1 * Real.exp 1 *
          (1 + concreteGateThreshold.Bs * concreteLambdaDerivBound) := by ring
  have hnext := concreteNextStateContribution_bound q i
  unfold serializedMemoryRemainder
  change |Sigma2Deriv concretePreParameters.tauS raw +
      concreteGateThreshold.mu * Psi2Deriv nxt * cd *
        Sigma1 concreteTheta cur -
      concreteGateThreshold.alpha * Psi2 cur *
        deriv (Lambda2 concreteTheta) nxt * cd *
        pi2 concreteSpatial.P0 (serializedA q i) +
      exitPulseDerivNext concreteGateThreshold.beta concreteTheta cur
        (serializedB q i) nxt * cd +
      serializedNextStateContribution concretePreParameters q i| ≤ concreteCs
  calc
    |_ + _ - _ + _ + _| ≤
        |Sigma2Deriv concretePreParameters.tauS raw| +
        |concreteGateThreshold.mu * Psi2Deriv nxt * cd *
          Sigma1 concreteTheta cur| +
        |concreteGateThreshold.alpha * Psi2 cur *
          deriv (Lambda2 concreteTheta) nxt * cd *
          pi2 concreteSpatial.P0 (serializedA q i)| +
        |exitPulseDerivNext concreteGateThreshold.beta concreteTheta cur
          (serializedB q i) nxt * cd| +
        |serializedNextStateContribution concretePreParameters q i| :=
      abs_five_memory_terms _ _ _ _ _
    _ ≤ concreteCs := by
      unfold concreteSuccessorBound at hnext
      unfold concreteCs concreteSuccessorBound
      linarith

theorem concreteCs_pos : 0 < concreteCs := by
  have hP : 0 < concreteSpatial.P0 + 5 / 2 := by
    linarith [concreteSpatial.P0_gt_one]
  have hBs : 0 < concreteGateThreshold.Bs :=
    lt_trans (by norm_num) concreteGateThreshold.Bs_gt_three
  have hL := concreteLambdaDerivBound_nonneg
  have hS := concreteSigmaBound_nonneg
  have h1 : 0 ≤ concreteGateThreshold.mu * 24 * concreteSigmaBound := by
    exact mul_nonneg
      (mul_nonneg concreteGateThreshold.mu_pos.le (by norm_num)) hS
  have h2 : 0 ≤ concreteGateThreshold.alpha * Real.exp 1 *
      concreteLambdaDerivBound * (concreteSpatial.P0 + 5 / 2) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg concreteGateThreshold.alpha_pos.le (Real.exp_pos 1).le) hL)
      hP.le
  have h3 : 0 ≤ concreteGateThreshold.beta * Real.exp 1 * Real.exp 1 *
      (1 + concreteGateThreshold.Bs * concreteLambdaDerivBound) := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg concreteGateThreshold.beta_pos.le (Real.exp_pos 1).le)
        (Real.exp_pos 1).le)
      (by exact add_nonneg zero_le_one (mul_nonneg hBs.le hL))
  have h4 : 0 ≤ concreteSuccessorBound := by
    unfold concreteSuccessorBound
    exact add_nonneg
      (add_nonneg
        (mul_nonneg concreteGateThreshold.mu_pos.le (Real.exp_pos 1).le)
        (mul_nonneg
          (mul_nonneg concreteGateThreshold.alpha_pos.le (by norm_num)) hP.le))
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg concreteGateThreshold.beta_pos.le (by norm_num))
            (Real.exp_pos 1).le) hBs.le)
  unfold concreteCs
  linarith

/-- The final transition choice, made only after the actual `c_s` theorem. -/
def concreteTransitionEta : TransitionEtaConstants concreteCs 2 :=
  Classical.choice <| transitionEtaConstants_nonempty concreteCs_pos.le
    (by norm_num)

/-- The two dependency-correct stages assembled into the record used by the
radial estimates. -/
def concreteRadialTransition :
    RadialTransitionConstants concreteGateThreshold.gamma
      concreteCp concreteCq concreteCs
      2 concreteGateThreshold.deltaS concreteGateThreshold.Bs :=
  assembleRadialTransition concreteSpatial concreteTransitionEta

/-- The paper's scalar choices assembled into the parameter record consumed
by the literal objective.  In particular, the wall width is `tauS delta`,
not an independent parameter. -/
def concreteUnscaledParameters : UnscaledParameters where
  theta := concreteTheta
  delta := concreteGateThreshold.deltaS
  P0 := concreteRadialTransition.P0
  tauS := tauS concreteGateThreshold.deltaS
  alpha := concreteGateThreshold.alpha
  beta := concreteGateThreshold.beta
  gamma := concreteGateThreshold.gamma
  mu := concreteGateThreshold.mu
  eta := concreteRadialTransition.eta
  P1 := concreteRadialTransition.P1
  K := concreteRadialTransition.K
  theta_pos := concreteTheta_pos
  delta_pos := concreteGateThreshold.deltaS_pos
  P0_gt_one := concreteRadialTransition.P0_gt_one
  tauS_pos := by
    unfold tauS
    exact div_pos concreteGateThreshold.deltaS_pos (by norm_num)

theorem concreteCs_dominates_final_memory_remainder {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1)) :
    |serializedMemoryRemainder concreteUnscaledParameters q i| ≤ concreteCs := by
  change |serializedMemoryRemainder concretePreParameters q i| ≤ concreteCs
  exact concreteCs_dominates_memory_remainder q i

/-- The literal primal-unconstrained domain `X_uc`. -/
def unscaledPrimalDomain (T : Nat) : Set (UnscaledPrimal T) := Set.univ

/-- The literal dual domain `Y_D = D Ball`, whose Euclidean radius is
`D/2` in the paper's normalization. -/
def unscaledDualDomain (T n : Nat) (D : ℝ) : Set (UnscaledDual T n) :=
  diameterBall (n * (T - 1)) D

/-- The complete unscaled problem datum, with the genuine Fréchet gradients
proved in `UnscaledSerialization.lean`. -/
def unscaledNCCInstance {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (D : ℝ) :
    NCCInstance (3 * (T - 1)) (n * (T - 1)) where
  X := unscaledPrimalDomain T
  Y := unscaledDualDomain T n D
  f := unscaledObjective hn P
  gradX := unscaledTrueGradX hn P
  gradY := unscaledTrueGradY hn P
  x0 := 0

@[simp] theorem concreteUnscaledObjective_zero_zero {T n : Nat} (hn : 0 < n) :
    unscaledObjective hn concreteUnscaledParameters (0 : UnscaledPrimal T)
      (0 : UnscaledDual T n) = 0 := by
  have hP0 : 0 < concreteRadialTransition.P0 := by
    linarith [concreteRadialTransition.P0_gt_one]
  have hP1 : 0 < concreteRadialTransition.P1 :=
    hP0.trans concreteRadialTransition.P0_lt_P1
  have hsq : concreteRadialTransition.P0 ^ 2 <
      concreteRadialTransition.P1 ^ 2 := by
    have hd : 0 < concreteRadialTransition.P1 -
        concreteRadialTransition.P0 := sub_pos.mpr
      concreteRadialTransition.P0_lt_P1
    have hs : 0 < concreteRadialTransition.P1 +
        concreteRadialTransition.P0 := add_pos hP1 hP0
    nlinarith [mul_pos hd hs]
  have hpi : pi1 concreteGateThreshold.deltaS
      concreteRadialTransition.P0 0 = 0 := by
    simpa [concreteUnscaledParameters] using
      (pi1_zero_of_parameters concreteUnscaledParameters)
  have hsigma : Sigma2 (tauS concreteGateThreshold.deltaS) 0 = 0 := by
    exact Sigma2_eq_zero concreteUnscaledParameters.tauS_pos le_rfl
  have hinner : innerChain hn (innerC hn) 0 0 (fun _ => 0) = 0 := by
    change innerChain hn (innerC hn) 0 0 (0 : EVec n) = 0
    exact innerChain_zero_dual hn (innerC hn) 0 0
  have hrad : Sigma3 concreteRadialTransition.P0
      concreteRadialTransition.P1 concreteRadialTransition.K 0 = 0 := by
    exact Sigma3_eq_zero hsq (sq_nonneg concreteRadialTransition.P0)
  unfold unscaledObjective unscaledBlock clippedCurrent clippedNext currentState
    primalA primalB primalState dualBlock pulseSq entrancePulse exitPulse
  simp [concreteUnscaledParameters, hpi, hsigma, hinner, hrad,
    primalA, primalB, pi2_zero, Psi1_zero, Psi2_zero]

theorem concreteUnscaledObjective_zero_nonpos {T n : Nat} (hn : 0 < n)
    (y : UnscaledDual T n) :
    unscaledObjective hn concreteUnscaledParameters (0 : UnscaledPrimal T) y ≤ 0 := by
  have hP0 : 0 < concreteRadialTransition.P0 := by
    linarith [concreteRadialTransition.P0_gt_one]
  have hP1 : 0 < concreteRadialTransition.P1 :=
    hP0.trans concreteRadialTransition.P0_lt_P1
  have hsq : concreteRadialTransition.P0 ^ 2 <
      concreteRadialTransition.P1 ^ 2 := by
    have hd : 0 < concreteRadialTransition.P1 -
        concreteRadialTransition.P0 := sub_pos.mpr
      concreteRadialTransition.P0_lt_P1
    have hs : 0 < concreteRadialTransition.P1 +
        concreteRadialTransition.P0 := add_pos hP1 hP0
    nlinarith [mul_pos hd hs]
  have hpi : pi1 concreteGateThreshold.deltaS
      concreteRadialTransition.P0 0 = 0 := by
    simpa [concreteUnscaledParameters] using
      (pi1_zero_of_parameters concreteUnscaledParameters)
  have hsigma : Sigma2 (tauS concreteGateThreshold.deltaS) 0 = 0 :=
    Sigma2_eq_zero concreteUnscaledParameters.tauS_pos le_rfl
  have hrad : Sigma3 concreteRadialTransition.P0
      concreteRadialTransition.P1 concreteRadialTransition.K 0 = 0 :=
    Sigma3_eq_zero hsq (sq_nonneg concreteRadialTransition.P0)
  have heq :
      unscaledObjective hn concreteUnscaledParameters (0 : UnscaledPrimal T) y =
        ∑ i : Fin (T - 1),
          innerChain hn (innerC hn) 0 0 (dualBlock y i) := by
    unfold unscaledObjective unscaledBlock clippedCurrent clippedNext currentState
      primalA primalB primalState pulseSq entrancePulse exitPulse
    simp [concreteUnscaledParameters, hpi, hsigma, hrad,
      primalA, primalB, pi2_zero, Psi1_zero, Psi2_zero]
  rw [heq]
  exact Finset.sum_nonpos fun i _ =>
    innerChain_zero_primal_nonpos hn (innerC hn) (dualBlock y i)

theorem concreteUnscaledValue_zero {T n : Nat} (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) :
    ValueOn (unscaledDualDomain T n D)
      (unscaledObjective hn concreteUnscaledParameters)
      (0 : UnscaledPrimal T) = 0 := by
  have hmax : IsMaximizerOn (unscaledDualDomain T n D)
      (unscaledObjective hn concreteUnscaledParameters)
      (0 : UnscaledPrimal T) (0 : UnscaledDual T n) := by
    refine ⟨zero_mem_diameterBall _ _ hD, ?_⟩
    intro y hy
    rw [concreteUnscaledObjective_zero_zero]
    exact concreteUnscaledObjective_zero_nonpos hn y
  simpa using value_eq_of_isMaximizerOn hmax

/-- A genuine value bound for the two pulse summands in one block. -/
def concretePulseValueBound : ℝ :=
  concreteGateThreshold.alpha * Real.exp 1 *
      (concreteSpatial.P0 + 5 / 2) +
    concreteGateThreshold.beta * Real.exp 1 * Real.exp 1 *
      concreteGateThreshold.Bs

theorem concretePulseValueBound_nonneg : 0 ≤ concretePulseValueBound := by
  unfold concretePulseValueBound
  have hP : 0 ≤ concreteSpatial.P0 + 5 / 2 := by
    linarith [concreteSpatial.P0_gt_one]
  have hBs : 0 ≤ concreteGateThreshold.Bs := by
    linarith [concreteGateThreshold.Bs_gt_three]
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg concreteGateThreshold.alpha_pos.le (Real.exp_pos 1).le) hP)
    (mul_nonneg
      (mul_nonneg
        (mul_nonneg concreteGateThreshold.beta_pos.le (Real.exp_pos 1).le)
          (Real.exp_pos 1).le) hBs)

private theorem concreteBlock_zero_dual_lower {T n : Nat} (hn : 10 ≤ n)
    (x : UnscaledPrimal T) (i : Fin (T - 1)) :
    -concretePulseValueBound - concreteCq *
        ((primalA x i) ^ 2 + (primalB x i) ^ 2) ≤
      unscaledBlock (by omega : 0 < n) concreteUnscaledParameters x 0 i := by
  let cur := clippedCurrent concreteUnscaledParameters x i
  let nxt := clippedNext concreteUnscaledParameters x i
  let a := primalA x i
  let b := primalB x i
  have halpha : 0 ≤ concreteGateThreshold.alpha :=
    concreteGateThreshold.alpha_pos.le
  have hbeta : 0 ≤ concreteGateThreshold.beta :=
    concreteGateThreshold.beta_pos.le
  have hP : 0 ≤ concreteSpatial.P0 + 5 / 2 := by
    linarith [concreteSpatial.P0_gt_one]
  have hBs : 0 ≤ concreteGateThreshold.Bs := by
    linarith [concreteGateThreshold.Bs_gt_three]
  have hentrance :
      |entrancePulse concreteGateThreshold.alpha concreteTheta
          concreteSpatial.P0 cur nxt a| ≤
        concreteGateThreshold.alpha * Real.exp 1 *
          (concreteSpatial.P0 + 5 / 2) := by
    unfold entrancePulse
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg halpha]
    have hp := Psi2_mem_range cur
    have hl := Lambda2_mem_unitInterval concreteTheta nxt
    rw [abs_of_nonneg hp.1, abs_of_nonneg hl.1]
    calc
      concreteGateThreshold.alpha * Psi2 cur * Lambda2 concreteTheta nxt *
          |pi2 concreteSpatial.P0 a| ≤
        concreteGateThreshold.alpha * Real.exp 1 * 1 *
          (concreteSpatial.P0 + 5 / 2) := by
            gcongr
            · exact hl.1
            · exact hp.2
            · exact hl.2
            · exact pi2_abs_le concreteSpatial.P0_gt_one
      _ = concreteGateThreshold.alpha * Real.exp 1 *
          (concreteSpatial.P0 + 5 / 2) := by ring
  have hexit :
      |exitPulse concreteGateThreshold.beta concreteTheta cur b nxt| ≤
        concreteGateThreshold.beta * Real.exp 1 * Real.exp 1 *
          concreteGateThreshold.Bs := by
    unfold exitPulse
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_nonneg hbeta]
    have hc := Psi2_mem_range cur
    have hb := Psi2_mem_range b
    rw [abs_of_nonneg hc.1, abs_of_nonneg hb.1]
    have hr : |exitRelay concreteTheta nxt| ≤ concreteGateThreshold.Bs := by
      exact concreteExitRelay_abs_le (primalState x i)
    calc
      concreteGateThreshold.beta * Psi2 cur * Psi2 b *
          |exitRelay concreteTheta nxt| ≤
        concreteGateThreshold.beta * Real.exp 1 * Psi2 b *
          |exitRelay concreteTheta nxt| := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hc.2 hbeta) hb.1)
              (abs_nonneg _)
      _ ≤ concreteGateThreshold.beta * Real.exp 1 * Real.exp 1 *
          |exitRelay concreteTheta nxt| := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hb.2
                (mul_nonneg hbeta (Real.exp_pos 1).le)) (abs_nonneg _)
      _ ≤ concreteGateThreshold.beta * Real.exp 1 * Real.exp 1 *
          concreteGateThreshold.Bs := by
            exact mul_le_mul_of_nonneg_left hr
              (mul_nonneg
                (mul_nonneg hbeta (Real.exp_pos 1).le)
                (Real.exp_pos 1).le)
  have hpulses : -concretePulseValueBound ≤
      entrancePulse concreteGateThreshold.alpha concreteTheta
          concreteSpatial.P0 cur nxt a +
        exitPulse concreteGateThreshold.beta concreteTheta cur b nxt := by
    unfold concretePulseValueBound
    calc
      -(concreteGateThreshold.alpha * Real.exp 1 *
            (concreteSpatial.P0 + 5 / 2) +
          concreteGateThreshold.beta * Real.exp 1 * Real.exp 1 *
            concreteGateThreshold.Bs) ≤
          -(|entrancePulse concreteGateThreshold.alpha concreteTheta
              concreteSpatial.P0 cur nxt a| +
            |exitPulse concreteGateThreshold.beta concreteTheta cur b nxt|) := by
        exact neg_le_neg (add_le_add hentrance hexit)
      _ ≤ -|entrancePulse concreteGateThreshold.alpha concreteTheta
              concreteSpatial.P0 cur nxt a +
            exitPulse concreteGateThreshold.beta concreteTheta cur b nxt| := by
        exact neg_le_neg (abs_add_le _ _)
      _ ≤ entrancePulse concreteGateThreshold.alpha concreteTheta
              concreteSpatial.P0 cur nxt a +
            exitPulse concreteGateThreshold.beta concreteTheta cur b nxt := by
        exact neg_abs_le _
  have hdual : dualBlock (0 : UnscaledDual T n) i = 0 := by
    funext k
    simp [dualBlock]
  unfold unscaledBlock
  change -concretePulseValueBound - concreteCq * (a ^ 2 + b ^ 2) ≤ _
  rw [hdual, innerChain_zero_dual]
  dsimp [cur, nxt, a, b] at hpulses ⊢
  simp only [clippedCurrent, clippedNext, concreteUnscaledParameters,
    concreteRadialTransition, assembleRadialTransition] at hpulses ⊢
  nlinarith [concreteCq_dominates_quadratic_correction hn
    (primalA x i) (primalB x i)]

/-- A dimension-dependent but completely explicit global lower bound for the
unscaled value. -/
def concreteValueLower (T : Nat) : ℝ :=
  -((T - 1 : Nat) : ℝ) *
      (concreteTransitionEta.eta * Real.exp 1 + concretePulseValueBound) -
    concreteCq * concreteSpatial.P1 ^ 2

theorem concreteObjective_zero_dual_lower {T n : Nat} (hn : 10 ≤ n)
    (x : UnscaledPrimal T) :
    concreteValueLower T ≤
      unscaledObjective (by omega : 0 < n) concreteUnscaledParameters x 0 := by
  let P := concreteUnscaledParameters
  have heta : 0 ≤ concreteTransitionEta.eta :=
    concreteTransitionEta.eta_pos.le
  have hpsiSum :
      (∑ i : Fin (T - 1), Psi1 (clippedNext P x i)) ≤
        ((T - 1 : Nat) : ℝ) * Real.exp 1 := by
    calc
      (∑ i : Fin (T - 1), Psi1 (clippedNext P x i)) ≤
          ∑ _i : Fin (T - 1), Real.exp 1 := by
            exact Finset.sum_le_sum fun i _ => (Psi1_mem_range _).2
      _ = ((T - 1 : Nat) : ℝ) * Real.exp 1 := by simp
  have hwall : 0 ≤ ∑ i : Fin (T - 1),
      Sigma2 P.tauS (primalState x i) := by
    exact Finset.sum_nonneg fun i _ => Sigma2_nonneg P.tauS_pos _
  have hmemory : 0 ≤ P.mu * ∑ i : Fin (T - 1),
      Psi2 (clippedNext P x i) * Sigma1 P.theta (clippedCurrent P x i) := by
    apply mul_nonneg concreteGateThreshold.mu_pos.le
    exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (Psi2_mem_range _).1 (Sigma1_nonneg concreteTheta_pos _)
  have hblockEach := fun i : Fin (T - 1) =>
    concreteBlock_zero_dual_lower hn x i
  have hblockSum :
      -((T - 1 : Nat) : ℝ) * concretePulseValueBound -
          concreteCq * pulseSq x ≤
        ∑ i : Fin (T - 1),
          unscaledBlock (by omega : 0 < n) P x 0 i := by
    have hs := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) => hblockEach i
    unfold pulseSq
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hs
    simpa [P, mul_add, Finset.mul_sum] using hs
  have hrad : -concreteCq * concreteSpatial.P1 ^ 2 ≤
      Sigma3 concreteSpatial.P0 concreteSpatial.P1 concreteSpatial.K
          (pulseSq x) - concreteCq * pulseSq x := by
    have hP0 : 0 < concreteSpatial.P0 := by
      linarith [concreteSpatial.P0_gt_one]
    have hP1 : 0 < concreteSpatial.P1 :=
      hP0.trans concreteSpatial.P0_lt_P1
    have hsq : concreteSpatial.P0 ^ 2 < concreteSpatial.P1 ^ 2 := by
      have hd : 0 < concreteSpatial.P1 - concreteSpatial.P0 :=
        sub_pos.mpr concreteSpatial.P0_lt_P1
      have hs : 0 < concreteSpatial.P1 + concreteSpatial.P0 := add_pos hP1 hP0
      nlinarith [mul_pos hd hs]
    have hpulse : 0 ≤ pulseSq x := by
      unfold pulseSq
      exact Finset.sum_nonneg fun i _ =>
        add_nonneg (sq_nonneg _) (sq_nonneg _)
    let p : EVec 1 := fun _ => Real.sqrt (pulseSq x)
    have hpvec : vecSq p = pulseSq x := by
      unfold vecSq NCPLVerification.vecSq p
      simp [Real.sq_sqrt hpulse]
    have hbase := radialBudget_sub_quadratic_lower
      (P0 := concreteSpatial.P0) (P1 := concreteSpatial.P1)
      (K := concreteSpatial.K) (cq := concreteCq)
      hsq concreteCq_pos.le (by linarith [concreteSpatial.K_gt]) p
    simpa [radialBudget, hpvec] using hbase
  unfold concreteValueLower unscaledObjective
  change -((T - 1 : Nat) : ℝ) *
        (concreteTransitionEta.eta * Real.exp 1 + concretePulseValueBound) -
      concreteCq * concreteSpatial.P1 ^ 2 ≤
    -P.eta * (∑ i : Fin (T - 1), Psi1 (clippedNext P x i)) +
      (∑ i : Fin (T - 1), Sigma2 P.tauS (primalState x i)) +
      P.mu * (∑ i : Fin (T - 1),
        Psi2 (clippedNext P x i) * Sigma1 P.theta (clippedCurrent P x i)) +
      (∑ i : Fin (T - 1),
        unscaledBlock (by omega : 0 < n) P x 0 i) +
      Sigma3 concreteSpatial.P0 concreteSpatial.P1 concreteSpatial.K (pulseSq x)
  have hetaField : P.eta = concreteTransitionEta.eta := by
    rfl
  rw [hetaField]
  have hneg := neg_le_neg
    (mul_le_mul_of_nonneg_left hpsiSum heta)
  nlinarith

@[simp] theorem zero_mem_unscaledPrimalDomain (T : Nat) :
    (0 : UnscaledPrimal T) ∈ unscaledPrimalDomain T := by
  simp [unscaledPrimalDomain]

theorem unscaledPrimalDomain_nonempty (T : Nat) :
    (unscaledPrimalDomain T).Nonempty := Set.univ_nonempty

theorem unscaledPrimalDomain_closed (T : Nat) :
    IsClosed (unscaledPrimalDomain T) := isClosed_univ

theorem unscaledPrimalDomain_convex (T : Nat) :
    Convex ℝ (unscaledPrimalDomain T) := convex_univ

theorem unscaledDualDomain_nonempty {T n : Nat} {D : ℝ} (hD : 0 ≤ D) :
    (unscaledDualDomain T n D).Nonempty := by
  exact diameterBall_nonempty _ _ hD

theorem unscaledDualDomain_closed (T n : Nat) (D : ℝ) :
    IsClosed (unscaledDualDomain T n D) := by
  exact diameterBall_closed _ _

theorem unscaledDualDomain_convex (T n : Nat) (D : ℝ) :
    Convex ℝ (unscaledDualDomain T n D) := by
  exact diameterBall_convex _ _

theorem unscaledDualDomain_diameter {T n : Nat} {D : ℝ} (hD : 0 ≤ D)
    {y y' : UnscaledDual T n} (hy : y ∈ unscaledDualDomain T n D)
    (hy' : y' ∈ unscaledDualDomain T n D) :
    vecSq (y - y') ≤ D ^ 2 := by
  exact diameterBall_vecSq_sub_le hD hy hy'

theorem unscaledDualDomain_isBounded (T n : Nat) (D : ℝ) :
    Bornology.IsBounded (unscaledDualDomain T n D) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : UnscaledDual T n)]
  refine ⟨|D / 2|, ?_⟩
  intro y hy
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg (D / 2))).2
  intro i
  have hi : (y i) ^ 2 ≤ vecSq y := by
    unfold vecSq NCPLVerification.vecSq
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (y j)) (Finset.mem_univ i)
  have hyr : vecSq y ≤ (D / 2) ^ 2 := hy
  have habsSq : |y i| ^ 2 ≤ |D / 2| ^ 2 := by
    simpa only [sq_abs] using hi.trans hyr
  simpa only [Real.norm_eq_abs] using
    (sq_le_sq₀ (abs_nonneg (y i)) (abs_nonneg (D / 2))).mp habsSq

theorem unscaledDualDomain_compact (T n : Nat) (D : ℝ) :
    IsCompact (unscaledDualDomain T n D) := by
  exact Metric.isCompact_of_isClosed_isBounded (unscaledDualDomain_closed T n D)
    (unscaledDualDomain_isBounded T n D)

theorem unscaledNCCInstance_gradient_representation {T n : Nat}
    (hn : 0 < n) (P : UnscaledParameters) (D : ℝ) :
    NCPLVerification.RepresentsJointGradient
      (unscaledNCCInstance (T := T) hn P D).f
      (unscaledNCCInstance (T := T) hn P D).gradX
      (unscaledNCCInstance (T := T) hn P D).gradY := by
  exact unscaledTrueGradient_representsJointGradient hn P

theorem unscaledObjective_dual_continuous {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) :
    Continuous (unscaledObjective hn P x) := by
  rw [continuous_iff_continuousAt]
  intro y
  have hp := (hasFDerivAt_const (𝕜 := ℝ) (x := y) x).prodMk
    (hasFDerivAt_id (𝕜 := ℝ) y)
  have hc := (unscaledObjective_hasFDerivAt hn P x y).comp y hp |>.continuousAt
  exact hc

theorem unscaledObjective_maximum_attained {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) {D : ℝ} (hD : 0 ≤ D)
    (x : UnscaledPrimal T) :
    ∃ y, IsMaximizerOn (unscaledDualDomain T n D)
      (unscaledObjective hn P) x y := by
  obtain ⟨y, hy, hmax⟩ := (unscaledDualDomain_compact T n D).exists_isMaxOn
    (unscaledDualDomain_nonempty hD)
    (unscaledObjective_dual_continuous hn P x).continuousOn
  exact ⟨y, hy, fun z hz ↦ hmax hz⟩

theorem concreteUnscaledValue_lower {T n : Nat} (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) (x : UnscaledPrimal T) :
    concreteValueLower T ≤
      ValueOn (unscaledDualDomain T n D)
        (unscaledObjective (by omega : 0 < n) concreteUnscaledParameters) x := by
  obtain ⟨y, hy, hmax⟩ := unscaledObjective_maximum_attained
    (T := T) (by omega : 0 < n) concreteUnscaledParameters hD x
  rw [value_eq_of_isMaximizerOn ⟨hy, hmax⟩]
  exact (concreteObjective_zero_dual_lower hn x).trans
    (hmax 0 (zero_mem_diameterBall _ _ hD))

theorem concreteUnscaledValue_bddBelow {T n : Nat} (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) :
    BddBelow
      (ValueOn (unscaledDualDomain T n D)
        (unscaledObjective (by omega : 0 < n) concreteUnscaledParameters) ''
          unscaledPrimalDomain T) := by
  refine ⟨concreteValueLower T, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact concreteUnscaledValue_lower hn hD x

def concreteDelta0 (T : Nat) : ℝ := 1 + |concreteValueLower T|

theorem concreteDelta0_pos (T : Nat) : 0 < concreteDelta0 T := by
  unfold concreteDelta0
  linarith [abs_nonneg (concreteValueLower T)]

/-- A single numerical coefficient controlling the initial gap for every
chain length.  Unlike `concreteDelta0 T`, this constant has no dependence on
`T`, `n`, or the dual diameter. -/
def concreteCDelta : ℝ :=
  1 + (concreteTransitionEta.eta * Real.exp 1 + concretePulseValueBound) +
    concreteCq * concreteSpatial.P1 ^ 2

theorem concreteCDelta_pos : 0 < concreteCDelta := by
  have heta : 0 ≤ concreteTransitionEta.eta := concreteTransitionEta.eta_pos.le
  have hexp : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have hpulse : 0 ≤ concretePulseValueBound := concretePulseValueBound_nonneg
  have hrad : 0 ≤ concreteCq * concreteSpatial.P1 ^ 2 :=
    mul_nonneg concreteCq_pos.le (sq_nonneg _)
  unfold concreteCDelta
  positivity

/-- The explicit initial-gap witness grows at most linearly in the chain
length, with the fixed coefficient `concreteCDelta`. -/
theorem concreteDelta0_le_concreteCDelta_mul (T : Nat) (hT : 1 ≤ T) :
    concreteDelta0 T ≤ concreteCDelta * T := by
  let A : ℝ := concreteTransitionEta.eta * Real.exp 1 + concretePulseValueBound
  let B : ℝ := concreteCq * concreteSpatial.P1 ^ 2
  have hA : 0 ≤ A := by
    dsimp [A]
    exact add_nonneg
      (mul_nonneg concreteTransitionEta.eta_pos.le (Real.exp_pos 1).le)
      concretePulseValueBound_nonneg
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg concreteCq_pos.le (sq_nonneg _)
  have hTreal : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTm1 : (((T - 1 : Nat) : ℝ)) ≤ (T : ℝ) := by
    exact_mod_cast Nat.sub_le T 1
  have hvalue : concreteValueLower T ≤ 0 := by
    unfold concreteValueLower
    change -(((T - 1 : Nat) : ℝ)) * A - B ≤ 0
    have hm : 0 ≤ (((T - 1 : Nat) : ℝ)) := by positivity
    nlinarith [mul_nonneg hm hA]
  rw [concreteDelta0, abs_of_nonpos hvalue]
  unfold concreteCDelta concreteValueLower
  have hAT := mul_le_mul_of_nonneg_right hTm1 hA
  have hBT : B ≤ B * T := by nlinarith
  dsimp [A, B] at hAT hBT
  nlinarith

theorem concreteUnscaled_initial_gap {T n : Nat} (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 ≤ D) :
    ValueOn (unscaledDualDomain T n D)
        (unscaledObjective (by omega : 0 < n) concreteUnscaledParameters)
        (0 : UnscaledPrimal T) -
      sInf
        (ValueOn (unscaledDualDomain T n D)
          (unscaledObjective (by omega : 0 < n) concreteUnscaledParameters) ''
            unscaledPrimalDomain T) ≤ concreteDelta0 T := by
  let S := ValueOn (unscaledDualDomain T n D)
      (unscaledObjective (by omega : 0 < n) concreteUnscaledParameters) ''
        unscaledPrimalDomain T
  have hSne : S.Nonempty := by
    refine ⟨ValueOn (unscaledDualDomain T n D)
      (unscaledObjective (by omega : 0 < n) concreteUnscaledParameters) 0, ?_⟩
    exact ⟨0, zero_mem_unscaledPrimalDomain T, rfl⟩
  have hlower : concreteValueLower T ≤ sInf S := by
    apply le_csInf hSne
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact concreteUnscaledValue_lower hn hD x
  have hzero := concreteUnscaledValue_zero (T := T) (n := n)
    (by omega : 0 < n) hD
  change ValueOn (unscaledDualDomain T n D)
      (unscaledObjective (by omega : 0 < n) concreteUnscaledParameters) 0 -
      sInf S ≤ concreteDelta0 T
  rw [hzero]
  unfold concreteDelta0
  have habs : -|concreteValueLower T| ≤ concreteValueLower T := neg_abs_le _
  linarith

/-! ## Bounded-Lipschitz calculus for the global Hessian estimate -/

private structure BoundedLipschitz {E : Type*} [PseudoMetricSpace E]
    (f : E → ℝ) where
  B : ℝ
  B_nonneg : 0 ≤ B
  bound : ∀ x, |f x| ≤ B
  C : NNReal
  lipschitz : LipschitzWith C f

namespace BoundedLipschitz

variable {E F : Type*} [PseudoMetricSpace E] [PseudoMetricSpace F]
  {f g : E → ℝ}

def const (c : ℝ) : BoundedLipschitz (fun _ : E => c) := {
  B := |c|
  B_nonneg := abs_nonneg c
  bound := fun _ => le_rfl
  C := 0
  lipschitz := LipschitzWith.const c
}

def neg (hf : BoundedLipschitz f) :
    BoundedLipschitz (fun x => -f x) := {
  B := hf.B
  B_nonneg := hf.B_nonneg
  bound := by intro x; simpa using hf.bound x
  C := hf.C
  lipschitz := hf.lipschitz.neg
}

def add (hf : BoundedLipschitz f) (hg : BoundedLipschitz g) :
    BoundedLipschitz (fun x => f x + g x) := {
  B := hf.B + hg.B
  B_nonneg := add_nonneg hf.B_nonneg hg.B_nonneg
  bound := by
    intro x
    exact (abs_add_le _ _).trans (add_le_add (hf.bound x) (hg.bound x))
  C := hf.C + hg.C
  lipschitz := hf.lipschitz.add hg.lipschitz
}

def sub (hf : BoundedLipschitz f) (hg : BoundedLipschitz g) :
    BoundedLipschitz (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

def smul (c : ℝ) (hf : BoundedLipschitz f) :
    BoundedLipschitz (fun x => c * f x) := {
  B := |c| * hf.B
  B_nonneg := mul_nonneg (abs_nonneg c) hf.B_nonneg
  bound := by
    intro x
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hf.bound x) (abs_nonneg c)
  C := Real.toNNReal |c| * hf.C
  lipschitz := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, show c * f x - c * f y = c * (f x - f y) by ring,
      abs_mul]
    have h := hf.lipschitz.dist_le_mul x y
    rw [Real.dist_eq] at h
    have hc : (↑(Real.toNNReal |c|) : ℝ) = |c| :=
      Real.coe_toNNReal |c| (abs_nonneg c)
    rw [NNReal.coe_mul, hc]
    simpa only [mul_assoc] using
      (mul_le_mul_of_nonneg_left h (abs_nonneg c))
}

def mul (hf : BoundedLipschitz f) (hg : BoundedLipschitz g) :
    BoundedLipschitz (fun x => f x * g x) := by
  let C : ℝ := hf.B * hg.C + hg.B * hf.C
  have hC : 0 ≤ C := by
    exact add_nonneg
      (mul_nonneg hf.B_nonneg (NNReal.coe_nonneg hg.C))
      (mul_nonneg hg.B_nonneg (NNReal.coe_nonneg hf.C))
  refine {
    B := hf.B * hg.B
    B_nonneg := mul_nonneg hf.B_nonneg hg.B_nonneg
    bound := ?_
    C := ⟨C, hC⟩
    lipschitz := ?_
  }
  · intro x
    rw [abs_mul]
    exact mul_le_mul (hf.bound x) (hg.bound x) (abs_nonneg _) hf.B_nonneg
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq, show f x * g x - f y * g y =
      f x * (g x - g y) + g y * (f x - f y) by ring]
    calc
      |f x * (g x - g y) + g y * (f x - f y)| ≤
          |f x| * |g x - g y| + |g y| * |f x - f y| := by
        simpa only [abs_mul] using abs_add_le
          (f x * (g x - g y)) (g y * (f x - f y))
      _ ≤
          hf.B * (hg.C * dist x y) + hg.B * (hf.C * dist x y) := by
        exact add_le_add
          (mul_le_mul (hf.bound x)
            (by simpa [Real.dist_eq] using hg.lipschitz.dist_le_mul x y)
            (abs_nonneg _) hf.B_nonneg)
          (mul_le_mul (hg.bound y)
            (by simpa [Real.dist_eq] using hf.lipschitz.dist_le_mul x y)
            (abs_nonneg _) hg.B_nonneg)
      _ = C * dist x y := by dsimp [C]; ring

def comp (hf : BoundedLipschitz f) {u : F → E} {K : NNReal}
    (hu : LipschitzWith K u) : BoundedLipschitz (fun x => f (u x)) := {
  B := hf.B
  B_nonneg := hf.B_nonneg
  bound := fun x => hf.bound (u x)
  C := hf.C * K
  lipschitz := hf.lipschitz.comp hu
}

end BoundedLipschitz

private def realBL_of_deriv_bounds (f f' : ℝ → ℝ) (B C : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hval : ∀ t, |f t| ≤ B)
    (hderiv : ∀ t, HasDerivAt f (f' t) t) (hprime : ∀ t, |f' t| ≤ C) :
    BoundedLipschitz f := by
  refine {
    B := B
    B_nonneg := hB
    bound := hval
    C := ⟨C, hC⟩
    lipschitz := ?_
  }
  apply lipschitzWith_of_nnnorm_deriv_le
  · intro t
    exact (hderiv t).differentiableAt
  · intro t
    rw [(hderiv t).deriv]
    exact_mod_cast hprime t

private def psi1DerivBL : BoundedLipschitz Psi1Deriv :=
  realBL_of_deriv_bounds Psi1Deriv Psi1Second 24 432 (by norm_num) (by norm_num)
    abs_Psi1Deriv_le_twentyFour hasDerivAt_Psi1Deriv
    abs_Psi1Second_le_fourHundredThirtyTwo

private def psi2BL : BoundedLipschitz Psi2 :=
  realBL_of_deriv_bounds Psi2 Psi2Deriv (Real.exp 1) 24 (Real.exp_pos 1).le
    (by norm_num) (fun t ↦ by rw [abs_of_nonneg (Psi2_nonneg t)]; exact Psi2_le_exp_one t)
    hasDerivAt_Psi2 abs_Psi2Deriv_le_twentyFour

private def psi2DerivBL : BoundedLipschitz Psi2Deriv :=
  realBL_of_deriv_bounds Psi2Deriv Psi2Second 24 432 (by norm_num) (by norm_num)
    abs_Psi2Deriv_le_twentyFour hasDerivAt_Psi2Deriv
    abs_Psi2Second_le_fourHundredThirtyTwo

private def concretePi2BL : BoundedLipschitz (pi2 concreteSpatial.P0) :=
  realBL_of_deriv_bounds (pi2 concreteSpatial.P0) (pi2Deriv concreteSpatial.P0)
    (concreteSpatial.P0 + 5 / 2) 1 (by linarith [concreteSpatial.P0_gt_one])
    (by norm_num)
    (fun t ↦ pi2_abs_le concreteSpatial.P0_gt_one)
    (hasDerivAt_pi2 concreteSpatial.P0)
    (fun t ↦ by
      have h := pi2_deriv_mem_unitInterval concreteSpatial.P0 t
      rw [deriv_pi2] at h
      rw [abs_of_nonneg h.1]
      exact h.2)

private noncomputable def concretePi2SecondBound : ℝ :=
  Classical.choose (pi2Second_bounded concreteSpatial.P0_gt_one)

private theorem concretePi2SecondBound_spec :
    0 ≤ concretePi2SecondBound ∧
      ∀ t, |pi2Second concreteSpatial.P0 t| ≤ concretePi2SecondBound :=
  Classical.choose_spec (pi2Second_bounded concreteSpatial.P0_gt_one)

private noncomputable def concretePi2DerivBL :
    BoundedLipschitz (pi2Deriv concreteSpatial.P0) :=
  realBL_of_deriv_bounds (pi2Deriv concreteSpatial.P0)
    (pi2Second concreteSpatial.P0) 1 concretePi2SecondBound (by norm_num)
    concretePi2SecondBound_spec.1
    (fun t ↦ by
      have h := pi2_deriv_mem_unitInterval concreteSpatial.P0 t
      rw [deriv_pi2] at h
      rw [abs_of_nonneg h.1]
      exact h.2)
    (fun _ ↦ hasDerivAt_pi2Deriv concreteSpatial.P0_gt_one)
    concretePi2SecondBound_spec.2

private def concretePi1BL : BoundedLipschitz
    (pi1 concreteGateThreshold.deltaS concreteSpatial.P0) :=
  realBL_of_deriv_bounds
    (pi1 concreteGateThreshold.deltaS concreteSpatial.P0)
    (pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0)
    concreteGateThreshold.Bs 1 (by linarith [concreteGateThreshold.Bs_gt_three])
    (by norm_num)
    concretePi1_abs_le_Bs
    (fun _ ↦ hasDerivAt_pi1 concreteGateThreshold.deltaS_pos
      concreteSpatial.P0_gt_one)
    (fun t ↦ by
      have h := pi1Deriv_mem_unitInterval concreteGateThreshold.deltaS
        concreteSpatial.P0 t
      rw [abs_of_nonneg h.1]
      exact h.2)

private noncomputable def concretePi1SecondBound : ℝ :=
  Classical.choose (pi1Second_bounded concreteGateThreshold.deltaS_pos
    concreteSpatial.P0_gt_one)

private theorem concretePi1SecondBound_spec :
    0 ≤ concretePi1SecondBound ∧ ∀ t,
      |pi1Second concreteGateThreshold.deltaS concreteSpatial.P0 t| ≤
        concretePi1SecondBound :=
  Classical.choose_spec (pi1Second_bounded concreteGateThreshold.deltaS_pos
    concreteSpatial.P0_gt_one)

private noncomputable def concretePi1DerivBL : BoundedLipschitz
    (pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0) :=
  realBL_of_deriv_bounds
    (pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0)
    (pi1Second concreteGateThreshold.deltaS concreteSpatial.P0) 1
    concretePi1SecondBound (by norm_num) concretePi1SecondBound_spec.1
    (fun t ↦ by
      have h := pi1Deriv_mem_unitInterval concreteGateThreshold.deltaS
        concreteSpatial.P0 t
      rw [abs_of_nonneg h.1]
      exact h.2)
    (fun _ ↦ hasDerivAt_pi1Deriv concreteGateThreshold.deltaS_pos
      concreteSpatial.P0_gt_one) concretePi1SecondBound_spec.2

private def concreteLambdaBL : BoundedLipschitz (Lambda2 concreteTheta) :=
  realBL_of_deriv_bounds (Lambda2 concreteTheta) (deriv (Lambda2 concreteTheta))
    1 concreteLambdaDerivBound (by norm_num) concreteLambdaDerivBound_nonneg
    (fun t ↦ by
      have h := Lambda2_mem_unitInterval concreteTheta t
      rw [abs_of_nonneg h.1]
      exact h.2)
    (fun t ↦ ((@Lambda2_contDiff concreteTheta 1).differentiable
      (by norm_num)).differentiableAt.hasDerivAt)
    deriv_Lambda2_concrete_bound

private noncomputable def concreteLambdaC1 : ℝ :=
  Classical.choose (Lambda2_iteratedDeriv_bounded concreteTheta_pos 1)

private theorem concreteLambdaC1_spec : 0 ≤ concreteLambdaC1 ∧
    ∀ t, |deriv (Lambda2 concreteTheta) t| ≤ concreteLambdaC1 := by
  have h := Classical.choose_spec
    (Lambda2_iteratedDeriv_bounded concreteTheta_pos 1)
  unfold concreteLambdaC1
  refine ⟨h.1, ?_⟩
  intro t
  simpa using h.2 t

private noncomputable def concreteLambdaC2 : ℝ :=
  Classical.choose (Lambda2_iteratedDeriv_bounded concreteTheta_pos 2)

private theorem concreteLambdaC2_spec : 0 ≤ concreteLambdaC2 ∧
    ∀ t, |iteratedDeriv 2 (Lambda2 concreteTheta) t| ≤ concreteLambdaC2 :=
  Classical.choose_spec (Lambda2_iteratedDeriv_bounded concreteTheta_pos 2)

private noncomputable def concreteLambdaDerivBL :
    BoundedLipschitz (deriv (Lambda2 concreteTheta)) := by
  apply realBL_of_deriv_bounds (deriv (Lambda2 concreteTheta))
    (iteratedDeriv 2 (Lambda2 concreteTheta)) concreteLambdaC1 concreteLambdaC2
    concreteLambdaC1_spec.1 concreteLambdaC2_spec.1 concreteLambdaC1_spec.2
  · intro t
    have hdiff : Differentiable ℝ (iteratedDeriv 1 (Lambda2 concreteTheta)) :=
      (@Lambda2_contDiff concreteTheta 3).differentiable_iteratedDeriv 1 (by norm_num)
    have h := (hdiff t).hasDerivAt
    simpa [iteratedDeriv_succ] using h
  · exact concreteLambdaC2_spec.2

private noncomputable def concreteSigma1SecondBound : ℝ :=
  Classical.choose (Sigma1Second_bounded concreteTheta_pos)

private theorem concreteSigma1SecondBound_spec : 0 ≤ concreteSigma1SecondBound ∧
    ∀ t, |Sigma1Second concreteTheta t| ≤ concreteSigma1SecondBound :=
  Classical.choose_spec (Sigma1Second_bounded concreteTheta_pos)

private noncomputable def concreteSigma1DerivBL :
    BoundedLipschitz (Sigma1Deriv concreteTheta) :=
  realBL_of_deriv_bounds (Sigma1Deriv concreteTheta)
    (Sigma1Second concreteTheta) 1 concreteSigma1SecondBound (by norm_num)
    concreteSigma1SecondBound_spec.1 abs_Sigma1Deriv_le_one
    (fun _ ↦ hasDerivAt_Sigma1Deriv _ _ ) concreteSigma1SecondBound_spec.2

private noncomputable def concreteSigma2SecondBound : ℝ :=
  Classical.choose (Sigma2Second_bounded concreteUnscaledParameters.tauS_pos)

private theorem concreteSigma2SecondBound_spec : 0 ≤ concreteSigma2SecondBound ∧
    ∀ t, |Sigma2Second concreteUnscaledParameters.tauS t| ≤
      concreteSigma2SecondBound :=
  Classical.choose_spec (Sigma2Second_bounded concreteUnscaledParameters.tauS_pos)

private noncomputable def concreteSigma2DerivBL :
    BoundedLipschitz (Sigma2Deriv concreteUnscaledParameters.tauS) :=
  realBL_of_deriv_bounds (Sigma2Deriv concreteUnscaledParameters.tauS)
    (Sigma2Second concreteUnscaledParameters.tauS) 1 concreteSigma2SecondBound
    (by norm_num) concreteSigma2SecondBound_spec.1
    (abs_Sigma2Deriv_le_one concreteUnscaledParameters.tauS)
    (fun _ ↦ hasDerivAt_Sigma2Deriv _ _) concreteSigma2SecondBound_spec.2

private structure GloballyLipschitz {E : Type*} [PseudoMetricSpace E]
    (f : E → ℝ) where
  C : NNReal
  lipschitz : LipschitzWith C f

namespace GloballyLipschitz

variable {E : Type*} [PseudoMetricSpace E] {f g : E → ℝ}

def ofBL (hf : BoundedLipschitz f) : GloballyLipschitz f :=
  ⟨hf.C, hf.lipschitz⟩

def const (c : ℝ) : GloballyLipschitz (fun _ : E => c) :=
  ⟨0, LipschitzWith.const c⟩

def add (hf : GloballyLipschitz f) (hg : GloballyLipschitz g) :
    GloballyLipschitz (fun x => f x + g x) :=
  ⟨hf.C + hg.C, hf.lipschitz.add hg.lipschitz⟩

def neg (hf : GloballyLipschitz f) :
    GloballyLipschitz (fun x => -f x) :=
  ⟨hf.C, hf.lipschitz.neg⟩

def sub (hf : GloballyLipschitz f) (hg : GloballyLipschitz g) :
    GloballyLipschitz (fun x => f x - g x) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

def smul (c : ℝ) (hf : GloballyLipschitz f) :
    GloballyLipschitz (fun x => c * f x) := by
  refine ⟨Real.toNNReal |c| * hf.C, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, show c * f x - c * f y = c * (f x - f y) by ring,
    abs_mul]
  have h := hf.lipschitz.dist_le_mul x y
  rw [Real.dist_eq] at h
  have hc : (↑(Real.toNNReal |c|) : ℝ) = |c| :=
    Real.coe_toNNReal |c| (abs_nonneg c)
  rw [NNReal.coe_mul, hc]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (abs_nonneg c)

def eval {ι : Type*} [Fintype ι] (i : ι) :
    GloballyLipschitz (fun q : ι → ℝ => q i) :=
  ⟨1, LipschitzWith.eval i⟩

end GloballyLipschitz

private noncomputable def concreteSerializedCurrentStateLip {T n : Nat}
    (i : Fin (T - 1)) : GloballyLipschitz
      (fun q : SerializedSpace T n => serializedCurrentState q i) := by
  unfold serializedCurrentState
  split
  · exact GloballyLipschitz.const 2
  · exact GloballyLipschitz.eval _

private noncomputable def concreteSerializedClippedCurrentBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n =>
        serializedClippedCurrent concreteUnscaledParameters q i) := by
  have h := concretePi1BL.comp (concreteSerializedCurrentStateLip (n := n) i).lipschitz
  simpa [serializedClippedCurrent, concreteUnscaledParameters,
    concreteRadialTransition, assembleRadialTransition] using h

private noncomputable def concreteSerializedClippedNextBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n =>
        serializedClippedNext concreteUnscaledParameters q i) := by
  have h := concretePi1BL.comp
    (GloballyLipschitz.eval (serializedStateIndex (n := n) i)).lipschitz
  simpa [serializedClippedNext, serializedState, concreteUnscaledParameters,
    concreteRadialTransition, assembleRadialTransition] using h

private noncomputable def concreteSerializedClipDerivBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => pi1Deriv concreteUnscaledParameters.delta
        concreteUnscaledParameters.P0 (serializedState q i)) := by
  have h := concretePi1DerivBL.comp
    (GloballyLipschitz.eval (serializedStateIndex (n := n) i)).lipschitz
  simpa [serializedState, concreteUnscaledParameters, concreteRadialTransition,
    assembleRadialTransition] using h

private noncomputable def concreteSerializedPi2ABL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => pi2 concreteUnscaledParameters.P0
        (serializedA q i)) := by
  have h := concretePi2BL.comp
    (GloballyLipschitz.eval (serializedAIndex (n := n) i)).lipschitz
  simpa [serializedA, concreteUnscaledParameters, concreteRadialTransition,
    assembleRadialTransition] using h

private noncomputable def concreteSerializedPi2DerivABL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => pi2Deriv concreteUnscaledParameters.P0
        (serializedA q i)) := by
  have h := concretePi2DerivBL.comp
    (GloballyLipschitz.eval (serializedAIndex (n := n) i)).lipschitz
  simpa [serializedA, concreteUnscaledParameters, concreteRadialTransition,
    assembleRadialTransition] using h

private noncomputable def concreteSerializedPsi2CurrentBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => Psi2
        (serializedClippedCurrent concreteUnscaledParameters q i)) :=
  psi2BL.comp (concreteSerializedClippedCurrentBL (n := n) i).lipschitz

private noncomputable def concreteSerializedPsi2NextBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => Psi2
        (serializedClippedNext concreteUnscaledParameters q i)) :=
  psi2BL.comp (concreteSerializedClippedNextBL (n := n) i).lipschitz

private noncomputable def concreteSerializedPsi2DerivNextBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => Psi2Deriv
        (serializedClippedNext concreteUnscaledParameters q i)) :=
  psi2DerivBL.comp (concreteSerializedClippedNextBL (n := n) i).lipschitz

private noncomputable def concreteSigma1Pi1BL : BoundedLipschitz
    (fun t ↦ Sigma1 concreteTheta
      (pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t)) := by
  apply realBL_of_deriv_bounds _
    (fun t ↦ Sigma1Deriv concreteTheta
      (pi1 concreteGateThreshold.deltaS concreteSpatial.P0 t) *
        pi1Deriv concreteGateThreshold.deltaS concreteSpatial.P0 t)
    concreteSigmaBound 1 concreteSigmaBound_nonneg (by norm_num)
  · intro t
    have hm := concretePi1_mem t
    rw [abs_of_nonneg (Sigma1_nonneg concreteTheta_pos _)]
    exact concreteSigma1_le _ hm
  · intro t
    exact (hasDerivAt_Sigma1 concreteTheta _).comp t
      (hasDerivAt_pi1 concreteGateThreshold.deltaS_pos
        concreteSpatial.P0_gt_one)
  · intro t
    rw [abs_mul]
    exact mul_le_one₀ (abs_Sigma1Deriv_le_one _) (abs_nonneg _) (by
        have h := pi1Deriv_mem_unitInterval concreteGateThreshold.deltaS
          concreteSpatial.P0 t
        rw [abs_of_nonneg h.1]
        exact h.2)

private noncomputable def concreteSerializedSigma1CurrentBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => Sigma1 concreteUnscaledParameters.theta
        (serializedClippedCurrent concreteUnscaledParameters q i)) := by
  have h := concreteSigma1Pi1BL.comp
    (concreteSerializedCurrentStateLip (n := n) i).lipschitz
  simpa [serializedClippedCurrent, concreteUnscaledParameters,
    concreteRadialTransition, assembleRadialTransition] using h

private noncomputable def concreteSerializedSigma1DerivNextBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => Sigma1Deriv concreteUnscaledParameters.theta
        (serializedClippedNext concreteUnscaledParameters q i)) := by
  have h := concreteSigma1DerivBL.comp
    (concreteSerializedClippedNextBL (n := n) i).lipschitz
  simpa [concreteUnscaledParameters] using h

private noncomputable def concreteSerializedPsi1DerivNextBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => Psi1Deriv
        (serializedClippedNext concreteUnscaledParameters q i)) :=
  psi1DerivBL.comp (concreteSerializedClippedNextBL (n := n) i).lipschitz

private noncomputable def concreteSerializedLambdaNextBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => Lambda2 concreteUnscaledParameters.theta
        (serializedClippedNext concreteUnscaledParameters q i)) := by
  have h := concreteLambdaBL.comp
    (concreteSerializedClippedNextBL (n := n) i).lipschitz
  simpa [concreteUnscaledParameters] using h

private noncomputable def concreteSerializedLambdaDerivNextBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => deriv (Lambda2 concreteUnscaledParameters.theta)
        (serializedClippedNext concreteUnscaledParameters q i)) := by
  have h := concreteLambdaDerivBL.comp
    (concreteSerializedClippedNextBL (n := n) i).lipschitz
  simpa [concreteUnscaledParameters] using h

private noncomputable def concreteSerializedPsi2BBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => Psi2 (serializedB q i)) := by
  exact psi2BL.comp
    (GloballyLipschitz.eval (serializedBIndex (n := n) i)).lipschitz

private noncomputable def concreteSerializedPsi2DerivBBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => Psi2Deriv (serializedB q i)) := by
  exact psi2DerivBL.comp
    (GloballyLipschitz.eval (serializedBIndex (n := n) i)).lipschitz

private noncomputable def concreteSerializedExitRelayNextBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => exitRelay concreteUnscaledParameters.theta
        (serializedClippedNext concreteUnscaledParameters q i)) := by
  have h := (concreteSerializedClippedNextBL (n := n) i).mul
    (concreteSerializedLambdaNextBL (n := n) i)
  simpa [exitRelay] using h

private noncomputable def concreteSerializedExitRelayDerivNextBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => exitRelayDeriv concreteUnscaledParameters.theta
        (serializedClippedNext concreteUnscaledParameters q i)) := by
  have h := (concreteSerializedLambdaNextBL (n := n) i).add
    ((concreteSerializedClippedNextBL (n := n) i).mul
      (concreteSerializedLambdaDerivNextBL (n := n) i))
  simpa [exitRelayDeriv] using h

private noncomputable def concreteEntranceGradABL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => entrancePulseDerivA
        concreteUnscaledParameters.alpha concreteUnscaledParameters.theta
        concreteUnscaledParameters.P0
        (serializedClippedCurrent concreteUnscaledParameters q i)
        (serializedClippedNext concreteUnscaledParameters q i) (serializedA q i)) := by
  have h := ((concreteSerializedPsi2CurrentBL (n := n) i).mul
    (concreteSerializedLambdaNextBL (n := n) i)).mul
      (concreteSerializedPi2DerivABL (n := n) i)
  convert h.smul (-concreteUnscaledParameters.alpha) using 1
  funext q
  unfold entrancePulseDerivA
  ring

private noncomputable def concreteExitGradBBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => exitPulseDerivB
        concreteUnscaledParameters.beta concreteUnscaledParameters.theta
        (serializedClippedCurrent concreteUnscaledParameters q i) (serializedB q i)
        (serializedClippedNext concreteUnscaledParameters q i)) := by
  have h := ((concreteSerializedPsi2CurrentBL (n := n) i).mul
    (concreteSerializedPsi2DerivBBL (n := n) i)).mul
      (concreteSerializedExitRelayNextBL (n := n) i)
  convert h.smul (-concreteUnscaledParameters.beta) using 1
  funext q
  unfold exitPulseDerivB
  ring

private noncomputable def concreteExitGradNextBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => exitPulseDerivNext
        concreteUnscaledParameters.beta concreteUnscaledParameters.theta
        (serializedClippedCurrent concreteUnscaledParameters q i) (serializedB q i)
        (serializedClippedNext concreteUnscaledParameters q i)) := by
  have h := ((concreteSerializedPsi2CurrentBL (n := n) i).mul
    (concreteSerializedPsi2BBL (n := n) i)).mul
      (concreteSerializedExitRelayDerivNextBL (n := n) i)
  convert h.smul (-concreteUnscaledParameters.beta) using 1
  funext q
  unfold exitPulseDerivNext
  ring

private noncomputable def concreteSerializedSigma2DerivRawBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n => Sigma2Deriv concreteUnscaledParameters.tauS
        (serializedState q i)) := by
  have h := concreteSigma2DerivBL.comp
    (GloballyLipschitz.eval (serializedStateIndex (n := n) i)).lipschitz
  simpa [serializedState] using h

private noncomputable def concreteNextStateContributionBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n =>
        serializedNextStateContribution concreteUnscaledParameters q i) := by
  unfold serializedNextStateContribution
  split
  next hidx =>
    let j : Fin (T - 1) := ⟨i.val + 1, hidx⟩
    let h1 := (((concreteSerializedPsi2NextBL (n := n) j).mul
      (concreteSerializedSigma1DerivNextBL (n := n) i)).mul
        (concreteSerializedClipDerivBL (n := n) i)).smul
          concreteUnscaledParameters.mu
    let h2 := ((((concreteSerializedPsi2DerivNextBL (n := n) i).mul
      (concreteSerializedClipDerivBL (n := n) i)).mul
        (concreteSerializedLambdaNextBL (n := n) j)).mul
          (concreteSerializedPi2ABL (n := n) j)).smul
            concreteUnscaledParameters.alpha
    let h3 := ((((concreteSerializedPsi2DerivNextBL (n := n) i).mul
      (concreteSerializedClipDerivBL (n := n) i)).mul
        (concreteSerializedPsi2BBL (n := n) j)).mul
          (concreteSerializedExitRelayNextBL (n := n) j)).smul
            concreteUnscaledParameters.beta
    convert h1.sub h2 |>.sub h3 using 1
    funext q
    dsimp [h1, h2, h3, j]
    ring
  · exact BoundedLipschitz.const 0

private noncomputable def concreteSerializedGradStateBL {T n : Nat}
    (i : Fin (T - 1)) : BoundedLipschitz
      (fun q : SerializedSpace T n =>
        serializedGradState concreteUnscaledParameters q i) := by
  let h1 := ((concreteSerializedPsi1DerivNextBL (n := n) i).mul
    (concreteSerializedClipDerivBL (n := n) i)).smul
      (-concreteUnscaledParameters.eta)
  let h2 := concreteSerializedSigma2DerivRawBL (n := n) i
  let h3 := (((concreteSerializedPsi2DerivNextBL (n := n) i).mul
    (concreteSerializedClipDerivBL (n := n) i)).mul
      (concreteSerializedSigma1CurrentBL (n := n) i)).smul
        concreteUnscaledParameters.mu
  let h4 := ((((concreteSerializedPsi2CurrentBL (n := n) i).mul
    (concreteSerializedLambdaDerivNextBL (n := n) i)).mul
      (concreteSerializedClipDerivBL (n := n) i)).mul
        (concreteSerializedPi2ABL (n := n) i)).smul
          concreteUnscaledParameters.alpha
  let h5 := (concreteExitGradNextBL (n := n) i).mul
    (concreteSerializedClipDerivBL (n := n) i)
  let h6 := concreteNextStateContributionBL (n := n) i
  convert (((h1.add h2).add h3).sub h4).add h5 |>.add h6 using 1
  funext q
  unfold serializedGradState
  ring

/-! ### A fixed four-coordinate prototype for every nonlinear chain block -/

abbrev LocalGateSpace := EVec 4

private abbrev localGateBlock0 : Fin (3 - 1) := ⟨0, by omega⟩
private abbrev localGateBlock1 : Fin (3 - 1) := ⟨1, by omega⟩

def localGateEmbed (z : LocalGateSpace) : SerializedSpace 3 1 := fun j =>
  if j = serializedAIndex (n := 1) localGateBlock1 then z ⟨0, by omega⟩
  else if j = serializedBIndex (n := 1) localGateBlock1 then z ⟨1, by omega⟩
  else if j = serializedStateIndex (n := 1) localGateBlock0 then z ⟨2, by omega⟩
  else if j = serializedStateIndex (n := 1) localGateBlock1 then z ⟨3, by omega⟩
  else 0

@[simp] theorem serializedA_localGateEmbed (z : LocalGateSpace) :
    serializedA (localGateEmbed z) localGateBlock1 = z ⟨0, by omega⟩ := by
  simp [serializedA, localGateEmbed, serializedAIndex, serializedBIndex,
    serializedStateIndex, localGateBlock0, localGateBlock1]

@[simp] theorem serializedB_localGateEmbed (z : LocalGateSpace) :
    serializedB (localGateEmbed z) localGateBlock1 = z ⟨1, by omega⟩ := by
  simp [serializedB, localGateEmbed, serializedAIndex, serializedBIndex,
    serializedStateIndex, localGateBlock0, localGateBlock1]

@[simp] theorem serializedState0_localGateEmbed (z : LocalGateSpace) :
    serializedState (localGateEmbed z) localGateBlock0 = z ⟨2, by omega⟩ := by
  simp [serializedState, localGateEmbed, serializedAIndex, serializedBIndex,
    serializedStateIndex, localGateBlock0, localGateBlock1]

@[simp] theorem serializedState1_localGateEmbed (z : LocalGateSpace) :
    serializedState (localGateEmbed z) localGateBlock1 = z ⟨3, by omega⟩ := by
  simp [serializedState, localGateEmbed, serializedAIndex, serializedBIndex,
    serializedStateIndex, localGateBlock0, localGateBlock1]

@[simp] theorem serializedCurrentState1_localGateEmbed (z : LocalGateSpace) :
    serializedCurrentState (localGateEmbed z) localGateBlock1 = z ⟨2, by omega⟩ := by
  unfold serializedCurrentState
  simp only [localGateBlock1, Fin.isValue, OfNat.ofNat_ne_zero, ↓reduceDIte]
  simpa [localGateBlock0] using serializedState0_localGateEmbed z

@[simp] private theorem serializedState_localGateEmbed_any (z : LocalGateSpace)
    (j : Fin (3 - 1)) :
    serializedState (localGateEmbed z) j =
      if j.val = 0 then z ⟨2, by omega⟩ else z ⟨3, by omega⟩ := by
  fin_cases j
  · simpa using serializedState0_localGateEmbed z
  · simpa using serializedState1_localGateEmbed z

@[simp] private theorem serializedCurrentState_localGateEmbed_any
    (z : LocalGateSpace) (j : Fin (3 - 1)) :
    serializedCurrentState (localGateEmbed z) j =
      if j.val = 0 then 2 else z ⟨2, by omega⟩ := by
  fin_cases j
  · simp [serializedCurrentState]
  · simpa using serializedCurrentState1_localGateEmbed z

@[simp] private theorem serializedA_localGateEmbed_any (z : LocalGateSpace)
    (j : Fin (3 - 1)) :
    serializedA (localGateEmbed z) j =
      if j.val = 0 then 0 else z ⟨0, by omega⟩ := by
  fin_cases j
  · simp [serializedA, localGateEmbed, serializedAIndex, serializedBIndex,
      serializedStateIndex, localGateBlock0, localGateBlock1]
  · simpa using serializedA_localGateEmbed z

@[simp] private theorem serializedB_localGateEmbed_any (z : LocalGateSpace)
    (j : Fin (3 - 1)) :
    serializedB (localGateEmbed z) j =
      if j.val = 0 then 0 else z ⟨1, by omega⟩ := by
  fin_cases j
  · simp [serializedB, localGateEmbed, serializedAIndex, serializedBIndex,
      serializedStateIndex, localGateBlock0, localGateBlock1]
  · simpa using serializedB_localGateEmbed z

private theorem localGateEmbed_lipschitz :
    LipschitzWith 1 localGateEmbed := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  apply (dist_pi_le_iff (by positivity)).2
  intro j
  simp only [localGateEmbed, one_mul]
  split
  · simpa using
      (LipschitzWith.eval (⟨0, by omega⟩ : Fin 4)).dist_le_mul z w
  · split
    · simpa using
        (LipschitzWith.eval (⟨1, by omega⟩ : Fin 4)).dist_le_mul z w
    · split
      · simpa using
          (LipschitzWith.eval (⟨2, by omega⟩ : Fin 4)).dist_le_mul z w
      · split
        · simpa using
            (LipschitzWith.eval (⟨3, by omega⟩ : Fin 4)).dist_le_mul z w
        · simp

def localGateA (z : LocalGateSpace) : ℝ :=
  entrancePulseDerivA concreteUnscaledParameters.alpha
    concreteUnscaledParameters.theta concreteUnscaledParameters.P0
    (serializedClippedCurrent concreteUnscaledParameters (localGateEmbed z)
      localGateBlock1)
    (serializedClippedNext concreteUnscaledParameters (localGateEmbed z)
      localGateBlock1)
    (serializedA (localGateEmbed z) localGateBlock1)

def localGateB (z : LocalGateSpace) : ℝ :=
  exitPulseDerivB concreteUnscaledParameters.beta
    concreteUnscaledParameters.theta
    (serializedClippedCurrent concreteUnscaledParameters (localGateEmbed z)
      localGateBlock1)
    (serializedB (localGateEmbed z) localGateBlock1)
    (serializedClippedNext concreteUnscaledParameters (localGateEmbed z)
      localGateBlock1)

def localGateCurrent (z : LocalGateSpace) : ℝ :=
  serializedNextStateContribution concreteUnscaledParameters
    (localGateEmbed z) localGateBlock0

def localGateNext (z : LocalGateSpace) : ℝ :=
  serializedGradState concreteUnscaledParameters
    (localGateEmbed z) localGateBlock1

def localGateGradient (z : LocalGateSpace) : LocalGateSpace := fun k =>
  if k.val = 0 then localGateA z
  else if k.val = 1 then localGateB z
  else if k.val = 2 then localGateCurrent z
  else localGateNext z

private noncomputable def localGateABL : BoundedLipschitz localGateA := by
  have h := (concreteEntranceGradABL (T := 3) (n := 1)
    localGateBlock1).comp localGateEmbed_lipschitz
  change BoundedLipschitz (fun z : LocalGateSpace =>
    entrancePulseDerivA concreteUnscaledParameters.alpha
      concreteUnscaledParameters.theta concreteUnscaledParameters.P0
      (serializedClippedCurrent concreteUnscaledParameters (localGateEmbed z)
        localGateBlock1)
      (serializedClippedNext concreteUnscaledParameters (localGateEmbed z)
        localGateBlock1)
      (serializedA (localGateEmbed z) localGateBlock1))
  exact h

private noncomputable def localGateBBL : BoundedLipschitz localGateB := by
  have h := (concreteExitGradBBL (T := 3) (n := 1)
    localGateBlock1).comp localGateEmbed_lipschitz
  change BoundedLipschitz (fun z : LocalGateSpace =>
    exitPulseDerivB concreteUnscaledParameters.beta
      concreteUnscaledParameters.theta
      (serializedClippedCurrent concreteUnscaledParameters (localGateEmbed z)
        localGateBlock1)
      (serializedB (localGateEmbed z) localGateBlock1)
      (serializedClippedNext concreteUnscaledParameters (localGateEmbed z)
        localGateBlock1))
  exact h

private noncomputable def localGateCurrentBL :
    BoundedLipschitz localGateCurrent := by
  have h := (concreteNextStateContributionBL (T := 3) (n := 1)
    localGateBlock0).comp localGateEmbed_lipschitz
  change BoundedLipschitz (fun z : LocalGateSpace =>
    serializedNextStateContribution concreteUnscaledParameters
      (localGateEmbed z) localGateBlock0)
  exact h

private noncomputable def localGateNextBL : BoundedLipschitz localGateNext := by
  have h := (concreteSerializedGradStateBL (T := 3) (n := 1)
    localGateBlock1).comp localGateEmbed_lipschitz
  change BoundedLipschitz (fun z : LocalGateSpace =>
    serializedGradState concreteUnscaledParameters
      (localGateEmbed z) localGateBlock1)
  exact h

noncomputable def concreteLocalGateC : ℝ :=
  (localGateABL.C : ℝ) + localGateBBL.C + localGateCurrentBL.C + localGateNextBL.C

theorem concreteLocalGateC_nonneg : 0 ≤ concreteLocalGateC := by
  unfold concreteLocalGateC
  positivity

private theorem norm_le_sqrt_vecSq_local {m : Nat} (x : EVec m) :
    ‖x‖ ≤ Real.sqrt (vecSq x) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  have hi : (x i) ^ 2 ≤ vecSq x := by
    unfold vecSq NCPLVerification.vecSq
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j))
      (Finset.mem_univ i)
  have hs0 := Real.sqrt_nonneg (vecSq x)
  have hs2 := Real.sq_sqrt (vecSq_nonneg x)
  have habs : |x i| ≤ Real.sqrt (vecSq x) := by
    nlinarith [sq_abs (x i), abs_nonneg (x i)]
  simpa only [Real.norm_eq_abs] using habs

private theorem localGateGradient_coord_bound (z w : LocalGateSpace)
    (k : Fin 4) :
    |localGateGradient z k - localGateGradient w k| ≤
      concreteLocalGateC * Real.sqrt (vecSq (z - w)) := by
  have hnorm := norm_le_sqrt_vecSq_local (z - w)
  have hA := localGateABL.lipschitz.dist_le_mul z w
  have hB := localGateBBL.lipschitz.dist_le_mul z w
  have hC := localGateCurrentBL.lipschitz.dist_le_mul z w
  have hN := localGateNextBL.lipschitz.dist_le_mul z w
  rw [Real.dist_eq] at hA hB hC hN
  have hCA : (localGateABL.C : ℝ) ≤ concreteLocalGateC := by
    unfold concreteLocalGateC
    nlinarith [NNReal.coe_nonneg localGateBBL.C,
      NNReal.coe_nonneg localGateCurrentBL.C, NNReal.coe_nonneg localGateNextBL.C]
  have hCB : (localGateBBL.C : ℝ) ≤ concreteLocalGateC := by
    unfold concreteLocalGateC
    nlinarith [NNReal.coe_nonneg localGateABL.C,
      NNReal.coe_nonneg localGateCurrentBL.C, NNReal.coe_nonneg localGateNextBL.C]
  have hCC : (localGateCurrentBL.C : ℝ) ≤ concreteLocalGateC := by
    unfold concreteLocalGateC
    nlinarith [NNReal.coe_nonneg localGateABL.C,
      NNReal.coe_nonneg localGateBBL.C, NNReal.coe_nonneg localGateNextBL.C]
  have hCN : (localGateNextBL.C : ℝ) ≤ concreteLocalGateC := by
    unfold concreteLocalGateC
    nlinarith [NNReal.coe_nonneg localGateABL.C,
      NNReal.coe_nonneg localGateBBL.C, NNReal.coe_nonneg localGateCurrentBL.C]
  rw [dist_eq_norm] at hA hB hC hN
  fin_cases k
  · simp only [localGateGradient, ↓reduceIte]
    exact hA.trans <| (mul_le_mul_of_nonneg_right hCA (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hnorm concreteLocalGateC_nonneg)
  · simp only [localGateGradient, ↓reduceIte]
    exact hB.trans <| (mul_le_mul_of_nonneg_right hCB (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hnorm concreteLocalGateC_nonneg)
  · simp only [localGateGradient, ↓reduceIte]
    exact hC.trans <| (mul_le_mul_of_nonneg_right hCC (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hnorm concreteLocalGateC_nonneg)
  · simp only [localGateGradient, ↓reduceIte]
    exact hN.trans <| (mul_le_mul_of_nonneg_right hCN (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hnorm concreteLocalGateC_nonneg)

/-- Euclidean squared bound for the fixed local nonlinear gradient. -/
theorem localGateGradient_vecSq_sub_le (z w : LocalGateSpace) :
    vecSq (localGateGradient z - localGateGradient w) ≤
      (2 * concreteLocalGateC) ^ 2 * vecSq (z - w) := by
  have hs : 0 ≤ vecSq (z - w) := vecSq_nonneg _
  have hroot := Real.sq_sqrt hs
  have hcoord : ∀ k : Fin 4,
      (localGateGradient z k - localGateGradient w k) ^ 2 ≤
        concreteLocalGateC ^ 2 * vecSq (z - w) := by
    intro k
    have hk := localGateGradient_coord_bound z w k
    have hleft : 0 ≤ |localGateGradient z k - localGateGradient w k| :=
      abs_nonneg _
    have hright : 0 ≤ concreteLocalGateC * Real.sqrt (vecSq (z - w)) :=
      mul_nonneg concreteLocalGateC_nonneg (Real.sqrt_nonneg _)
    have hsq := (sq_le_sq₀ hleft hright).2 hk
    rw [sq_abs, mul_pow, hroot] at hsq
    simpa only [Pi.sub_apply] using hsq
  calc
    vecSq (localGateGradient z - localGateGradient w) ≤
        ∑ _k : Fin 4, concreteLocalGateC ^ 2 * vecSq (z - w) := by
      unfold vecSq NCPLVerification.vecSq
      exact Finset.sum_le_sum fun k _ => hcoord k
    _ = 4 * (concreteLocalGateC ^ 2 * vecSq (z - w)) := by simp
    _ = (2 * concreteLocalGateC) ^ 2 * vecSq (z - w) := by ring

/-- Euclidean energy in one contiguous serialized block. -/
def serializedBlockSq {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) : ℝ :=
  ∑ k : Fin (n + 3), q (finProdFinEquiv (i, k)) ^ 2

theorem vecSq_eq_sum_serializedBlockSq {T n : Nat}
    (q : SerializedSpace T n) :
    vecSq q = ∑ i : Fin (T - 1), serializedBlockSq q i := by
  unfold vecSq NCPLVerification.vecSq serializedBlockSq
  rw [← Equiv.sum_comp finProdFinEquiv]
  rw [Fintype.sum_prod_type]

def localGateInput {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) : LocalGateSpace := fun k =>
  if k.val = 0 then serializedA q i
  else if k.val = 1 then serializedB q i
  else if k.val = 2 then serializedCurrentState q i
  else serializedState q i

@[simp] theorem localGateInput_zero {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) :
    localGateInput q i ⟨0, by omega⟩ = serializedA q i := by
  simp [localGateInput]

@[simp] theorem localGateInput_one {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) :
    localGateInput q i ⟨1, by omega⟩ = serializedB q i := by
  simp [localGateInput]

@[simp] theorem localGateInput_two {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) :
    localGateInput q i ⟨2, by omega⟩ = serializedCurrentState q i := by
  simp [localGateInput]

@[simp] theorem localGateInput_three {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) :
    localGateInput q i ⟨3, by omega⟩ = serializedState q i := by
  simp [localGateInput]

def serializedBlockCurrentGrad {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) : ℝ :=
  concreteUnscaledParameters.mu *
      Psi2 (serializedClippedNext concreteUnscaledParameters q i) *
      Sigma1Deriv concreteUnscaledParameters.theta
        (serializedClippedCurrent concreteUnscaledParameters q i) *
      pi1Deriv concreteUnscaledParameters.delta concreteUnscaledParameters.P0
        (serializedCurrentState q i) -
    concreteUnscaledParameters.alpha *
      Psi2Deriv (serializedClippedCurrent concreteUnscaledParameters q i) *
      pi1Deriv concreteUnscaledParameters.delta concreteUnscaledParameters.P0
        (serializedCurrentState q i) *
      Lambda2 concreteUnscaledParameters.theta
        (serializedClippedNext concreteUnscaledParameters q i) *
      pi2 concreteUnscaledParameters.P0 (serializedA q i) -
    concreteUnscaledParameters.beta *
      Psi2Deriv (serializedClippedCurrent concreteUnscaledParameters q i) *
      pi1Deriv concreteUnscaledParameters.delta concreteUnscaledParameters.P0
        (serializedCurrentState q i) *
      Psi2 (serializedB q i) *
      exitRelay concreteUnscaledParameters.theta
        (serializedClippedNext concreteUnscaledParameters q i)

def serializedBlockNextGrad {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) : ℝ :=
  let raw := serializedState q i
  let cur := serializedClippedCurrent concreteUnscaledParameters q i
  let nxt := serializedClippedNext concreteUnscaledParameters q i
  let cd := pi1Deriv concreteUnscaledParameters.delta
    concreteUnscaledParameters.P0 raw;
  -concreteUnscaledParameters.eta * Psi1Deriv nxt * cd +
    Sigma2Deriv concreteUnscaledParameters.tauS raw +
    concreteUnscaledParameters.mu * Psi2Deriv nxt * cd *
      Sigma1 concreteUnscaledParameters.theta cur -
    concreteUnscaledParameters.alpha * Psi2 cur *
      deriv (Lambda2 concreteUnscaledParameters.theta) nxt * cd *
      pi2 concreteUnscaledParameters.P0 (serializedA q i) +
    exitPulseDerivNext concreteUnscaledParameters.beta
      concreteUnscaledParameters.theta cur (serializedB q i) nxt * cd

theorem localGateA_input {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) :
    localGateA (localGateInput q i) =
      entrancePulseDerivA concreteUnscaledParameters.alpha
        concreteUnscaledParameters.theta concreteUnscaledParameters.P0
        (serializedClippedCurrent concreteUnscaledParameters q i)
        (serializedClippedNext concreteUnscaledParameters q i)
        (serializedA q i) := by
  have hcur : serializedCurrentState (localGateEmbed (localGateInput q i))
      localGateBlock1 = serializedCurrentState q i := by
    rw [serializedCurrentState1_localGateEmbed, localGateInput_two]
  have hnxt : serializedState (localGateEmbed (localGateInput q i))
      localGateBlock1 = serializedState q i := by
    rw [serializedState1_localGateEmbed, localGateInput_three]
  have ha : serializedA (localGateEmbed (localGateInput q i))
      localGateBlock1 = serializedA q i := by
    rw [serializedA_localGateEmbed, localGateInput_zero]
  unfold localGateA serializedClippedCurrent serializedClippedNext
  rw [hcur, hnxt, ha]

theorem localGateB_input {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) :
    localGateB (localGateInput q i) =
      exitPulseDerivB concreteUnscaledParameters.beta
        concreteUnscaledParameters.theta
        (serializedClippedCurrent concreteUnscaledParameters q i)
      (serializedB q i)
      (serializedClippedNext concreteUnscaledParameters q i) := by
  have hcur : serializedCurrentState (localGateEmbed (localGateInput q i))
      localGateBlock1 = serializedCurrentState q i := by
    rw [serializedCurrentState1_localGateEmbed, localGateInput_two]
  have hnxt : serializedState (localGateEmbed (localGateInput q i))
      localGateBlock1 = serializedState q i := by
    rw [serializedState1_localGateEmbed, localGateInput_three]
  have hb : serializedB (localGateEmbed (localGateInput q i))
      localGateBlock1 = serializedB q i := by
    rw [serializedB_localGateEmbed, localGateInput_one]
  unfold localGateB serializedClippedCurrent serializedClippedNext
  rw [hcur, hnxt, hb]

theorem localGateCurrent_input {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) :
    localGateCurrent (localGateInput q i) = serializedBlockCurrentGrad q i := by
  unfold localGateCurrent serializedNextStateContribution
  simp only [localGateBlock0, Fin.isValue, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceLT, ↓reduceDIte]
  simp only [serializedClippedCurrent, serializedClippedNext,
    serializedState_localGateEmbed_any,
    serializedCurrentState_localGateEmbed_any,
    serializedA_localGateEmbed_any, serializedB_localGateEmbed_any]
  simp [localGateInput]
  unfold serializedBlockCurrentGrad serializedClippedCurrent serializedClippedNext
  ring

theorem localGateNext_input {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) :
    localGateNext (localGateInput q i) = serializedBlockNextGrad q i := by
  unfold localGateNext serializedGradState serializedNextStateContribution
  simp only [localGateBlock1, Fin.isValue, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceLT, ↓reduceDIte]
  simp only [serializedClippedCurrent, serializedClippedNext,
    serializedState_localGateEmbed_any,
    serializedCurrentState_localGateEmbed_any,
    serializedA_localGateEmbed_any, serializedB_localGateEmbed_any]
  simp [localGateInput]
  unfold serializedBlockNextGrad serializedClippedCurrent serializedClippedNext
  ring

private noncomputable def serializedInnerGradALip {T n : Nat} (hn : 0 < n)
    (i : Fin (T - 1)) : GloballyLipschitz
      (fun q : SerializedSpace T n =>
        innerGradA hn (innerC hn) (serializedDualBlock q i)) := by
  have h := (GloballyLipschitz.eval
    (serializedDualIndex i (innerFirst hn))).smul (innerScale n (innerC hn))
  simpa [innerGradA, serializedDualBlock, serializedY] using h

private noncomputable def serializedInnerGradBLip {T n : Nat} (hn : 0 < n)
    (i : Fin (T - 1)) : GloballyLipschitz
      (fun q : SerializedSpace T n =>
        innerGradB hn (innerC hn) (serializedDualBlock q i)) := by
  have h := (GloballyLipschitz.eval
    (serializedDualIndex i (innerLast hn))).smul
      (-(1 / 2 : ℝ) * innerScale n (innerC hn))
  simpa [innerGradB, serializedDualBlock, serializedY] using h

def serializedGradANonradial {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) : ℝ :=
  entrancePulseDerivA P.alpha P.theta P.P0
      (serializedClippedCurrent P q i) (serializedClippedNext P q i)
      (serializedA q i) +
    innerGradA hn (innerC hn) (serializedDualBlock q i) +
    2 * (innerC1 hn + P.gamma) * serializedA q i

def serializedGradBNonradial {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (q : SerializedSpace T n) (i : Fin (T - 1)) : ℝ :=
  innerGradB hn (innerC hn) (serializedDualBlock q i) +
    2 * (innerC2 hn + P.gamma) * serializedB q i +
    exitPulseDerivB P.beta P.theta (serializedClippedCurrent P q i)
      (serializedB q i) (serializedClippedNext P q i)

private noncomputable def concreteSerializedGradANonradialLip {T n : Nat}
    (hn : 0 < n) (i : Fin (T - 1)) : GloballyLipschitz
      (fun q : SerializedSpace T n =>
        serializedGradANonradial hn concreteUnscaledParameters q i) := by
  let h1 := GloballyLipschitz.ofBL (concreteEntranceGradABL (n := n) i)
  let h2 := serializedInnerGradALip hn i
  let h3 := (GloballyLipschitz.eval (serializedAIndex (n := n) i)).smul
    (2 * (innerC1 hn + concreteUnscaledParameters.gamma))
  convert (h1.add h2).add h3 using 1
  funext q
  unfold serializedGradANonradial
  unfold serializedA
  ring

private noncomputable def concreteSerializedGradBNonradialLip {T n : Nat}
    (hn : 0 < n) (i : Fin (T - 1)) : GloballyLipschitz
      (fun q : SerializedSpace T n =>
        serializedGradBNonradial hn concreteUnscaledParameters q i) := by
  let h1 := serializedInnerGradBLip hn i
  let h2 := (GloballyLipschitz.eval (serializedBIndex (n := n) i)).smul
    (2 * (innerC2 hn + concreteUnscaledParameters.gamma))
  let h3 := GloballyLipschitz.ofBL (concreteExitGradBBL (n := n) i)
  convert (h1.add h2).add h3 using 1
  funext q
  unfold serializedGradBNonradial
  unfold serializedB
  ring

private noncomputable def serializedRegularizedPathCoordLip {T n : Nat}
    (i : Fin (T - 1)) (k : Fin n) : GloballyLipschitz
      (fun q : SerializedSpace T n =>
        regularizedPathCoord (serializedDualBlock q i) k) := by
  let hself : GloballyLipschitz (fun q : SerializedSpace T n => serializedY q i k) := by
    simpa [serializedY] using
      (GloballyLipschitz.eval (serializedDualIndex i k))
  let hreg := hself.smul (pathRegularization n)
  unfold regularizedPathCoord pathLaplacianCoord
  split
  next hp =>
    let kp : Fin n := ⟨k.val - 1, by omega⟩
    let hprev : GloballyLipschitz
        (fun q : SerializedSpace T n => serializedY q i kp) := by
      simpa [serializedY] using
        (GloballyLipschitz.eval (serializedDualIndex i kp))
    split
    next hnxt =>
      let kn : Fin n := ⟨k.val + 1, hnxt⟩
      let hnext : GloballyLipschitz
          (fun q : SerializedSpace T n => serializedY q i kn) := by
        simpa [serializedY] using
          (GloballyLipschitz.eval (serializedDualIndex i kn))
      simpa [serializedDualBlock, add_zero, zero_add] using
        hreg.add ((hself.sub hprev).add (hself.sub hnext))
    · simpa [serializedDualBlock, add_zero, zero_add] using
        hreg.add (hself.sub hprev)
  · split
    next hnxt =>
      let kn : Fin n := ⟨k.val + 1, hnxt⟩
      let hnext : GloballyLipschitz
          (fun q : SerializedSpace T n => serializedY q i kn) := by
        simpa [serializedY] using
          (GloballyLipschitz.eval (serializedDualIndex i kn))
      simpa [serializedDualBlock, add_zero, zero_add] using
        hreg.add (hself.sub hnext)
    · simpa [serializedDualBlock, add_zero, zero_add] using hreg

private noncomputable def serializedInnerSourceLip {T n : Nat} (hn : 0 < n)
    (i : Fin (T - 1)) (k : Fin n) : GloballyLipschitz
      (fun q : SerializedSpace T n => innerSource hn
        (serializedA q i) (serializedB q i) k) := by
  classical
  let ha : GloballyLipschitz (fun q : SerializedSpace T n => serializedA q i) := by
    simpa [serializedA] using
      (GloballyLipschitz.eval (serializedAIndex (n := n) i))
  let hb : GloballyLipschitz (fun q : SerializedSpace T n => serializedB q i) := by
    simpa [serializedB] using
      (GloballyLipschitz.eval (serializedBIndex (n := n) i))
  by_cases hka : k = innerFirst hn
  · subst k
    by_cases hab : innerFirst hn = innerLast hn
    · have h := ha.sub (hb.smul (1 / 2))
      convert h using 1
      funext q
      simp [innerSource, Pi.single_apply, hab]
      ring
    · simpa [innerSource, Pi.single_apply, hab] using ha
  · by_cases hkb : k = innerLast hn
    · subst k
      have h := hb.smul (-(1 / 2 : ℝ))
      convert h using 1
      funext q
      simp [innerSource, Pi.single_apply, hka]
      ring
    · simpa [innerSource, Pi.single_apply, hka, hkb] using
        (GloballyLipschitz.const (E := SerializedSpace T n) 0)

private noncomputable def concreteSerializedGradYLip {T n : Nat} (hn : 0 < n)
    (i : Fin (T - 1)) (k : Fin n) : GloballyLipschitz
      (fun q : SerializedSpace T n =>
        serializedSaddleGradY hn concreteUnscaledParameters q i k) := by
  let h1 := serializedRegularizedPathCoordLip (T := T) i k
  let h2 := (serializedInnerSourceLip hn i k).smul (innerScale n (innerC hn))
  convert h1.sub h2 using 1
  funext q
  unfold serializedSaddleGradY innerSaddleGradW
  rfl

def serializedPulseDot {T n : Nat} (q h : SerializedSpace T n) : ℝ :=
  Finset.univ.sum fun i : Fin (T - 1) ↦
    serializedA q i * serializedA h i + serializedB q i * serializedB h i

def serializedLine {T n : Nat} (q h : SerializedSpace T n) (t : ℝ) :
    SerializedSpace T n := fun j ↦ q j + t * h j

private theorem hasDerivAt_serializedPulseSq_line {T n : Nat}
    (q h : SerializedSpace T n) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ serializedPulseSq (serializedLine q h s))
      (2 * serializedPulseDot (serializedLine q h t) h) t := by
  unfold serializedPulseSq serializedPulseDot serializedLine serializedA serializedB
  have hs : HasDerivAt
      (fun s : ℝ ↦ Finset.univ.sum fun i : Fin (T - 1) ↦
        (q (serializedAIndex (n := n) i) + s * h (serializedAIndex (n := n) i)) ^ 2 +
          (q (serializedBIndex (n := n) i) + s * h (serializedBIndex (n := n) i)) ^ 2)
      (Finset.univ.sum fun i : Fin (T - 1) ↦
        2 * ((q (serializedAIndex (n := n) i) + t * h (serializedAIndex (n := n) i)) *
          h (serializedAIndex (n := n) i) +
        (q (serializedBIndex (n := n) i) + t * h (serializedBIndex (n := n) i)) *
          h (serializedBIndex (n := n) i))) t := by
    apply HasDerivAt.fun_sum
    intro i _
    have ha : HasDerivAt
        (fun s : ℝ ↦ q (serializedAIndex (n := n) i) +
          s * h (serializedAIndex (n := n) i))
        (h (serializedAIndex (n := n) i)) t := by
      convert (hasDerivAt_const t (q (serializedAIndex (n := n) i))).add
          ((hasDerivAt_id t).mul_const (h (serializedAIndex (n := n) i))) using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      · funext s
        rfl
      · ring
    have hb : HasDerivAt
        (fun s : ℝ ↦ q (serializedBIndex (n := n) i) +
          s * h (serializedBIndex (n := n) i))
        (h (serializedBIndex (n := n) i)) t := by
      convert (hasDerivAt_const t (q (serializedBIndex (n := n) i))).add
          ((hasDerivAt_id t).mul_const (h (serializedBIndex (n := n) i))) using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      · funext s
        rfl
      · ring
    have hp := (ha.pow 2).add (hb.pow 2)
    exact hp.congr_deriv (by ring)
  convert hs using 1
  rw [Finset.mul_sum]

private theorem hasDerivAt_serializedRadialA_line {T n : Nat}
    (P : UnscaledParameters) (q h : SerializedSpace T n)
    (i : Fin (T - 1)) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ 2 * Sigma3Deriv P.P0 P.P1 P.K
        (serializedPulseSq (serializedLine q h s)) *
          serializedA (serializedLine q h s) i)
      (2 * Sigma3Deriv P.P0 P.P1 P.K
          (serializedPulseSq (serializedLine q h t)) * serializedA h i +
        4 * Sigma3Second P.P0 P.P1 P.K
          (serializedPulseSq (serializedLine q h t)) *
          serializedPulseDot (serializedLine q h t) h *
            serializedA (serializedLine q h t) i) t := by
  have hs := (hasDerivAt_Sigma3Deriv P.P0 P.P1 P.K
    (serializedPulseSq (serializedLine q h t))).comp t
      (hasDerivAt_serializedPulseSq_line q h t)
  have ha : HasDerivAt (fun s : ℝ ↦ serializedA (serializedLine q h s) i)
      (serializedA h i) t := by
    unfold serializedA serializedLine
    convert (hasDerivAt_const t (q (serializedAIndex (n := n) i))).add
        ((hasDerivAt_id t).mul_const (h (serializedAIndex (n := n) i))) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext s
      rfl
    · ring
  have hp := (hs.const_mul 2).mul ha
  apply hp.congr_deriv
  simp only [Function.comp_apply]
  ring

private theorem hasDerivAt_serializedRadialB_line {T n : Nat}
    (P : UnscaledParameters) (q h : SerializedSpace T n)
    (i : Fin (T - 1)) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ 2 * Sigma3Deriv P.P0 P.P1 P.K
        (serializedPulseSq (serializedLine q h s)) *
          serializedB (serializedLine q h s) i)
      (2 * Sigma3Deriv P.P0 P.P1 P.K
          (serializedPulseSq (serializedLine q h t)) * serializedB h i +
        4 * Sigma3Second P.P0 P.P1 P.K
          (serializedPulseSq (serializedLine q h t)) *
          serializedPulseDot (serializedLine q h t) h *
            serializedB (serializedLine q h t) i) t := by
  have hs := (hasDerivAt_Sigma3Deriv P.P0 P.P1 P.K
    (serializedPulseSq (serializedLine q h t))).comp t
      (hasDerivAt_serializedPulseSq_line q h t)
  have hb : HasDerivAt (fun s : ℝ ↦ serializedB (serializedLine q h s) i)
      (serializedB h i) t := by
    unfold serializedB serializedLine
    convert (hasDerivAt_const t (q (serializedBIndex (n := n) i))).add
        ((hasDerivAt_id t).mul_const (h (serializedBIndex (n := n) i))) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext s
      rfl
    · ring
  have hp := (hs.const_mul 2).mul hb
  apply hp.congr_deriv
  simp only [Function.comp_apply]
  ring

private theorem concreteP1_pos : 0 < concreteUnscaledParameters.P1 := by
  change 0 < concreteSpatial.P1
  exact lt_trans (lt_trans zero_lt_one concreteSpatial.P0_gt_one)
    concreteSpatial.P0_lt_P1

private theorem concreteP0_sq_lt_P1_sq :
    concreteUnscaledParameters.P0 ^ 2 < concreteUnscaledParameters.P1 ^ 2 := by
  have hd : 0 < concreteUnscaledParameters.P1 - concreteUnscaledParameters.P0 := by
    change 0 < concreteSpatial.P1 - concreteSpatial.P0
    linarith [concreteSpatial.P0_lt_P1]
  have hs : 0 < concreteUnscaledParameters.P1 + concreteUnscaledParameters.P0 := by
    have hp0 : 0 < concreteUnscaledParameters.P0 := by
      change 0 < concreteSpatial.P0
      linarith [concreteSpatial.P0_gt_one]
    exact add_pos concreteP1_pos hp0
  nlinarith

private theorem concreteK_nonneg : 0 ≤ concreteUnscaledParameters.K := by
  change 0 ≤ concreteSpatial.K
  linarith [concreteSpatial.K_gt, concreteCq_pos]

/-! ### A genuinely dimension-free Euclidean bound for the radial field -/

private noncomputable def concreteSigma3WeightedSecondBound : ℝ :=
  Classical.choose (Sigma3_weightedSecond_bounded
    (K := concreteUnscaledParameters.K) concreteP0_sq_lt_P1_sq)

private theorem concreteSigma3WeightedSecondBound_spec :
    0 ≤ concreteSigma3WeightedSecondBound ∧ ∀ r,
      |r * Sigma3Second concreteUnscaledParameters.P0
        concreteUnscaledParameters.P1 concreteUnscaledParameters.K r| ≤
          concreteSigma3WeightedSecondBound :=
  Classical.choose_spec (Sigma3_weightedSecond_bounded
    (K := concreteUnscaledParameters.K) concreteP0_sq_lt_P1_sq)

private theorem vecSq_add_le_two_local {d : Nat} (u v : EVec d) :
    vecSq (u + v) ≤ 2 * vecSq u + 2 * vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (u i - v i)]

/-- Squared Euclidean operator estimate for the literal radial Hessian.
The right-hand coefficient only involves the already fixed numerical
parameters, and in particular is independent of the ambient dimension. -/
private theorem concreteRadialHessianApply_vecSq_le {d : Nat}
    (p h : EVec d) :
    vecSq (radialHessianApply concreteUnscaledParameters.P0
      concreteUnscaledParameters.P1 concreteUnscaledParameters.K p h) ≤
      (8 * concreteUnscaledParameters.K ^ 2 +
        32 * concreteSigma3WeightedSecondBound ^ 2) * vecSq h := by
  let r := vecSq p
  let q := vecSq h
  let s := Sigma3Deriv concreteUnscaledParameters.P0
    concreteUnscaledParameters.P1 concreteUnscaledParameters.K r
  let t := Sigma3Second concreteUnscaledParameters.P0
    concreteUnscaledParameters.P1 concreteUnscaledParameters.K r
  let z := radialDot p h
  let u : EVec d := fun i => 2 * s * h i
  let v : EVec d := fun i => 4 * t * z * p i
  have hr : 0 ≤ r := vecSq_nonneg p
  have hq : 0 ≤ q := vecSq_nonneg h
  have hs := Sigma3Deriv_mem (P0 := concreteUnscaledParameters.P0)
    (P1 := concreteUnscaledParameters.P1) (r := r) concreteK_nonneg
  have hweighted : |r * t| ≤ concreteSigma3WeightedSecondBound :=
    concreteSigma3WeightedSecondBound_spec.2 r
  have hC : 0 ≤ concreteSigma3WeightedSecondBound :=
    concreteSigma3WeightedSecondBound_spec.1
  have hdot : z ^ 2 ≤ r * q := by
    simpa [z, r, q] using radialDot_sq_le p h
  have hweightedSq : (r * t) ^ 2 ≤ concreteSigma3WeightedSecondBound ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ (abs_nonneg (r * t)) hC).2 hweighted
  have hsecond : t ^ 2 * z ^ 2 * r ≤
      concreteSigma3WeightedSecondBound ^ 2 * q := by
    have h1 := mul_le_mul_of_nonneg_left hdot (sq_nonneg t)
    have h2 := mul_le_mul_of_nonneg_right h1 hr
    have h3 := mul_le_mul_of_nonneg_right hweightedSq hq
    nlinarith
  have hu : vecSq u = 4 * s ^ 2 * q := by
    unfold vecSq NCPLVerification.vecSq u q
    change (∑ i : Fin d, (2 * s * h i) ^ 2) =
      4 * s ^ 2 * ∑ i : Fin d, h i ^ 2
    calc
      (∑ i : Fin d, (2 * s * h i) ^ 2) =
          ∑ i : Fin d, 4 * s ^ 2 * h i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 4 * s ^ 2 * ∑ i : Fin d, h i ^ 2 :=
        (Finset.mul_sum _ _ _).symm
  have hv : vecSq v = 16 * t ^ 2 * z ^ 2 * r := by
    unfold vecSq NCPLVerification.vecSq v r
    change (∑ i : Fin d, (4 * t * z * p i) ^ 2) =
      (16 * t ^ 2 * z ^ 2) * ∑ i : Fin d, p i ^ 2
    calc
      (∑ i : Fin d, (4 * t * z * p i) ^ 2) =
          ∑ i : Fin d, (16 * t ^ 2 * z ^ 2) * p i ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = (16 * t ^ 2 * z ^ 2) * ∑ i : Fin d, p i ^ 2 :=
        (Finset.mul_sum _ _ _).symm
  have hsu : s ^ 2 ≤ concreteUnscaledParameters.K ^ 2 := by
    exact (sq_le_sq₀ hs.1 concreteK_nonneg).2 hs.2
  have hfirst : vecSq u ≤ 4 * concreteUnscaledParameters.K ^ 2 * q := by
    rw [hu]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsu (by norm_num)) hq
  have hsecond' : vecSq v ≤
      16 * concreteSigma3WeightedSecondBound ^ 2 * q := by
    rw [hv]
    nlinarith
  have hadd := vecSq_add_le_two_local u v
  have hform : radialHessianApply concreteUnscaledParameters.P0
      concreteUnscaledParameters.P1 concreteUnscaledParameters.K p h = u + v := by
    funext i
    simp [radialHessianApply, u, v, s, t, z, r]
  rw [hform]
  change vecSq (u + v) ≤
    (8 * concreteUnscaledParameters.K ^ 2 +
      32 * concreteSigma3WeightedSecondBound ^ 2) * q
  nlinarith

private abbrev RegularityEuclideanVec (d : Nat) := EuclideanSpace ℝ (Fin d)

private def regularityToEuclidean {d : Nat} (x : EVec d) :
    RegularityEuclideanVec d := WithLp.toLp 2 x

private def regularityFromEuclidean {d : Nat} (x : RegularityEuclideanVec d) :
    EVec d := WithLp.ofLp x

@[simp] private theorem regularityFromToEuclidean {d : Nat} (x : EVec d) :
    regularityFromEuclidean (regularityToEuclidean x) = x := rfl

@[simp] private theorem regularityToFromEuclidean {d : Nat}
    (x : RegularityEuclideanVec d) :
    regularityToEuclidean (regularityFromEuclidean x) = x := rfl

private def regularityToEuclideanLinear (d : Nat) :
    EVec d →ₗ[ℝ] RegularityEuclideanVec d where
  toFun := regularityToEuclidean
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

private def regularityToEuclideanCLM (d : Nat) :
    EVec d →L[ℝ] RegularityEuclideanVec d :=
  ⟨regularityToEuclideanLinear d,
    (regularityToEuclideanLinear d).continuous_of_finiteDimensional⟩

private theorem norm_regularityToEuclidean {d : Nat} (x : EVec d) :
    ‖regularityToEuclidean x‖ = Real.sqrt (vecSq x) := by
  rw [EuclideanSpace.norm_eq]
  congr 1
  unfold vecSq NCPLVerification.vecSq regularityToEuclidean
  apply Finset.sum_congr rfl
  intro i _
  simp only [Real.norm_eq_abs, sq_abs]

private theorem hasDerivAt_concreteRadialGradient_line {d : Nat}
    (p h : EVec d) (t : ℝ) :
    HasDerivAt
      (fun z : ℝ => radialGradient concreteUnscaledParameters.P0
        concreteUnscaledParameters.P1 concreteUnscaledParameters.K
          (radialLine p h z))
      (radialHessianApply concreteUnscaledParameters.P0
        concreteUnscaledParameters.P1 concreteUnscaledParameters.K
          (radialLine p h t) h) t := by
  rw [hasDerivAt_pi]
  intro i
  have hs := (hasDerivAt_Sigma3Deriv concreteUnscaledParameters.P0
    concreteUnscaledParameters.P1 concreteUnscaledParameters.K
      (vecSq (radialLine p h t))).comp t
        (hasDerivAt_vecSq_radialLine p h t)
  have hp : HasDerivAt (fun z : ℝ => radialLine p h z i) (h i) t := by
    unfold radialLine
    convert (hasDerivAt_const t (p i)).add
      ((hasDerivAt_id t).mul_const (h i)) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext z
      rfl
    · ring
  have hprod := (hs.const_mul 2).mul hp
  convert hprod using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  · rfl
  · simp only [Function.comp_apply]
    unfold radialHessianApply
    ring

/-- A fixed numerical Lipschitz coefficient for the whole radial gradient,
viewed with the Euclidean norm. -/
noncomputable def concreteRadialEuclideanL0 : ℝ :=
  Real.sqrt (8 * concreteUnscaledParameters.K ^ 2 +
    32 * concreteSigma3WeightedSecondBound ^ 2)

theorem concreteRadialEuclideanL0_nonneg : 0 ≤ concreteRadialEuclideanL0 :=
  Real.sqrt_nonneg _

private theorem norm_concreteRadialHessianApply_le {d : Nat}
    (p h : EVec d) :
    ‖regularityToEuclidean
      (radialHessianApply concreteUnscaledParameters.P0
        concreteUnscaledParameters.P1 concreteUnscaledParameters.K p h)‖ ≤
      concreteRadialEuclideanL0 * ‖regularityToEuclidean h‖ := by
  let M : ℝ := 8 * concreteUnscaledParameters.K ^ 2 +
    32 * concreteSigma3WeightedSecondBound ^ 2
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hsquare := concreteRadialHessianApply_vecSq_le p h
  rw [norm_regularityToEuclidean, norm_regularityToEuclidean]
  change Real.sqrt (vecSq
      (radialHessianApply concreteUnscaledParameters.P0
        concreteUnscaledParameters.P1 concreteUnscaledParameters.K p h)) ≤
    Real.sqrt M * Real.sqrt (vecSq h)
  calc
    Real.sqrt (vecSq
        (radialHessianApply concreteUnscaledParameters.P0
          concreteUnscaledParameters.P1 concreteUnscaledParameters.K p h)) ≤
        Real.sqrt (M * vecSq h) := Real.sqrt_le_sqrt hsquare
    _ = Real.sqrt M * Real.sqrt (vecSq h) := Real.sqrt_mul hM _

private def concreteEuclideanRadialGradient {d : Nat}
    (p : RegularityEuclideanVec d) : RegularityEuclideanVec d :=
  regularityToEuclidean
    (radialGradient concreteUnscaledParameters.P0
      concreteUnscaledParameters.P1 concreteUnscaledParameters.K
        (regularityFromEuclidean p))

/-- Dimension-free Euclidean Lipschitz theorem for the radial gradient.
This is the radial ingredient used by the final uniform `concreteL0`; the
older coordinatewise sup-norm estimate is intentionally not used there. -/
theorem concreteEuclideanRadialGradient_lipschitz {d : Nat} :
    LipschitzWith ⟨concreteRadialEuclideanL0,
      concreteRadialEuclideanL0_nonneg⟩
      (concreteEuclideanRadialGradient (d := d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let p : EVec d := regularityFromEuclidean x
  let h : EVec d := regularityFromEuclidean (y - x)
  let f : ℝ → RegularityEuclideanVec d := fun t =>
    regularityToEuclidean
      (radialGradient concreteUnscaledParameters.P0
        concreteUnscaledParameters.P1 concreteUnscaledParameters.K
          (radialLine p h t))
  have hderiv : ∀ t, HasDerivAt f
      (regularityToEuclidean
        (radialHessianApply concreteUnscaledParameters.P0
          concreteUnscaledParameters.P1 concreteUnscaledParameters.K
            (radialLine p h t) h)) t := by
    intro t
    exact (regularityToEuclideanCLM d).hasFDerivAt.comp_hasDerivAt t
      (hasDerivAt_concreteRadialGradient_line p h t)
  have hdiff : ∀ t ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ f t :=
    fun t _ => (hderiv t).differentiableAt
  have hbound : ∀ t ∈ (Set.univ : Set ℝ),
      ‖deriv f t‖ ≤ concreteRadialEuclideanL0 * ‖y - x‖ := by
    intro t _
    rw [(hderiv t).deriv]
    have hb := norm_concreteRadialHessianApply_le (radialLine p h t) h
    simpa [h, regularityToFromEuclidean] using hb
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (x := (0 : ℝ)) (y := (1 : ℝ)) hdiff hbound convex_univ
      (Set.mem_univ 0) (Set.mem_univ 1)
  have hline0 : radialLine p h 0 = regularityFromEuclidean x := by
    funext i
    simp [radialLine, p]
  have hline1 : radialLine p h 1 = regularityFromEuclidean y := by
    funext i
    simp only [radialLine, p, h, one_mul]
    change regularityFromEuclidean x i +
      (regularityFromEuclidean y i - regularityFromEuclidean x i) =
        regularityFromEuclidean y i
    ring
  change dist (concreteEuclideanRadialGradient x)
      (concreteEuclideanRadialGradient y) ≤
    concreteRadialEuclideanL0 * dist x y
  simpa [f, concreteEuclideanRadialGradient, hline0, hline1,
    dist_eq_norm, norm_sub_rev] using hm

/-- Squared-coordinate form of the dimension-free radial Lipschitz bound.
This public interface avoids exposing the auxiliary `EuclideanSpace`
conversion used in the proof. -/
theorem concreteRadialGradient_vecSq_sub_le {d : Nat} (p r : EVec d) :
    vecSq
        (radialGradient concreteUnscaledParameters.P0
            concreteUnscaledParameters.P1 concreteUnscaledParameters.K p -
          radialGradient concreteUnscaledParameters.P0
            concreteUnscaledParameters.P1 concreteUnscaledParameters.K r) ≤
      concreteRadialEuclideanL0 ^ 2 * vecSq (p - r) := by
  let x := regularityToEuclidean p
  let y := regularityToEuclidean r
  have hdist := concreteEuclideanRadialGradient_lipschitz.dist_le_mul x y
  have hnorm : Real.sqrt
        (vecSq
          (radialGradient concreteUnscaledParameters.P0
              concreteUnscaledParameters.P1 concreteUnscaledParameters.K p -
            radialGradient concreteUnscaledParameters.P0
              concreteUnscaledParameters.P1 concreteUnscaledParameters.K r)) ≤
      concreteRadialEuclideanL0 * Real.sqrt (vecSq (p - r)) := by
    have houtEq :
        regularityToEuclidean
            (radialGradient concreteUnscaledParameters.P0
                concreteUnscaledParameters.P1 concreteUnscaledParameters.K p) -
          regularityToEuclidean
            (radialGradient concreteUnscaledParameters.P0
                concreteUnscaledParameters.P1 concreteUnscaledParameters.K r) =
        regularityToEuclidean
          (radialGradient concreteUnscaledParameters.P0
              concreteUnscaledParameters.P1 concreteUnscaledParameters.K p -
            radialGradient concreteUnscaledParameters.P0
              concreteUnscaledParameters.P1 concreteUnscaledParameters.K r) := rfl
    have hinEq : regularityToEuclidean p - regularityToEuclidean r =
        regularityToEuclidean (p - r) := rfl
    rw [dist_eq_norm, dist_eq_norm] at hdist
    simp only [x, y, concreteEuclideanRadialGradient,
      regularityFromToEuclidean] at hdist
    rw [houtEq, hinEq, norm_regularityToEuclidean,
      norm_regularityToEuclidean] at hdist
    change Real.sqrt
        (vecSq
          (radialGradient concreteUnscaledParameters.P0
              concreteUnscaledParameters.P1 concreteUnscaledParameters.K p -
            radialGradient concreteUnscaledParameters.P0
              concreteUnscaledParameters.P1 concreteUnscaledParameters.K r)) ≤
      concreteRadialEuclideanL0 * Real.sqrt (vecSq (p - r)) at hdist
    exact hdist
  have hout := vecSq_nonneg
    (radialGradient concreteUnscaledParameters.P0
        concreteUnscaledParameters.P1 concreteUnscaledParameters.K p -
      radialGradient concreteUnscaledParameters.P0
        concreteUnscaledParameters.P1 concreteUnscaledParameters.K r)
  have hin := vecSq_nonneg (p - r)
  have hsout := Real.sq_sqrt hout
  have hsin := Real.sq_sqrt hin
  have hL := concreteRadialEuclideanL0_nonneg
  have hsquare := (sq_le_sq₀
    (Real.sqrt_nonneg _)
    (mul_nonneg hL (Real.sqrt_nonneg _))).2 hnorm
  rw [hsout, mul_pow, hsin] at hsquare
  exact hsquare

private noncomputable def concreteSigma3SecondBound : ℝ :=
  Classical.choose (Sigma3Second_bounded (K := concreteUnscaledParameters.K)
    concreteP0_sq_lt_P1_sq)

private theorem concreteSigma3SecondBound_spec :
    0 ≤ concreteSigma3SecondBound ∧ ∀ r,
      |Sigma3Second concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
        concreteUnscaledParameters.K r| ≤ concreteSigma3SecondBound :=
  Classical.choose_spec (Sigma3Second_bounded (K := concreteUnscaledParameters.K)
    concreteP0_sq_lt_P1_sq)

private theorem abs_serializedA_le_norm {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) : |serializedA q i| ≤ ‖q‖ := by
  have h := (LipschitzWith.eval (serializedAIndex (n := n) i)).dist_le_mul q 0
  simpa [serializedA, Real.dist_eq, dist_zero_right] using h

private theorem abs_serializedB_le_norm {T n : Nat} (q : SerializedSpace T n)
    (i : Fin (T - 1)) : |serializedB q i| ≤ ‖q‖ := by
  have h := (LipschitzWith.eval (serializedBIndex (n := n) i)).dist_le_mul q 0
  simpa [serializedB, Real.dist_eq, dist_zero_right] using h

private theorem abs_serializedA_le_P1_of_pulseSq {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1))
    (hq : serializedPulseSq q ≤ concreteUnscaledParameters.P1 ^ 2) :
    |serializedA q i| ≤ concreteUnscaledParameters.P1 := by
  have hcoord : (serializedA q i) ^ 2 ≤ serializedPulseSq q := by
    unfold serializedPulseSq
    calc
      serializedA q i ^ 2 ≤ serializedA q i ^ 2 + serializedB q i ^ 2 :=
        le_add_of_nonneg_right (sq_nonneg _)
      _ ≤ Finset.univ.sum (fun j : Fin (T - 1) ↦
          serializedA q j ^ 2 + serializedB q j ^ 2) :=
        Finset.single_le_sum
          (f := fun j : Fin (T - 1) ↦ serializedA q j ^ 2 + serializedB q j ^ 2)
          (fun j _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_univ i)
  have habs : |serializedA q i| ^ 2 ≤ concreteUnscaledParameters.P1 ^ 2 := by
    rw [sq_abs]
    exact hcoord.trans hq
  nlinarith [sq_nonneg (|serializedA q i| + concreteUnscaledParameters.P1),
    concreteP1_pos]

private theorem abs_serializedB_le_P1_of_pulseSq {T n : Nat}
    (q : SerializedSpace T n) (i : Fin (T - 1))
    (hq : serializedPulseSq q ≤ concreteUnscaledParameters.P1 ^ 2) :
    |serializedB q i| ≤ concreteUnscaledParameters.P1 := by
  have hcoord : (serializedB q i) ^ 2 ≤ serializedPulseSq q := by
    unfold serializedPulseSq
    calc
      serializedB q i ^ 2 ≤ serializedA q i ^ 2 + serializedB q i ^ 2 :=
        le_add_of_nonneg_left (sq_nonneg _)
      _ ≤ Finset.univ.sum (fun j : Fin (T - 1) ↦
          serializedA q j ^ 2 + serializedB q j ^ 2) :=
        Finset.single_le_sum
          (f := fun j : Fin (T - 1) ↦ serializedA q j ^ 2 + serializedB q j ^ 2)
          (fun j _ ↦ add_nonneg (sq_nonneg _) (sq_nonneg _)) (Finset.mem_univ i)
  have habs : |serializedB q i| ^ 2 ≤ concreteUnscaledParameters.P1 ^ 2 := by
    rw [sq_abs]
    exact hcoord.trans hq
  nlinarith [sq_nonneg (|serializedB q i| + concreteUnscaledParameters.P1),
    concreteP1_pos]

private theorem abs_serializedPulseDot_le {T n : Nat}
    (q h : SerializedSpace T n)
    (hq : serializedPulseSq q ≤ concreteUnscaledParameters.P1 ^ 2) :
    |serializedPulseDot q h| ≤
      (2 * ((T - 1 : Nat) : ℝ)) * concreteUnscaledParameters.P1 * ‖h‖ := by
  unfold serializedPulseDot
  calc
    |Finset.univ.sum (fun i : Fin (T - 1) ↦
        serializedA q i * serializedA h i + serializedB q i * serializedB h i)| ≤
        Finset.univ.sum (fun i : Fin (T - 1) ↦
          |serializedA q i * serializedA h i +
            serializedB q i * serializedB h i|) := Finset.abs_sum_le_sum_abs _ _
    _ ≤ Finset.univ.sum (fun _i : Fin (T - 1) ↦
        2 * concreteUnscaledParameters.P1 * ‖h‖) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        |serializedA q i * serializedA h i + serializedB q i * serializedB h i| ≤
            |serializedA q i| * |serializedA h i| +
              |serializedB q i| * |serializedB h i| := by
                simpa only [abs_mul] using abs_add_le
                  (serializedA q i * serializedA h i)
                  (serializedB q i * serializedB h i)
        _ ≤ concreteUnscaledParameters.P1 * ‖h‖ +
              concreteUnscaledParameters.P1 * ‖h‖ := by
            exact add_le_add
              (mul_le_mul (abs_serializedA_le_P1_of_pulseSq q i hq)
                (abs_serializedA_le_norm h i) (abs_nonneg _) concreteP1_pos.le)
              (mul_le_mul (abs_serializedB_le_P1_of_pulseSq q i hq)
                (abs_serializedB_le_norm h i) (abs_nonneg _) concreteP1_pos.le)
        _ = 2 * concreteUnscaledParameters.P1 * ‖h‖ := by ring
    _ = (2 * ((T - 1 : Nat) : ℝ)) * concreteUnscaledParameters.P1 * ‖h‖ := by
      simp
      ring

def concreteRadialLipConstant (T : Nat) : ℝ :=
  2 * concreteUnscaledParameters.K +
    (8 * ((T - 1 : Nat) : ℝ)) * concreteSigma3SecondBound *
      concreteUnscaledParameters.P1 ^ 2

private theorem concreteRadialLipConstant_nonneg (T : Nat) :
    0 ≤ concreteRadialLipConstant T := by
  unfold concreteRadialLipConstant
  exact add_nonneg (mul_nonneg (by norm_num) concreteK_nonneg)
    (mul_nonneg
      (mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * ((T - 1 : Nat) : ℝ))
        concreteSigma3SecondBound_spec.1)
      (sq_nonneg concreteUnscaledParameters.P1))

private theorem abs_concreteRadialA_line_deriv_le {T n : Nat}
    (q h : SerializedSpace T n) (i : Fin (T - 1)) (t : ℝ) :
    |2 * Sigma3Deriv concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
          concreteUnscaledParameters.K
          (serializedPulseSq (serializedLine q h t)) * serializedA h i +
      4 * Sigma3Second concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
          concreteUnscaledParameters.K
          (serializedPulseSq (serializedLine q h t)) *
        serializedPulseDot (serializedLine q h t) h *
          serializedA (serializedLine q h t) i| ≤
      concreteRadialLipConstant T * ‖h‖ := by
  let z := serializedLine q h t
  let r := serializedPulseSq z
  let s := Sigma3Deriv concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
    concreteUnscaledParameters.K r
  let u := Sigma3Second concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
    concreteUnscaledParameters.K r
  have hs := Sigma3Deriv_mem (P0 := concreteUnscaledParameters.P0)
    (P1 := concreteUnscaledParameters.P1) (r := r) concreteK_nonneg
  have hfirst : |2 * s * serializedA h i| ≤
      2 * concreteUnscaledParameters.K * ‖h‖ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hs.1]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hs.2 (by norm_num))
      (abs_serializedA_le_norm h i) (abs_nonneg _)
      (mul_nonneg (by norm_num) concreteK_nonneg)
  have hsecond : |4 * u * serializedPulseDot z h * serializedA z i| ≤
      (8 * ((T - 1 : Nat) : ℝ)) * concreteSigma3SecondBound *
        concreteUnscaledParameters.P1 ^ 2 * ‖h‖ := by
    by_cases hr : r ∈ Set.Icc (concreteUnscaledParameters.P0 ^ 2)
      (concreteUnscaledParameters.P1 ^ 2)
    · have hu := concreteSigma3SecondBound_spec.2 r
      have hdot := abs_serializedPulseDot_le z h hr.2
      have hz := abs_serializedA_le_P1_of_pulseSq z i hr.2
      have hC : 0 ≤ concreteSigma3SecondBound := concreteSigma3SecondBound_spec.1
      have hP : 0 ≤ concreteUnscaledParameters.P1 := concreteP1_pos.le
      have hN : 0 ≤ ((T - 1 : Nat) : ℝ) := Nat.cast_nonneg _
      have hnrm : 0 ≤ ‖h‖ := norm_nonneg h
      calc
        |4 * u * serializedPulseDot z h * serializedA z i| =
            4 * |u| * |serializedPulseDot z h| * |serializedA z i| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
        _ ≤ 4 * concreteSigma3SecondBound *
              ((2 * ((T - 1 : Nat) : ℝ)) *
                concreteUnscaledParameters.P1 * ‖h‖) *
              concreteUnscaledParameters.P1 := by
            gcongr
        _ = (8 * ((T - 1 : Nat) : ℝ)) * concreteSigma3SecondBound *
              concreteUnscaledParameters.P1 ^ 2 * ‖h‖ := by ring
    · have hu : u = 0 := by
        exact Sigma3Second_eq_zero_of_not_mem concreteP0_sq_lt_P1_sq hr
      rw [hu]
      have hnonneg := mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * ((T - 1 : Nat) : ℝ))
            concreteSigma3SecondBound_spec.1)
          (sq_nonneg concreteUnscaledParameters.P1))
        (norm_nonneg h)
      simpa only [mul_zero, zero_mul, abs_zero] using hnonneg
  change |2 * s * serializedA h i + 4 * u * serializedPulseDot z h *
    serializedA z i| ≤ concreteRadialLipConstant T * ‖h‖
  calc
    |2 * s * serializedA h i + 4 * u * serializedPulseDot z h * serializedA z i| ≤
        |2 * s * serializedA h i| +
          |4 * u * serializedPulseDot z h * serializedA z i| := abs_add_le _ _
    _ ≤ 2 * concreteUnscaledParameters.K * ‖h‖ +
        (8 * ((T - 1 : Nat) : ℝ)) * concreteSigma3SecondBound *
          concreteUnscaledParameters.P1 ^ 2 * ‖h‖ := add_le_add hfirst hsecond
    _ = concreteRadialLipConstant T * ‖h‖ := by
      unfold concreteRadialLipConstant
      ring

private theorem abs_concreteRadialB_line_deriv_le {T n : Nat}
    (q h : SerializedSpace T n) (i : Fin (T - 1)) (t : ℝ) :
    |2 * Sigma3Deriv concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
          concreteUnscaledParameters.K
          (serializedPulseSq (serializedLine q h t)) * serializedB h i +
      4 * Sigma3Second concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
          concreteUnscaledParameters.K
          (serializedPulseSq (serializedLine q h t)) *
        serializedPulseDot (serializedLine q h t) h *
          serializedB (serializedLine q h t) i| ≤
      concreteRadialLipConstant T * ‖h‖ := by
  let z := serializedLine q h t
  let r := serializedPulseSq z
  let s := Sigma3Deriv concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
    concreteUnscaledParameters.K r
  let u := Sigma3Second concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
    concreteUnscaledParameters.K r
  have hs := Sigma3Deriv_mem (P0 := concreteUnscaledParameters.P0)
    (P1 := concreteUnscaledParameters.P1) (r := r) concreteK_nonneg
  have hfirst : |2 * s * serializedB h i| ≤
      2 * concreteUnscaledParameters.K * ‖h‖ := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      abs_of_nonneg hs.1]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hs.2 (by norm_num))
      (abs_serializedB_le_norm h i) (abs_nonneg _)
      (mul_nonneg (by norm_num) concreteK_nonneg)
  have hsecond : |4 * u * serializedPulseDot z h * serializedB z i| ≤
      (8 * ((T - 1 : Nat) : ℝ)) * concreteSigma3SecondBound *
        concreteUnscaledParameters.P1 ^ 2 * ‖h‖ := by
    by_cases hr : r ∈ Set.Icc (concreteUnscaledParameters.P0 ^ 2)
      (concreteUnscaledParameters.P1 ^ 2)
    · have hu := concreteSigma3SecondBound_spec.2 r
      have hdot := abs_serializedPulseDot_le z h hr.2
      have hz := abs_serializedB_le_P1_of_pulseSq z i hr.2
      have hC : 0 ≤ concreteSigma3SecondBound := concreteSigma3SecondBound_spec.1
      have hP : 0 ≤ concreteUnscaledParameters.P1 := concreteP1_pos.le
      have hN : 0 ≤ ((T - 1 : Nat) : ℝ) := Nat.cast_nonneg _
      have hnrm : 0 ≤ ‖h‖ := norm_nonneg h
      calc
        |4 * u * serializedPulseDot z h * serializedB z i| =
            4 * |u| * |serializedPulseDot z h| * |serializedB z i| := by
              rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
        _ ≤ 4 * concreteSigma3SecondBound *
              ((2 * ((T - 1 : Nat) : ℝ)) *
                concreteUnscaledParameters.P1 * ‖h‖) *
              concreteUnscaledParameters.P1 := by
            gcongr
        _ = (8 * ((T - 1 : Nat) : ℝ)) * concreteSigma3SecondBound *
              concreteUnscaledParameters.P1 ^ 2 * ‖h‖ := by ring
    · have hu : u = 0 := by
        exact Sigma3Second_eq_zero_of_not_mem concreteP0_sq_lt_P1_sq hr
      rw [hu]
      have hnonneg := mul_nonneg
        (mul_nonneg
          (mul_nonneg (by positivity : (0 : ℝ) ≤ 8 * ((T - 1 : Nat) : ℝ))
            concreteSigma3SecondBound_spec.1)
          (sq_nonneg concreteUnscaledParameters.P1))
        (norm_nonneg h)
      simpa only [mul_zero, zero_mul, abs_zero] using hnonneg
  change |2 * s * serializedB h i + 4 * u * serializedPulseDot z h *
    serializedB z i| ≤ concreteRadialLipConstant T * ‖h‖
  calc
    |2 * s * serializedB h i + 4 * u * serializedPulseDot z h * serializedB z i| ≤
        |2 * s * serializedB h i| +
          |4 * u * serializedPulseDot z h * serializedB z i| := abs_add_le _ _
    _ ≤ 2 * concreteUnscaledParameters.K * ‖h‖ +
        (8 * ((T - 1 : Nat) : ℝ)) * concreteSigma3SecondBound *
          concreteUnscaledParameters.P1 ^ 2 * ‖h‖ := add_le_add hfirst hsecond
    _ = concreteRadialLipConstant T * ‖h‖ := by
      unfold concreteRadialLipConstant
      ring

private noncomputable def concreteSerializedRadialALip {T n : Nat}
    (i : Fin (T - 1)) : GloballyLipschitz
      (fun q : SerializedSpace T n =>
        2 * Sigma3Deriv concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
          concreteUnscaledParameters.K (serializedPulseSq q) * serializedA q i) := by
  let L := concreteRadialLipConstant T
  have hL : 0 ≤ L := concreteRadialLipConstant_nonneg T
  refine ⟨⟨L, hL⟩, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro q q'
  let h : SerializedSpace T n := q' - q
  let f : ℝ → ℝ := fun t ↦
    2 * Sigma3Deriv concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
      concreteUnscaledParameters.K (serializedPulseSq (serializedLine q h t)) *
        serializedA (serializedLine q h t) i
  have hderiv : ∀ t, HasDerivAt f
      (2 * Sigma3Deriv concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
          concreteUnscaledParameters.K (serializedPulseSq (serializedLine q h t)) *
          serializedA h i +
        4 * Sigma3Second concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
          concreteUnscaledParameters.K (serializedPulseSq (serializedLine q h t)) *
          serializedPulseDot (serializedLine q h t) h *
          serializedA (serializedLine q h t) i) t := by
    intro t
    exact hasDerivAt_serializedRadialA_line concreteUnscaledParameters q h i t
  have hdiff : ∀ t ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ f t :=
    fun t _ ↦ (hderiv t).differentiableAt
  have hbound : ∀ t ∈ (Set.univ : Set ℝ), ‖deriv f t‖ ≤ L * ‖h‖ := by
    intro t _
    rw [(hderiv t).deriv, Real.norm_eq_abs]
    exact abs_concreteRadialA_line_deriv_le q h i t
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (x := (0 : ℝ)) (y := (1 : ℝ)) hdiff hbound convex_univ
      (Set.mem_univ 0) (Set.mem_univ 1)
  have hline0 : serializedLine q h 0 = q := by
    funext j
    simp [serializedLine]
  have hline1 : serializedLine q h 1 = q' := by
    funext j
    simp [serializedLine, h]
  have hhnorm : ‖h‖ = dist q q' := by
    simp [h, dist_eq_norm, norm_sub_rev]
  rw [hhnorm] at hm
  norm_num [f, hline0, hline1, Real.norm_eq_abs] at hm
  change _ ≤ L * dist q q'
  simpa [Real.dist_eq, abs_sub_comm] using hm

private noncomputable def concreteSerializedRadialBLip {T n : Nat}
    (i : Fin (T - 1)) : GloballyLipschitz
      (fun q : SerializedSpace T n =>
        2 * Sigma3Deriv concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
          concreteUnscaledParameters.K (serializedPulseSq q) * serializedB q i) := by
  let L := concreteRadialLipConstant T
  have hL : 0 ≤ L := concreteRadialLipConstant_nonneg T
  refine ⟨⟨L, hL⟩, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro q q'
  let h : SerializedSpace T n := q' - q
  let f : ℝ → ℝ := fun t ↦
    2 * Sigma3Deriv concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
      concreteUnscaledParameters.K (serializedPulseSq (serializedLine q h t)) *
        serializedB (serializedLine q h t) i
  have hderiv : ∀ t, HasDerivAt f
      (2 * Sigma3Deriv concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
          concreteUnscaledParameters.K (serializedPulseSq (serializedLine q h t)) *
          serializedB h i +
        4 * Sigma3Second concreteUnscaledParameters.P0 concreteUnscaledParameters.P1
          concreteUnscaledParameters.K (serializedPulseSq (serializedLine q h t)) *
          serializedPulseDot (serializedLine q h t) h *
          serializedB (serializedLine q h t) i) t := by
    intro t
    exact hasDerivAt_serializedRadialB_line concreteUnscaledParameters q h i t
  have hdiff : ∀ t ∈ (Set.univ : Set ℝ), DifferentiableAt ℝ f t :=
    fun t _ ↦ (hderiv t).differentiableAt
  have hbound : ∀ t ∈ (Set.univ : Set ℝ), ‖deriv f t‖ ≤ L * ‖h‖ := by
    intro t _
    rw [(hderiv t).deriv, Real.norm_eq_abs]
    exact abs_concreteRadialB_line_deriv_le q h i t
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (x := (0 : ℝ)) (y := (1 : ℝ)) hdiff hbound convex_univ
      (Set.mem_univ 0) (Set.mem_univ 1)
  have hline0 : serializedLine q h 0 = q := by
    funext j
    simp [serializedLine]
  have hline1 : serializedLine q h 1 = q' := by
    funext j
    simp [serializedLine, h]
  have hhnorm : ‖h‖ = dist q q' := by
    simp [h, dist_eq_norm, norm_sub_rev]
  rw [hhnorm] at hm
  norm_num [f, hline0, hline1, Real.norm_eq_abs] at hm
  change _ ≤ L * dist q q'
  simpa [Real.dist_eq, abs_sub_comm] using hm

private noncomputable def concreteSerializedGradALip {T n : Nat} (hn : 0 < n)
    (i : Fin (T - 1)) : GloballyLipschitz
      (fun q : SerializedSpace T n =>
        serializedGradA hn concreteUnscaledParameters q i) := by
  have h := (concreteSerializedGradANonradialLip hn i).add
    (concreteSerializedRadialALip (n := n) i)
  convert h using 1
  funext q
  unfold serializedGradA serializedGradANonradial
  ring

private noncomputable def concreteSerializedGradBLip {T n : Nat} (hn : 0 < n)
    (i : Fin (T - 1)) : GloballyLipschitz
      (fun q : SerializedSpace T n =>
        serializedGradB hn concreteUnscaledParameters q i) := by
  have h := (concreteSerializedGradBNonradialLip hn i).add
    (concreteSerializedRadialBLip (n := n) i)
  convert h using 1
  funext q
  unfold serializedGradB serializedGradBNonradial
  ring

private structure GloballyLipschitzMap {E F : Type*}
    [PseudoMetricSpace E] [SeminormedAddCommGroup F] (f : E → F) where
  C : NNReal
  lipschitz : LipschitzWith C f

namespace GloballyLipschitzMap

variable {E F : Type*} [PseudoMetricSpace E]
  [SeminormedAddCommGroup F] {f g : E → F}

def zero : GloballyLipschitzMap (fun _ : E => (0 : F)) :=
  ⟨0, LipschitzWith.const 0⟩

def add (hf : GloballyLipschitzMap f) (hg : GloballyLipschitzMap g) :
    GloballyLipschitzMap (fun x => f x + g x) :=
  ⟨hf.C + hg.C, hf.lipschitz.add hg.lipschitz⟩

def single {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ι)
    {f : E → ℝ} (hf : GloballyLipschitz f) :
    GloballyLipschitzMap (fun x => (Pi.single j (f x) : ι → ℝ)) := by
  refine ⟨hf.C, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) (dist_nonneg))).2
  intro k
  by_cases hk : k = j
  · subst k
    simpa [Pi.single_apply] using hf.lipschitz.dist_le_mul x y
  · simp [Pi.single_apply, hk]
    positivity

noncomputable def sum {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → E → F} (hf : ∀ i ∈ s, GloballyLipschitzMap (f i)) :
    GloballyLipschitzMap (fun x => ∑ i ∈ s, f i x) := by
  classical
  have hex : ∃ C : NNReal,
      LipschitzWith C (fun x => ∑ i ∈ s, f i x) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simpa using (LipschitzWith.const (0 : F))⟩
    | @insert a s ha ih =>
        obtain ⟨Ctail, htail⟩ := ih
          (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
        let hhead := hf a (Finset.mem_insert_self a s)
        exact ⟨hhead.C + Ctail, by
          simpa [Finset.sum_insert, ha] using hhead.lipschitz.add htail⟩
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

end GloballyLipschitzMap

private structure SerializedLipschitz {T n : Nat}
    (f : SerializedSpace T n → SerializedSpace T n) where
  C : NNReal
  lipschitz : LipschitzWith C f

namespace SerializedLipschitz

def add {T n : Nat} {f g : SerializedSpace T n → SerializedSpace T n}
    (hf : SerializedLipschitz f) (hg : SerializedLipschitz g) :
    SerializedLipschitz (fun x => f x + g x) :=
  ⟨hf.C + hg.C, hf.lipschitz.add hg.lipschitz⟩

def single {T n : Nat} (j : Fin ((T - 1) * (n + 3)))
    {f : SerializedSpace T n → ℝ} (hf : GloballyLipschitz f) :
    SerializedLipschitz (fun x => Pi.single j (f x)) := by
  refine ⟨hf.C, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg (NNReal.coe_nonneg _) (dist_nonneg))).2
  intro k
  by_cases hk : k = j
  · subst k
    simpa using hf.lipschitz.dist_le_mul x y
  · simp [Pi.single_apply, hk]
    positivity

noncomputable def sum {T n : Nat} {ι : Type*} [DecidableEq ι] {s : Finset ι}
    {f : ι → SerializedSpace T n → SerializedSpace T n}
    (hf : ∀ i ∈ s, SerializedLipschitz (f i)) :
    SerializedLipschitz (fun x => ∑ i ∈ s, f i x) := by
  classical
  have hex : ∃ C : NNReal,
      LipschitzWith C (fun x => ∑ i ∈ s, f i x) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert a s ha ih =>
        obtain ⟨Ctail, htail⟩ := ih
          (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))
        let hhead := hf a (Finset.mem_insert_self a s)
        exact ⟨hhead.C + Ctail, by
          simpa [Finset.sum_insert, ha] using hhead.lipschitz.add htail⟩
  exact ⟨Classical.choose hex, Classical.choose_spec hex⟩

end SerializedLipschitz

private noncomputable def concreteSerializedSaddleFieldLip {T n : Nat}
    (hn : 0 < n) : SerializedLipschitz
      (serializedSaddleField (T := T) hn concreteUnscaledParameters) := by
  classical
  let hA := SerializedLipschitz.sum
    (s := (Finset.univ : Finset (Fin (T - 1))))
    (f := fun i q ↦ (Pi.single (serializedAIndex (n := n) i)
      (serializedGradA hn concreteUnscaledParameters q i) : SerializedSpace T n))
    (fun i _ ↦ SerializedLipschitz.single _ (concreteSerializedGradALip hn i))
  let hYinner : ∀ i : Fin (T - 1), SerializedLipschitz
      (fun q : SerializedSpace T n => ∑ k : Fin n,
        (Pi.single (serializedDualIndex i k)
          (serializedSaddleGradY hn concreteUnscaledParameters q i k) :
            SerializedSpace T n)) := fun i ↦
    SerializedLipschitz.sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun k q ↦ (Pi.single (serializedDualIndex i k)
        (serializedSaddleGradY hn concreteUnscaledParameters q i k) :
          SerializedSpace T n))
      (fun k _ ↦ SerializedLipschitz.single _ (concreteSerializedGradYLip hn i k))
  let hY := SerializedLipschitz.sum
    (s := (Finset.univ : Finset (Fin (T - 1))))
    (f := fun i q ↦ ∑ k : Fin n,
      (Pi.single (serializedDualIndex i k)
        (serializedSaddleGradY hn concreteUnscaledParameters q i k) :
          SerializedSpace T n))
    (fun i _ ↦ hYinner i)
  let hB := SerializedLipschitz.sum
    (s := (Finset.univ : Finset (Fin (T - 1))))
    (f := fun i q ↦ (Pi.single (serializedBIndex (n := n) i)
      (serializedGradB hn concreteUnscaledParameters q i) : SerializedSpace T n))
    (fun i _ ↦ SerializedLipschitz.single _ (concreteSerializedGradBLip hn i))
  let hS := SerializedLipschitz.sum
    (s := (Finset.univ : Finset (Fin (T - 1))))
    (f := fun i q ↦ (Pi.single (serializedStateIndex (n := n) i)
      (serializedGradState concreteUnscaledParameters q i) : SerializedSpace T n))
    (fun i _ ↦ SerializedLipschitz.single _
      (GloballyLipschitz.ofBL (concreteSerializedGradStateBL (n := n) i)))
  let hall := ((SerializedLipschitz.add hA hY).add hB).add hS
  refine ⟨hall.C, ?_⟩
  change LipschitzWith hall.C (fun q : SerializedSpace T n =>
    (Finset.univ.sum fun i : Fin (T - 1) ↦
      (Pi.single (serializedAIndex (n := n) i)
        (serializedGradA hn concreteUnscaledParameters q i) : SerializedSpace T n)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦
      Finset.univ.sum fun k : Fin n ↦
        (Pi.single (serializedDualIndex i k)
          (serializedSaddleGradY hn concreteUnscaledParameters q i k) :
            SerializedSpace T n)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦
      (Pi.single (serializedBIndex (n := n) i)
        (serializedGradB hn concreteUnscaledParameters q i) : SerializedSpace T n)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦
      (Pi.single (serializedStateIndex (n := n) i)
        (serializedGradState concreteUnscaledParameters q i) : SerializedSpace T n)))
  exact hall.lipschitz

def concreteSerializedTrueField {T n : Nat} (hn : 0 < n)
    (q : SerializedSpace T n) : SerializedSpace T n :=
  (Finset.univ.sum fun i : Fin (T - 1) ↦
      (Pi.single (serializedAIndex (n := n) i)
        (serializedGradA hn concreteUnscaledParameters q i) : SerializedSpace T n)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦
      Finset.univ.sum fun k : Fin n ↦
        (Pi.single (serializedDualIndex i k)
          (-serializedSaddleGradY hn concreteUnscaledParameters q i k) :
            SerializedSpace T n)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦
      (Pi.single (serializedBIndex (n := n) i)
        (serializedGradB hn concreteUnscaledParameters q i) : SerializedSpace T n)) +
    (Finset.univ.sum fun i : Fin (T - 1) ↦
      (Pi.single (serializedStateIndex (n := n) i)
        (serializedGradState concreteUnscaledParameters q i) : SerializedSpace T n))

theorem concreteSerializedTrueField_eq_trueGradient {T n : Nat} (hn : 0 < n)
    (q : SerializedSpace T n) :
    concreteSerializedTrueField hn q =
      serializedTrueGradient hn concreteUnscaledParameters q := by
  classical
  apply SerializedSpace.ext_blocks
  · intro i
    unfold concreteSerializedTrueField serializedA
    simp [serializedAIndex_ne_dualIndex, serializedAIndex_ne_BIndex,
      serializedAIndex_ne_stateIndex]
    rw [Finset.sum_eq_single i]
    · simp [serializedTrueGradient_A]
    · intro c _ hci
      have hne : serializedAIndex (n := n) c ≠ serializedAIndex i :=
        fun h ↦ hci (serializedAIndex_injective h)
      simp [hne]
    · simp
  · intro i k
    unfold concreteSerializedTrueField serializedY
    simp [serializedAIndex_ne_dualIndex, serializedBIndex_ne_dualIndex,
      serializedStateIndex_ne_dualIndex]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single k]
      · simp [serializedTrueGradient_Y]
      · intro c _ hck
        have hne : serializedDualIndex i c ≠ serializedDualIndex i k := by
          intro h
          have hp : (i, c) = (i, k) := serializedDualIndex_injective h
          exact hck (congrArg Prod.snd hp)
        simp [hne]
      · simp
    · intro l _ hli
      apply Finset.sum_eq_zero
      intro c _
      have hne : serializedDualIndex l c ≠ serializedDualIndex i k := by
        intro h
        have hp : (l, c) = (i, k) := serializedDualIndex_injective h
        exact hli (congrArg Prod.fst hp)
      simp [hne]
    · simp
  · intro i
    unfold concreteSerializedTrueField serializedB
    simp [serializedAIndex_ne_BIndex, serializedBIndex_ne_dualIndex,
      serializedBIndex_ne_stateIndex]
    rw [Finset.sum_eq_single i]
    · simp [serializedTrueGradient_B]
    · intro c _ hci
      have hne : serializedBIndex (n := n) c ≠ serializedBIndex i :=
        fun h ↦ hci (serializedBIndex_injective h)
      simp [hne]
    · simp
  · intro i
    unfold concreteSerializedTrueField serializedState
    simp [serializedAIndex_ne_stateIndex, serializedBIndex_ne_stateIndex,
      serializedStateIndex_ne_dualIndex]
    rw [Finset.sum_eq_single i]
    · simp [serializedTrueGradient_state]
    · intro c _ hci
      have hne : serializedStateIndex (n := n) c ≠ serializedStateIndex i :=
        fun h ↦ hci (serializedStateIndex_injective h)
      simp [hne]
    · simp

private noncomputable def concreteSerializedTrueFieldLip {T n : Nat}
    (hn : 0 < n) : SerializedLipschitz
      (serializedTrueGradient (T := T) hn concreteUnscaledParameters) := by
  classical
  let hA := SerializedLipschitz.sum
    (s := (Finset.univ : Finset (Fin (T - 1))))
    (f := fun i q ↦ (Pi.single (serializedAIndex (n := n) i)
      (serializedGradA hn concreteUnscaledParameters q i) : SerializedSpace T n))
    (fun i _ ↦ SerializedLipschitz.single _ (concreteSerializedGradALip hn i))
  let hYinner : ∀ i : Fin (T - 1), SerializedLipschitz
      (fun q : SerializedSpace T n => ∑ k : Fin n,
        (Pi.single (serializedDualIndex i k)
          (-serializedSaddleGradY hn concreteUnscaledParameters q i k) :
            SerializedSpace T n)) := fun i ↦
    SerializedLipschitz.sum
      (s := (Finset.univ : Finset (Fin n)))
      (f := fun k q ↦ (Pi.single (serializedDualIndex i k)
        (-serializedSaddleGradY hn concreteUnscaledParameters q i k) :
          SerializedSpace T n))
      (fun k _ ↦ SerializedLipschitz.single _ (concreteSerializedGradYLip hn i k).neg)
  let hY := SerializedLipschitz.sum
    (s := (Finset.univ : Finset (Fin (T - 1))))
    (f := fun i q ↦ ∑ k : Fin n,
      (Pi.single (serializedDualIndex i k)
        (-serializedSaddleGradY hn concreteUnscaledParameters q i k) :
          SerializedSpace T n))
    (fun i _ ↦ hYinner i)
  let hB := SerializedLipschitz.sum
    (s := (Finset.univ : Finset (Fin (T - 1))))
    (f := fun i q ↦ (Pi.single (serializedBIndex (n := n) i)
      (serializedGradB hn concreteUnscaledParameters q i) : SerializedSpace T n))
    (fun i _ ↦ SerializedLipschitz.single _ (concreteSerializedGradBLip hn i))
  let hS := SerializedLipschitz.sum
    (s := (Finset.univ : Finset (Fin (T - 1))))
    (f := fun i q ↦ (Pi.single (serializedStateIndex (n := n) i)
      (serializedGradState concreteUnscaledParameters q i) : SerializedSpace T n))
    (fun i _ ↦ SerializedLipschitz.single _
      (GloballyLipschitz.ofBL (concreteSerializedGradStateBL (n := n) i)))
  let hall := ((SerializedLipschitz.add hA hY).add hB).add hS
  refine ⟨hall.C, ?_⟩
  rw [← show concreteSerializedTrueField hn =
      serializedTrueGradient hn concreteUnscaledParameters from by
    funext q
    exact concreteSerializedTrueField_eq_trueGradient hn q]
  exact hall.lipschitz

noncomputable def concreteSerializedL0 {T n : Nat} (hn : 0 < n) : ℝ :=
  max 1 (concreteSerializedTrueFieldLip (T := T) (n := n) hn).C

theorem concreteSerializedL0_pos {T n : Nat} (hn : 0 < n) :
    0 < concreteSerializedL0 (T := T) hn :=
  lt_of_lt_of_le zero_lt_one (le_max_left 1 _)

theorem concreteSerializedTrueGradient_lipschitz {T n : Nat} (hn : 0 < n) :
    LipschitzWith ⟨concreteSerializedL0 (T := T) (n := n) hn,
      (concreteSerializedL0_pos (T := T) (n := n) hn).le⟩
      (serializedTrueGradient (T := T) hn concreteUnscaledParameters) := by
  let h := concreteSerializedTrueFieldLip (T := T) (n := n) hn
  exact h.lipschitz.weaken (by
    exact_mod_cast le_max_right (1 : ℝ) (h.C : ℝ))

/-! ## Genuine dual concavity -/

private theorem regularizedPathQuad_combo_le (n : Nat) (u v : EVec n)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    regularizedPathQuad n (a • u + b • v) ≤
      a * regularizedPathQuad n u + b * regularizedPathQuad n v := by
  rw [regularizedPathQuad_add_expansion,
    regularizedPathQuad_smul, regularizedPathQuad_smul,
    regularizedPathBilinear_smul_left,
    regularizedPathBilinear_smul_right]
  have hq := regularizedPathQuad_nonneg n (u - v)
  rw [regularizedPathQuad_sub_expansion] at hq
  have hab0 : 0 ≤ a * b := mul_nonneg ha hb
  have hmul := mul_nonneg hab0 hq
  have haid : a ^ 2 + a * b = a := by
    calc
      a ^ 2 + a * b = a * (a + b) := by ring
      _ = a := by rw [hab, mul_one]
  have hbid : b ^ 2 + a * b = b := by
    calc
      b ^ 2 + a * b = b * (a + b) := by ring
      _ = b := by rw [hab, mul_one]
  have hrearrange :
      a ^ 2 * regularizedPathQuad n u +
          b ^ 2 * regularizedPathQuad n v +
          2 * (a * (b * regularizedPathBilinear n u v)) =
        a * regularizedPathQuad n u + b * regularizedPathQuad n v -
          a * b * (regularizedPathQuad n u + regularizedPathQuad n v -
            2 * regularizedPathBilinear n u v) := by
    calc
      _ = (a ^ 2 + a * b) * regularizedPathQuad n u +
            (b ^ 2 + a * b) * regularizedPathQuad n v -
            a * b * (regularizedPathQuad n u + regularizedPathQuad n v -
              2 * regularizedPathBilinear n u v) := by ring
      _ = _ := by rw [haid, hbid]
  rw [hrearrange]
  linarith

private theorem innerForcing_combo {n : Nat} (hn : 0 < n) (q r : ℝ)
    (u v : EVec n) (a b : ℝ) :
    innerForcing hn q r (a • u + b • v) =
      a * innerForcing hn q r u + b * innerForcing hn q r v := by
  unfold innerForcing
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem innerChain_concaveOn_univ {n : Nat} (hn : 0 < n)
    (C q r : ℝ) :
    ConcaveOn ℝ Set.univ (innerChain hn C q r) := by
  rw [concaveOn_iff_forall_pos]
  refine ⟨convex_univ, ?_⟩
  intro u _ v _ a b ha hb hab
  have hquad := regularizedPathQuad_combo_le n u v ha.le hb.le hab
  simp only [innerChain, smul_eq_mul]
  rw [innerForcing_combo hn]
  nlinarith

private theorem dualBlock_combo {T n : Nat} (y z : UnscaledDual T n)
    (i : Fin (T - 1)) (a b : ℝ) :
    dualBlock (a • y + b • z) i = a • dualBlock y i + b • dualBlock z i := by
  funext k
  simp [dualBlock]

/-- The part of the unscaled objective independent of the dual variable. -/
def unscaledOuterValue {T n : Nat} (hn : 0 < n) (P : UnscaledParameters)
    (x : UnscaledPrimal T) : ℝ :=
  -P.eta * (∑ i : Fin (T - 1), Psi1 (clippedNext P x i)) +
    (∑ i : Fin (T - 1), Sigma2 P.tauS (primalState x i)) +
    P.mu * (∑ i : Fin (T - 1),
      Psi2 (clippedNext P x i) * Sigma1 P.theta (clippedCurrent P x i)) +
    (∑ i : Fin (T - 1), (
      entrancePulse P.alpha P.theta P.P0 (clippedCurrent P x i)
          (clippedNext P x i) (primalA x i) +
        innerC1 hn * (primalA x i) ^ 2 +
        innerC2 hn * (primalB x i) ^ 2 +
        P.gamma * ((primalA x i) ^ 2 + (primalB x i) ^ 2) +
        exitPulse P.beta P.theta (clippedCurrent P x i) (primalB x i)
          (clippedNext P x i))) +
    Sigma3 P.P0 P.P1 P.K (pulseSq x)

theorem unscaledObjective_eq_outer_add_inner {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) (y : UnscaledDual T n) :
    unscaledObjective hn P x y =
      unscaledOuterValue hn P x +
        ∑ i : Fin (T - 1),
          innerChain hn (innerC hn) (primalA x i) (primalB x i)
            (dualBlock y i) := by
  have hsplit :
      (∑ i : Fin (T - 1), unscaledBlock hn P x y i) =
        (∑ i : Fin (T - 1),
          innerChain hn (innerC hn) (primalA x i) (primalB x i)
            (dualBlock y i)) +
        (∑ i : Fin (T - 1), (
          entrancePulse P.alpha P.theta P.P0 (clippedCurrent P x i)
              (clippedNext P x i) (primalA x i) +
            innerC1 hn * (primalA x i) ^ 2 +
            innerC2 hn * (primalB x i) ^ 2 +
            P.gamma * ((primalA x i) ^ 2 + (primalB x i) ^ 2) +
            exitPulse P.beta P.theta (clippedCurrent P x i) (primalB x i)
              (clippedNext P x i))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold unscaledBlock
    ring
  rw [unscaledObjective, hsplit]
  unfold unscaledOuterValue
  ring

/- The dual strong-concavity calculation in TeX lines 2926--2928 implies,
in particular, the exact `ConcaveOn` field required by `ScalingSource`.
This theorem proves that conclusion directly from the path quadratic, with
no concavity hypothesis on the objective. -/
set_option maxHeartbeats 0 in
theorem unscaledObjective_dual_concave {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) (x : UnscaledPrimal T) (D : ℝ) :
    ConcaveOn ℝ (unscaledDualDomain T n D)
      (unscaledObjective hn P x) := by
  rw [concaveOn_iff_forall_pos]
  refine ⟨unscaledDualDomain_convex T n D, ?_⟩
  intro y _ z _ a b ha hb hab
  have hblocks :
      ∀ i : Fin (T - 1),
        a * innerChain hn (innerC hn) (primalA x i) (primalB x i)
              (dualBlock y i) +
            b * innerChain hn (innerC hn) (primalA x i) (primalB x i)
              (dualBlock z i) ≤
          innerChain hn (innerC hn) (primalA x i) (primalB x i)
            (dualBlock (a • y + b • z) i) := by
    intro i
    have hconc := (innerChain_concaveOn_univ hn (innerC hn)
      (primalA x i) (primalB x i)).2
      (Set.mem_univ (dualBlock y i)) (Set.mem_univ (dualBlock z i))
      ha.le hb.le hab
    rw [← dualBlock_combo] at hconc
    simpa only [smul_eq_mul] using hconc
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) ↦ hblocks i
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [unscaledObjective_eq_outer_add_inner,
    unscaledObjective_eq_outer_add_inner,
    unscaledObjective_eq_outer_add_inner]
  simp only [smul_eq_mul]
  let A : ℝ := unscaledOuterValue hn P x
  let Sy : ℝ := ∑ i : Fin (T - 1),
    innerChain hn (innerC hn) (primalA x i) (primalB x i) (dualBlock y i)
  let Sz : ℝ := ∑ i : Fin (T - 1),
    innerChain hn (innerC hn) (primalA x i) (primalB x i) (dualBlock z i)
  let Sc : ℝ := ∑ i : Fin (T - 1),
    innerChain hn (innerC hn) (primalA x i) (primalB x i)
      (dualBlock (a • y + b • z) i)
  change a * Sy + b * Sz ≤ Sc at hsum
  change a * (A + Sy) + b * (A + Sz) ≤ A + Sc
  have hweight : a * A + b * A = A := by
    rw [← add_mul, hab, one_mul]
  have hmain : a * (A + Sy) + b * (A + Sz) ≤ A + Sc := by
    calc
      a * (A + Sy) + b * (A + Sz) =
          (a * A + b * A) + (a * Sy + b * Sz) := by ring
      _ = A + (a * Sy + b * Sz) := by rw [hweight]
      _ ≤ A + Sc := by
        simpa only [add_comm] using add_le_add_left hsum A
  exact hmain

/-- All non-analytic fields of `ScalingSource`, bundled so the remaining
global smoothness/value proof cannot silently replace the paper's domains. -/
theorem unscaledNCCInstance_domain_data {T n : Nat} (hn : 0 < n)
    (P : UnscaledParameters) {D : ℝ} (hD : 0 ≤ D) :
    (unscaledNCCInstance (T := T) hn P D).x0 ∈
        (unscaledNCCInstance (T := T) hn P D).X ∧
    (unscaledNCCInstance (T := T) hn P D).X.Nonempty ∧
    IsClosed (unscaledNCCInstance (T := T) hn P D).X ∧
    Convex ℝ (unscaledNCCInstance (T := T) hn P D).X ∧
    (unscaledNCCInstance (T := T) hn P D).Y.Nonempty ∧
    IsClosed (unscaledNCCInstance (T := T) hn P D).Y ∧
    Convex ℝ (unscaledNCCInstance (T := T) hn P D).Y ∧
    (∀ y ∈ (unscaledNCCInstance (T := T) hn P D).Y,
      ∀ y' ∈ (unscaledNCCInstance (T := T) hn P D).Y,
        vecSq (y - y') ≤ D ^ 2) := by
  exact ⟨zero_mem_unscaledPrimalDomain T, unscaledPrimalDomain_nonempty T,
    unscaledPrimalDomain_closed T, unscaledPrimalDomain_convex T,
    unscaledDualDomain_nonempty hD, unscaledDualDomain_closed T n D,
    unscaledDualDomain_convex T n D,
    fun _ hy _ hy' ↦ unscaledDualDomain_diameter hD hy hy'⟩

end

end NCCLowerBoundVerification
