import NCCLowerBoundVerification.Lower.ClipSoftHinge
import NCCLowerBoundVerification.Lower.SmoothStep

/-!
# Left-wall margins

This module proves `lem:wall-properties` from the concrete state clip and
soft-hinge definitions.  The two cases in the paper are kept explicit: in
the far-left tail the wall derivative is already `-1`; outside that tail the
state clip is in its identity interval.
-/

namespace NCCLowerBoundVerification

noncomputable section

theorem Sigma1Deriv_nonpos (theta t : ℝ) :
    Sigma1Deriv theta t ≤ 0 :=
  (leftHingeDeriv_mem 1 (1 + theta) t).2

theorem Sigma2Deriv_nonpos (tau t : ℝ) :
    Sigma2Deriv tau t ≤ 0 :=
  (leftHingeDeriv_mem (-tau) 0 t).2

theorem pi1_argument_le_stateUpper {delta P0 t : ℝ}
    (hdelta : 0 < delta) (hP0 : 1 < P0)
    (hpi : pi1 delta P0 t ≤ 1) : t ≤ stateUpper := by
  change t ≤ 3
  by_contra ht
  have hthree : pi1 delta P0 3 = 3 := by
    apply pi1_eq_self hdelta hP0
    · unfold stateLower
      linarith
    · exact le_rfl
  have hmono := pi1_monotone hdelta hP0 (le_of_not_ge ht)
  rw [hthree] at hmono
  linarith

theorem stateLower_le_of_neg_tauS_le {delta t : ℝ}
    (hdelta : 0 < delta) (ht : -tauS delta ≤ t) :
    stateLower delta ≤ t := by
  rw [stateLower_eq_neg_two_tauS]
  have htau : 0 < tauS delta := by
    unfold tauS
    linarith
  linarith

/-- Equation `eq:wall-order-interface`. -/
theorem wall_order_margin {theta delta P0 mu xi t : ℝ}
    (htheta : 0 < theta) (hdelta : 0 < delta) (hP0 : 1 < P0)
    (hmargin : 1 ≤ mu * xi) (hpi : pi1 delta P0 t ≤ 1) :
    Sigma2Deriv (tauS delta) t +
        mu * xi * Sigma1Deriv theta (pi1 delta P0 t) *
          pi1Deriv delta P0 t ≤ -1 := by
  have hscale : 0 ≤ mu * xi := le_trans (by norm_num) hmargin
  have hpiDeriv : 0 ≤ pi1Deriv delta P0 t :=
    (pi1Deriv_mem_unitInterval delta P0 t).1
  by_cases htail : t ≤ -tauS delta
  · rw [Sigma2Deriv_eq_neg_one (by unfold tauS; linarith) htail]
    have hhinge : Sigma1Deriv theta (pi1 delta P0 t) ≤ 0 :=
      Sigma1Deriv_nonpos _ _
    have : mu * xi * Sigma1Deriv theta (pi1 delta P0 t) *
        pi1Deriv delta P0 t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos hscale hhinge) hpiDeriv
    linarith
  · have hlow : stateLower delta ≤ t :=
      stateLower_le_of_neg_tauS_le hdelta (le_of_not_ge htail)
    have hhigh : t ≤ stateUpper :=
      pi1_argument_le_stateUpper hdelta hP0 hpi
    have hclip : pi1 delta P0 t = t :=
      pi1_eq_self hdelta hP0 hlow hhigh
    have hclipDeriv : pi1Deriv delta P0 t = 1 :=
      pi1Deriv_eq_one hdelta hP0 hlow hhigh
    have hwall : Sigma2Deriv (tauS delta) t ≤ 0 :=
      Sigma2Deriv_nonpos _ _
    rw [hclip, hclipDeriv, Sigma1Deriv_eq_neg_one htheta (by simpa [hclip] using hpi)]
    nlinarith

/-- Equation `eq:wall-exit-interface`. -/
theorem wall_exit_margin {theta delta P0 beta xi t : ℝ}
    (htheta : 0 < theta) (hdelta : 0 < delta) (hP0 : 1 < P0)
    (hmargin : 1 ≤ beta * xi ^ 2) (hpi : pi1 delta P0 t ≤ 1) :
    Sigma2Deriv (tauS delta) t -
        beta * xi ^ 2 * Lambda2 theta (pi1 delta P0 t) *
          pi1Deriv delta P0 t ≤ -1 := by
  have hscale : 0 ≤ beta * xi ^ 2 := le_trans (by norm_num) hmargin
  have hpiDeriv : 0 ≤ pi1Deriv delta P0 t :=
    (pi1Deriv_mem_unitInterval delta P0 t).1
  have hLambda : 0 ≤ Lambda2 theta (pi1 delta P0 t) :=
    (Lambda2_mem_unitInterval _ _).1
  by_cases htail : t ≤ -tauS delta
  · rw [Sigma2Deriv_eq_neg_one (by unfold tauS; linarith) htail]
    have : 0 ≤ beta * xi ^ 2 * Lambda2 theta (pi1 delta P0 t) *
        pi1Deriv delta P0 t :=
      mul_nonneg (mul_nonneg hscale hLambda) hpiDeriv
    linarith
  · have hlow : stateLower delta ≤ t :=
      stateLower_le_of_neg_tauS_le hdelta (le_of_not_ge htail)
    have hhigh : t ≤ stateUpper :=
      pi1_argument_le_stateUpper hdelta hP0 hpi
    have hclipDeriv : pi1Deriv delta P0 t = 1 :=
      pi1Deriv_eq_one hdelta hP0 hlow hhigh
    have hwall : Sigma2Deriv (tauS delta) t ≤ 0 :=
      Sigma2Deriv_nonpos _ _
    rw [hclipDeriv, Lambda2_eq_one_of_le_one htheta hpi]
    nlinarith

end

end NCCLowerBoundVerification
