import NCC.Construction.Scalar.Quantitative
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compact derivative supports for the literal scalar construction

The first derivative of `q` vanishes outside `[1/5,1]`, and the first
derivatives of `e_s` and `e_nu` vanish outside `[-3,3]` and `[-22,22]`.
Consequently every positive-order derivative has compact support and is
uniformly bounded. This includes the plateau endpoints themselves.
-/

namespace NCC.Construction

noncomputable section

open Set

theorem hasCompactSupport_deriv_q : HasCompactSupport (deriv q) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Icc (1 / 5 : ℝ) 1))
  intro t ht
  by_cases hlo : t < 1 / 5
  · exact deriv_q_eq_zero_left hlo.le
  have hhi : 1 < t := lt_of_not_ge fun hb => ht ⟨le_of_not_gt hlo, hb⟩
  exact deriv_q_eq_zero_right hhi.le

theorem hasCompactSupport_deriv_identityExtension {radius : ℝ} (hr : 0 ≤ radius) :
    HasCompactSupport (deriv (identityExtension radius)) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Icc (-(radius + 1)) (radius + 1)))
  intro t ht
  by_cases hlo : t < -(radius + 1)
  · exact deriv_identityExtension_eq_zero_left hr hlo.le
  have hhi : radius + 1 < t := lt_of_not_ge fun hb => ht ⟨le_of_not_gt hlo, hb⟩
  exact deriv_identityExtension_eq_zero_right hr hhi.le

theorem hasCompactSupport_deriv_e_s : HasCompactSupport (deriv e_s) := by
  rw [e_s_eq_identityExtension]
  exact hasCompactSupport_deriv_identityExtension (by norm_num)

theorem hasCompactSupport_deriv_e_nu : HasCompactSupport (deriv e_nu) := by
  rw [e_nu_eq_identityExtension]
  exact hasCompactSupport_deriv_identityExtension (by norm_num)

/-- Compact first-derivative support propagates to every positive order.
No differentiability assumption is needed for the support implication. -/
theorem hasCompactSupport_positive_iteratedDeriv {f : ℝ → ℝ}
    (hf : HasCompactSupport (deriv f)) (k : ℕ) :
    HasCompactSupport (iteratedDeriv (k + 1) f) := by
  induction k with
  | zero => simpa only [Nat.zero_add, iteratedDeriv_one] using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem q_positive_iteratedDeriv_hasCompactSupport (k : ℕ) :
    HasCompactSupport (iteratedDeriv (k + 1) q) :=
  hasCompactSupport_positive_iteratedDeriv hasCompactSupport_deriv_q k

theorem e_s_positive_iteratedDeriv_hasCompactSupport (k : ℕ) :
    HasCompactSupport (iteratedDeriv (k + 1) e_s) :=
  hasCompactSupport_positive_iteratedDeriv hasCompactSupport_deriv_e_s k

theorem e_nu_positive_iteratedDeriv_hasCompactSupport (k : ℕ) :
    HasCompactSupport (iteratedDeriv (k + 1) e_nu) :=
  hasCompactSupport_positive_iteratedDeriv hasCompactSupport_deriv_e_nu k

/-- Smoothness and compact derivative support give a finite global
bound separately at each positive derivative order. -/
theorem positive_iteratedDeriv_bounded {f : ℝ → ℝ}
    (hf : HasCompactSupport (deriv f)) (hc : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |iteratedDeriv (k + 1) f t| ≤ C := by
  have hcont := (hc.of_le (WithTop.coe_le_coe.mpr le_top)).continuous_iteratedDeriv' (k + 1)
  simpa only [Real.norm_eq_abs] using
    (hasCompactSupport_positive_iteratedDeriv hf k).exists_bound_of_continuous hcont

theorem q_positive_iteratedDeriv_bounded (k : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |iteratedDeriv (k + 1) q t| ≤ C :=
  positive_iteratedDeriv_bounded hasCompactSupport_deriv_q q_contDiff k

theorem e_s_positive_iteratedDeriv_bounded (k : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |iteratedDeriv (k + 1) e_s t| ≤ C := by
  rw [e_s_eq_identityExtension]
  exact positive_iteratedDeriv_bounded
    (hasCompactSupport_deriv_identityExtension (by norm_num : (0 : ℝ) ≤ 2))
    (identityExtension_contDiff 2) k

theorem e_nu_positive_iteratedDeriv_bounded (k : ℕ) :
    ∃ C : ℝ, ∀ t : ℝ, |iteratedDeriv (k + 1) e_nu t| ≤ C := by
  rw [e_nu_eq_identityExtension]
  exact positive_iteratedDeriv_bounded
    (hasCompactSupport_deriv_identityExtension (by norm_num : (0 : ℝ) ≤ 21))
    (identityExtension_contDiff 21) k

end

end NCC.Construction
