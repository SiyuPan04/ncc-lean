import NCC.Moreau.Within
import NCCLowerBoundVerification.Upper.PerturbationBias

/-!
# Dual regularization and actual Moreau gradients on closed domains

Source: `lem:smoothing`. Every maximum and proximal minimum in this module
is derived using only the feasible-domain class. In particular, the bias
comparison is only used at feasible proximal points; it does not require
an extension of the objective outside its domain.
-/

namespace NCC.Upper.WithinRegularization

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper

variable {m n : Nat} {ell D Delta r : ℝ} {P : NCCInstance m n}

theorem regularized_joint_continuousOn (h : Model.WithinClass ell D Delta P) :
    ContinuousOn (Function.uncurry (fun x y => P.f x y - r / 2 * vecSq y))
      (P.X ×ˢ P.Y) :=
  h.gradient_representation.continuousOn.sub
    (continuous_const.mul (continuous_vecSq.comp continuous_snd)).continuousOn

theorem maximum_attained (h : Model.WithinClass ell D Delta P)
    {x : EVec m} (hx : x ∈ P.X) :
    ∃ y, IsMaximizerOn P.Y (fun u v => P.f u v - r / 2 * vecSq v) x y := by
  have hc : ContinuousOn (fun y => P.f x y - r / 2 * vecSq y) P.Y :=
    (regularized_joint_continuousOn h).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hy => ⟨hx, hy⟩)
  obtain ⟨y, hy, hm⟩ := h.dual_compact.exists_isMaxOn ⟨0, h.dual_origin⟩ hc
  exact ⟨y, hy, fun _ hv => hm hv⟩

theorem value_continuousOn (h : Model.WithinClass ell D Delta P) :
    ContinuousOn (DualRegularizedValueOn P.Y P.f r) P.X :=
  Model.value_continuousOn_of_joint_continuousOn h.dual_compact
    (regularized_joint_continuousOn h)

theorem section_weaklyConvex (h : Model.WithinClass ell D Delta P)
    {y : EVec n} (hy : y ∈ P.Y) :
    IsWeaklyConvexOn ell P.X (fun x => P.f x y - r / 2 * vecSq y) := by
  have hb := Model.section_weaklyConvex_of_within h.ell_pos h.X_convex
    h.gradient_representation h.jointly_smooth hy
  have hc := hb.add_const (-(r / 2 * vecSq y))
  unfold IsWeaklyConvexOn
  apply hc.congr
  intro x _
  change (P.f x y + quadraticCorrection ell x) + (-(r / 2 * vecSq y)) =
    P.f x y - r / 2 * vecSq y + quadraticCorrection ell x
  ring

theorem value_weaklyConvex (h : Model.WithinClass ell D Delta P) :
    IsWeaklyConvexOn ell P.X (DualRegularizedValueOn P.Y P.f r) :=
  value_weaklyConvexOn_of_sections h.X_convex
    (fun _ hx => maximum_attained h hx) (fun _ hy => section_weaklyConvex h hy)

theorem value_bias (h : Model.WithinClass ell D Delta P) (hr : 0 ≤ r)
    {x : EVec m} (hx : x ∈ P.X) :
    0 ≤ ValueOn P.Y P.f x - DualRegularizedValueOn P.Y P.f r x ∧
      ValueOn P.Y P.f x - DualRegularizedValueOn P.Y P.f r x ≤ r / 2 * D ^ 2 := by
  apply dualRegularizedValue_bias hr ?_ (h.maximum_attained hx) (maximum_attained h hx)
  intro y hy
  simpa only [sub_zero] using h.dual_diameter y hy 0 h.dual_origin

theorem prox_exists (h : Model.WithinClass ell D Delta P) (hr : 0 ≤ r) :
    HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell := by
  apply hasProxEverywhere_of_continuousOn_bddBelow ⟨0, h.primal_origin⟩
    h.X_closed h.ell_pos (value_continuousOn h)
    (lower := ValueOn P.Y P.f 0 - Delta - r / 2 * D ^ 2)
  intro x hx
  linarith [h.initial_gap_pointwise x hx, (value_bias h hr hx).2]

def prox (h : Model.WithinClass ell D Delta P) (hr : 0 ≤ r) (z : EVec m) : EVec m :=
  selectedProx (prox_exists h hr) z

def envelope (h : Model.WithinClass ell D Delta P) (hr : 0 ≤ r) (z : EVec m) : ℝ :=
  moreauEnvelope (DualRegularizedValueOn P.Y P.f r) ell (prox_exists h hr) z

def gradient (h : Model.WithinClass ell D Delta P) (hr : 0 ≤ r) (z : EVec m) : EVec m :=
  residualGradient (prox_exists h hr) z

theorem prox_spec (h : Model.WithinClass ell D Delta P) (hr : 0 ≤ r) (z : EVec m) :
    IsProxPoint P.X (DualRegularizedValueOn P.Y P.f r) ell z (prox h hr z) :=
  selectedProx_spec (prox_exists h hr) z

theorem gradient_formula (h : Model.WithinClass ell D Delta P) (hr : 0 ≤ r) (z : EVec m) :
    gradient h hr z = (2 * ell) • (z - prox h hr z) := rfl

theorem hasFDerivAt_envelope (h : Model.WithinClass ell D Delta P) (hr : 0 ≤ r) (z : EVec m) :
    HasFDerivAt (envelope h hr) (residualCLM (gradient h hr z)) z :=
  hasFDerivAt_moreauEnvelope h.ell_pos (value_weaklyConvex h) (prox_exists h hr) z

theorem gradient_lipschitz_sq (h : Model.WithinClass ell D Delta P)
    (hr : 0 ≤ r) (z w : EVec m) :
    vecSq (gradient h hr z - gradient h hr w) ≤ (2 * ell) ^ 2 * vecSq (z - w) :=
  residualGradient_lipschitz_sq h.ell_pos (value_weaklyConvex h) (prox_exists h hr) z w

/-- Squared form of the manuscript's Moreau gradient bias
`D * sqrt(2*ell*r)`, for actual derivatives of both envelopes. -/
theorem gradient_bias_squared (h : Model.WithinClass ell D Delta P)
    (hr : 0 ≤ r) (z : EVec m) :
    vecSq (Moreau.Within.gradient h z - gradient h hr z) ≤ 2 * ell * r * D ^ 2 := by
  let u := Moreau.Within.prox h z
  let v := prox h hr z
  have hu := Moreau.Within.prox_spec h z
  have hv := prox_spec h hr z
  have hsu := proxPoint_strongMinimizer_expanded h.ell_pos h.value_weaklyConvex hu hv.1
  have hsv := proxPoint_strongMinimizer_expanded h.ell_pos (value_weaklyConvex h) hv hu.1
  have hbu := (value_bias h hr hu.1).1
  have hbv := (value_bias h hr hv.1).2
  have hsym := vecSq_sub_comm u v
  have hd : ell * vecSq (u - v) ≤ r / 2 * D ^ 2 := by
    change _ + ell / 2 * vecSq (v - u) ≤ _ at hsu
    change _ + ell / 2 * vecSq (u - v) ≤ _ at hsv
    rw [← hsym] at hsu
    linarith
  have hb := scaledResidualDifference_vecSq_le h.ell_pos.le (z := z) hd
  rw [Moreau.Within.gradient_formula, gradient_formula]
  calc
    _ ≤ 4 * ell * (r / 2 * D ^ 2) := hb
    _ = 2 * ell * r * D ^ 2 := by ring

/-- Unsquared Euclidean statement of `lem:smoothing`. -/
theorem gradient_bias (h : Model.WithinClass ell D Delta P)
    (hr : 0 ≤ r) (z : EVec m) :
    Real.sqrt (vecSq (Moreau.Within.gradient h z - gradient h hr z)) ≤
      D * Real.sqrt (2 * ell * r) := by
  have hell := h.ell_pos
  have hD := h.D_pos
  have hs := gradient_bias_squared h hr z
  have hleft := Real.sq_sqrt (vecSq_nonneg (Moreau.Within.gradient h z - gradient h hr z))
  have hright := Real.sq_sqrt (show 0 ≤ 2 * ell * r by positivity)
  have hp : 0 ≤ D * Real.sqrt (2 * ell * r) := by positivity
  have hl := Real.sqrt_nonneg (vecSq (Moreau.Within.gradient h z - gradient h hr z))
  nlinarith

/-- The actual prescribed accuracy for regularization bounds its squared
gradient bias by `eps^2/4`. -/
theorem gradient_bias_at_target (h : Model.WithinClass ell D Delta P)
    (hr : 0 ≤ r) {eps : ℝ}
    (htarget : r ≤ eps ^ 2 / (8 * ell * D ^ 2)) (z : EVec m) :
    vecSq (Moreau.Within.gradient h z - gradient h hr z) ≤ eps ^ 2 / 4 := by
  have hell := h.ell_pos
  have hD := h.D_pos
  have ht := (le_div_iff₀ (by positivity : 0 < 8 * ell * D ^ 2)).1 htarget
  have hb := gradient_bias_squared h hr z
  nlinarith

theorem os_of_regularized_gradient (h : Model.WithinClass ell D Delta P)
    (hr : 0 ≤ r) {eps : ℝ} (heps : 0 < eps)
    (htarget : r ≤ eps ^ 2 / (8 * ell * D ^ 2)) {z : EVec m} (hz : z ∈ P.X)
    (hsmall : vecSq (gradient h hr z) ≤ eps ^ 2 / 4) :
    Moreau.Within.IsOS h eps z := by
  refine ⟨heps, hz, ?_⟩
  have hb := gradient_bias_at_target h hr htarget z
  have hadd : vecSq (Moreau.Within.gradient h z) ≤
      2 * vecSq (Moreau.Within.gradient h z - gradient h hr z) +
        2 * vecSq (gradient h hr z) := by
    unfold vecSq NCPLVerification.vecSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    simp only [Pi.sub_apply]
    nlinarith [sq_nonneg (Moreau.Within.gradient h z i - 2 * gradient h hr z i)]
  linarith

end

end NCC.Upper.WithinRegularization
