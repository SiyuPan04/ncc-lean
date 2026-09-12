import NCCLowerBoundVerification.Basic

/-!
# The effective pulse link

This module verifies Definition `def:Q` and the algebraic content of Lemma
`lem:Q` in `Upper+Lower_unified_lower.tex`.  The Hessian Loewner bounds are
stated as the equivalent inequalities for its quadratic form on an arbitrary
direction `(u, v)`.
-/

namespace NCCLowerBoundVerification

noncomputable section

/-- Definition `def:Q`: the effective two-dimensional pulse link. -/
def effectivePulse (gamma a b : ℝ) : ℝ :=
  6 * (a - b / 2) ^ 2 + gamma * (a ^ 2 + b ^ 2)

/-- The `a`-coordinate derivative displayed in Lemma `lem:Q`. -/
def effectivePulseGradA (gamma a b : ℝ) : ℝ :=
  12 * (a - b / 2) + 2 * gamma * a

/-- The `b`-coordinate derivative displayed in Lemma `lem:Q`. -/
def effectivePulseGradB (gamma a b : ℝ) : ℝ :=
  -6 * (a - b / 2) + 2 * gamma * b

/-- The Hessian quadratic form of `effectivePulse` in direction `(u, v)`. -/
def effectivePulseHessianQuad (gamma u v : ℝ) : ℝ :=
  (12 + 2 * gamma) * u ^ 2 - 12 * u * v + (3 + 2 * gamma) * v ^ 2

/-- The formula defining `effectivePulse` is available without unfolding. -/
theorem effectivePulse_formula (gamma a b : ℝ) :
    effectivePulse gamma a b =
      6 * (a - b / 2) ^ 2 + gamma * (a ^ 2 + b ^ 2) := by
  rfl

/-- Direct differentiation in the first coordinate. -/
theorem hasDerivAt_effectivePulse_left (gamma a b : ℝ) :
    HasDerivAt (fun x : ℝ ↦ effectivePulse gamma x b)
      (effectivePulseGradA gamma a b) a := by
  unfold effectivePulse effectivePulseGradA
  have hlin : HasDerivAt (fun x : ℝ ↦ x - b / 2) 1 a := by
    simpa using (hasDerivAt_id a).sub_const (b / 2)
  have hsix : HasDerivAt (fun x : ℝ ↦ 6 * (x - b / 2) ^ 2)
      (6 * (2 * (a - b / 2))) a := by
    convert (hlin.pow 2).const_mul 6 using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    all_goals simp [Pi.pow_apply]
  have hgamma : HasDerivAt (fun x : ℝ ↦ gamma * (x ^ 2 + b ^ 2))
      (gamma * (2 * a)) a := by
    have hsum := ((hasDerivAt_id a).pow 2).add_const (b ^ 2)
    convert hsum.const_mul gamma using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    all_goals simp [Pi.pow_apply]
  convert hsix.add hgamma using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext x
    simp only [Pi.add_apply]
  · ring

/-- Direct differentiation in the second coordinate. -/
theorem hasDerivAt_effectivePulse_right (gamma a b : ℝ) :
    HasDerivAt (fun y : ℝ ↦ effectivePulse gamma a y)
      (effectivePulseGradB gamma a b) b := by
  unfold effectivePulse effectivePulseGradB
  have hlin : HasDerivAt (fun y : ℝ ↦ a - y / 2) (-(1 / 2 : ℝ)) b := by
    convert (hasDerivAt_const b a).sub ((hasDerivAt_id b).div_const 2) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext y
      simp only [Pi.sub_apply, id_eq]
    · ring
  have hsix : HasDerivAt (fun y : ℝ ↦ 6 * (a - y / 2) ^ 2)
      (6 * (2 * (a - b / 2) * (-(1 / 2 : ℝ)))) b := by
    convert (hlin.pow 2).const_mul 6 using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    all_goals simp [Pi.pow_apply]
  have hgamma : HasDerivAt (fun y : ℝ ↦ gamma * (a ^ 2 + y ^ 2))
      (gamma * (2 * b)) b := by
    have hsum := (hasDerivAt_const b (a ^ 2)).add ((hasDerivAt_id b).pow 2)
    convert hsum.const_mul gamma using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    all_goals simp [Pi.pow_apply]
  convert hsix.add hgamma using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext y
    simp only [Pi.add_apply]
  · ring

/-- The principal coupling cancels in `∂ₐQ + 2 ∂ᵦQ`. -/
theorem effectivePulse_weighted_gradient_cancellation (gamma a b : ℝ) :
    effectivePulseGradA gamma a b + 2 * effectivePulseGradB gamma a b =
      2 * gamma * a + 4 * gamma * b := by
  unfold effectivePulseGradA effectivePulseGradB
  ring

/-- Algebraic decomposition exposing the two Hessian eigen-directions. -/
theorem effectivePulseHessianQuad_decomposition (gamma u v : ℝ) :
    effectivePulseHessianQuad gamma u v =
      3 * (2 * u - v) ^ 2 + 2 * gamma * (u ^ 2 + v ^ 2) := by
  unfold effectivePulseHessianQuad
  ring

/-- The lower Loewner bound `2γ I₂ ≼ ∇²Q`, in quadratic-form form. -/
theorem effectivePulseHessianQuad_lower (gamma u v : ℝ) :
    2 * gamma * (u ^ 2 + v ^ 2) ≤
      effectivePulseHessianQuad gamma u v := by
  rw [effectivePulseHessianQuad_decomposition]
  nlinarith [sq_nonneg (2 * u - v)]

/-- The upper Loewner bound `∇²Q ≼ 16 I₂` under `γ ≤ 1/2`. -/
theorem effectivePulseHessianQuad_upper {gamma : ℝ}
    (hgamma : gamma ≤ 1 / 2) (u v : ℝ) :
    effectivePulseHessianQuad gamma u v ≤ 16 * (u ^ 2 + v ^ 2) := by
  rw [effectivePulseHessianQuad_decomposition]
  have hnorm : 0 ≤ u ^ 2 + v ^ 2 := by positivity
  have hbase : 3 * (2 * u - v) ^ 2 ≤ 15 * (u ^ 2 + v ^ 2) := by
    nlinarith [sq_nonneg (u + 2 * v)]
  nlinarith

/-- Lemma `lem:Q`'s complete curvature certificate for `0 < γ ≤ 1/2`. -/
theorem effectivePulse_curvature_bounds {gamma : ℝ}
    (_hgamma_pos : 0 < gamma) (hgamma_half : gamma ≤ 1 / 2) (u v : ℝ) :
    2 * gamma * (u ^ 2 + v ^ 2) ≤
        effectivePulseHessianQuad gamma u v ∧
      effectivePulseHessianQuad gamma u v ≤ 16 * (u ^ 2 + v ^ 2) := by
  exact ⟨effectivePulseHessianQuad_lower gamma u v,
    effectivePulseHessianQuad_upper hgamma_half u v⟩

end

end NCCLowerBoundVerification
