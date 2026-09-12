import NCC.Lower.Rotation

/-!
# Full source rotation invariance under feasible-domain derivatives

The projected product map sends the ambient primal-space/dual-ball domain
into the original feasible domain. Its within-domain chain rule gives the
actual rotated gradients without any global representative or extension.
All parameters are preserved exactly.
-/
namespace NCC.Lower.WithinRotation
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open NCPLVerification
set_option maxHeartbeats 3000000

variable {m n M N : ℕ} {ell D Delta : ℝ} {P : NCCInstance m n}
  {U : Fin m → NCCLowerBoundVerification.EVec M}
  {V : Fin n → NCCLowerBoundVerification.EVec N}

theorem projected_feasible (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    (hV : IsOrthonormalFrame V) :
    Set.MapsTo (frameProductProjectCLM U V)
      (Set.univ ×ˢ diameterBall N D) (P.X ×ˢ P.Y) := by
  intro p hp
  refine ⟨?_, ?_⟩
  · rw [hX]
    trivial
  · rw [hY]
    exact frameProject_mem_diameterBall hV hp.2

theorem gradient_representation (h : RepresentsJointGradientWithin P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    (hV : IsOrthonormalFrame V) :
    RepresentsJointGradientWithin (rotatedNCCInstance D U V P) := by
  intro x hx y hy
  have hmem := projected_feasible (U := U) hX hY hV (show (x, y) ∈
      Set.univ ×ˢ diameterBall N D from ⟨hx, hy⟩)
  have hb := h (frameProject U x) hmem.1 (frameProject V y) hmem.2
  have hc := hb.comp (x, y)
    ((frameProductProjectCLM U V).hasFDerivAt.hasFDerivWithinAt)
    (projected_feasible (U := U) hX hY hV)
  convert! hc using 1
  apply ContinuousLinearMap.ext
  rintro ⟨dx, dy⟩
  simp only [ContinuousLinearMap.comp_apply, frameProductProjectCLM_apply,
    jointGradientCLM_apply, rotatedNCCInstance, rotatedGradX, rotatedGradY]
  change evecDotValue (frameEmbed U (P.gradX (frameProject U x) (frameProject V y))) dx +
      evecDotValue (frameEmbed V (P.gradY (frameProject U x) (frameProject V y))) dy = _
  rw [evecDotValue_frameEmbed_left, evecDotValue_frameEmbed_left]
  rfl

/-- Exact class closure, with precisely the source within-domain class and
orthogonal-frame assumptions. No ambient differentiability premise occurs. -/
theorem class_rotate (h : WithinClass ell D Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V) :
    WithinClass ell D Delta (rotatedNCCInstance D U V P) := by
  refine {
    ell_pos := h.ell_pos
    D_pos := h.D_pos
    Delta_pos := h.Delta_pos
    primal_origin := Set.mem_univ _
    dual_origin := zero_mem_diameterBall N D h.D_pos.le
    initialization := rfl
    X_closed := isClosed_univ
    X_convex := convex_univ
    Y_closed := diameterBall_closed N D
    Y_convex := diameterBall_convex N D
    gradient_representation := gradient_representation h.gradient_representation hX hY hV
    jointly_smooth := ?_
    dual_concave := ?_
    dual_diameter := ?_
    initial_gap_pointwise := ?_ }
  · intro x hx y hy x' hx' y' hy'
    have hm := projected_feasible (U := U) hX hY hV (show (x, y) ∈
      Set.univ ×ˢ diameterBall N D from ⟨hx, hy⟩)
    have hm' := projected_feasible (U := U) hX hY hV (show (x', y') ∈
      Set.univ ×ˢ diameterBall N D from ⟨hx', hy'⟩)
    have hb := h.jointly_smooth _ hm.1 _ hm.2 _ hm'.1 _ hm'.2
    have hin : NCCLowerBoundVerification.jointSq
        (frameProject U x - frameProject U x') (frameProject V y - frameProject V y') ≤
        NCCLowerBoundVerification.jointSq (x - x') (y - y') := by
      rw [frameProject_sub U x x', frameProject_sub V y y']
      exact jointSq_frameProject_le_eq hU hV (x - x') (y - y')
    unfold rotatedNCCInstance rotatedGradX rotatedGradY
    rw [frameEmbed_sub, frameEmbed_sub, jointSq_frameEmbed_eq hU hV]
    exact hb.trans (mul_le_mul_of_nonneg_left hin (sq_nonneg ell))
  · intro x _
    have hx : frameProject U x ∈ P.X := by rw [hX]; trivial
    have hc := (h.dual_concave _ hx).comp_linearMap (frameProjectCLM V).toLinearMap
    apply hc.subset
    · intro y hy
      change frameProject V y ∈ P.Y
      rw [hY]
      exact frameProject_mem_diameterBall hV hy
    · exact diameterBall_convex N D
  · intro y hy y' hy'
    exact diameterBall_vecSq_sub_le h.D_pos.le hy hy'
  · intro x _
    rw [Rotation.value_covariance h hX hY hV,
      Rotation.value_covariance h hX hY hV, frameProject_zero]
    exact h.initial_gap_pointwise _ (by rw [hX]; trivial)

/-- Vector covariance of the proved full Moreau derivative, with the rotated
class witness constructed rather than assumed. -/
theorem gradient_covariance (h : WithinClass ell D Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V) (x : NCCLowerBoundVerification.EVec M) :
    Moreau.Within.gradient (class_rotate h hX hY hU hV) x =
      frameEmbed U (Moreau.Within.gradient h (frameProject U x)) :=
  Rotation.gradient_covariance h hX hY hU hV (class_rotate h hX hY hU hV) x

/-- Literal Euclidean norm equality from the source rotation lemma. -/
theorem gradient_norm_covariance (h : WithinClass ell D Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V) (x : NCCLowerBoundVerification.EVec M) :
    Real.sqrt (NCCLowerBoundVerification.vecSq
      (Moreau.Within.gradient (class_rotate h hX hY hU hV) x)) =
    Real.sqrt (NCCLowerBoundVerification.vecSq
      (Moreau.Within.gradient h (frameProject U x))) := by
  exact congrArg Real.sqrt
    (Rotation.gradient_squared_covariance h hX hY hU hV (class_rotate h hX hY hU hV) x)

theorem isOS_covariance (h : WithinClass ell D Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V) (eps : ℝ)
    (x : NCCLowerBoundVerification.EVec M) :
    Moreau.Within.IsOS (class_rotate h hX hY hU hV) eps x ↔
      Moreau.Within.IsOS h eps (frameProject U x) :=
  Rotation.isOS_covariance h hX hY hU hV (class_rotate h hX hY hU hV) x

end
end NCC.Lower.WithinRotation
