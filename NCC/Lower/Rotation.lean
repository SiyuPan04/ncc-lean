import NCC.Moreau.Within
import NCCLowerBoundVerification.Lower.RotationClosure

/-!
# Exact orthogonal covariance for the current feasible-domain model

The class-closure theorem takes a globally differentiable represented
objective explicitly. This holds for the constructed hard family and is not
inferred from the weaker `WithinClass` convention. The covariance statements
concern the actual selected prox, infimum envelope, and proven envelope
derivative from `Moreau.Within`; their proofs use Euclidean frame identities.
-/

namespace NCC.Lower.Rotation

noncomputable section

open NCCLowerBoundVerification
open NCPLVerification (RepresentsJointGradient IsOrthonormalFrame frameEmbed frameProject
  frameEmbedCLM frameEmbed_sub frameProject_zero)

theorem global_representation_within {m n : ℕ} {P : NCCInstance m n}
    (h : RepresentsJointGradient P.f P.gradX P.gradY) :
    Model.RepresentsJointGradientWithin P := by
  intro x _ y _
  have hf := (h.1 (x, y)).hasFDerivAt
  have heq : fderiv ℝ (Function.uncurry P.f) (x, y) =
      Model.jointGradientCLM (P.gradX x y) (P.gradY x y) := by
    apply ContinuousLinearMap.ext
    intro z
    rcases z with ⟨dx, dy⟩
    exact h.2 x y dx dy
  rw [heq] at hf
  exact hf.hasFDerivWithinAt

/-- All extra analytic-backend fields are derived, not postulated. -/
theorem toAnalytic {m n : ℕ} {ell D Delta : ℝ} {P : NCCInstance m n}
    (h : Model.WithinClass ell D Delta P)
    (hg : RepresentsJointGradient P.f P.gradX P.gradY) : IsNCCClass ell D Delta P := by
  refine
    { ell_pos := h.ell_pos
      D_pos := h.D_pos
      Delta_pos := h.Delta_pos
      x0_mem := by rw [h.initialization]; exact h.primal_origin
      X_nonempty := ⟨0, h.primal_origin⟩
      X_closed := h.X_closed
      X_convex := h.X_convex
      Y_nonempty := ⟨0, h.dual_origin⟩
      Y_closed := h.Y_closed
      Y_convex := h.Y_convex
      gradient_representation := hg
      jointly_smooth := h.jointly_smooth
      dual_concave := h.dual_concave
      maximum_attained := fun _ hx => h.maximum_attained hx
      value_bddBelow := h.value_bddBelow
      initial_gap := ?_
      dual_diameter := h.dual_diameter }
  rw [h.initialization]
  exact h.initial_gap

theorem withinClass_of_analytic {m n : ℕ} {ell D Delta : ℝ} {P : NCCInstance m n}
    (h : IsNCCClass ell D Delta P) (hinit : P.x0 = 0) (hy0 : (0 : EVec n) ∈ P.Y) :
    Model.WithinClass ell D Delta P := by
  refine
    { ell_pos := h.ell_pos
      D_pos := h.D_pos
      Delta_pos := h.Delta_pos
      primal_origin := by simpa [hinit] using h.x0_mem
      dual_origin := hy0
      initialization := hinit
      X_closed := h.X_closed
      X_convex := h.X_convex
      Y_closed := h.Y_closed
      Y_convex := h.Y_convex
      gradient_representation := global_representation_within h.gradient_representation
      jointly_smooth := h.jointly_smooth
      dual_concave := h.dual_concave
      dual_diameter := h.dual_diameter
      initial_gap_pointwise := ?_ }
  apply Model.pointwise_gap_of_inf_gap h.value_bddBelow
  simpa [hinit] using h.initial_gap

theorem class_rotate {m n M N : ℕ} {ell D Delta : ℝ} {P : NCCInstance m n}
    (h : Model.WithinClass ell D Delta P)
    (hg : RepresentsJointGradient P.f P.gradX P.gradY)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V) :
    Model.WithinClass ell D Delta (rotatedNCCInstance D U V P) ∧
      IsNCCClass ell D Delta (rotatedNCCInstance D U V P) := by
  have hr := (toAnalytic h hg).rotate_symmetric hX hY h.initialization hU hV
  refine ⟨withinClass_of_analytic hr rfl ?_, hr⟩
  exact zero_mem_diameterBall N D h.D_pos.le

theorem maximum_attained_everywhere {m n : ℕ} {ell D Delta : ℝ} {P : NCCInstance m n}
    (h : Model.WithinClass ell D Delta P) (hX : P.X = Set.univ) :
    ∀ x, ∃ y, IsMaximizerOn P.Y P.f x y := by
  intro x
  exact h.maximum_attained (by rw [hX]; trivial)

theorem value_covariance {m n M N : ℕ} {ell D Delta : ℝ} {P : NCCInstance m n}
    (h : Model.WithinClass ell D Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hV : IsOrthonormalFrame V) (X : EVec M) :
    ValueOn (rotatedNCCInstance D U V P).Y (rotatedNCCInstance D U V P).f X =
      ValueOn P.Y P.f (frameProject U X) :=
  rotatedValue_eq hV hY (maximum_attained_everywhere h hX) X

theorem prox_covariance {m n M N : ℕ} {ell D Delta : ℝ} {P : NCCInstance m n}
    (h : Model.WithinClass ell D Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    (hr : Model.WithinClass ell D Delta (rotatedNCCInstance D U V P)) (X : EVec M) :
    Moreau.Within.prox hr X =
      liftedProxCandidate U X (Moreau.Within.prox h (frameProject U X)) := by
  apply Moreau.Within.prox_unique hr
  have hb := Moreau.Within.prox_spec h (frameProject U X)
  rw [hX] at hb
  have hp := liftedProxCandidate_isProxPoint hU h.ell_pos.le hb
  have hv : ValueOn (rotatedNCCInstance D U V P).Y (rotatedNCCInstance D U V P).f =
      liftedValueFunction U (ValueOn P.Y P.f) := by
    funext Z
    exact value_covariance h hX hY hV Z
  rw [hv]
  exact hp

theorem envelope_covariance {m n M N : ℕ} {ell D Delta : ℝ} {P : NCCInstance m n}
    (h : Model.WithinClass ell D Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    (hr : Model.WithinClass ell D Delta (rotatedNCCInstance D U V P)) (X : EVec M) :
    Moreau.Within.envelope hr X = Moreau.Within.envelope h (frameProject U X) := by
  change ValueOn (rotatedNCCInstance D U V P).Y (rotatedNCCInstance D U V P).f
      (Moreau.Within.prox hr X) + ell * vecSq (Moreau.Within.prox hr X - X) =
    ValueOn P.Y P.f (Moreau.Within.prox h (frameProject U X)) +
      ell * vecSq (Moreau.Within.prox h (frameProject U X) - frameProject U X)
  rw [prox_covariance h hX hY hU hV hr X, value_covariance h hX hY hV,
    frameProject_liftedProxCandidate hU, vecSq_liftedProxCandidate_sub hU]

/-- Covariance of the vector already proved to represent the full derivative. -/
theorem gradient_covariance {m n M N : ℕ} {ell D Delta : ℝ} {P : NCCInstance m n}
    (h : Model.WithinClass ell D Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    (hr : Model.WithinClass ell D Delta (rotatedNCCInstance D U V P)) (X : EVec M) :
    Moreau.Within.gradient hr X =
      frameEmbed U (Moreau.Within.gradient h (frameProject U X)) := by
  rw [Moreau.Within.gradient_formula, Moreau.Within.gradient_formula,
    prox_covariance h hX hY hU hV hr X]
  have hd : X - liftedProxCandidate U X (Moreau.Within.prox h (frameProject U X)) =
      frameEmbed U (frameProject U X - Moreau.Within.prox h (frameProject U X)) := by
    unfold liftedProxCandidate frameResidual
    rw [← frameEmbed_sub]
    abel
  rw [hd]
  exact ((frameEmbedCLM U).map_smul (2 * ell) _).symm

theorem gradient_squared_covariance {m n M N : ℕ} {ell D Delta : ℝ} {P : NCCInstance m n}
    (h : Model.WithinClass ell D Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    (hr : Model.WithinClass ell D Delta (rotatedNCCInstance D U V P)) (X : EVec M) :
    vecSq (Moreau.Within.gradient hr X) =
      vecSq (Moreau.Within.gradient h (frameProject U X)) := by
  rw [gradient_covariance h hX hY hU hV hr X, vecSq_frameEmbed_eq hU]

theorem isOS_covariance {m n M N : ℕ} {ell D Delta eps : ℝ} {P : NCCInstance m n}
    (h : Model.WithinClass ell D Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    (hr : Model.WithinClass ell D Delta (rotatedNCCInstance D U V P)) (X : EVec M) :
    Moreau.Within.IsOS hr eps X ↔ Moreau.Within.IsOS h eps (frameProject U X) := by
  unfold Moreau.Within.IsOS
  rw [gradient_squared_covariance h hX hY hU hV hr X]
  simp [hX, rotatedNCCInstance]

end

end NCC.Lower.Rotation
