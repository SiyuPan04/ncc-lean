import NCCLowerBoundVerification.Lower.ScaledObjective

/-!
# Exact scaling identities

Wrappers for Lemma `lem:scaling` of the simplified manuscript.  The source
objective is evaluated at `(x/lambda,y/lambda)` and multiplied by
`ell * lambda^2 / ell0`.
-/

namespace NCCLowerBound
namespace Simplified

noncomputable section

open NCCLowerBoundVerification

def paperAmplitude (ell ell0 lambda : ℝ) : ℝ :=
  ell * lambda ^ 2 / ell0

theorem paperAmplitude_eq_lowerAmplitude (ell ell0 lambda : ℝ) :
    paperAmplitude ell ell0 lambda = lowerAmplitude ell ell0 lambda := rfl

/-- The scaled joint smoothness constant is exactly `ell`. -/
theorem exact_smoothness_scaling
    {ell ell0 lambda : ℝ} (hell0 : ell0 ≠ 0) (hlambda : lambda ≠ 0) :
    paperAmplitude ell ell0 lambda * ell0 / lambda ^ 2 = ell := by
  exact lowerAmplitude_smooth_constant hell0 hlambda

/-- The gradient multiplier is exactly `ell * lambda / ell0`. -/
theorem exact_gradient_scaling
    {ell ell0 lambda : ℝ} (hell0 : ell0 ≠ 0) (hlambda : lambda ≠ 0) :
    paperAmplitude ell ell0 lambda / lambda = ell * lambda / ell0 := by
  exact lowerAmplitude_gradient_factor hell0 hlambda

/-- Exact value identity after scaling the dual domain. -/
theorem exact_value_scaling
    {m n : Nat} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ}
    {ell ell0 lambda : ℝ}
    (hlambda : lambda ≠ 0)
    (hamp : 0 ≤ paperAmplitude ell ell0 lambda)
    (hmax : ∀ x, ∃ y, IsMaximizerOn Y f x y) :
    ValueOn (scaledDomain lambda Y)
        (scaledObjective lambda (paperAmplitude ell ell0 lambda) f) =
      scaledScalar lambda (paperAmplitude ell ell0 lambda) (ValueOn Y f) := by
  exact scaledValue_eq_scaledScalar hlambda hamp hmax

/-- Coordinate support is preserved by the exact scalar rescaling. -/
theorem exact_scaling_preserves_zero_chain
    {d : Nat} {ell ell0 lambda : ℝ} {G : EVec d → EVec d}
    (hG : NCPLVerification.IsFirstOrderZeroChain G) :
    NCPLVerification.IsFirstOrderZeroChain
      (scaledVectorField lambda (paperAmplitude ell ell0 lambda) G) := by
  exact scaledVectorField_isFirstOrderZeroChain hG

end

end Simplified
end NCCLowerBound
