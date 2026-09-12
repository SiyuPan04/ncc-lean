import NCCLowerBoundVerification.Lower.RotationClosure
import NCCLowerBoundVerification.Lower.ScaledObjective
import NCCLowerBoundVerification.PaperClass

/-!
# `C^1` regularity through the lower-bound transformations

The lower-bound instance is first dilated and then embedded through hidden
orthonormal frames.  This file records that both transformations preserve the
global `C^1` representative used to enter the paper's neighborhood class.
-/

namespace NCCLowerBoundVerification

noncomputable section

open NCPLVerification

/-- Product version of coordinate contraction. -/
def unscaleProductCLM (m n : Nat) (lambda : ℝ) :
    (EVec m × EVec n) →L[ℝ] (EVec m × EVec n) :=
  ((unscaleCLM m lambda).comp
      (ContinuousLinearMap.fst ℝ (EVec m) (EVec n))).prod
    ((unscaleCLM n lambda).comp
      (ContinuousLinearMap.snd ℝ (EVec m) (EVec n)))

@[simp] theorem unscaleProductCLM_apply {m n : Nat} (lambda : ℝ)
    (p : EVec m × EVec n) :
    unscaleProductCLM m n lambda p =
      (unscaleCoords lambda p.1, unscaleCoords lambda p.2) := by
  ext <;> simp [unscaleProductCLM, unscaleCLM_apply]

/-- Dilation and positive/negative amplitude multiplication preserve global
`C^1` regularity; no sign assumption on either scalar is needed. -/
theorem scaledObjective_contDiff_one {m n : Nat} {f : EVec m → EVec n → ℝ}
    (lambda amp : ℝ)
    (hf : ContDiff ℝ 1 (Function.uncurry f)) :
    ContDiff ℝ 1 (Function.uncurry (scaledObjective lambda amp f)) := by
  have hcomp : ContDiff ℝ 1
      ((Function.uncurry f) ∘ unscaleProductCLM m n lambda) :=
    hf.comp (unscaleProductCLM m n lambda).contDiff
  have hscaled := ContDiff.const_smul amp hcomp
  change ContDiff ℝ 1 (fun p : EVec m × EVec n =>
    amp * f (unscaleCoords lambda p.1) (unscaleCoords lambda p.2))
  simpa [Function.comp_apply, Function.uncurry, smul_eq_mul]
    using hscaled

/-- Hidden-frame rotation is precomposition by a continuous linear map and
therefore preserves global `C^1` regularity. -/
theorem rotatedF_contDiff_one {m n M N : Nat}
    {f : EVec m → EVec n → ℝ}
    (U : Fin m → EVec M) (V : Fin n → EVec N)
    (hf : ContDiff ℝ 1 (Function.uncurry f)) :
    ContDiff ℝ 1 (Function.uncurry (rotatedF U V f)) := by
  have hcomp : ContDiff ℝ 1
      ((Function.uncurry f) ∘ frameProductProjectCLM U V) :=
    hf.comp (frameProductProjectCLM U V).contDiff
  change ContDiff ℝ 1 (fun p : EVec M × EVec N =>
    f (frameProject U p.1) (frameProject V p.2)) at hcomp
  change ContDiff ℝ 1 (fun p : EVec M × EVec N =>
    f (frameProject U p.1) (frameProject V p.2))
  exact hcomp

end

end NCCLowerBoundVerification
