import NCCLowerBoundVerification.Upper.TrackingConcrete
import NCCLowerBoundVerification.Upper.ProjectionGeometry
import NCCLowerBoundVerification.Upper.ProjectedMicro

/-!
# Fast-state readout on the genuine constrained conjugate domain

The original algebraic readout accepted an objective on all dual vectors.
Here the fast objective is correctly typed on the subtype `Y`; its strong gap
is derived from the actual `Pzr` strong minimizer and projection
nonexpansiveness is derived from the Euclidean projection interface.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace FastReadoutConcrete

noncomputable section

open RelativeFOAM TrackingAnalytic TrackingConcrete ProjectionGeometry

theorem constrained_fastState_readout {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {P : EVec m → Y → ℝ} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r)
    {qStar : EVec m} {yStar : Y} {xStar : EVec m}
    (hxStar : xStar ∈ X)
    (hqStar : qStar = (-mu) • xStar)
    (hP : IsSubtypePairStrongMinimizer P mu r qStar yStar)
    {projectX : EVec m → EVec m}
    (hprojectX : IsEuclideanProjection X projectX)
    (S : State m n) (hyFast : S.yFast ∈ Y) :
    mu * vecSq (projectX ((-mu⁻¹) • S.qFast) - xStar) ≤
      constrainedEnergy mu r qStar yStar P (P qStar yStar) S hyFast := by
  classical
  let Ptotal : EVec m → EVec n → ℝ := fun q y ↦
    if hy : y ∈ Y then P q ⟨y, hy⟩ else 0
  have hgap := hP S.qFast ⟨S.yFast, hyFast⟩
  have hySq0 : 0 ≤ vecSq (S.yFast - yStar.1) := Tracking.vecSq_nonneg _
  have hstrong : 1 / mu * vecSq (S.qFast - qStar) ≤
      2 * (Ptotal S.qFast S.yFast - P qStar yStar) := by
    have hry : 0 ≤ r * vecSq (S.yFast - yStar.1) :=
      mul_nonneg hr hySq0
    simp only [Ptotal, dif_pos hyFast]
    unfold pairSq at hgap
    nlinarith
  have hfixed : projectX xStar = xStar := by
    exact ProjectedMicro.projection_fixed_of_mem hprojectX hxStar
  have hproject := projection_nonexpansive hprojectX
    ((-mu⁻¹) • S.qFast) xStar
  rw [hfixed] at hproject
  have hread := RelativeFOAM.fastState_readout
    (mu := mu) (alphaR := 2 * RelativeFOAM.alpha mu r / mu) (r := r)
    (qStar := qStar) (yStar := yStar.1) (xStar := xStar)
    (P := Ptotal) (PStar := P qStar yStar) (projectX := projectX)
    hmu (div_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hmu.le)
      hr S hqStar hstrong hproject
  simpa only [Ptotal, dif_pos hyFast,
    constrainedEnergy, RelativeFOAM.energy] using hread

/-- Specialization to a real pointwise-conjugate minimizer, with the strong
minimizer property proved from its gamma subgradient and stationarity. -/
theorem Pzr_fastState_readout {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r)
    {qStar xStar : EVec m} {yStar : Y} {wStar : EVec n}
    (hxStar : xStar ∈ X)
    (hsubgrad : PointwiseConjugate.IsGammaSubgradient
      X Y H qStar yStar xStar wStar)
    (hstationQ : xStar + mu⁻¹ • qStar = 0)
    (hstationY : wStar + r • yStar.1 = 0)
    {projectX : EVec m → EVec m}
    (hprojectX : IsEuclideanProjection X projectX)
    (S : State m n) (hyFast : S.yFast ∈ Y) :
    mu * vecSq (projectX ((-mu⁻¹) • S.qFast) - xStar) ≤
      constrainedEnergy mu r qStar yStar
        (PointwiseConjugate.Pzr X Y H mu r)
        (PointwiseConjugate.Pzr X Y H mu r qStar yStar) S hyFast := by
  have hqStar := PointwiseConjugate.q_eq_neg_mu_smul_of_stationary
    hmu hstationQ
  have hP := Pzr_isSubtypePairStrongMinimizer hmu hr hsubgrad
    hstationQ hstationY
  exact constrained_fastState_readout hmu hr.le hxStar hqStar hP
    hprojectX S hyFast

end

end FastReadoutConcrete
end Upper
end NCCLowerBoundVerification
