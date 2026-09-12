import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import NCCLowerBoundVerification.Upper.ProjectedVIExistence

/-!
# Euclidean projections onto the class domains

The ambient `EVec d` carries Lean's product norm, while the paper uses the
coordinate Euclidean square.  We transfer a closed convex set to
`EuclideanSpace`, apply the Hilbert projection theorem there, and transfer
the chosen nearest point and its variational inequality back coordinatewise.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace ProjectionExistence

noncomputable section

open RelativeFOAM ProjectionGeometry ProjectedVIExistence

theorem euclideanSet_nonempty {d : Nat} {C : Set (EVec d)}
    (hC : C.Nonempty) : (euclideanSet C).Nonempty := by
  obtain ⟨x, hx⟩ := hC
  exact ⟨ProjectedVIExistence.toEuclidean x, hx⟩

theorem euclideanSet_convex {d : Nat} {C : Set (EVec d)}
    (hC : Convex ℝ C) : Convex ℝ (euclideanSet C) := by
  intro x hx y hy a b ha hb hab
  change ProjectedVIExistence.fromEuclidean (a • x + b • y) ∈ C
  change a • ProjectedVIExistence.fromEuclidean x +
    b • ProjectedVIExistence.fromEuclidean y ∈ C
  exact hC hx hy ha hb hab

/-- Every nonempty closed convex finite-dimensional domain has the exact
coordinate-Euclidean projection interface used by the algorithms. -/
theorem exists_euclideanProjection {d : Nat} {C : Set (EVec d)}
    (hne : C.Nonempty) (hclosed : IsClosed C) (hconvex : Convex ℝ C) :
    ∃ project : EVec d → EVec d, IsEuclideanProjection C project := by
  let CE : Set (EuclideanVec d) := euclideanSet C
  have hneE : CE.Nonempty := euclideanSet_nonempty hne
  have hclosedE : IsClosed CE := euclideanSet_isClosed hclosed
  have hconvexE : Convex ℝ CE := euclideanSet_convex hconvex
  have hnear : ∀ z : EVec d, ∃ v ∈ CE,
      ‖ProjectedVIExistence.toEuclidean z - v‖ =
        ⨅ w : CE, ‖ProjectedVIExistence.toEuclidean z - w‖ := by
    intro z
    exact exists_norm_eq_iInf_of_complete_convex hneE hclosedE.isComplete
      hconvexE (ProjectedVIExistence.toEuclidean z)
  choose p hp_mem hp_min using hnear
  let project : EVec d → EVec d := fun z =>
    ProjectedVIExistence.fromEuclidean (p z)
  refine ⟨project, ?_⟩
  constructor
  · intro z
    exact hp_mem z
  · intro z w hw
    have hwE : ProjectedVIExistence.toEuclidean w ∈ CE := hw
    have hinner :=
      (norm_eq_iInf_iff_real_inner_le_zero hconvexE (hp_mem z)).1
        (hp_min z) (ProjectedVIExistence.toEuclidean w) hwE
    rw [PiLp.inner_apply] at hinner
    simp only [Real.inner_apply] at hinner
    change (∑ i : Fin d,
      ProjectedVIExistence.fromEuclidean
          (ProjectedVIExistence.toEuclidean z - p z) i *
        ProjectedVIExistence.fromEuclidean
          (ProjectedVIExistence.toEuclidean w - p z) i) ≤ 0 at hinner
    rw [ProjectedVIExistence.fromEuclidean_sub,
      ProjectedVIExistence.fromEuclidean_sub,
      ProjectedVIExistence.fromEuclidean_toEuclidean,
      ProjectedVIExistence.fromEuclidean_toEuclidean] at hinner
    change (∑ i : Fin d,
      (z i - project z i) * (w i - project z i)) ≤ 0
    simpa only [project, Pi.sub_apply] using hinner

end

end ProjectionExistence
end Upper
end NCCLowerBoundVerification
