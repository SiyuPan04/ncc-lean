import NCC.Upper.WithinSystem

/-!
# The normal-cone stationarity notion used in the GS extension

The cited definition requires small normal-cone residuals, not merely
small projected steps at the original pair. We use explicit normal
witnesses, which in particular bound the corresponding distances to zero.

The exact regularized saddle point below is a mathematical witness.
Its existence is NOT an oracle algorithm, nor a proof of the GS rate.
-/
namespace NCC.Extensions
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open RelativeFOAM NCC.Upper NCC.Upper.WithinSystem

/-- Explicit witnesses for the two normal-cone residual bounds. -/
def HasGSWitness {m n : Nat} (P : NCCInstance m n) (eps : ℝ)
    (x : EVec m) (y : EVec n) : Prop :=
  0 < eps ∧ x ∈ P.X ∧ y ∈ P.Y ∧
    ∃ nx : EVec m, ∃ ny : EVec n,
      IsEuclideanNormal P.X x nx ∧ IsEuclideanNormal P.Y y ny ∧
      vecSq (P.gradX x y + nx) ≤ eps ^ 2 ∧
      vecSq (-P.gradY x y + ny) ≤ eps ^ 2

/-- The residual set in the actual Euclidean metric, rather than the
supremum norm on Lean's raw finite-coordinate function type. -/
def normalResidualSet {d : Nat} (C : Set (EVec d)) (x g : EVec d) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  (fun b : EVec d => WithLp.toLp 2 (g + b)) '' {b | IsEuclideanNormal C x b}

/-- The two distances to the shifted normal cones, as in the cited GS
definition. For a closed convex set these normals are the subgradients
of its indicator function. -/
def IsGS {m n : Nat} (P : NCCInstance m n) (eps : ℝ)
    (x : EVec m) (y : EVec n) : Prop :=
  0 < eps ∧ x ∈ P.X ∧ y ∈ P.Y ∧
    Metric.infDist 0 (normalResidualSet P.X x (P.gradX x y)) ≤ eps ∧
    Metric.infDist 0 (normalResidualSet P.Y y (-P.gradY x y)) ≤ eps

theorem normalResidual_distance_le {d : Nat} {C : Set (EVec d)}
    {x g b : EVec d} {eps : ℝ} (heps : 0 < eps)
    (hb : IsEuclideanNormal C x b) (hsq : vecSq (g + b) ≤ eps ^ 2) :
    Metric.infDist 0 (normalResidualSet C x g) ≤ eps := by
  have hmem : (WithLp.toLp 2 (g + b) : EuclideanSpace ℝ (Fin d)) ∈
      normalResidualSet C x g := ⟨b, hb, rfl⟩
  have hd := Metric.infDist_le_dist_of_mem (x := (0 : EuclideanSpace ℝ (Fin d))) hmem
  have hn : ‖(WithLp.toLp 2 (g + b) : EuclideanSpace ℝ (Fin d))‖ ^ 2 =
      vecSq (g + b) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  have hbound : ‖(WithLp.toLp 2 (g + b) : EuclideanSpace ℝ (Fin d))‖ ≤ eps := by
    nlinarith [norm_nonneg (WithLp.toLp 2 (g + b) : EuclideanSpace ℝ (Fin d))]
  have hd' : Metric.infDist 0 (normalResidualSet C x g) ≤
      ‖(WithLp.toLp 2 (g + b) : EuclideanSpace ℝ (Fin d))‖ := by
    simpa only [dist_zero_left] using hd
  exact hd'.trans hbound

theorem HasGSWitness.isGS {m n : Nat} {P : NCCInstance m n} {eps : ℝ}
    {x : EVec m} {y : EVec n} (h : HasGSWitness P eps x y) : IsGS P eps x y := by
  obtain ⟨heps, hx, hy, nx, ny, hnx, hny, hsx, hsy⟩ := h
  exact ⟨heps, hx, hy, normalResidual_distance_le heps hnx hsx,
    normalResidual_distance_le heps hny hsy⟩

theorem SaddleWitness.primal_residual {m n : Nat} {P : NCCInstance m n}
    {ell r : ℝ} {z : EVec m} (W : WithinSystem.SaddleWitness P ell r z) :
    P.gradX W.x W.y + (-saddleX P ell z W.x W.y) =
      (2 * ell) • (z - W.x) := by
  ext i
  simp only [saddleX, ClassOperator.gradXHat, Pi.add_apply, Pi.neg_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem SaddleWitness.dual_residual {m n : Nat} {P : NCCInstance m n}
    {ell r : ℝ} {z : EVec m} (W : WithinSystem.SaddleWitness P ell r z) :
    -P.gradY W.x W.y + (-saddleY P r W.x W.y) = (-r) • W.y := by
  ext i
  simp only [saddleY, ClassOperator.gradYHat, Pi.add_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

/-- Exact primal displacement and dual perturbation bounds are sufficient
for genuine normal-cone stationarity of the unregularized objective. -/
theorem SaddleWitness.hasGSWitness {m n : Nat} {P : NCCInstance m n}
    {ell D Delta r eps : ℝ} {z : EVec m}
    (hP : WithinClass ell D Delta P)
    (W : WithinSystem.SaddleWitness P ell r z) (heps : 0 < eps)
    (hprimal : 4 * ell ^ 2 * vecSq (z - W.x) ≤ eps ^ 2)
    (hdual : r ^ 2 * D ^ 2 ≤ eps ^ 2) :
    HasGSWitness P eps W.x W.y := by
  refine ⟨heps, W.x_mem, W.y_mem, -saddleX P ell z W.x W.y,
    -saddleY P r W.x W.y, W.normalX, W.normalY, ?_, ?_⟩
  · rw [SaddleWitness.primal_residual W, vecSq_smul]
    nlinarith
  · rw [SaddleWitness.dual_residual W, vecSq_smul]
    have hy := hP.dual_vecSq_le W.y_mem
    have hmul := mul_le_mul_of_nonneg_left hy (sq_nonneg r)
    nlinarith

/-- The genuine VI solution used internally by the existing upper system. -/
def canonicalSaddle {m n : Nat} {P : NCCInstance m n} {ell D Delta r : ℝ}
    (hP : WithinClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hpX : ProjectionGeometry.IsEuclideanProjection P.X projectX)
    (hpY : ProjectionGeometry.IsEuclideanProjection P.Y projectY) (z : EVec m) :
    WithinSystem.SaddleWitness P ell r z :=
  Classical.choice (exists_saddleWitness hP hr hrle hpX hpY z)

theorem canonicalSaddle_x {m n : Nat} {P : NCCInstance m n} {ell D Delta r : ℝ}
    (hP : WithinClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hpX : ProjectionGeometry.IsEuclideanProjection P.X projectX)
    (hpY : ProjectionGeometry.IsEuclideanProjection P.Y projectY)
    (hexistsR : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) :
    (canonicalSaddle hP hr hrle hpX hpY z).x = selectedProx hexistsR z := by
  apply Eq.symm
  exact selectedProx_unique hP.ell_pos hP.regularizedValue_weaklyConvex hexistsR
    ((canonicalSaddle hP hr hrle hpX hpY z).isProxPoint hP hr)

theorem canonicalSaddle_y {m n : Nat} {P : NCCInstance m n} {ell D Delta r : ℝ}
    (hP : WithinClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hpX : ProjectionGeometry.IsEuclideanProjection P.X projectX)
    (hpY : ProjectionGeometry.IsEuclideanProjection P.Y projectY)
    (hexistsR : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell)
    (z : EVec m) :
    (canonicalSaddle hP hr hrle hpX hpY z).y =
      (stationaryAt_of_class hP hr hrle hpX hpY hexistsR z).yStar.val := rfl

end
end NCC.Extensions
