import NCCLowerBoundVerification.DiameterBall
import NCPLVerification.OrthogonalFrames

/-!
# Orthogonal covariance of optimization stationarity

This module proves `lem:os-covariance` for column-orthogonal finite frames.
The proof works directly with the paper's coordinate Euclidean square
`vecSq`; it does not appeal to an ambient norm equivalence.
-/

namespace NCCLowerBoundVerification

noncomputable section

open NCPLVerification

def liftedValueFunction {m M : Nat} (U : Fin m → EVec M)
    (phi : EVec m → ℝ) (X : EVec M) : ℝ :=
  phi (frameProject U X)

/-- The component of an ambient point orthogonal to the chosen frame. -/
def frameResidual {m M : Nat} (U : Fin m → EVec M)
    (X : EVec M) : EVec M :=
  X - frameEmbed U (frameProject U X)

def liftedProxCandidate {m M : Nat} (U : Fin m → EVec M)
    (X : EVec M) (u : EVec m) : EVec M :=
  frameEmbed U u + frameResidual U X

theorem frameProject_add {m M : Nat} (U : Fin m → EVec M)
    (X W : EVec M) :
    frameProject U (X + W) = frameProject U X + frameProject U W := by
  funext i
  unfold frameProject evecDotValue
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem vecSq_frameEmbed_eq {m M : Nat}
    {U : Fin m → EVec M} (hU : IsOrthonormalFrame U) (u : EVec m) :
    vecSq (frameEmbed U u) = vecSq u := by
  simpa [vecSq] using NCPLVerification.vecSq_frameEmbed hU u

theorem frameProject_frameResidual_eq_zero {m M : Nat}
    {U : Fin m → EVec M} (hU : IsOrthonormalFrame U) (X : EVec M) :
    frameProject U (frameResidual U X) = 0 := by
  unfold frameResidual
  rw [← frameProject_sub, frameProject_frameEmbed hU]
  exact sub_self _

theorem frameProject_liftedProxCandidate {m M : Nat}
    {U : Fin m → EVec M} (hU : IsOrthonormalFrame U)
    (X : EVec M) (u : EVec m) :
    frameProject U (liftedProxCandidate U X u) = u := by
  unfold liftedProxCandidate
  rw [frameProject_add, frameProject_frameEmbed hU,
    frameProject_frameResidual_eq_zero hU]
  exact add_zero u

theorem liftedProxCandidate_sub {m M : Nat}
    (U : Fin m → EVec M) (X : EVec M) (u : EVec m) :
    liftedProxCandidate U X u - X =
      frameEmbed U (u - frameProject U X) := by
  unfold liftedProxCandidate frameResidual
  rw [show frameEmbed U u + (X - frameEmbed U (frameProject U X)) - X =
      frameEmbed U u - frameEmbed U (frameProject U X) by abel]
  exact frameEmbed_sub U u (frameProject U X)

theorem vecSq_liftedProxCandidate_sub {m M : Nat}
    {U : Fin m → EVec M} (hU : IsOrthonormalFrame U)
    (X : EVec M) (u : EVec m) :
    vecSq (liftedProxCandidate U X u - X) =
      vecSq (u - frameProject U X) := by
  rw [liftedProxCandidate_sub, vecSq_frameEmbed_eq hU]

theorem vecSq_projected_sub_le {m M : Nat}
    {U : Fin m → EVec M} (hU : IsOrthonormalFrame U)
    (X W : EVec M) :
    vecSq (frameProject U W - frameProject U X) ≤ vecSq (W - X) := by
  rw [frameProject_sub]
  exact vecSq_frameProject_le hU (W - X)

/-- Formula `eq:prox-embedding`: a base prox point gives the ambient prox
point obtained by retaining the orthogonal component of the anchor. -/
theorem liftedProxCandidate_isProxPoint {m M : Nat}
    {U : Fin m → EVec M} (hU : IsOrthonormalFrame U)
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 ≤ ell)
    {X : EVec M} {u : EVec m}
    (hu : IsProxPoint Set.univ phi ell (frameProject U X) u) :
    IsProxPoint Set.univ (liftedValueFunction U phi) ell X
      (liftedProxCandidate U X u) := by
  constructor
  · simp
  intro W _
  have hbase := hu.2 (frameProject U W) (Set.mem_univ _)
  have hproj := vecSq_projected_sub_le hU X W
  have hscaled := mul_le_mul_of_nonneg_left hproj hell
  unfold liftedValueFunction
  rw [frameProject_liftedProxCandidate hU,
    vecSq_liftedProxCandidate_sub hU]
  calc
    phi u + ell * vecSq (u - frameProject U X) ≤
        phi (frameProject U W) +
          ell * vecSq (frameProject U W - frameProject U X) := hbase
    _ ≤ phi (frameProject U W) + ell * vecSq (W - X) := by
      gcongr

/-- Projection of any ambient prox point is a base prox point. -/
theorem frameProject_isProxPoint_of_lifted {m M : Nat}
    {U : Fin m → EVec M} (hU : IsOrthonormalFrame U)
    {phi : EVec m → ℝ} {ell : ℝ} (hell : 0 ≤ ell)
    {X W : EVec M}
    (hW : IsProxPoint Set.univ (liftedValueFunction U phi) ell X W) :
    IsProxPoint Set.univ phi ell (frameProject U X) (frameProject U W) := by
  constructor
  · simp
  intro v _
  let V := liftedProxCandidate U X v
  have hmin := hW.2 V (Set.mem_univ _)
  have hproj := vecSq_projected_sub_le hU X W
  have hscaled := mul_le_mul_of_nonneg_left hproj hell
  unfold liftedValueFunction at hmin
  rw [frameProject_liftedProxCandidate hU,
    vecSq_liftedProxCandidate_sub hU] at hmin
  calc
    phi (frameProject U W) +
        ell * vecSq (frameProject U W - frameProject U X) ≤
      phi (frameProject U W) + ell * vecSq (W - X) := by
        gcongr
    _ ≤ phi v + ell * vecSq (v - frameProject U X) := hmin

/-- Formula `eq:prox-covariance` and its OS consequence, expressed without
choosing an `argmin`. -/
theorem optimizationStationarity_lift_iff {m M : Nat}
    {U : Fin m → EVec M} (hU : IsOrthonormalFrame U)
    {phi : EVec m → ℝ} {ell eps : ℝ} (hell : 0 ≤ ell)
    (X : EVec M) :
    IsOptimizationStationary Set.univ (liftedValueFunction U phi) ell eps X ↔
      IsOptimizationStationary Set.univ phi ell eps (frameProject U X) := by
  constructor
  · rintro ⟨W, hW, hres⟩
    refine ⟨frameProject U W,
      frameProject_isProxPoint_of_lifted hU hell hW, ?_⟩
    exact (vecSq_projected_sub_le hU X W).trans hres
  · rintro ⟨u, hu, hres⟩
    refine ⟨liftedProxCandidate U X u,
      liftedProxCandidate_isProxPoint hU hell hu, ?_⟩
    rw [vecSq_liftedProxCandidate_sub hU]
    exact hres

/-- Lift a base saddle function through two column-orthogonal frames. -/
def liftedSaddle {m n M N : Nat}
    (U : Fin m → EVec M) (V : Fin n → EVec N)
    (f : EVec m → EVec n → ℝ) (X : EVec M) (Y : EVec N) : ℝ :=
  f (frameProject U X) (frameProject V Y)

theorem frameProject_mem_diameterBall {n N : Nat}
    {V : Fin n → EVec N} (hV : IsOrthonormalFrame V)
    {D : ℝ} {Y : EVec N} (hY : Y ∈ diameterBall N D) :
    frameProject V Y ∈ diameterBall n D := by
  unfold diameterBall at *
  exact (vecSq_frameProject_le hV Y).trans hY

theorem frameEmbed_mem_diameterBall {n N : Nat}
    {V : Fin n → EVec N} (hV : IsOrthonormalFrame V)
    {D : ℝ} {y : EVec n} (hy : y ∈ diameterBall n D) :
    frameEmbed V y ∈ diameterBall N D := by
  change vecSq (frameEmbed V y) ≤ (D / 2) ^ 2
  change vecSq y ≤ (D / 2) ^ 2 at hy
  rw [vecSq_frameEmbed_eq hV]
  exact hy

theorem liftedSaddle_maximizer {m n M N : Nat}
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hV : IsOrthonormalFrame V)
    {f : EVec m → EVec n → ℝ} {D : ℝ} {X : EVec M} {y : EVec n}
    (hy : IsMaximizerOn (diameterBall n D) f (frameProject U X) y) :
    IsMaximizerOn (diameterBall N D) (liftedSaddle U V f) X (frameEmbed V y) := by
  constructor
  · exact frameEmbed_mem_diameterBall hV hy.1
  intro Y hY
  unfold liftedSaddle
  rw [frameProject_frameEmbed hV]
  exact hy.2 (frameProject V Y) (frameProject_mem_diameterBall hV hY)

theorem liftedValue_eq {m n M N : Nat}
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hV : IsOrthonormalFrame V)
    {f : EVec m → EVec n → ℝ} {D : ℝ} {X : EVec M}
    (hmax : ∃ y, IsMaximizerOn (diameterBall n D) f (frameProject U X) y) :
    ValueOn (diameterBall N D) (liftedSaddle U V f) X =
      ValueOn (diameterBall n D) f (frameProject U X) := by
  obtain ⟨y, hy⟩ := hmax
  rw [value_eq_of_isMaximizerOn (liftedSaddle_maximizer hV hy),
    value_eq_of_isMaximizerOn hy]
  unfold liftedSaddle
  rw [frameProject_frameEmbed hV]

/-- `lem:os-covariance` for the maximized saddle values. -/
theorem liftedSaddle_optimizationStationarity_iff {m n M N : Nat}
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    {f : EVec m → EVec n → ℝ} {D ell eps : ℝ}
    (hell : 0 ≤ ell)
    (hmax : ∀ x, ∃ y, IsMaximizerOn (diameterBall n D) f x y)
    (X : EVec M) :
    IsOptimizationStationary Set.univ
        (ValueOn (diameterBall N D) (liftedSaddle U V f)) ell eps X ↔
      IsOptimizationStationary Set.univ
        (ValueOn (diameterBall n D) f) ell eps (frameProject U X) := by
  have hfun : ValueOn (diameterBall N D) (liftedSaddle U V f) =
      liftedValueFunction U (ValueOn (diameterBall n D) f) := by
    funext Z
    exact liftedValue_eq hV (hmax (frameProject U Z))
  rw [hfun]
  exact optimizationStationarity_lift_iff hU hell X

end

end NCCLowerBoundVerification
