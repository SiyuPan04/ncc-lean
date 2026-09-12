import NCC.Extensions.NCSCAuxiliary
import NCC.Extensions.NCSCZeroChainObstruction
import NCC.Lower.WithinRotation

/-!
# Strongly concave lifting with a quadratic on the orthogonal complement

A rectangular dual projection alone destroys strong concavity. The lift
below rotates the concave auxiliary objective and subtracts the known full
dual quadratic. This preserves strong concavity on the entire ambient space.
The smoothness bound is deliberately coarse and dimension independent.
-/
namespace NCC.Extensions.NCSCRotation
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open NCPLVerification (IsOrthonormalFrame frameEmbed frameProject frameProductProjectCLM
  frameProject_zero frameEmbed_zero frameProject_frameEmbed vecSq_frameEmbed
  vecSq_frameProject_le frameProject_sub frameEmbed_sub evecDotValue
  evecDotValue_frameEmbed_left frameProductProjectCLM_apply)
open NCC.Extensions.NCSC
set_option maxHeartbeats 3000000

def lifted {m n M N : Nat} (mu : ℝ) (U : Fin m → EVec M) (V : Fin n → EVec N)
    (P : NCCInstance m n) : NCCInstance M N where
  X := Set.univ
  Y := Set.univ
  f := fun x y => (auxiliary P mu).f (frameProject U x) (frameProject V y) -
    quadraticCorrection mu y
  gradX := fun x y => frameEmbed U (P.gradX (frameProject U x) (frameProject V y))
  gradY := fun x y => frameEmbed V ((auxiliary P mu).gradY
    (frameProject U x) (frameProject V y)) - mu • y
  x0 := 0

def smoothness (ell mu : ℝ) : ℝ := 2 * (internalSmoothness ell mu + mu)

variable {m n M N : Nat} {ell mu Delta : ℝ} {P : NCCInstance m n}
  {U : Fin m → EVec M} {V : Fin n → EVec N}

theorem embed_sq (hU : IsOrthonormalFrame U) (x : EVec m) :
    vecSq (frameEmbed U x) = vecSq x := vecSq_frameEmbed hU x

theorem project_sq (hU : IsOrthonormalFrame U) (x : EVec M) :
    vecSq (frameProject U x) ≤ vecSq x := vecSq_frameProject_le hU x

theorem gradient_representation (h : NCSCClass ell mu Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = Set.univ) :
    RepresentsJointGradientWithin (lifted mu U V P) := by
  intro x _ y _
  have hm : Set.MapsTo (frameProductProjectCLM U V)
      (Set.univ ×ˢ Set.univ) (P.X ×ˢ P.Y) := by
    intro z _
    simp [hX, hY]
  have hb := auxiliary_representation h (frameProject U x) (by simp [auxiliary, hX])
    (frameProject V y) (by simp [auxiliary, hY])
  have hc := hb.comp (x, y)
    ((frameProductProjectCLM U V).hasFDerivAt.hasFDerivWithinAt) hm
  have hq := (hasFDerivAt_quadraticCorrection mu y).comp (x, y)
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y)))
  convert! hc.sub hq.hasFDerivWithinAt using 1
  apply ContinuousLinearMap.ext
  rintro ⟨dx, dy⟩
  simp only [ContinuousLinearMap.comp_apply, frameProductProjectCLM_apply,
    jointGradientCLM_apply, lifted, auxiliary, sub_apply, residualCLM_apply]
  change evecDotValue (frameEmbed U (P.gradX (frameProject U x) (frameProject V y))) dx +
      evecDotValue (frameEmbed V (P.gradY (frameProject U x) (frameProject V y) +
        mu • frameProject V y) - mu • y) dy = _
  simp only [evecDotValue, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  change evecDotValue (frameEmbed U (P.gradX (frameProject U x) (frameProject V y))) dx +
      (evecDotValue (frameEmbed V (P.gradY (frameProject U x) (frameProject V y) +
        mu • frameProject V y)) dy - evecDotValue (mu • y) dy) = _
  rw [evecDotValue_frameEmbed_left, evecDotValue_frameEmbed_left]
  simp only [frameProject, eDot, evecDotValue]
  ring_nf
  congr 2

theorem jointly_smooth (h : NCSCClass ell mu Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = Set.univ)
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V) :
    JointlySmoothWithin (smoothness ell mu) (lifted mu U V P) := by
  intro x _ y _ u _ v _
  have hs := auxiliary_smooth h (frameProject U x) (by simp [auxiliary, hX])
    (frameProject V y) (by simp [auxiliary, hY])
    (frameProject U u) (by simp [auxiliary, hX])
    (frameProject V v) (by simp [auxiliary, hY])
  let gx := (auxiliary P mu).gradX (frameProject U x) (frameProject V y) -
    (auxiliary P mu).gradX (frameProject U u) (frameProject V v)
  let gy := (auxiliary P mu).gradY (frameProject U x) (frameProject V y) -
    (auxiliary P mu).gradY (frameProject U u) (frameProject V v)
  have hi := jointSq_frameProject_le_eq hU hV (x - u) (y - v)
  rw [← frameProject_sub U, ← frameProject_sub V] at hi
  have hbase : vecSq gx + vecSq gy ≤
      internalSmoothness ell mu ^ 2 * (vecSq (x - u) + vecSq (y - v)) :=
    hs.trans (mul_le_mul_of_nonneg_left hi (sq_nonneg _))
  have hgy : (lifted mu U V P).gradY x y - (lifted mu U V P).gradY u v =
      frameEmbed V gy + (-mu) • (y - v) := by
    dsimp only [lifted, gy]
    rw [← frameEmbed_sub]
    module
  have hgx : (lifted mu U V P).gradX x y - (lifted mu U V P).gradX u v =
      frameEmbed U gx := frameEmbed_sub U _ _
  change vecSq ((lifted mu U V P).gradX x y - (lifted mu U V P).gradX u v) +
    vecSq ((lifted mu U V P).gradY x y - (lifted mu U V P).gradY u v) ≤ _
  rw [hgx, hgy, embed_sq hU]
  have hb := ScaledOperator.vecSq_add_le_two (frameEmbed V gy) ((-mu) • (y - v))
  rw [embed_sq hV, vecSq_smul, neg_sq] at hb
  have hcoef : 2 * internalSmoothness ell mu ^ 2 + 2 * mu ^ 2 ≤ smoothness ell mu ^ 2 := by
    have hL := internalSmoothness_pos h
    have hm := h.mu_pos
    unfold smoothness
    nlinarith
  have hh := mul_le_mul_of_nonneg_right hcoef
    (add_nonneg (vecSq_nonneg (x - u)) (vecSq_nonneg (y - v)))
  have hz := mul_nonneg (sq_nonneg mu) (vecSq_nonneg (x - u))
  unfold jointSq
  nlinarith [vecSq_nonneg gx]

theorem dual_stronglyConcave (h : NCSCClass ell mu Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = Set.univ) (x : EVec M) :
    ConcaveOn ℝ Set.univ (fun y => (lifted mu U V P).f x y + quadraticCorrection mu y) := by
  have hc := h.dual_stronglyConcave (frameProject U x) (by rw [hX]; trivial)
  rw [hY] at hc
  have he : (fun y => (lifted mu U V P).f x y + quadraticCorrection mu y) =
      (fun y => P.f (frameProject U x) (frameProject V y) +
        quadraticCorrection mu (frameProject V y)) := by
    funext y
    simp [lifted, auxiliary]
  rw [he]
  refine ⟨convex_univ, ?_⟩
  intro y _ v _ a b ha hb hab
  have hp : frameProject V (a • y + b • v) =
      a • frameProject V y + b • frameProject V v := by
    exact (NCPLVerification.frameProjectCLM V).map_add (a • y) (b • v) |>.trans
      (by rw [map_smul, map_smul]; rfl)
  dsimp only
  rw [hp]
  exact hc.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

theorem value_covariance (h : NCSCClass ell mu Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = Set.univ)
    (hV : IsOrthonormalFrame V) (x : EVec M) :
    ValueOn (lifted mu U V P).Y (lifted mu U V P).f x =
      ValueOn P.Y P.f (frameProject U x) := by
  obtain ⟨y, hy⟩ := maximum_attained h (by rw [hX]; trivial : frameProject U x ∈ P.X)
  have he : (lifted mu U V P).f x (frameEmbed V y) = P.f (frameProject U x) y := by
    simp [lifted, auxiliary, quadraticCorrection, frameProject_frameEmbed hV, embed_sq hV]
  have hm : IsMaximizerOn (lifted mu U V P).Y (lifted mu U V P).f x (frameEmbed V y) := by
    refine ⟨Set.mem_univ _, ?_⟩
    intro v _
    rw [he]
    have hv := hy.2 (frameProject V v) (by rw [hY]; trivial)
    have hq := mul_le_mul_of_nonneg_left (project_sq hV v)
      (div_nonneg h.mu_pos.le (by norm_num : (0 : ℝ) ≤ 2))
    dsimp only [lifted, auxiliary, quadraticCorrection]
    linarith
  rw [value_eq_of_isMaximizerOn hm, he, value_eq_of_isMaximizerOn hy]

theorem class_rotate (h : NCSCClass ell mu Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = Set.univ)
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V) :
    NCSCClass (smoothness ell mu) mu Delta (lifted mu U V P) where
  ell_pos := by have := internalSmoothness_pos h; have := h.mu_pos; unfold smoothness; positivity
  mu_pos := h.mu_pos
  Delta_pos := h.Delta_pos
  primal_origin := Set.mem_univ _
  dual_origin := Set.mem_univ _
  initialization := rfl
  X_closed := isClosed_univ
  X_convex := convex_univ
  Y_closed := isClosed_univ
  Y_convex := convex_univ
  gradient_representation := gradient_representation h hX hY
  jointly_smooth := jointly_smooth h hX hY hU hV
  dual_stronglyConcave := fun x _ => dual_stronglyConcave h hX hY x
  initial_gap_pointwise := by
    intro x _
    rw [value_covariance h hX hY hV, value_covariance h hX hY hV, frameProject_zero]
    exact h.initial_gap_pointwise _ (by rw [hX]; trivial)

theorem project_smul {d A : Nat} (V : Fin d → EVec A) (a : ℝ) (y : EVec A) :
    frameProject V (a • y) = a • frameProject V y :=
  (NCPLVerification.frameProjectCLM V).map_smul a y

theorem projected_gradY (hV : IsOrthonormalFrame V) (x : EVec M) (y : EVec N) :
    frameProject V ((lifted mu U V P).gradY x y) =
      P.gradY (frameProject U x) (frameProject V y) := by
  dsimp only [lifted]
  rw [← frameProject_sub, frameProject_frameEmbed hV, project_smul]
  simp [auxiliary]

theorem projected_gradX (hU : IsOrthonormalFrame U) (x : EVec M) (y : EVec N) :
    frameProject U ((lifted mu U V P).gradX x y) =
      P.gradX (frameProject U x) (frameProject V y) := frameProject_frameEmbed hU _

theorem fullSpace_residual_bound {d : Nat} {g y : EVec d} {eps : ℝ}
    (heps : 0 < eps)
    (h : Metric.infDist 0 (normalResidualSet Set.univ y g) ≤ eps) : vecSq g ≤ eps ^ 2 := by
  have hs : normalResidualSet Set.univ y g =
      {(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin d))} := by
    ext w
    constructor
    · rintro ⟨b, hb, rfl⟩
      rw [NCSCZeroChainObstruction.normal_univ_eq_zero hb]
      simp
    · intro hw
      rw [Set.mem_singleton_iff] at hw
      subst w
      refine ⟨0, ?_, by simp⟩
      intro z _
      simp
  rw [hs, Metric.infDist_singleton, dist_zero_left] at h
  have hn : ‖(WithLp.toLp 2 g : EuclideanSpace ℝ (Fin d))‖ ^ 2 = vecSq g := by
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  nlinarith [norm_nonneg (WithLp.toLp 2 g : EuclideanSpace ℝ (Fin d))]

/-- Small GS residuals of the corrected lift imply small GS residuals of
the original objective at the projected pair. No converse is needed for
the lower obstruction. -/
theorem isGS_projects (hX : P.X = Set.univ) (hY : P.Y = Set.univ)
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    {eps : ℝ} {x : EVec M} {y : EVec N} (h : IsGS (lifted mu U V P) eps x y) :
    IsGS P eps (frameProject U x) (frameProject V y) := by
  have hgx := fullSpace_residual_bound h.1 h.2.2.2.1
  have hgy := fullSpace_residual_bound h.1 h.2.2.2.2
  have hneg : vecSq (-(lifted mu U V P).gradY x y) =
      vecSq ((lifted mu U V P).gradY x y) := by
    simp [vecSq, NCPLVerification.vecSq]
  rw [hneg] at hgy
  have hpx := (project_sq hU ((lifted mu U V P).gradX x y)).trans hgx
  have hpy := (project_sq hV ((lifted mu U V P).gradY x y)).trans hgy
  rw [projected_gradX hU] at hpx
  rw [projected_gradY hV] at hpy
  apply HasGSWitness.isGS
  refine ⟨h.1, ?_, ?_, 0, 0, ?_, ?_, ?_, ?_⟩
  · rw [hX]; trivial
  · rw [hY]; trivial
  · intro z _; simp
  · intro z _; simp
  · simpa only [add_zero] using hpx
  · simpa only [add_zero, vecSq, NCPLVerification.vecSq, Pi.neg_apply, neg_sq] using hpy

end
end NCC.Extensions.NCSCRotation
