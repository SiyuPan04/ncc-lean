import NCCLowerBoundVerification.Upper.TrackingAnalytic

/-!
# Tracking estimates on the genuine constrained conjugate domain

`Pzr` is defined on `EVec m × Y`, while the slow FOAM state is unconstrained
and only its fast dual coordinate is queried.  This file states the moving
anchor energy calculation with exactly that typing, so no off-domain
extension of `Pzr` is hidden in the proof.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace TrackingConcrete

noncomputable section

open PointwiseConjugate RelativeFOAM TrackingAnalytic

def IsSubtypePairStrongMinimizer {m n : Nat} {Y : Set (EVec n)}
    (P : EVec m → Y → ℝ) (mu r : ℝ)
    (qStar : EVec m) (yStar : Y) : Prop :=
  ∀ q (y : Y), P qStar yStar + (1 / 2 : ℝ) *
      pairSq mu r (q - qStar) (y.1 - yStar.1) ≤ P q y

theorem Pzr_isSubtypePairStrongMinimizer {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) {q : EVec m} {y : Y}
    {x : EVec m} {w : EVec n}
    (hsubgrad : IsGammaSubgradient X Y H q y x w)
    (hstationQ : x + mu⁻¹ • q = 0)
    (hstationY : w + r • y.1 = 0) :
    IsSubtypePairStrongMinimizer (Pzr X Y H mu r) mu r q y := by
  exact TrackingAnalytic.Pzr_isPairStrongMinimizer hmu hr hsubgrad
    hstationQ hstationY

/-- Relative energy with the actual constrained fast objective. -/
def constrainedEnergy {m n : Nat} {Y : Set (EVec n)}
    (mu r : ℝ) (qStar : EVec m) (yStar : Y)
    (P : EVec m → Y → ℝ) (PStar : ℝ)
    (S : State m n) (hyFast : S.yFast ∈ Y) : ℝ :=
  2 * alpha mu r / mu * vecSq (S.q - qStar) +
    2 * r * vecSq (S.y - yStar.1) +
    2 * (P S.qFast ⟨S.yFast, hyFast⟩ - PStar)

/-- Reparametrize the new-anchor objective back into the old `q` coordinate
and remove an irrelevant scalar constant. -/
def coTranslatedObjective {m n : Nat} {Y : Set (EVec n)}
    (PNew : EVec m → Y → ℝ) (delta : EVec m) (c : ℝ) :
    EVec m → Y → ℝ :=
  fun q y ↦ PNew (q - delta) y - c

theorem coTranslatedObjective_strongMinimizer {m n : Nat}
    {Y : Set (EVec n)} {PNew : EVec m → Y → ℝ}
    {mu r c : ℝ} {delta qNew : EVec m} {yNew : Y}
    (hNew : IsSubtypePairStrongMinimizer PNew mu r qNew yNew) :
    IsSubtypePairStrongMinimizer
      (coTranslatedObjective PNew delta c) mu r (qNew + delta) yNew := by
  intro q y
  have h := hNew (q - delta) y
  have hcenter : qNew + delta - delta = qNew := by
    abel
  have hdist : q - delta - qNew = q - (qNew + delta) := by
    abel
  rw [hdist] at h
  unfold coTranslatedObjective
  rw [hcenter]
  linarith

/-- Co-translating the state is exactly the same as reparametrizing the
objective and its minimizer. -/
theorem constrainedEnergy_coTranslate {m n : Nat} {Y : Set (EVec n)}
    (mu r ell c : ℝ) (d : EVec m)
    {PNew : EVec m → Y → ℝ} {qNew : EVec m} {yNew : Y}
    (S : State m n) (hyFast : S.yFast ∈ Y) :
    constrainedEnergy mu r qNew yNew PNew (PNew qNew yNew)
        (Tracking.coTranslate ell d S) hyFast =
      constrainedEnergy mu r (qNew + (2 * ell) • d) yNew
        (coTranslatedObjective PNew ((2 * ell) • d) c)
        (coTranslatedObjective PNew ((2 * ell) • d) c
          (qNew + (2 * ell) • d) yNew) S hyFast := by
  have hcenter : qNew + (2 * ell) • d - (2 * ell) • d = qNew := by
    abel
  have hslow : S.q - (2 * ell) • d - qNew =
      S.q - (qNew + (2 * ell) • d) := by
    abel
  unfold constrainedEnergy coTranslatedObjective Tracking.coTranslate
  dsimp
  rw [hcenter, hslow]
  ring

/-- The concrete `sSup` conjugate calculation supplies the exact tilt needed
by `anchor_energy_tilt_bound`. -/
theorem Pzr_coTranslatedObjective_tilt {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} (hX : X.Nonempty)
    (f : EVec m → EVec n → ℝ) {ell mu r : ℝ}
    (hmu : mu ≠ 0) (z d : EVec m)
    (hbounded : GammaBddAbove X Y (decurved f ell r z)) :
    ∀ q (y : Y),
      coTranslatedObjective
          (Pzr X Y (decurved f ell r (z + d)) mu r)
          ((2 * ell) • d)
          (1 / (2 * mu) * vecSq ((2 * ell) • d) -
            (2 * ell * dot z d + ell * vecSq d)) q y =
        Pzr X Y (decurved f ell r z) mu r q y -
          1 / mu * dot ((2 * ell) • d) q := by
  intro q y
  exact Pzr_anchor_normalized_tilt hX f hmu z d q y hbounded

/-- The constrained-domain version of the anchor tilt estimate. -/
theorem anchor_energy_tilt_bound {m n : Nat} {Y : Set (EVec n)}
    {mu r : ℝ} (hmu : 0 < mu) (hr : 0 ≤ r)
    {P PT : EVec m → Y → ℝ} {delta : EVec m}
    {qStar qTilt : EVec m} {yStar yTilt : Y}
    (hP : IsSubtypePairStrongMinimizer P mu r qStar yStar)
    (hPT : IsSubtypePairStrongMinimizer PT mu r qTilt yTilt)
    (htilt : ∀ q (y : Y), PT q y = P q y - 1 / mu * dot delta q)
    (S : State m n) (hyFast : S.yFast ∈ Y)
    (halpha0 : 0 ≤ alpha mu r) (halpha1 : alpha mu r ≤ 1) :
    constrainedEnergy mu r qTilt yTilt PT (PT qTilt yTilt) S hyFast ≤
      2 * constrainedEnergy mu r qStar yStar P (P qStar yStar) S hyFast +
        6 * (1 / mu * vecSq delta) := by
  let yf : Y := ⟨S.yFast, hyFast⟩
  let D2 := pairSq mu r (qTilt - qStar) (yTilt.1 - yStar.1)
  have hdrift : D2 ≤ 1 / mu * vecSq delta := by
    have h1 := hP qTilt yTilt
    have h2 := hPT qStar yStar
    rw [htilt, htilt] at h2
    unfold pairSq at h1 h2
    rw [vecSq_sub_comm qStar qTilt,
      vecSq_sub_comm yStar.1 yTilt.1] at h2
    have hy := two_dot_le_sq_add_sq delta (qTilt - qStar)
    have hqnonneg : 0 ≤ 1 / mu * vecSq (qTilt - qStar) :=
      mul_nonneg (div_nonneg zero_le_one hmu.le) (Tracking.vecSq_nonneg _)
    have hynonneg : 0 ≤ r * vecSq (yTilt.1 - yStar.1) :=
      mul_nonneg hr (Tracking.vecSq_nonneg _)
    have hdot : dot delta qTilt - dot delta qStar =
        dot delta (qTilt - qStar) := by
      exact (dot_sub_right delta qTilt qStar).symm
    rw [← hdot] at hy
    have hmuinv : 0 ≤ 1 / mu := div_nonneg zero_le_one hmu.le
    have hscaled := mul_le_mul_of_nonneg_left hy hmuinv
    dsimp [D2, pairSq]
    nlinarith
  have hslowQ := vecSq_sub_triangle_two S.q qStar qTilt
  have hslowY := vecSq_sub_triangle_two S.y yStar.1 yTilt.1
  have hfastStrong := hP S.qFast yf
  have hyDelta := two_dot_le_sq_add_sq delta (S.qFast - qStar)
  have htiltFast := htilt S.qFast yf
  have htiltStar := htilt qTilt yTilt
  have hPAtTilt := hP qTilt yTilt
  have hdotFast : dot delta S.qFast - dot delta qStar =
      dot delta (S.qFast - qStar) := by rw [dot_sub_right]
  have hmu0 : 0 ≤ 1 / mu := div_nonneg zero_le_one hmu.le
  have hqscale := mul_le_mul_of_nonneg_left hyDelta hmu0
  have hyDeltaNeg := two_dot_le_sq_add_sq (-delta) (S.qFast - qStar)
  have hdotNeg : dot (-delta) (S.qFast - qStar) =
      -dot delta (S.qFast - qStar) := by
    unfold dot
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.neg_apply]
    ring
  rw [hdotNeg, Tracking.vecSq_neg] at hyDeltaNeg
  have hqscaleNeg := mul_le_mul_of_nonneg_left hyDeltaNeg hmu0
  have hyTilt := two_dot_le_sq_add_sq delta (qTilt - qStar)
  have hqscaleTilt := mul_le_mul_of_nonneg_left hyTilt hmu0
  have hdotTilt : dot delta qTilt - dot delta qStar =
      dot delta (qTilt - qStar) := by rw [dot_sub_right]
  have hlowerTilt :
      P qStar yStar - 1 / mu * dot delta qStar -
          1 / 2 * (1 / mu * vecSq delta) ≤ PT qTilt yTilt := by
    rw [htiltStar]
    unfold pairSq at hPAtTilt
    rw [← hdotTilt] at hqscaleTilt
    have hyMetric : 0 ≤ r * vecSq (yTilt.1 - yStar.1) :=
      mul_nonneg hr (Tracking.vecSq_nonneg _)
    nlinarith
  have hfast :
      PT S.qFast yf - PT qTilt yTilt ≤
        2 * (P S.qFast yf - P qStar yStar) +
          1 / mu * vecSq delta := by
    rw [htiltFast]
    unfold pairSq at hfastStrong
    rw [← hdotFast] at hqscale
    have hfastMetricNonneg :
        0 ≤ r * vecSq (S.yFast - yStar.1) :=
      mul_nonneg hr (Tracking.vecSq_nonneg _)
    dsimp [yf] at hfastStrong ⊢
    nlinarith
  unfold constrainedEnergy
  dsimp [D2, pairSq] at hdrift
  have hcoefQ : 0 ≤ 2 * alpha mu r / mu := by positivity
  have hcoefY : 0 ≤ 2 * r := by positivity
  have hslowQscaled := mul_le_mul_of_nonneg_left hslowQ hcoefQ
  have hslowYscaled := mul_le_mul_of_nonneg_left hslowY hcoefY
  rw [vecSq_sub_comm qStar qTilt] at hslowQscaled
  rw [vecSq_sub_comm yStar.1 yTilt.1] at hslowYscaled
  have hAlphaDrift :
      alpha mu r / mu * vecSq (qTilt - qStar) +
        r * vecSq (yTilt.1 - yStar.1) ≤
          1 / mu * vecSq (qTilt - qStar) +
            r * vecSq (yTilt.1 - yStar.1) := by
    have hq0 := Tracking.vecSq_nonneg (qTilt - qStar)
    have ha := mul_le_mul_of_nonneg_right halpha1 hq0
    have hscaled := mul_le_mul_of_nonneg_left ha hmu0
    calc
      alpha mu r / mu * vecSq (qTilt - qStar) +
          r * vecSq (yTilt.1 - yStar.1) =
        (1 / mu) * (alpha mu r * vecSq (qTilt - qStar)) +
          r * vecSq (yTilt.1 - yStar.1) := by ring
      _ ≤ (1 / mu) * (1 * vecSq (qTilt - qStar)) +
          r * vecSq (yTilt.1 - yStar.1) := by linarith
      _ = 1 / mu * vecSq (qTilt - qStar) +
          r * vecSq (yTilt.1 - yStar.1) := by ring
  have hDriftCost :
      4 * (alpha mu r / mu * vecSq (qTilt - qStar) +
        r * vecSq (yTilt.1 - yStar.1)) ≤
          4 * (1 / mu * vecSq delta) := by
    nlinarith
  have hslow :
      2 * alpha mu r / mu * vecSq (S.q - qTilt) +
          2 * r * vecSq (S.y - yTilt.1) ≤
        2 * (2 * alpha mu r / mu * vecSq (S.q - qStar) +
          2 * r * vecSq (S.y - yStar.1)) +
          4 * (1 / mu * vecSq delta) := by
    calc
      2 * alpha mu r / mu * vecSq (S.q - qTilt) +
          2 * r * vecSq (S.y - yTilt.1) ≤
        2 * alpha mu r / mu *
            (2 * vecSq (S.q - qStar) + 2 * vecSq (qTilt - qStar)) +
          2 * r * (2 * vecSq (S.y - yStar.1) +
            2 * vecSq (yTilt.1 - yStar.1)) :=
        add_le_add hslowQscaled hslowYscaled
      _ = 2 * (2 * alpha mu r / mu * vecSq (S.q - qStar) +
            2 * r * vecSq (S.y - yStar.1)) +
          4 * (alpha mu r / mu * vecSq (qTilt - qStar) +
            r * vecSq (yTilt.1 - yStar.1)) := by ring
      _ ≤ 2 * (2 * alpha mu r / mu * vecSq (S.q - qStar) +
            2 * r * vecSq (S.y - yStar.1)) +
          4 * (1 / mu * vecSq delta) := by linarith
  have hfast2 := mul_le_mul_of_nonneg_left hfast (by norm_num : (0 : ℝ) ≤ 2)
  change
    2 * alpha mu r / mu * vecSq (S.q - qTilt) +
        2 * r * vecSq (S.y - yTilt.1) +
        2 * (PT S.qFast ⟨S.yFast, hyFast⟩ - PT qTilt yTilt) ≤ _
  nlinarith

/-- Fully concrete moving-anchor estimate for the actual pointwise-conjugate
objectives.  The two minimizers are certified by genuine gamma subgradients
and stationarity equations. -/
theorem Pzr_anchor_energy_bound {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} (hX : X.Nonempty)
    (f : EVec m → EVec n → ℝ) {ell mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hrmu : r ≤ mu / 8)
    (z d : EVec m)
    (hbounded : GammaBddAbove X Y (decurved f ell r z))
    {qOld qNew : EVec m} {yOld yNew : Y}
    {xOld xNew : EVec m} {wOld wNew : EVec n}
    (hsubOld : IsGammaSubgradient X Y (decurved f ell r z)
      qOld yOld xOld wOld)
    (hstationQOld : xOld + mu⁻¹ • qOld = 0)
    (hstationYOld : wOld + r • yOld.1 = 0)
    (hsubNew : IsGammaSubgradient X Y (decurved f ell r (z + d))
      qNew yNew xNew wNew)
    (hstationQNew : xNew + mu⁻¹ • qNew = 0)
    (hstationYNew : wNew + r • yNew.1 = 0)
    (S : State m n) (hyFast : S.yFast ∈ Y) :
    constrainedEnergy mu r qNew yNew
        (Pzr X Y (decurved f ell r (z + d)) mu r)
        (Pzr X Y (decurved f ell r (z + d)) mu r qNew yNew)
        (Tracking.coTranslate ell d S) hyFast ≤
      2 * constrainedEnergy mu r qOld yOld
          (Pzr X Y (decurved f ell r z) mu r)
          (Pzr X Y (decurved f ell r z) mu r qOld yOld) S hyFast +
        6 * (1 / mu * vecSq ((2 * ell) • d)) := by
  let delta : EVec m := (2 * ell) • d
  let c : ℝ := 1 / (2 * mu) * vecSq delta -
    (2 * ell * dot z d + ell * vecSq d)
  have hOld : IsSubtypePairStrongMinimizer
      (Pzr X Y (decurved f ell r z) mu r) mu r qOld yOld :=
    Pzr_isSubtypePairStrongMinimizer hmu hr hsubOld
      hstationQOld hstationYOld
  have hNew : IsSubtypePairStrongMinimizer
      (Pzr X Y (decurved f ell r (z + d)) mu r) mu r qNew yNew :=
    Pzr_isSubtypePairStrongMinimizer hmu hr hsubNew
      hstationQNew hstationYNew
  have hNewTranslated : IsSubtypePairStrongMinimizer
      (coTranslatedObjective
        (Pzr X Y (decurved f ell r (z + d)) mu r) delta c)
      mu r (qNew + delta) yNew :=
    coTranslatedObjective_strongMinimizer hNew
  have htilt : ∀ q (y : Y),
      coTranslatedObjective
          (Pzr X Y (decurved f ell r (z + d)) mu r) delta c q y =
        Pzr X Y (decurved f ell r z) mu r q y -
          1 / mu * dot delta q := by
    simpa [delta, c] using
      Pzr_coTranslatedObjective_tilt hX f hmu.ne' z d hbounded
  have hmain := anchor_energy_tilt_bound hmu hr.le hOld hNewTranslated
    htilt S hyFast (alpha_pos hmu hr).le
    (alpha_le_one hmu hr.le hrmu)
  have heq := constrainedEnergy_coTranslate mu r ell c d
    (PNew := Pzr X Y (decurved f ell r (z + d)) mu r)
    (qNew := qNew) (yNew := yNew) S hyFast
  dsimp [delta] at hmain
  rw [heq]
  exact hmain

end

end TrackingConcrete
end Upper
end NCCLowerBoundVerification
