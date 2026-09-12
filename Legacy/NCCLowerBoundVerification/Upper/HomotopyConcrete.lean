import NCCLowerBoundVerification.DiameterBall
import NCCLowerBoundVerification.Upper.RelativeFOAMContraction
import NCCLowerBoundVerification.Upper.TrackingAnalytic

/-!
# Concrete curvature homotopy for the pointwise-conjugate objective

This file discharges the curvature-change interface using the actual constrained
objective `Pzr`.  In particular, every fast dual point is carried by
`RelativeFOAMContraction.ValidState Y`; the proof never evaluates the conjugate
outside `Y`.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace HomotopyConcrete

noncomputable section

open PointwiseConjugate
open RelativeFOAM
open RelativeFOAMContraction
open TrackingAnalytic

set_option maxHeartbeats 800000

/-- The slow quadratic part of the relative FOAM energy. -/
def slowEnergy {m n : Nat} (mu r : ℝ) (qStar : EVec m) (yStar : EVec n)
    (S : State m n) : ℝ :=
  2 * alpha mu r / mu * vecSq (S.q - qStar) +
    2 * r * vecSq (S.y - yStar)

/-- The fast gap, with feasibility retained in the type of the state. -/
def fastGap {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (H : EVec m → EVec n → ℝ) (mu r : ℝ)
    (qStar : EVec m) (yStar : Y) (S : ValidState (m := m) Y) : ℝ :=
  Pzr X Y H mu r S.1.qFast ⟨S.1.yFast, S.2⟩ -
    Pzr X Y H mu r qStar yStar

/-- The concrete constrained energy. -/
def concreteEnergy {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (H : EVec m → EVec n → ℝ) (mu r : ℝ)
    (qStar : EVec m) (yStar : Y) (S : ValidState (m := m) Y) : ℝ :=
  Tracking.splitEnergy (slowEnergy mu r qStar yStar.1 S.1)
    (fastGap X Y H mu r qStar yStar S)

/-- On a feasible state, the direct subtype energy is exactly the energy used
by the concrete FOAM contraction theorem. -/
theorem concreteEnergy_eq_energy {m n : Nat}
    (X : Set (EVec m)) (Y : Set (EVec n))
    (H : EVec m → EVec n → ℝ) (mu r : ℝ)
    (qStar : EVec m) (yStar : Y) (S : ValidState (m := m) Y) :
    concreteEnergy X Y H mu r qStar yStar S =
      energy mu r qStar yStar.1 (PzrTotal X Y H mu r)
        (Pzr X Y H mu r qStar yStar) S.1 := by
  unfold concreteEnergy slowEnergy fastGap Tracking.splitEnergy energy
  rw [PzrTotal_of_mem X Y H mu r S.1.qFast S.2]

/-- The exact objective change under `r ↦ r/4`. -/
theorem Pzr_quarter_identity {m n : Nat}
    (X : Set (EVec m)) (Y : Set (EVec n))
    (H : EVec m → EVec n → ℝ) (mu r : ℝ)
    (q : EVec m) (y : Y) :
    Pzr X Y H mu (r / 4) q y =
      Pzr X Y H mu r q y - (3 * r / 8) * vecSq y.1 := by
  unfold Pzr
  ring

/-- A subset of the radius-`D/2` ball supplies both the norm bound and the
diameter bound used by the curvature argument. -/
theorem dual_geometry_of_ball {n : Nat} {Y : Set (EVec n)} {D : ℝ}
    (hD : 0 ≤ D) (hY : Y ⊆ diameterBall n D) :
    (∀ y : Y, vecSq y.1 ≤ (D / 2) ^ 2) ∧
      (∀ y y' : Y, vecSq (y.1 - y'.1) ≤ D ^ 2) := by
  constructor
  · intro y
    exact hY y.2
  · intro y y'
    exact diameterBall_vecSq_sub_le hD (hY y.2) (hY y'.2)

/-- The minimizer drift is derived from the two real stationary
gamma-subgradients and the exact curvature identity.  The displayed bound is
already three times sharper than the `9rD²/4` allowance used in the TeX. -/
theorem Pzr_quarter_minimizer_drift {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r D : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (_hD : 0 ≤ D)
    (hYnorm : ∀ y : Y, vecSq y.1 ≤ D ^ 2)
    {qOld qNew : EVec m} {yOld yNew : Y}
    {xOld xNew : EVec m} {wOld wNew : EVec n}
    (hsubOld : IsGammaSubgradient X Y H qOld yOld xOld wOld)
    (hstationQOld : xOld + mu⁻¹ • qOld = 0)
    (hstationYOld : wOld + r • yOld.1 = 0)
    (hsubNew : IsGammaSubgradient X Y H qNew yNew xNew wNew)
    (hstationQNew : xNew + mu⁻¹ • qNew = 0)
    (hstationYNew : wNew + (r / 4) • yNew.1 = 0) :
    pairSq mu (r / 4) (qOld - qNew) (yOld.1 - yNew.1) ≤
      (3 * r / 4) * D ^ 2 := by
  have hr4 : 0 < r / 4 := by positivity
  have hOldMin :=
    (Pzr_unique_minimizer hmu hr hsubOld hstationQOld hstationYOld).1
  have hNewStrong :=
    Pzr_isPairStrongMinimizer hmu hr4 hsubNew hstationQNew hstationYNew
      qOld yOld
  rw [Pzr_quarter_identity, Pzr_quarter_identity] at hNewStrong
  have hmin := hOldMin qNew yNew
  have hyNewBall : vecSq yNew.1 ≤ D ^ 2 := hYnorm yNew
  have hyOld0 := Tracking.vecSq_nonneg yOld.1
  have hmetric0 := pairSq_nonneg hmu (by positivity : 0 ≤ r / 4)
    (qOld - qNew) (yOld.1 - yNew.1)
  have hc : 0 ≤ 3 * r / 8 := by positivity
  have hyOldScaled : 0 ≤ (3 * r / 8) * vecSq yOld.1 :=
    mul_nonneg hc hyOld0
  nlinarith [mul_le_mul_of_nonneg_left hyNewBall hc]

/-- Curvature transfer for the slow quadratic component. -/
theorem slowEnergy_quarter_le {m n : Nat}
    {mu r D : ℝ} (hmu : 0 < mu) (hr : 0 < r) (_hD : 0 ≤ D)
    (hrmu : r ≤ mu / 8)
    {qOld qNew : EVec m} {yOld yNew : EVec n}
    (hdrift : pairSq mu (r / 4) (qOld - qNew) (yOld - yNew) ≤
      (3 * r / 4) * D ^ 2)
    (S : State m n) :
    slowEnergy mu (r / 4) qNew yNew S ≤
      slowEnergy mu r qOld yOld S + 6 * r * D ^ 2 := by
  have haeq := alpha_quarter hmu hr.le
  have hale : alpha mu r ≤ 1 := alpha_le_one hmu hr.le hrmu
  have hqtri := vecSq_sub_triangle_two S.q qOld qNew
  have hytri := vecSq_sub_triangle_two S.y yOld yNew
  have ha0 : 0 ≤ alpha mu r := Real.sqrt_nonneg _
  have hqcoef : 0 ≤ alpha mu r / mu := div_nonneg ha0 hmu.le
  have hycoef : 0 ≤ r / 2 := by positivity
  have hqscaled := mul_le_mul_of_nonneg_left hqtri hqcoef
  have hyscaled := mul_le_mul_of_nonneg_left hytri hycoef
  have hq0 := Tracking.vecSq_nonneg (qOld - qNew)
  have hy0 := Tracking.vecSq_nonneg (yOld - yNew)
  have hmuinv : 0 ≤ 1 / mu := by positivity
  have halphaScaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hale hq0) hmuinv
  unfold pairSq at hdrift
  have hqalpha :
      alpha mu r / mu * vecSq (qOld - qNew) ≤
        1 / mu * vecSq (qOld - qNew) := by
    calc
      alpha mu r / mu * vecSq (qOld - qNew) =
          (1 / mu) * (alpha mu r * vecSq (qOld - qNew)) := by ring
      _ ≤ (1 / mu) * (1 * vecSq (qOld - qNew)) := halphaScaled
      _ = 1 / mu * vecSq (qOld - qNew) := by ring
  have hqmetric0 : 0 ≤ 1 / mu * vecSq (qOld - qNew) :=
    mul_nonneg hmuinv hq0
  have hcost :
      2 * alpha mu r / mu * vecSq (qOld - qNew) +
          r * vecSq (yOld - yNew) ≤
        3 * r * D ^ 2 := by
    calc
      2 * alpha mu r / mu * vecSq (qOld - qNew) +
          r * vecSq (yOld - yNew) ≤
        2 * (1 / mu * vecSq (qOld - qNew)) +
          r * vecSq (yOld - yNew) := by
            have hqalpha2 :
                2 * alpha mu r / mu * vecSq (qOld - qNew) ≤
                  2 * (1 / mu * vecSq (qOld - qNew)) := by
              calc
                2 * alpha mu r / mu * vecSq (qOld - qNew) =
                    2 * (alpha mu r / mu * vecSq (qOld - qNew)) := by ring
                _ ≤ 2 * (1 / mu * vecSq (qOld - qNew)) :=
                  mul_le_mul_of_nonneg_left hqalpha (by norm_num)
            simpa only [add_comm] using
              add_le_add_right hqalpha2 (r * vecSq (yOld - yNew))
      _ ≤ 4 * (1 / mu * vecSq (qOld - qNew) +
          r / 4 * vecSq (yOld - yNew)) := by nlinarith
      _ ≤ 3 * r * D ^ 2 := by nlinarith
  unfold slowEnergy
  rw [haeq]
  have hslowOldQ : 0 ≤ alpha mu r / mu * vecSq (S.q - qOld) :=
    mul_nonneg hqcoef (Tracking.vecSq_nonneg _)
  have hslowOldY : 0 ≤ r * vecSq (S.y - yOld) :=
    mul_nonneg hr.le (Tracking.vecSq_nonneg _)
  have hrD2 : 0 ≤ r * D ^ 2 := mul_nonneg hr.le (sq_nonneg D)
  calc
    2 * (alpha mu r / 2) / mu * vecSq (S.q - qNew) +
        2 * (r / 4) * vecSq (S.y - yNew) =
      alpha mu r / mu * vecSq (S.q - qNew) +
        r / 2 * vecSq (S.y - yNew) := by ring
    _ ≤ alpha mu r / mu *
          (2 * vecSq (S.q - qOld) + 2 * vecSq (qOld - qNew)) +
        r / 2 *
          (2 * vecSq (S.y - yOld) + 2 * vecSq (yOld - yNew)) :=
      add_le_add hqscaled hyscaled
    _ = 2 * alpha mu r / mu * vecSq (S.q - qOld) +
        r * vecSq (S.y - yOld) +
        (2 * alpha mu r / mu * vecSq (qOld - qNew) +
          r * vecSq (yOld - yNew)) := by ring
    _ ≤ 2 * alpha mu r / mu * vecSq (S.q - qOld) +
        2 * r * vecSq (S.y - yOld) + 6 * r * D ^ 2 := by
      nlinarith

/-- Curvature transfer for the feasible fast gap. -/
theorem fastGap_quarter_le {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r D : ℝ}
    (hr : 0 < r) (_hD : 0 ≤ D)
    (hYnorm : ∀ y : Y, vecSq y.1 ≤ D ^ 2)
    {qOld qNew : EVec m} {yOld yNew : Y}
    (hOldMin : ∀ q (y : Y),
      Pzr X Y H mu r qOld yOld ≤ Pzr X Y H mu r q y)
    (S : ValidState (m := m) Y) :
    2 * fastGap X Y H mu (r / 4) qNew yNew S ≤
      2 * fastGap X Y H mu r qOld yOld S +
        (3 / 4 : ℝ) * r * D ^ 2 := by
  have hmin := hOldMin qNew yNew
  have hyNewBall : vecSq yNew.1 ≤ D ^ 2 := hYnorm yNew
  have hyFast0 := Tracking.vecSq_nonneg S.1.yFast
  have hc : 0 ≤ 3 * r / 8 := by positivity
  unfold fastGap
  rw [Pzr_quarter_identity, Pzr_quarter_identity]
  nlinarith [mul_le_mul_of_nonneg_left hyNewBall hc,
    mul_nonneg hc hyFast0]

/-- TeX curvature transfer `E_{r/4}(S) ≤ E_r(S) + 27rD²/4`, proved on
the real constrained objective and a feasible fast state. -/
theorem concrete_curvature_transfer {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r D : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hD : 0 ≤ D)
    (hrmu : r ≤ mu / 8)
    (hYnorm : ∀ y : Y, vecSq y.1 ≤ D ^ 2)
    {qOld qNew : EVec m} {yOld yNew : Y}
    {xOld xNew : EVec m} {wOld wNew : EVec n}
    (hsubOld : IsGammaSubgradient X Y H qOld yOld xOld wOld)
    (hstationQOld : xOld + mu⁻¹ • qOld = 0)
    (hstationYOld : wOld + r • yOld.1 = 0)
    (hsubNew : IsGammaSubgradient X Y H qNew yNew xNew wNew)
    (hstationQNew : xNew + mu⁻¹ • qNew = 0)
    (hstationYNew : wNew + (r / 4) • yNew.1 = 0)
    (S : ValidState (m := m) Y) :
    concreteEnergy X Y H mu (r / 4) qNew yNew S ≤
      concreteEnergy X Y H mu r qOld yOld S +
        (27 / 4 : ℝ) * r * D ^ 2 := by
  have hdrift := Pzr_quarter_minimizer_drift hmu hr hD hYnorm hsubOld
    hstationQOld hstationYOld hsubNew hstationQNew hstationYNew
  have hslow := slowEnergy_quarter_le hmu hr hD hrmu hdrift S.1
  have hOldMin :=
    (Pzr_unique_minimizer hmu hr hsubOld hstationQOld hstationYOld).1
  have hfast := fastGap_quarter_le (qNew := qNew) (yNew := yNew)
    hr hD hYnorm hOldMin S
  unfold concreteEnergy
  exact Tracking.curvature_transfer_from_parts hslow hfast

/-- One concrete homotopy stage: first transfer from `r` to `r/4`, then run
the actual relative-FOAM block with contraction factor `1/8`. -/
theorem concrete_homotopy_stage {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r D : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hD : 0 ≤ D)
    (hrmu : r ≤ mu / 8)
    (hYnorm : ∀ y : Y, vecSq y.1 ≤ D ^ 2)
    {qOld qNew : EVec m} {yOld yNew : Y}
    {xOld xNew : EVec m} {wOld wNew : EVec n}
    (hsubOld : IsGammaSubgradient X Y H qOld yOld xOld wOld)
    (hstationQOld : xOld + mu⁻¹ • qOld = 0)
    (hstationYOld : wOld + r • yOld.1 = 0)
    (hsubNew : IsGammaSubgradient X Y H qNew yNew xNew wNew)
    (hstationQNew : xNew + mu⁻¹ • qNew = 0)
    (hstationYNew : wNew + (r / 4) • yNew.1 = 0)
    (oracle : ValidState (m := m) Y → MicroOutput m n)
    (hyNext : ∀ S, (oracle S).yFastNext ∈ Y)
    (horacleSubgrad : ∀ S, IsGammaSubgradient X Y H (oracle S).qFastNext
      ⟨(oracle S).yFastNext, hyNext S⟩ (oracle S).xFast (oracle S).wFastNext)
    (hres : ∀ S, RelativeResidual mu (r / 4) S.1 (oracle S))
    (S0 : ValidState (m := m) Y) :
    let S1 :=
      ((foamStep mu (r / 4) oracle hyNext)^[
        blockIterations (alpha mu (r / 4)) (1 / 8 : ℝ)] S0)
    concreteEnergy X Y H mu (r / 4) qNew yNew S1 ≤
      (concreteEnergy X Y H mu r qOld yOld S0 +
        (27 / 4 : ℝ) * r * D ^ 2) / 8 := by
  dsimp
  have hr4 : 0 < r / 4 := by positivity
  have hr4mu : r / 4 ≤ mu / 8 := by nlinarith
  have hNewMin :=
    (Pzr_unique_minimizer hmu hr4 hsubNew hstationQNew hstationYNew).1
  have hblock := block_energy_contraction hmu hr4 hr4mu qNew yNew hNewMin
    oracle hyNext horacleSubgrad hres S0
    (by norm_num : (0 : ℝ) < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1)
  have hblock' :
      concreteEnergy X Y H mu (r / 4) qNew yNew
          ((foamStep mu (r / 4) oracle hyNext)^[
            blockIterations (alpha mu (r / 4)) (1 / 8 : ℝ)] S0) ≤
        (1 / 8 : ℝ) * concreteEnergy X Y H mu (r / 4) qNew yNew S0 := by
    calc
      concreteEnergy X Y H mu (r / 4) qNew yNew
          ((foamStep mu (r / 4) oracle hyNext)^[
            blockIterations (alpha mu (r / 4)) (1 / 8 : ℝ)] S0) =
        energy mu (r / 4) qNew yNew.1 (PzrTotal X Y H mu (r / 4))
          (Pzr X Y H mu (r / 4) qNew yNew)
          (((foamStep mu (r / 4) oracle hyNext)^[
            blockIterations (alpha mu (r / 4)) (1 / 8 : ℝ)] S0).1) :=
        concreteEnergy_eq_energy X Y H mu (r / 4) qNew yNew _
      _ ≤ (1 / 8 : ℝ) *
          energy mu (r / 4) qNew yNew.1 (PzrTotal X Y H mu (r / 4))
            (Pzr X Y H mu (r / 4) qNew yNew) S0.1 := hblock
      _ = (1 / 8 : ℝ) *
          concreteEnergy X Y H mu (r / 4) qNew yNew S0 := by
        rw [concreteEnergy_eq_energy]
  have htransfer := concrete_curvature_transfer hmu hr hD hrmu hYnorm hsubOld
    hstationQOld hstationYOld hsubNew hstationQNew hstationYNew S0
  nlinarith

/-- The concrete stage is the analytic realization of the existing scalar
homotopy recurrence. -/
theorem concrete_stage_respects_majorant {r D B Eold Enew : ℝ}
    (hold : Eold ≤ B)
    (hnew : Enew ≤ (Eold + (27 / 4 : ℝ) * r * D ^ 2) / 8) :
    Enew ≤ (B + (27 / 4 : ℝ) * r * D ^ 2) / 8 := by
  linarith

/-- Concrete counterpart of one `HomotopyRecurrence` step: an old-stage
majorant is transferred and contracted without assuming either operation. -/
theorem concrete_homotopy_stage_majorized {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r D B : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) (hD : 0 ≤ D)
    (hrmu : r ≤ mu / 8)
    (hYnorm : ∀ y : Y, vecSq y.1 ≤ D ^ 2)
    {qOld qNew : EVec m} {yOld yNew : Y}
    {xOld xNew : EVec m} {wOld wNew : EVec n}
    (hsubOld : IsGammaSubgradient X Y H qOld yOld xOld wOld)
    (hstationQOld : xOld + mu⁻¹ • qOld = 0)
    (hstationYOld : wOld + r • yOld.1 = 0)
    (hsubNew : IsGammaSubgradient X Y H qNew yNew xNew wNew)
    (hstationQNew : xNew + mu⁻¹ • qNew = 0)
    (hstationYNew : wNew + (r / 4) • yNew.1 = 0)
    (oracle : ValidState (m := m) Y → MicroOutput m n)
    (hyNext : ∀ S, (oracle S).yFastNext ∈ Y)
    (horacleSubgrad : ∀ S, IsGammaSubgradient X Y H (oracle S).qFastNext
      ⟨(oracle S).yFastNext, hyNext S⟩ (oracle S).xFast (oracle S).wFastNext)
    (hres : ∀ S, RelativeResidual mu (r / 4) S.1 (oracle S))
    (S0 : ValidState (m := m) Y)
    (hold : concreteEnergy X Y H mu r qOld yOld S0 ≤ B) :
    let S1 :=
      ((foamStep mu (r / 4) oracle hyNext)^[
        blockIterations (alpha mu (r / 4)) (1 / 8 : ℝ)] S0)
    concreteEnergy X Y H mu (r / 4) qNew yNew S1 ≤
      (B + (27 / 4 : ℝ) * r * D ^ 2) / 8 := by
  dsimp
  have hstage := concrete_homotopy_stage hmu hr hD hrmu hYnorm hsubOld
    hstationQOld hstationYOld hsubNew hstationQNew hstationYNew oracle
    hyNext horacleSubgrad hres S0
  dsimp at hstage
  exact concrete_stage_respects_majorant hold hstage

/-- With `r = r₀/4^j`, the right side of the concrete stage theorem is
definitionally the next value of `Tracking.homotopyMajorant`. -/
theorem concrete_stage_matches_homotopyMajorant
    {r0 D B0 Eold Enew : ℝ} (j : ℕ)
    (hold : Eold ≤ Tracking.homotopyMajorant r0 (D ^ 2) B0 j)
    (hnew : Enew ≤
      (Eold + (27 / 4 : ℝ) * Tracking.curvature r0 j * D ^ 2) / 8) :
    Enew ≤ Tracking.homotopyMajorant r0 (D ^ 2) B0 (j + 1) := by
  simpa [Tracking.homotopyMajorant] using
    concrete_stage_respects_majorant hold hnew

end

end HomotopyConcrete
end Upper
end NCCLowerBoundVerification
