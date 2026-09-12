import NCCLowerBoundVerification.Upper.HomotopyRun
import NCCLowerBoundVerification.Upper.UniformSchedule

/-!
# Fully assembled uniform upper guarantee

This file combines the actual startup state, finite homotopy run, moving-anchor
trajectory, perturbation comparison, and literal ceiling horizon.  The only
input left abstract here is the class-instantiated family of bottom-level
systems; `SystemInstantiation` supplies that family.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace UniformTheorem

noncomputable section

open HomotopyRun HomotopySchedule UniformSchedule InitialGapBounds
open OuterTrajectoryConcrete

set_option maxHeartbeats 3000000

theorem exists_OS_with_system_family {m n : Nat}
    {ell D Delta eps : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    (heps : 0 < eps)
    {prox : ProxFamily P.X P.Y P.f ell (ell / 8)}
    (systems : SystemFamily P.X P.Y P.f ell (ell / 8) prox) :
    let target := targetCurvature ell D eps
    let J := homotopyStage (ell / 8) target
      (div_pos hP.ell_pos (by norm_num))
      (targetCurvature_pos hP.ell_pos hP.D_pos heps)
    let r := Tracking.curvature (ell / 8) J
    let S0 := HomotopyRun.startupState (systems 0) hzero
    let B0 := 8 * (Delta + (ell / 8) * D ^ 2)
    let R0 := homotopySnapshot (D := D) (B0 := B0)
      systems P.x0 S0 J
    let T := paperOuterIterations ell Delta r D eps
    ∃ t < T, IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (trajectory (systems J) R0 t).z := by
  dsimp
  let target := targetCurvature ell D eps
  have htarget : 0 < target := targetCurvature_pos hP.ell_pos hP.D_pos heps
  let J := homotopyStage (ell / 8) target
    (div_pos hP.ell_pos (by norm_num)) htarget
  let r := Tracking.curvature (ell / 8) J
  let S0 : RelativeFOAMContraction.ValidState (m := m) P.Y :=
    HomotopyRun.startupState (systems 0) hzero
  let B0 : ℝ := 8 * (Delta + (ell / 8) * D ^ 2)
  let R0 : Snapshot (m := m) P.Y :=
    homotopySnapshot (D := D) (B0 := B0) systems P.x0 S0 J
  let T := paperOuterIterations ell Delta r D eps
  have hr : 0 < r := by
    dsimp [r]
    exact HomotopyCost.curvature_pos (div_pos hP.ell_pos (by norm_num)) J
  have hrupper : r ≤ target := by
    dsimp [r, J]
    exact homotopyStage_spec (div_pos hP.ell_pos (by norm_num)) htarget
  have hrle : r ≤ ell / 8 :=
    hrupper.trans (targetCurvature_le_ell_div_eight
      (ell := ell) (D := D) (eps := eps))
  have hinit := initialized_homotopy_snapshot hP hzero systems J
  have hE0 : snapshotEnergy (systems J) R0 ≤ R0.B := by
    simpa [R0, S0, B0] using hinit.1
  have hB0 : 0 ≤ R0.B := by
    simpa [R0, S0, B0] using hinit.2.1
  have hBupper : R0.B ≤ 15 * (Delta + r * D ^ 2) := by
    simpa [R0, S0, B0, r] using hinit.2.2
  have hpotential : snapshotPotential (systems J) R0 -
      regularizedClassLower P r D ≤ 31 * (Delta + r * D ^ 2) := by
    exact initial_snapshot_potential_bound hP hzero hr.le (systems J) R0
      (by simp [R0]) hBupper
  have hTpos : 0 < T := by
    dsimp [T]
    exact paperOuterIterations_pos hP.ell_pos hP.Delta_pos hr.le heps
  have hcoeff : 0 ≤ 32 * ell / (T : ℝ) := by
    have hTreal : (0 : ℝ) < T := by exact_mod_cast hTpos
    exact div_nonneg (mul_nonneg (by norm_num) hP.ell_pos.le) hTreal.le
  have hcertificateCompare :
      (32 * ell / (T : ℝ)) *
          (snapshotPotential (systems J) R0 - regularizedClassLower P r D) ≤
        (32 * ell / (T : ℝ)) * (31 * (Delta + r * D ^ 2)) :=
    mul_le_mul_of_nonneg_left hpotential hcoeff
  have hcertificate :
      (32 * ell / (T : ℝ)) *
          (snapshotPotential (systems J) R0 - regularizedClassLower P r D) ≤
        eps ^ 2 / 4 := by
    exact le_of_lt (paper_certificate_budget hP.ell_pos hP.Delta_pos hr.le
      heps (by simpa [T] using hcertificateCompare))
  have hbias : 2 * ell * r * D ^ 2 ≤ eps ^ 2 / 4 :=
    homotopy_output_bias_budget hP.ell_pos hP.D_pos heps hr hrupper
  have hweak : IsWeaklyConvexOn ell P.X (ValueOn P.Y P.f) := by
    simpa [IsWeaklyConvexOn, quadraticCorrection] using hP.value_weakConvexity
  have hweakR : IsWeaklyConvexOn ell P.X
      (DualRegularizedValueOn P.Y P.f r) :=
    NCCLowerBoundVerification.Upper.IsNCCClass.regularizedValue_weaklyConvex hP
  let hexists : HasProxEverywhere P.X (ValueOn P.Y P.f) ell :=
    NCCLowerBoundVerification.Upper.IsNCCClass.value_hasProxEverywhere hP
  have hlower : ∀ z, regularizedClassLower P r D ≤
      regularizedEnvelope P.X P.Y P.f ell r (prox J) z := by
    intro z
    exact regularizedClassLower_le_envelope hP hzero hr.le hP.ell_pos.le
      (prox J) z
  have hYnorm : ∀ y ∈ P.Y, vecSq y ≤ D ^ 2 :=
    NCCLowerBoundVerification.Upper.IsNCCClass.dual_vecSq_le hP hzero
  have hmax : ∀ x, ∃ y, IsMaximizerOn P.Y P.f x y :=
    NCCLowerBoundVerification.Upper.IsNCCClass.maximum_attained_everywhere hP
  have hmaxR : ∀ x, ∃ y, IsMaximizerOn P.Y
      (fun u v ↦ P.f u v - r / 2 * vecSq v) x y :=
    NCCLowerBoundVerification.Upper.IsNCCClass.regularized_maximum_attained hP
  exact exists_original_OS_on_trajectory hP.X_nonempty hP.ell_pos hr hrle
    heps.le hweak hweakR hexists hYnorm hmax hmaxR (systems J) R0 hE0 hB0
    hTpos hlower hcertificate hbias

end

end UniformTheorem
end Upper
end NCCLowerBoundVerification
