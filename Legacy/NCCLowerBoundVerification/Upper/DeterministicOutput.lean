import NCCLowerBoundVerification.Upper.MainTheorem

/-!
# Deterministic minimum-certificate output

The outer analysis first proves that some finite trajectory certificate is
small.  The printed algorithm does not choose that existential witness: it
returns the least-certificate index with deterministic tie breaking.  This
file makes that final selection literal and proves that the selected anchor
is the stationary one.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace DeterministicOutput

noncomputable section

open OuterTrajectoryConcrete
open HomotopyRun HomotopySchedule UniformSchedule InitialGapBounds

private theorem exists_certificateIndex {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (T : Nat) (hT : 0 < T) :
    ∃ t : Fin T, ∀ s : Fin T,
      stepCertificate sys (trajectory sys R0 t.1) ≤
        stepCertificate sys (trajectory sys R0 s.1) := by
  letI : Nonempty (Fin T) := Fin.pos_iff_nonempty.mp hT
  let score : Fin T → ℝ := fun t =>
    stepCertificate sys (trajectory sys R0 t.1)
  obtain ⟨t, _ht, hmin⟩ := Set.exists_min_image
    (Set.univ : Set (Fin T)) score Set.finite_univ Set.univ_nonempty
  exact ⟨t, fun s => hmin s (Set.mem_univ s)⟩

/-- A deterministic minimizer of the computable certificate over `0,...,T-1`.
Classical choice fixes one of the finitely many minimizers. -/
def certificateIndex {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (T : Nat) (hT : 0 < T) : Fin T :=
  Classical.choose (exists_certificateIndex sys R0 T hT)

theorem certificateIndex_minimal {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) {T : Nat} (hT : 0 < T) (t : Fin T) :
    stepCertificate sys
        (trajectory sys R0 (certificateIndex sys R0 T hT).1) ≤
      stepCertificate sys (trajectory sys R0 t.1) := by
  exact Classical.choose_spec (exists_certificateIndex sys R0 T hT) t

/-- The literal anchor returned by the paper's deterministic tie-breaking
rule. -/
def selectedAnchor {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (T : Nat) (hT : 0 < T) : EVec m :=
  (trajectory sys R0 (certificateIndex sys R0 T hT).1).z

/-- Minimum-certificate form of the full finite-horizon theorem.  Unlike the
existential trajectory theorem, the conclusion names the exact deterministic
output selected by the algorithm. -/
theorem selectedAnchor_is_OS {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r D eps lower : ℝ} {T : Nat}
    (hX : X.Nonempty) (hell : 0 < ell) (hr : 0 < r)
    (hrle : r ≤ ell / 8) (heps : 0 ≤ eps)
    (hweak : IsWeaklyConvexOn ell X (ValueOn Y f))
    (hweakR : IsWeaklyConvexOn ell X (DualRegularizedValueOn Y f r))
    (hexists : HasProxEverywhere X (ValueOn Y f) ell)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (hYnorm : ∀ y ∈ Y, vecSq y ≤ D ^ 2)
    (hmax : ∀ x, ∃ y, IsMaximizerOn Y f x y)
    (hmaxR : ∀ x, ∃ y, IsMaximizerOn Y
      (fun u v => f u v - r / 2 * vecSq v) x y)
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (hE0 : snapshotEnergy sys R0 ≤ R0.B)
    (hB0 : 0 ≤ R0.B) (hT : 0 < T)
    (hlower : ∀ z, lower ≤ regularizedEnvelope X Y f ell r hexistsR z)
    (hcertificateBudget :
      (32 * ell / T) * (snapshotPotential sys R0 - lower) ≤ eps ^ 2 / 4)
    (hbiasBudget : 2 * ell * r * D ^ 2 ≤ eps ^ 2 / 4) :
    IsOptimizationStationary X (ValueOn Y f) ell eps
      (selectedAnchor sys R0 T hT) := by
  obtain ⟨t, ht, hsmall⟩ := exists_small_trajectory_certificate
    hX hell hr hrle hweakR sys R0 hE0 hB0 hT hlower
  let ti : Fin T := ⟨t, ht⟩
  let ts := certificateIndex sys R0 T hT
  have hmin : stepCertificate sys (trajectory sys R0 ts.1) ≤
      stepCertificate sys (trajectory sys R0 ti.1) :=
    certificateIndex_minimal sys R0 hT ti
  have hnonneg (j : Nat) :
      0 ≤ stepCertificate sys (trajectory sys R0 j) := by
    unfold stepCertificate Tracking.certificate
    have hBj : 0 ≤ (trajectory sys R0 j).B :=
      trajectory_B_nonneg hell.le sys R0 hB0 j
    have hd : 0 ≤ vecSq (stepDisplacement sys (trajectory sys R0 j)) :=
      Tracking.vecSq_nonneg _
    positivity
  have hsq : stepCertificate sys (trajectory sys R0 ts.1) ^ 2 ≤
      stepCertificate sys (trajectory sys R0 ti.1) ^ 2 := by
    nlinarith [hnonneg ts.1, hnonneg ti.1]
  have hcert : stepCertificate sys (trajectory sys R0 ts.1) ^ 2 ≤
      eps ^ 2 / 4 := by
    exact hsq.trans (hsmall.trans hcertificateBudget)
  unfold selectedAnchor
  exact original_OS_of_small_certificate hell hr heps hweak hweakR hexists
    hYnorm hmax hmaxR sys (trajectory sys R0 ts.1)
    (trajectory_B_nonneg hell.le sys R0 hB0 ts.1)
    (trajectory_energy_le_B hX hell hr hrle sys R0 hE0 ts.1)
    hcert hbiasBudget

/- Fully assembled version of `selectedAnchor_is_OS` for an actual homotopy
system family.  This is the deterministic-output strengthening of
`UniformTheorem.exists_OS_with_system_family`. -/
set_option maxHeartbeats 3000000 in
theorem selected_OS_with_system_family {m n : Nat}
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
    let hT : 0 < T := paperOuterIterations_pos hP.ell_pos hP.Delta_pos
      (HomotopyCost.curvature_pos
        (div_pos hP.ell_pos (by norm_num)) J).le
      heps
    IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (selectedAnchor (systems J) R0 T hT) := by
  dsimp only
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
      32 * ell / (T : ℝ) *
          (snapshotPotential (systems J) R0 - regularizedClassLower P r D) ≤
        32 * ell / (T : ℝ) * (31 * (Delta + r * D ^ 2)) :=
    mul_le_mul_of_nonneg_left hpotential hcoeff
  have hcertificate :
      32 * ell / (T : ℝ) *
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
      (fun u v => P.f u v - r / 2 * vecSq v) x y :=
    NCCLowerBoundVerification.Upper.IsNCCClass.regularized_maximum_attained hP
  exact selectedAnchor_is_OS hP.X_nonempty hP.ell_pos hr hrle heps.le
    hweak hweakR hexists hYnorm hmax hmaxR (systems J) R0 hE0 hB0
    hTpos hlower hcertificate hbias

/-- Class-instantiated deterministic output under the temporary dual-origin
normalization. -/
theorem selected_OS_of_class_zero {m n : Nat}
    {ell D Delta eps : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    (heps : 0 < eps) :
    let prox := MainTheorem.classProxFamily hP
    let systems := MainTheorem.classSystemFamily hP
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
    let hT : 0 < T := paperOuterIterations_pos hP.ell_pos hP.Delta_pos
      (HomotopyCost.curvature_pos
        (div_pos hP.ell_pos (by norm_num)) J).le heps
    IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (selectedAnchor (systems J) R0 T hT) := by
  exact selected_OS_with_system_family hP hzero heps
    (MainTheorem.classSystemFamily hP)

/-- The exact deterministic output after translating an arbitrary feasible
dual basepoint to zero, with its certificate transferred back to the original
value function. -/
theorem selected_OS_of_class_at_dual_basepoint {m n : Nat}
    {ell D Delta eps : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) {ybar : EVec n} (hybar : ybar ∈ P.Y)
    (heps : 0 < eps) :
    let Pbar := DualTranslation.translatedInstance P ybar
    let hPbar := DualTranslation.IsNCCClass.translateDual hP hybar
    let prox := MainTheorem.classProxFamily hPbar
    let systems := MainTheorem.classSystemFamily hPbar
    let target := targetCurvature ell D eps
    let J := homotopyStage (ell / 8) target
      (div_pos hP.ell_pos (by norm_num))
      (targetCurvature_pos hP.ell_pos hP.D_pos heps)
    let r := Tracking.curvature (ell / 8) J
    let hzero := DualTranslation.zero_mem_translatedDualSet hybar
    let S0 := HomotopyRun.startupState (systems 0) hzero
    let B0 := 8 * (Delta + (ell / 8) * D ^ 2)
    let R0 := homotopySnapshot (D := D) (B0 := B0)
      systems Pbar.x0 S0 J
    let T := paperOuterIterations ell Delta r D eps
    let hT : 0 < T := paperOuterIterations_pos hP.ell_pos hP.Delta_pos
      (HomotopyCost.curvature_pos
        (div_pos hP.ell_pos (by norm_num)) J).le heps
    IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (selectedAnchor (systems J) R0 T hT) := by
  dsimp only
  let Pbar := DualTranslation.translatedInstance P ybar
  let hPbar := DualTranslation.IsNCCClass.translateDual hP hybar
  let systems := MainTheorem.classSystemFamily hPbar
  have htranslated := selected_OS_of_class_zero hPbar
    (DualTranslation.zero_mem_translatedDualSet hybar) heps
  dsimp only at htranslated
  apply MainTheorem.optimizationStationary_congr_on (X := P.X) ?_ htranslated
  intro u hu
  exact DualTranslation.translatedValue_eq (hP.maximum_attained u hu)

/-- Normalization-free named output of the complete deterministic upper
algorithm. -/
theorem selected_OS_of_class {m n : Nat}
    {ell D Delta eps : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (heps : 0 < eps) :
    let ybar := MainTheorem.classDualBasepoint hP
    let Pbar := DualTranslation.translatedInstance P ybar
    let hPbar := DualTranslation.IsNCCClass.translateDual hP
      (MainTheorem.classDualBasepoint_mem hP)
    let systems := MainTheorem.classSystemFamily hPbar
    let target := targetCurvature ell D eps
    let J := homotopyStage (ell / 8) target
      (div_pos hP.ell_pos (by norm_num))
      (targetCurvature_pos hP.ell_pos hP.D_pos heps)
    let r := Tracking.curvature (ell / 8) J
    let hzero := DualTranslation.zero_mem_translatedDualSet
      (MainTheorem.classDualBasepoint_mem hP)
    let S0 := HomotopyRun.startupState (systems 0) hzero
    let B0 := 8 * (Delta + (ell / 8) * D ^ 2)
    let R0 := homotopySnapshot (D := D) (B0 := B0)
      systems Pbar.x0 S0 J
    let T := paperOuterIterations ell Delta r D eps
    let hT : 0 < T := paperOuterIterations_pos hP.ell_pos hP.Delta_pos
      (HomotopyCost.curvature_pos
        (div_pos hP.ell_pos (by norm_num)) J).le heps
    IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (selectedAnchor (systems J) R0 T hT) := by
  exact selected_OS_of_class_at_dual_basepoint hP
    (MainTheorem.classDualBasepoint_mem hP) heps

end

end DeterministicOutput
end Upper
end NCCLowerBoundVerification
