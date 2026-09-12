import NCCLowerBoundVerification.Upper.ClassAnalytic
import NCCLowerBoundVerification.Upper.OuterTrajectoryConcrete

/-!
# Concrete lower levels and initial-gap bounds for the upper algorithm

This module turns the class's `sInf` gap into the particular lower level used
by startup, homotopy, and the final outer averaging argument.  It closes the
otherwise easy-to-miss link between the abstract initial-gap field and the
actual selected regularized proximal point.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace InitialGapBounds

noncomputable section

open OuterTrajectoryConcrete

def classValueInf {m n : Nat} (P : NCCInstance m n) : ℝ :=
  sInf (ValueOn P.Y P.f '' P.X)

def regularizedClassLower {m n : Nat} (P : NCCInstance m n)
    (r D : ℝ) : ℝ :=
  classValueInf P - r / 2 * D ^ 2

theorem classValueInf_le {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    {x : EVec m} (hx : x ∈ P.X) :
    classValueInf P ≤ ValueOn P.Y P.f x := by
  unfold classValueInf
  exact csInf_le hP.value_bddBelow ⟨x, hx, rfl⟩

theorem regularizedClassLower_le {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (hr : 0 ≤ r)
    {x : EVec m} (hx : x ∈ P.X) :
    regularizedClassLower P r D ≤
      DualRegularizedValueOn P.Y P.f r x := by
  have hbias := dualRegularizedValue_bias hr
    (NCCLowerBoundVerification.Upper.IsNCCClass.dual_vecSq_le hP hzero)
    (hP.maximum_attained x hx)
    (NCCLowerBoundVerification.Upper.IsNCCClass.regularized_maximum_attained hP x)
  have hinf := classValueInf_le hP hx
  unfold regularizedClassLower
  linarith

theorem regularized_initial_gap {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (hr : 0 ≤ r) :
    DualRegularizedValueOn P.Y P.f r P.x0 -
        regularizedClassLower P r D ≤ Delta + r / 2 * D ^ 2 := by
  have hbias := dualRegularizedValue_bias hr
    (NCCLowerBoundVerification.Upper.IsNCCClass.dual_vecSq_le hP hzero)
    (hP.maximum_attained P.x0 hP.x0_mem)
    (NCCLowerBoundVerification.Upper.IsNCCClass.regularized_maximum_attained hP P.x0)
  unfold regularizedClassLower classValueInf
  linarith [hP.initial_gap]

/-- The actual selected regularized prox point obeys the startup displacement
bound used by `startup_pzr_computable_majorant`. -/
theorem selected_regularizedProx_displacement {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    (hr : 0 ≤ r)
    (hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell) :
    ell * vecSq (P.x0 - selectedProx hexistsR P.x0) ≤
      Delta + r / 2 * D ^ 2 := by
  apply TrackingAnalytic.prox_displacement_from_initial_gap hP.x0_mem
    (selectedProx_spec hexistsR P.x0)
    (regularizedClassLower_le hP hzero hr
      (selectedProx_spec hexistsR P.x0).1)
  exact regularized_initial_gap hP hzero hr

/-- The chosen lower level also bounds the genuine regularized Moreau
envelope at every anchor. -/
theorem regularizedClassLower_le_envelope {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    (hr : 0 ≤ r) (hell : 0 ≤ ell)
    (hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell) (z : EVec m) :
    regularizedClassLower P r D ≤
      regularizedEnvelope P.X P.Y P.f ell r hexistsR z := by
  have hvalue := regularizedClassLower_le hP hzero hr
    (selectedProx_spec hexistsR z).1
  have hsq : 0 ≤ ell * vecSq (selectedProx hexistsR z - z) := by
    exact mul_nonneg hell (Tracking.vecSq_nonneg _)
  unfold regularizedEnvelope moreauEnvelope proxObjective
  linarith

/-- At the original anchor, the regularized Moreau envelope inherits the same
`Delta + r D²/2` upper gap. -/
theorem initial_envelope_gap {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y) (hr : 0 ≤ r)
    (hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell) :
    regularizedEnvelope P.X P.Y P.f ell r hexistsR P.x0 -
        regularizedClassLower P r D ≤ Delta + r / 2 * D ^ 2 := by
  have hprox := (selectedProx_spec hexistsR P.x0).2 P.x0 hP.x0_mem
  have hzeroSq : vecSq (P.x0 - P.x0) = 0 := by
    simp [vecSq, NCPLVerification.vecSq]
  unfold regularizedEnvelope moreauEnvelope proxObjective
  rw [hzeroSq] at hprox
  have hgap := regularized_initial_gap hP hzero hr
  linarith

/-- The constant `31` in the final certificate calculation follows from a
homotopy energy majorant `B ≤ 15 (Delta + r D²)`. -/
theorem initial_snapshot_potential_bound {m n : Nat}
    {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    (hr : 0 ≤ r)
    {hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell}
    (sys : OuterSystem P.X P.Y P.f ell r hexistsR)
    (R : Snapshot (m := m) P.Y) (hz : R.z = P.x0)
    (hB : R.B ≤ 15 * (Delta + r * D ^ 2)) :
    snapshotPotential sys R - regularizedClassLower P r D ≤
      31 * (Delta + r * D ^ 2) := by
  have henv := initial_envelope_gap hP hzero hr hexistsR
  unfold snapshotPotential
  rw [hz]
  nlinarith

end

end InitialGapBounds
end Upper
end NCCLowerBoundVerification
