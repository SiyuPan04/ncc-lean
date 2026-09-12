import NCCLowerBoundVerification.Upper.HomotopyConcrete
import NCCLowerBoundVerification.Upper.TrackingConcrete
import NCCLowerBoundVerification.Upper.ProjectionGeometry
import NCCLowerBoundVerification.Upper.FastReadoutConcrete
import NCCLowerBoundVerification.Upper.ScaledOperator

/-!
# The concrete tracked outer trajectory

The trajectory in this file contains the actual anchor, feasible FOAM state,
and computable majorant.  Its minimizers are stationary points of the real
constrained `Pzr`, tied to the selected proximal point of the regularized
value.  Moving-anchor tracking and block contraction are proved when needed;
neither is stored in the trajectory.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace OuterTrajectoryConcrete

noncomputable section

open PointwiseConjugate
open RelativeFOAM
open RelativeFOAMContraction
open TrackingConcrete

set_option maxHeartbeats 3000000

/-- A stationary minimizer of the real pointwise-conjugate objective at an
anchor.  Its primal support point is the actual selected proximal point. -/
structure StationaryAt {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (f : EVec m → EVec n → ℝ) (ell r : ℝ)
    (hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell)
    (z : EVec m) where
  qStar : EVec m
  yStar : Y
  wStar : EVec n
  subgradient : IsGammaSubgradient X Y (decurved f ell r z)
    qStar yStar (selectedProx hexistsR z) wStar
  stationQ : selectedProx hexistsR z + ell⁻¹ • qStar = 0
  stationY : wStar + r • yStar.1 = 0

/-- All bottom-level operations used by the outer method.  The fields are
local analytic/existence data: Euclidean projection, stationary solutions,
and the actual feasible micro oracle with its residual test. -/
structure OuterSystem {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (f : EVec m → EVec n → ℝ) (ell r : ℝ)
    (hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell) where
  projectX : EVec m → EVec m
  project_spec : ProjectionGeometry.IsEuclideanProjection X projectX
  gamma_bounded : ∀ z, GammaBddAbove X Y (decurved f ell r z)
  stationary : ∀ z, StationaryAt X Y f ell r hexistsR z
  oracle : EVec m → ValidState (m := m) Y → MicroOutput m n
  oracle_feasible : ∀ z S, (oracle z S).yFastNext ∈ Y
  oracle_subgradient : ∀ z S,
    IsGammaSubgradient X Y (decurved f ell r z) (oracle z S).qFastNext
      ⟨(oracle z S).yFastNext, oracle_feasible z S⟩
      (oracle z S).xFast (oracle z S).wFastNext
  oracle_residual : ∀ z S, RelativeResidual ell r S.1 (oracle z S)

/-- One visible outer snapshot. -/
structure Snapshot {m n : Nat} (Y : Set (EVec n)) where
  z : EVec m
  state : ValidState (m := m) Y
  B : ℝ

/-- Co-translation preserves fast-dual feasibility definitionally. -/
def coTranslateValid {m n : Nat} {Y : Set (EVec n)}
    (ell : ℝ) (d : EVec m) (S : ValidState (m := m) Y) :
    ValidState (m := m) Y :=
  ⟨Tracking.coTranslate ell d S.1, S.2⟩

/-- The real `rho = 1/400` block at a fixed anchor. -/
def runBlock {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (z : EVec m)
    (S : ValidState (m := m) Y) : ValidState (m := m) Y :=
  ((foamStep ell r (sys.oracle z) (sys.oracle_feasible z))^[
    blockIterations (alpha ell r) (1 / 400 : ℝ)] S)

/-- The paper's fast-state primal readout. -/
def readout {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (S : ValidState (m := m) Y) :
    EVec m :=
  sys.projectX ((-ell⁻¹) • S.1.qFast)

/-- One actual outer update. -/
def nextSnapshot {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (R : Snapshot (m := m) Y) :
    Snapshot (m := m) Y :=
  let zNext := readout sys R.state
  let d := zNext - R.z
  let shifted := coTranslateValid ell d R.state
  { z := zNext
    state := runBlock sys zNext shifted
    B := Tracking.nextMajorant (1 / 400) ell (vecSq d) R.B }

/-- The genuine recursively generated outer trajectory. -/
def trajectory {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) : ℕ → Snapshot (m := m) Y
  | 0 => R0
  | t + 1 => nextSnapshot sys (trajectory sys R0 t)

@[simp] theorem trajectory_zero {m n : Nat} {X : Set (EVec m)}
    {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) : trajectory sys R0 0 = R0 := rfl

@[simp] theorem trajectory_succ {m n : Nat} {X : Set (EVec m)}
    {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (t : ℕ) :
    trajectory sys R0 (t + 1) = nextSnapshot sys (trajectory sys R0 t) := rfl

/-- Hidden true energy at an explicit anchor and feasible state. -/
def energyAt {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (z : EVec m)
    (S : ValidState (m := m) Y) : ℝ :=
  let st := sys.stationary z
  constrainedEnergy ell r st.qStar st.yStar
    (Pzr X Y (decurved f ell r z) ell r)
    (Pzr X Y (decurved f ell r z) ell r st.qStar st.yStar) S.1 S.2

/-- Hidden true energy of a snapshot. -/
def snapshotEnergy {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (R : Snapshot (m := m) Y) : ℝ :=
  energyAt sys R.z R.state

/-- The constrained energy equals the total-function energy exactly on a
valid state. -/
theorem snapshotEnergy_eq_foamEnergy {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (R : Snapshot (m := m) Y) :
    snapshotEnergy sys R =
      energy ell r (sys.stationary R.z).qStar (sys.stationary R.z).yStar.1
        (PzrTotal X Y (decurved f ell r R.z) ell r)
        (Pzr X Y (decurved f ell r R.z) ell r
          (sys.stationary R.z).qStar (sys.stationary R.z).yStar) R.state.1 := by
  unfold snapshotEnergy energyAt constrainedEnergy energy
  rw [PzrTotal_of_mem X Y (decurved f ell r R.z) ell r
    R.state.1.qFast R.state.2]

/-- The readout error follows from real `Pzr` strong minimization and genuine
projection nonexpansiveness. -/
theorem readout_error_le_energy {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    (hell : 0 < ell) (hr : 0 < r)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (R : Snapshot (m := m) Y) :
    ell * vecSq (readout sys R.state - selectedProx hexistsR R.z) ≤
      snapshotEnergy sys R := by
  let st := sys.stationary R.z
  have hxmem : selectedProx hexistsR R.z ∈ X :=
    (selectedProx_spec hexistsR R.z).1
  have hread := FastReadoutConcrete.Pzr_fastState_readout hell hr hxmem
    st.subgradient st.stationQ st.stationY sys.project_spec
    R.state.1 R.state.2
  change ell * vecSq (readout sys R.state - selectedProx hexistsR R.z) ≤ _
  unfold snapshotEnergy energyAt
  dsimp only
  exact hread

/-- One explicit real co-translation followed by one real `1/400` FOAM
block, before packaging it as a trajectory step. -/
theorem translated_block_energy_le_majorant {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    (hX : X.Nonempty) (hell : 0 < ell) (hr : 0 < r)
    (hrle : r ≤ ell / 8)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (z d : EVec m) (S : ValidState (m := m) Y) (B : ℝ)
    (hEB : energyAt sys z S ≤ B) :
    energyAt sys (z + d)
        (runBlock sys (z + d) (coTranslateValid ell d S)) ≤
      Tracking.nextMajorant (1 / 400) ell (vecSq d) B := by
  let shifted := coTranslateValid ell d S
  let stOld := sys.stationary z
  let stNew := sys.stationary (z + d)
  have hanchor := Pzr_anchor_energy_bound hX f hell hr hrle z d
    (sys.gamma_bounded z) stOld.subgradient stOld.stationQ stOld.stationY
    stNew.subgradient stNew.stationQ stNew.stationY S.1 S.2
  have hscale :
      6 * (1 / ell * vecSq ((2 * ell) • d)) = 24 * ell * vecSq d := by
    rw [vecSq_smul]
    field_simp [ne_of_gt hell]
    ring
  rw [hscale] at hanchor
  have hanchor' :
      constrainedEnergy ell r stNew.qStar stNew.yStar
          (Pzr X Y (decurved f ell r (z + d)) ell r)
          (Pzr X Y (decurved f ell r (z + d)) ell r stNew.qStar stNew.yStar)
          shifted.1 shifted.2 ≤
        2 * energyAt sys z S + 24 * ell * vecSq d := by
    simpa only [energyAt, stOld, stNew, shifted, coTranslateValid] using hanchor
  have hnewMin :=
    (Pzr_unique_minimizer hell hr stNew.subgradient stNew.stationQ
      stNew.stationY).1
  have hblock := block_energy_contraction hell hr hrle stNew.qStar stNew.yStar
    hnewMin (sys.oracle (z + d)) (sys.oracle_feasible (z + d))
    (sys.oracle_subgradient (z + d)) (sys.oracle_residual (z + d)) shifted
    (by norm_num : (0 : ℝ) < 1 / 400) (by norm_num : (1 / 400 : ℝ) < 1)
  have hshiftEq :
      constrainedEnergy ell r stNew.qStar stNew.yStar
          (Pzr X Y (decurved f ell r (z + d)) ell r)
          (Pzr X Y (decurved f ell r (z + d)) ell r stNew.qStar stNew.yStar)
          shifted.1 shifted.2 =
        energy ell r stNew.qStar stNew.yStar.1
          (PzrTotal X Y (decurved f ell r (z + d)) ell r)
          (Pzr X Y (decurved f ell r (z + d)) ell r stNew.qStar stNew.yStar)
          shifted.1 := by
    unfold constrainedEnergy energy
    rw [PzrTotal_of_mem X Y (decurved f ell r (z + d)) ell r
      shifted.1.qFast shifted.2]
  have hblock' :
      energyAt sys (z + d) (runBlock sys (z + d) shifted) ≤
        (1 / 400 : ℝ) *
          constrainedEnergy ell r stNew.qStar stNew.yStar
            (Pzr X Y (decurved f ell r (z + d)) ell r)
            (Pzr X Y (decurved f ell r (z + d)) ell r stNew.qStar stNew.yStar)
            shifted.1 shifted.2 := by
    have houtEq :
        energyAt sys (z + d) (runBlock sys (z + d) shifted) =
          energy ell r stNew.qStar stNew.yStar.1
          (PzrTotal X Y (decurved f ell r (z + d)) ell r)
          (Pzr X Y (decurved f ell r (z + d)) ell r stNew.qStar stNew.yStar)
          (runBlock sys (z + d) shifted).1 := by
      unfold energyAt constrainedEnergy energy
      dsimp only
      rw [PzrTotal_of_mem X Y (decurved f ell r (z + d)) ell r
        (runBlock sys (z + d) shifted).1.qFast
        (runBlock sys (z + d) shifted).2]
    rw [houtEq, hshiftEq]
    exact hblock
  unfold Tracking.nextMajorant
  nlinarith

/-- The explicit theorem specialized to the readout-generated next
snapshot. -/
theorem next_energy_le_majorant {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    (hX : X.Nonempty) (hell : 0 < ell) (hr : 0 < r)
    (hrle : r ≤ ell / 8)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (R : Snapshot (m := m) Y)
    (hEB : snapshotEnergy sys R ≤ R.B) :
    snapshotEnergy sys (nextSnapshot sys R) ≤ (nextSnapshot sys R).B := by
  let zNext := readout sys R.state
  let d := zNext - R.z
  have hzd : R.z + d = zNext := by dsimp [d]; abel
  have h := translated_block_energy_le_majorant hX hell hr hrle sys
    R.z d R.state R.B hEB
  rw [hzd] at h
  simpa only [nextSnapshot, snapshotEnergy, zNext, d] using h

/-- Energy-majorant invariant along the recursively generated trajectory. -/
theorem trajectory_energy_le_B {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    (hX : X.Nonempty) (hell : 0 < ell) (hr : 0 < r)
    (hrle : r ≤ ell / 8)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (hE0 : snapshotEnergy sys R0 ≤ R0.B) :
    ∀ t, snapshotEnergy sys (trajectory sys R0 t) ≤ (trajectory sys R0 t).B := by
  intro t
  induction t with
  | zero => exact hE0
  | succ t ih =>
      exact next_energy_le_majorant hX hell hr hrle sys (trajectory sys R0 t) ih

/-! ## Outer potential and certificate on the real trajectory -/

def regularizedEnvelope {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (f : EVec m → EVec n → ℝ) (ell r : ℝ)
    (hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell) :
    EVec m → ℝ :=
  moreauEnvelope (DualRegularizedValueOn Y f r) ell hexistsR

def anchorError {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (_sys : OuterSystem X Y f ell r hexistsR)
    (R : Snapshot (m := m) Y) : EVec m :=
  R.z - selectedProx hexistsR R.z

def readoutError {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R : Snapshot (m := m) Y) : EVec m :=
  readout sys R.state - selectedProx hexistsR R.z

def stepDisplacement {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R : Snapshot (m := m) Y) : EVec m :=
  readout sys R.state - R.z

theorem displacement_eq {m n : Nat} {X : Set (EVec m)}
    {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R : Snapshot (m := m) Y) :
    stepDisplacement sys R = -anchorError sys R + readoutError sys R := by
  unfold stepDisplacement anchorError readoutError
  abel

def snapshotPotential {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (_sys : OuterSystem X Y f ell r hexistsR)
    (R : Snapshot (m := m) Y) : ℝ :=
  regularizedEnvelope X Y f ell r hexistsR R.z + 2 * R.B

def stepCertificate {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R : Snapshot (m := m) Y) : ℝ :=
  Tracking.certificate ell (vecSq (stepDisplacement sys R)) R.B

theorem next_B_nonneg {m n : Nat} {X : Set (EVec m)}
    {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    (hell : 0 ≤ ell)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R : Snapshot (m := m) Y) (hB : 0 ≤ R.B) :
    0 ≤ (nextSnapshot sys R).B := by
  unfold nextSnapshot Tracking.nextMajorant
  dsimp only
  have hd0 := Tracking.vecSq_nonneg
    (readout sys R.state - R.z)
  nlinarith

theorem trajectory_B_nonneg {m n : Nat} {X : Set (EVec m)}
    {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    (hell : 0 ≤ ell)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (hB0 : 0 ≤ R0.B) :
    ∀ t, 0 ≤ (trajectory sys R0 t).B := by
  intro t
  induction t with
  | zero => exact hB0
  | succ t ih => exact next_B_nonneg hell sys _ ih

/-- Actual Moreau descent for one readout step. -/
theorem one_step_outer_descent {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    (hell : 0 < ell) (hr : 0 < r)
    (hweakR : IsWeaklyConvexOn ell X (DualRegularizedValueOn Y f r))
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (R : Snapshot (m := m) Y)
    (hEB : snapshotEnergy sys R ≤ R.B) :
    regularizedEnvelope X Y f ell r hexistsR (nextSnapshot sys R).z -
        regularizedEnvelope X Y f ell r hexistsR R.z ≤
      -ell * vecSq (anchorError sys R) + R.B := by
  have hreadE := readout_error_le_energy hell hr sys R
  have hread : ell * vecSq (readoutError sys R) ≤ R.B :=
    hreadE.trans hEB
  have hsmooth := TrackingAnalytic.moreau_smoothDescentAt hell hweakR hexistsR
    R.z (stepDisplacement sys R)
  rw [displacement_eq sys R] at hsmooth
  have hout := Tracking.outer_descent hsmooth hread
  have hz : R.z + (-anchorError sys R + readoutError sys R) =
      readout sys R.state := by
    unfold anchorError readoutError
    abel
  rw [hz] at hout
  simpa only [regularizedEnvelope, nextSnapshot] using hout

/-- The next computable majorant obeys the scalar tracking estimate derived
from the actual displacement and fast readout. -/
theorem one_step_B_bound {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    (hell : 0 < ell) (hr : 0 < r)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (R : Snapshot (m := m) Y)
    (hEB : snapshotEnergy sys R ≤ R.B) :
    (nextSnapshot sys R).B ≤
      (48 / 400 : ℝ) * ell * vecSq (anchorError sys R) +
        (50 / 400 : ℝ) * R.B := by
  have hreadE := readout_error_le_energy hell hr sys R
  have hread : ell * vecSq (readoutError sys R) ≤ R.B :=
    hreadE.trans hEB
  have hd := Tracking.vecSq_neg_add_le_two (anchorError sys R) (readoutError sys R)
  rw [← displacement_eq sys R] at hd
  have hnext := Tracking.next_majorant_bound
    (rho := (1 / 400 : ℝ)) hell.le (by norm_num) hd hread
  change Tracking.nextMajorant (1 / 400) ell
      (vecSq (stepDisplacement sys R)) R.B ≤ _
  norm_num at hnext ⊢
  exact hnext

/-- TeX joint-potential decrease on the genuine trajectory step. -/
theorem one_step_potential_descent {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    (hell : 0 < ell) (hr : 0 < r)
    (hweakR : IsWeaklyConvexOn ell X (DualRegularizedValueOn Y f r))
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (R : Snapshot (m := m) Y)
    (hEB : snapshotEnergy sys R ≤ R.B) :
    snapshotPotential sys (nextSnapshot sys R) - snapshotPotential sys R ≤
      -(3 / 4 : ℝ) * (ell * vecSq (anchorError sys R) + R.B) := by
  have hp := one_step_outer_descent hell hr hweakR sys R hEB
  have hB := one_step_B_bound hell hr sys R hEB
  have hA : 0 ≤ ell * vecSq (anchorError sys R) :=
    mul_nonneg hell.le (Tracking.vecSq_nonneg _)
  unfold snapshotPotential
  exact Tracking.joint_potential_descent hp hA hB

/-- Certificate square bound on one real snapshot. -/
theorem stepCertificate_sq_bound {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    (hell : 0 < ell) (hr : 0 < r)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (R : Snapshot (m := m) Y)
    (hB : 0 ≤ R.B) (hEB : snapshotEnergy sys R ≤ R.B) :
    stepCertificate sys R ^ 2 ≤
      24 * ell * (ell * vecSq (anchorError sys R) + R.B) := by
  have hreadE := readout_error_le_energy hell hr sys R
  have hread : ell * vecSq (readoutError sys R) ≤ R.B :=
    hreadE.trans hEB
  have hd := Tracking.vecSq_neg_add_le_two (anchorError sys R) (readoutError sys R)
  rw [← displacement_eq sys R] at hd
  exact Tracking.certificate_sq_bound hell.le (Tracking.vecSq_nonneg _)
    (Tracking.vecSq_nonneg _) hB hd hread

/-- The computable certificate controls the squared regularized Moreau
gradient, not merely an abstract scalar. -/
theorem regularizedGradient_sq_le_certificate {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    (hell : 0 < ell) (hr : 0 < r)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (R : Snapshot (m := m) Y)
    (hB : 0 ≤ R.B) (hEB : snapshotEnergy sys R ≤ R.B) :
    vecSq (residualGradient hexistsR R.z) ≤ stepCertificate sys R ^ 2 := by
  have hreadE := readout_error_le_energy hell hr sys R
  have hread : ell * vecSq (readoutError sys R) ≤ R.B :=
    hreadE.trans hEB
  have hg := Tracking.gradient_sq_le_certificate_sq
    (stepDisplacement sys R) (readoutError sys R) hell.le hB hread
  have hea : readoutError sys R - stepDisplacement sys R = anchorError sys R := by
    rw [displacement_eq sys R]
    abel
  rw [hea] at hg
  have ha0 := Tracking.vecSq_nonneg (anchorError sys R)
  have hid :
      vecSq (residualGradient hexistsR R.z) =
        (2 * ell * Real.sqrt (vecSq (anchorError sys R))) ^ 2 := by
    unfold residualGradient
    rw [vecSq_smul]
    change (2 * ell) ^ 2 * vecSq (anchorError sys R) = _
    calc
      (2 * ell) ^ 2 * vecSq (anchorError sys R) =
          (2 * ell) ^ 2 * (Real.sqrt (vecSq (anchorError sys R))) ^ 2 := by
            rw [Real.sq_sqrt ha0]
      _ = (2 * ell * Real.sqrt (vecSq (anchorError sys R))) ^ 2 := by ring
  rw [hid]
  exact hg

/-- Potential descent at every index of the generated trajectory. -/
theorem trajectory_potential_descent {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    (hX : X.Nonempty) (hell : 0 < ell) (hr : 0 < r)
    (hrle : r ≤ ell / 8)
    (hweakR : IsWeaklyConvexOn ell X (DualRegularizedValueOn Y f r))
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (hE0 : snapshotEnergy sys R0 ≤ R0.B) :
    ∀ t,
      snapshotPotential sys (trajectory sys R0 (t + 1)) -
          snapshotPotential sys (trajectory sys R0 t) ≤
        -(3 / 4 : ℝ) *
          (ell * vecSq (anchorError sys (trajectory sys R0 t)) +
            (trajectory sys R0 t).B) := by
  intro t
  rw [trajectory_succ]
  exact one_step_potential_descent hell hr hweakR sys _
    (trajectory_energy_le_B hX hell hr hrle sys R0 hE0 t)

/-- Finite-horizon existence of a small computable certificate. -/
theorem exists_small_trajectory_certificate {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r lower : ℝ} {T : ℕ}
    (hX : X.Nonempty) (hell : 0 < ell) (hr : 0 < r)
    (hrle : r ≤ ell / 8)
    (hweakR : IsWeaklyConvexOn ell X (DualRegularizedValueOn Y f r))
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (hE0 : snapshotEnergy sys R0 ≤ R0.B)
    (hB0 : 0 ≤ R0.B) (hT : 0 < T)
    (hlower : ∀ z, lower ≤ regularizedEnvelope X Y f ell r hexistsR z) :
    ∃ t < T,
      stepCertificate sys (trajectory sys R0 t) ^ 2 ≤
        (32 * ell / T) * (snapshotPotential sys R0 - lower) := by
  let W : ℕ → ℝ := fun t => snapshotPotential sys (trajectory sys R0 t)
  let A : ℕ → ℝ := fun t => ell * vecSq (anchorError sys (trajectory sys R0 t))
  let Bt : ℕ → ℝ := fun t => (trajectory sys R0 t).B
  let C : ℕ → ℝ := fun t => stepCertificate sys (trajectory sys R0 t)
  have hstep : ∀ t, W (t + 1) - W t ≤ -(3 / 4 : ℝ) * (A t + Bt t) :=
    trajectory_potential_descent hX hell hr hrle hweakR sys R0 hE0
  have hcert : ∀ t, C t ^ 2 ≤ 24 * ell * (A t + Bt t) := by
    intro t
    exact stepCertificate_sq_bound hell hr sys _
      (trajectory_B_nonneg hell.le sys R0 hB0 t)
      (trajectory_energy_le_B hX hell hr hrle sys R0 hE0 t)
  have hlowerT : lower ≤ W T := by
    dsimp [W, snapshotPotential]
    have hp := hlower (trajectory sys R0 T).z
    have hbt := trajectory_B_nonneg hell.le sys R0 hB0 T
    nlinarith
  simpa only [W, C, trajectory_zero] using
    Tracking.exists_small_certificate W A Bt C hT hell.le hstep hcert hlowerT

/-! ## Transfer to optimization stationarity of the original value -/

/-- A small actual Moreau residual is exactly an optimization-stationarity
witness using the selected proximal point. -/
theorem optimizationStationary_of_residualGradient {m : Nat}
    {X : Set (EVec m)} {phi : EVec m → ℝ} {ell eps : ℝ}
    (hell : 0 < ell) (_heps : 0 ≤ eps)
    (hexists : HasProxEverywhere X phi ell) (z : EVec m)
    (hgrad : vecSq (residualGradient hexists z) ≤ eps ^ 2) :
    IsOptimizationStationary X phi ell eps z := by
  refine ⟨selectedProx hexists z, selectedProx_spec hexists z, ?_⟩
  have hscale :
      vecSq (residualGradient hexists z) =
        (2 * ell) ^ 2 * vecSq (z - selectedProx hexists z) := by
    unfold residualGradient
    rw [vecSq_smul]
  rw [hscale] at hgrad
  rw [vecSq_sub_comm]
  have hden : 0 < (2 * ell) ^ 2 := sq_pos_of_pos (by positivity)
  have hgrad' :
      vecSq (z - selectedProx hexists z) * (2 * ell) ^ 2 ≤ eps ^ 2 := by
    simpa only [mul_comm] using hgrad
  calc
    vecSq (z - selectedProx hexists z) ≤ eps ^ 2 / (2 * ell) ^ 2 :=
      (le_div_iff₀ hden).2 hgrad'
    _ = (eps / (2 * ell)) ^ 2 := by
      field_simp [ne_of_gt hell]

/-- A small trajectory certificate plus the genuine dual-regularization bias
gives epsilon optimization stationarity for the original maximized value. -/
theorem original_OS_of_small_certificate {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r D eps : ℝ}
    (hell : 0 < ell) (hr : 0 < r) (heps : 0 ≤ eps)
    (hweak : IsWeaklyConvexOn ell X (ValueOn Y f))
    (hweakR : IsWeaklyConvexOn ell X (DualRegularizedValueOn Y f r))
    (hexists : HasProxEverywhere X (ValueOn Y f) ell)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (hYnorm : ∀ y ∈ Y, vecSq y ≤ D ^ 2)
    (hmax : ∀ x, ∃ y, IsMaximizerOn Y f x y)
    (hmaxR : ∀ x, ∃ y, IsMaximizerOn Y
      (fun u v ↦ f u v - r / 2 * vecSq v) x y)
    (sys : OuterSystem X Y f ell r hexistsR) (R : Snapshot (m := m) Y)
    (hB : 0 ≤ R.B) (hEB : snapshotEnergy sys R ≤ R.B)
    (hcert : stepCertificate sys R ^ 2 ≤ eps ^ 2 / 4)
    (hbiasBudget : 2 * ell * r * D ^ 2 ≤ eps ^ 2 / 4) :
    IsOptimizationStationary X (ValueOn Y f) ell eps R.z := by
  have hbias := dualRegularizedValue_uniform_bias hr.le hYnorm hmax hmaxR
  have hdiff := residualGradient_regularization_vecSq_le hell hweak hweakR
    hexists hexistsR hbias R.z
  have hreg0 := regularizedGradient_sq_le_certificate hell hr sys R hB hEB
  have hreg : vecSq (residualGradient hexistsR R.z) ≤ eps ^ 2 / 4 :=
    hreg0.trans hcert
  have hdiffSmall :
      vecSq (residualGradient hexists R.z - residualGradient hexistsR R.z) ≤
        eps ^ 2 / 4 := hdiff.trans hbiasBudget
  let g := residualGradient hexists R.z
  let gR := residualGradient hexistsR R.z
  have htri := ScaledOperator.vecSq_add_le_two (g - gR) gR
  have hsum : g - gR + gR = g := by abel
  rw [hsum] at htri
  have htrue : vecSq g ≤ eps ^ 2 :=
    Tracking.stationarity_from_smoothed_and_bias htri hdiffSmall hreg
  exact optimizationStationary_of_residualGradient hell heps hexists R.z htrue

/-- Full finite-horizon conclusion: one generated anchor is epsilon-OS for
the original value function. -/
theorem exists_original_OS_on_trajectory {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r D eps lower : ℝ} {T : ℕ}
    (hX : X.Nonempty) (hell : 0 < ell) (hr : 0 < r)
    (hrle : r ≤ ell / 8) (heps : 0 ≤ eps)
    (hweak : IsWeaklyConvexOn ell X (ValueOn Y f))
    (hweakR : IsWeaklyConvexOn ell X (DualRegularizedValueOn Y f r))
    (hexists : HasProxEverywhere X (ValueOn Y f) ell)
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (hYnorm : ∀ y ∈ Y, vecSq y ≤ D ^ 2)
    (hmax : ∀ x, ∃ y, IsMaximizerOn Y f x y)
    (hmaxR : ∀ x, ∃ y, IsMaximizerOn Y
      (fun u v ↦ f u v - r / 2 * vecSq v) x y)
    (sys : OuterSystem X Y f ell r hexistsR)
    (R0 : Snapshot (m := m) Y) (hE0 : snapshotEnergy sys R0 ≤ R0.B)
    (hB0 : 0 ≤ R0.B) (hT : 0 < T)
    (hlower : ∀ z, lower ≤ regularizedEnvelope X Y f ell r hexistsR z)
    (hcertificateBudget :
      (32 * ell / T) * (snapshotPotential sys R0 - lower) ≤ eps ^ 2 / 4)
    (hbiasBudget : 2 * ell * r * D ^ 2 ≤ eps ^ 2 / 4) :
    ∃ t < T,
      IsOptimizationStationary X (ValueOn Y f) ell eps
        (trajectory sys R0 t).z := by
  obtain ⟨t, ht, hsmall⟩ := exists_small_trajectory_certificate
    hX hell hr hrle hweakR sys R0 hE0 hB0 hT hlower
  have hcert : stepCertificate sys (trajectory sys R0 t) ^ 2 ≤ eps ^ 2 / 4 :=
    hsmall.trans hcertificateBudget
  refine ⟨t, ht, ?_⟩
  exact original_OS_of_small_certificate hell hr heps hweak hweakR hexists
    hYnorm hmax hmaxR sys (trajectory sys R0 t)
    (trajectory_B_nonneg hell.le sys R0 hB0 t)
    (trajectory_energy_le_B hX hell hr hrle sys R0 hE0 t)
    hcert hbiasBudget

/-! ## Query and projection accounting -/

/-- Cost of one projected micro solve in each macrostep plus the outer primal
readout projection. -/
def outerStepCost (ell r : ℝ) (microSteps : ℕ) : Cost where
  oracleCalls := blockIterations (alpha ell r) (1 / 400 : ℝ) *
    (microSteps + 1)
  projections := blockIterations (alpha ell r) (1 / 400 : ℝ) *
    (microSteps + 1) + 1

/-- Cost of `T` generated outer steps, including the possible final
compatibility oracle query. -/
def outerTrajectoryCost (ell r : ℝ) (T microSteps : ℕ) : Cost where
  oracleCalls := T * (outerStepCost ell r microSteps).oracleCalls + 1
  projections := T * (outerStepCost ell r microSteps).projections

@[simp] theorem outerTrajectoryCost_oracleCalls (ell r : ℝ)
    (T microSteps : ℕ) :
    (outerTrajectoryCost ell r T microSteps).oracleCalls =
      T * blockIterations (alpha ell r) (1 / 400 : ℝ) *
        (microSteps + 1) + 1 := by
  simp [outerTrajectoryCost, outerStepCost]
  rw [Nat.mul_assoc]

@[simp] theorem outerTrajectoryCost_projections (ell r : ℝ)
    (T microSteps : ℕ) :
    (outerTrajectoryCost ell r T microSteps).projections =
      T * (blockIterations (alpha ell r) (1 / 400 : ℝ) *
        (microSteps + 1) + 1) := rfl

end

end OuterTrajectoryConcrete
end Upper
end NCCLowerBoundVerification
