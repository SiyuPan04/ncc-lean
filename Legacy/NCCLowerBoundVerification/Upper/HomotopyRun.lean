import NCCLowerBoundVerification.Upper.HomotopyConcrete
import NCCLowerBoundVerification.Upper.InitialGapBounds
import NCCLowerBoundVerification.Upper.StartupConcrete
import NCCLowerBoundVerification.Upper.HomotopyCost

/-!
# The actual finite homotopy run

The scalar homotopy recurrence and each analytic curvature-transfer step were
proved separately.  This module joins them into one recursively generated
feasible state sequence.  In particular, the final outer snapshot is no
longer supplied with an assumed initial-energy estimate.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace HomotopyRun

noncomputable section

open PointwiseConjugate RelativeFOAM RelativeFOAMContraction
open OuterTrajectoryConcrete StartupConcrete InitialGapBounds

set_option maxHeartbeats 3000000

def startupSeed {m n : Nat} {ell : ℝ} {P : NCCInstance m n}
    (hzero : (0 : EVec n) ∈ P.Y) : ValidState (m := m) P.Y :=
  ⟨coincidentState ((-ell) • P.x0) 0, hzero⟩

def startupState {m n : Nat} {ell r : ℝ} {P : NCCInstance m n}
    {hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell}
    (sys : OuterSystem P.X P.Y P.f ell r hexistsR)
    (hzero : (0 : EVec n) ∈ P.Y) : ValidState (m := m) P.Y :=
  let O := sys.oracle P.x0 (startupSeed (ell := ell) hzero)
  ⟨coincidentState O.qFastNext O.yFastNext,
    sys.oracle_feasible P.x0 (startupSeed (ell := ell) hzero)⟩

@[simp] theorem startupState_val {m n : Nat} {ell r : ℝ}
    {P : NCCInstance m n}
    {hexistsR : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell}
    (sys : OuterSystem P.X P.Y P.f ell r hexistsR)
    (hzero : (0 : EVec n) ∈ P.Y) :
    (startupState sys hzero).1 =
      coincidentState
        (sys.oracle P.x0 (startupSeed (ell := ell) hzero)).qFastNext
        (sys.oracle P.x0 (startupSeed (ell := ell) hzero)).yFastNext := rfl

/-- The first actual micro solve at `r₀ = ell/8` produces a feasible state
whose genuine hidden energy is bounded by the paper's computable majorant. -/
theorem startup_snapshot_energy {m n : Nat} {ell D Delta r : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    (hzero : (0 : EVec n) ∈ P.Y)
    (hr : r = ell / 8)
    (hexists0 : HasProxEverywhere P.X
      (DualRegularizedValueOn P.Y P.f r) ell)
    (sys0 : OuterSystem P.X P.Y P.f ell r hexists0) :
    let R0 : Snapshot (m := m) P.Y :=
      { z := P.x0
        state := startupState sys0 hzero
        B := 8 * (Delta + (ell / 8) * D ^ 2) }
    snapshotEnergy sys0 R0 ≤ R0.B := by
  subst r
  dsimp
  let Sseed := startupSeed (ell := ell) hzero
  let O := sys0.oracle P.x0 Sseed
  let st := sys0.stationary P.x0
  have hfast : IsGammaSubgradient P.X P.Y
      (decurved P.f ell (ell / 8) P.x0) O.qFastNext
      ⟨O.yFastNext, sys0.oracle_feasible P.x0 Sseed⟩ O.xFast O.wFastNext :=
    sys0.oracle_subgradient P.x0 Sseed
  have hres : RelativeResidual ell (ell / 8) (coincidentState
      ((-ell) • P.x0) 0)
      (startupOutput O.xFast O.qFastNext O.yFastNext O.wFastNext) := by
    simpa [Sseed, startupSeed, O, startupOutput] using
      sys0.oracle_residual P.x0 Sseed
  have hprimal : ell * vecSq
      (P.x0 - selectedProx hexists0 P.x0) ≤
        Delta + (ell / 8) / 2 * D ^ 2 := by
    simpa using selected_regularizedProx_displacement hP hzero
      (div_nonneg hP.ell_pos.le (by norm_num)) hexists0
  have hstartup := startup_pzr_computable_majorant
    hP.ell_pos hP.Delta_pos.le (sq_nonneg D)
    hfast st.subgradient st.stationQ st.stationY hres
    hprimal
    (NCCLowerBoundVerification.Upper.IsNCCClass.dual_vecSq_le hP hzero
      st.yStar.1 st.yStar.2)
  dsimp [snapshotEnergy, energyAt, startupState, Sseed, O, st]
  simpa using hstartup.2

/-! ## The recursively generated curvature sequence -/

abbrev ProxFamily {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (f : EVec m → EVec n → ℝ) (ell r0 : ℝ) :=
  (j : Nat) → HasProxEverywhere X
    (DualRegularizedValueOn Y f (Tracking.curvature r0 j)) ell

abbrev SystemFamily {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (f : EVec m → EVec n → ℝ) (ell r0 : ℝ)
    (prox : ProxFamily X Y f ell r0) :=
  (j : Nat) → OuterSystem X Y f ell (Tracking.curvature r0 j) (prox j)

def homotopyState {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r0 : ℝ}
    {prox : ProxFamily X Y f ell r0}
    (systems : SystemFamily X Y f ell r0 prox) (z : EVec m)
    (S0 : ValidState (m := m) Y) : Nat → ValidState (m := m) Y
  | 0 => S0
  | j + 1 =>
      let sys := systems (j + 1)
      ((foamStep ell (Tracking.curvature r0 (j + 1)) (sys.oracle z)
        (sys.oracle_feasible z))^[
          blockIterations (alpha ell (Tracking.curvature r0 (j + 1)))
            (1 / 8 : ℝ)]) (homotopyState systems z S0 j)

@[simp] theorem homotopyState_zero {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r0 : ℝ}
    {prox : ProxFamily X Y f ell r0}
    (systems : SystemFamily X Y f ell r0 prox) (z : EVec m)
    (S0 : ValidState (m := m) Y) :
    homotopyState systems z S0 0 = S0 := rfl

@[simp] theorem homotopyState_succ {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r0 : ℝ}
    {prox : ProxFamily X Y f ell r0}
    (systems : SystemFamily X Y f ell r0 prox) (z : EVec m)
    (S0 : ValidState (m := m) Y) (j : Nat) :
    homotopyState systems z S0 (j + 1) =
      let sys := systems (j + 1)
      ((foamStep ell (Tracking.curvature r0 (j + 1)) (sys.oracle z)
        (sys.oracle_feasible z))^[
          blockIterations (alpha ell (Tracking.curvature r0 (j + 1)))
            (1 / 8 : ℝ)]) (homotopyState systems z S0 j) := rfl

def homotopySnapshot {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r0 D B0 : ℝ}
    {prox : ProxFamily X Y f ell r0}
    (systems : SystemFamily X Y f ell r0 prox) (z : EVec m)
    (S0 : ValidState (m := m) Y) (j : Nat) : Snapshot (m := m) Y where
  z := z
  state := homotopyState systems z S0 j
  B := Tracking.homotopyMajorant r0 (D ^ 2) B0 j

@[simp] theorem homotopySnapshot_z {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r0 D B0 : ℝ}
    {prox : ProxFamily X Y f ell r0}
    (systems : SystemFamily X Y f ell r0 prox) (z : EVec m)
    (S0 : ValidState (m := m) Y) (j : Nat) :
    (homotopySnapshot (D := D) (B0 := B0) systems z S0 j).z = z := rfl

@[simp] theorem homotopySnapshot_B {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r0 D B0 : ℝ}
    {prox : ProxFamily X Y f ell r0}
    (systems : SystemFamily X Y f ell r0 prox) (z : EVec m)
    (S0 : ValidState (m := m) Y) (j : Nat) :
    (homotopySnapshot (D := D) (B0 := B0) systems z S0 j).B =
      Tracking.homotopyMajorant r0 (D ^ 2) B0 j := rfl

theorem snapshotEnergy_eq_concreteEnergy {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r : ℝ}
    {hexistsR : HasProxEverywhere X (DualRegularizedValueOn Y f r) ell}
    (sys : OuterSystem X Y f ell r hexistsR) (R : Snapshot (m := m) Y) :
    snapshotEnergy sys R =
      HomotopyConcrete.concreteEnergy X Y (decurved f ell r R.z) ell r
        (sys.stationary R.z).qStar (sys.stationary R.z).yStar R.state := by
  unfold snapshotEnergy energyAt HomotopyConcrete.concreteEnergy
    HomotopyConcrete.slowEnergy HomotopyConcrete.fastGap
    Tracking.splitEnergy TrackingConcrete.constrainedEnergy
  rfl

/-- Every recursively generated homotopy state satisfies its recursively
generated computable energy majorant. -/
theorem homotopySnapshot_energy_le {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {ell r0 D B0 : ℝ}
    (hell : 0 < ell) (hr0 : 0 < r0) (hr0le : r0 ≤ ell / 8)
    (hD : 0 ≤ D) (hYnorm : ∀ y : Y, vecSq y.1 ≤ D ^ 2)
    {prox : ProxFamily X Y f ell r0}
    (systems : SystemFamily X Y f ell r0 prox) (z : EVec m)
    (S0 : ValidState (m := m) Y)
    (hE0 : snapshotEnergy (systems 0)
      (homotopySnapshot (D := D) (B0 := B0) systems z S0 0) ≤ B0) :
    ∀ j, snapshotEnergy (systems j)
        (homotopySnapshot (D := D) (B0 := B0) systems z S0 j) ≤
      Tracking.homotopyMajorant r0 (D ^ 2) B0 j := by
  intro j
  induction j with
  | zero =>
      simpa [Tracking.homotopyMajorant] using hE0
  | succ j ih =>
      let r := Tracking.curvature r0 j
      let oldSys := systems j
      let newSys := systems (j + 1)
      let oldSt := oldSys.stationary z
      let newSt := newSys.stationary z
      let qNew : EVec m := newSt.qStar
      let yNew : Y := newSt.yStar
      let xNew : EVec m := selectedProx (prox (j + 1)) z
      let wNew : EVec n := newSt.wStar
      have hr : 0 < r := by
        dsimp [r]
        exact HomotopyCost.curvature_pos hr0 j
      have hrle0 : r ≤ r0 := by
        dsimp [r, Tracking.curvature]
        exact Tracking.div_pow_le_self hr0.le (by norm_num) j
      have hrle : r ≤ ell / 8 := hrle0.trans hr0le
      have hcurv : Tracking.curvature r0 (j + 1) = r / 4 := by
        simpa [r] using Tracking.curvature_succ r0 j
      have hH : decurved f ell (Tracking.curvature r0 (j + 1)) z =
          decurved f ell r z := by
        funext x y
        rw [decurved_eq, decurved_eq]
      have hsubNew : IsGammaSubgradient X Y (decurved f ell r z)
          qNew yNew xNew wNew := by
        rw [← hH]
        exact newSt.subgradient
      have hstationQNew : xNew + ell⁻¹ • qNew = 0 := newSt.stationQ
      have hstationYNew : wNew + (r / 4) • yNew.1 = 0 := by
        rw [← hcurv]
        exact newSt.stationY
      have horacleSubgradient : ∀ S,
          IsGammaSubgradient X Y (decurved f ell r z)
            (newSys.oracle z S).qFastNext
            ⟨(newSys.oracle z S).yFastNext,
              newSys.oracle_feasible z S⟩
            (newSys.oracle z S).xFast (newSys.oracle z S).wFastNext := by
        intro S
        rw [← hH]
        exact newSys.oracle_subgradient z S
      have horacleResidual : ∀ S,
          RelativeResidual ell (r / 4) S.1 (newSys.oracle z S) := by
        intro S
        rw [← hcurv]
        exact newSys.oracle_residual z S
      have hold : HomotopyConcrete.concreteEnergy X Y
          (decurved f ell r z) ell r oldSt.qStar oldSt.yStar
            (homotopyState systems z S0 j) ≤
          Tracking.homotopyMajorant r0 (D ^ 2) B0 j := by
        have ih' := ih
        rw [snapshotEnergy_eq_concreteEnergy] at ih'
        simpa [homotopySnapshot, r, oldSys, oldSt] using ih'
      have hstage := HomotopyConcrete.concrete_homotopy_stage_majorized
        hell hr hD hrle hYnorm oldSt.subgradient oldSt.stationQ
        oldSt.stationY hsubNew hstationQNew hstationYNew
        (newSys.oracle z) (newSys.oracle_feasible z)
        horacleSubgradient horacleResidual
        (homotopyState systems z S0 j) hold
      rw [snapshotEnergy_eq_concreteEnergy]
      simp only [homotopySnapshot_z]
      change HomotopyConcrete.concreteEnergy X Y
          (decurved f ell (Tracking.curvature r0 (j + 1)) z) ell
          (Tracking.curvature r0 (j + 1)) qNew yNew
          (homotopyState systems z S0 (j + 1)) ≤
        Tracking.homotopyMajorant r0 (D ^ 2) B0 (j + 1)
      calc
        _ = HomotopyConcrete.concreteEnergy X Y (decurved f ell r z)
            ell (r / 4) qNew yNew
              (homotopyState systems z S0 (j + 1)) := by
                rw [hH, hcurv]
        _ ≤ (Tracking.homotopyMajorant r0 (D ^ 2) B0 j +
              (27 / 4 : ℝ) * r * D ^ 2) / 8 := by
                simpa [homotopyState, hcurv, r, oldSys, newSys, oldSt, newSt,
                  qNew, yNew, xNew, wNew]
                  using hstage
        _ = Tracking.homotopyMajorant r0 (D ^ 2) B0 (j + 1) := rfl

theorem homotopyMajorant_nonneg {r0 D2 B0 : ℝ}
    (hr0 : 0 ≤ r0) (hD2 : 0 ≤ D2) (hB0 : 0 ≤ B0) :
    ∀ j, 0 ≤ Tracking.homotopyMajorant r0 D2 B0 j := by
  intro j
  induction j with
  | zero => simpa [Tracking.homotopyMajorant] using hB0
  | succ j ih =>
      unfold Tracking.homotopyMajorant
      have hrj : 0 ≤ Tracking.curvature r0 j := by
        unfold Tracking.curvature
        positivity
      positivity

/-- Combining startup, every genuine homotopy stage, and the scalar geometric
bound gives the exact initial snapshot required by the outer trajectory. -/
theorem initialized_homotopy_snapshot {m n : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    {prox : ProxFamily P.X P.Y P.f ell (ell / 8)}
    (systems : SystemFamily P.X P.Y P.f ell (ell / 8) prox) (j : Nat) :
    let S0 := startupState (systems 0) hzero
    let B0 := 8 * (Delta + (ell / 8) * D ^ 2)
    let Rj := homotopySnapshot (D := D) (B0 := B0)
      systems P.x0 S0 j
    snapshotEnergy (systems j) Rj ≤ Rj.B ∧
      0 ≤ Rj.B ∧
      Rj.B ≤ 15 * (Delta + Tracking.curvature (ell / 8) j * D ^ 2) := by
  dsimp
  let B0 : ℝ := 8 * (Delta + (ell / 8) * D ^ 2)
  let S0 : ValidState (m := m) P.Y := startupState (systems 0) hzero
  have hE0 : snapshotEnergy (systems 0)
      (homotopySnapshot (D := D) (B0 := B0) systems P.x0 S0 0) ≤ B0 := by
    have hs := startup_snapshot_energy hP hzero
      (by simp [Tracking.curvature]) (prox 0) (systems 0)
    simpa [B0, S0, homotopySnapshot, homotopyState,
      Tracking.homotopyMajorant, Tracking.curvature] using hs
  have henergy := homotopySnapshot_energy_le hP.ell_pos
    (div_pos hP.ell_pos (by norm_num)) (le_rfl) hP.D_pos.le
    (fun y => NCCLowerBoundVerification.Upper.IsNCCClass.dual_vecSq_le
      hP hzero y.1 y.2)
    systems P.x0 S0 hE0 j
  have hB0 : 0 ≤ B0 := by
    dsimp [B0]
    exact mul_nonneg (by norm_num)
      (add_nonneg hP.Delta_pos.le
        (mul_nonneg (div_nonneg hP.ell_pos.le (by norm_num)) (sq_nonneg D)))
  have hnonneg := homotopyMajorant_nonneg
    (r0 := ell / 8) (D2 := D ^ 2) (B0 := B0)
    (div_nonneg hP.ell_pos.le (by norm_num)) (sq_nonneg D) hB0 j
  have huniform := Tracking.homotopy_uniform_majorant
    (r0 := ell / 8) (D2 := D ^ 2) (Delta := Delta)
    j hP.Delta_pos.le
    (div_nonneg hP.ell_pos.le (by norm_num)) (sq_nonneg D)
  have henergy' : snapshotEnergy (systems j)
      (homotopySnapshot (D := D) (B0 := B0) systems P.x0 S0 j) ≤
        (homotopySnapshot (D := D) (B0 := B0) systems P.x0 S0 j).B := by
    simpa [homotopySnapshot] using henergy
  have hnonneg' : 0 ≤
      (homotopySnapshot (D := D) (B0 := B0) systems P.x0 S0 j).B := by
    simpa [homotopySnapshot] using hnonneg
  have huniform' :
      (homotopySnapshot (D := D) (B0 := B0) systems P.x0 S0 j).B ≤
        15 * (Delta + Tracking.curvature (ell / 8) j * D ^ 2) := by
    simpa [homotopySnapshot, B0] using huniform
  simpa [S0, B0] using ⟨henergy', hnonneg', huniform'⟩

end

end HomotopyRun
end Upper
end NCCLowerBoundVerification
