import NCC.Extensions.NCSCExecution
import NCC.Extensions.NCSCCanonical
import NCC.Extensions.NCSCCost

/-!
# Intrinsic NC-SC GS execution

The tracked solver queries the original objective through the exact auxiliary
reply adapter. Its final projected readout uses the original gradients and
zero dual regularization. Initial energy and potential bounds are local,
explicit premises; the concrete counted normalization discharges them.
-/
namespace NCC.Extensions.NCSCGSProgram
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle RelativeFOAM RelativeFOAMContraction ProjectionGeometry
open OuterTrajectoryConcrete SharedOracle ScaledOperator ProjectedReadout
open NCC.Upper NCC.Upper.AdaptiveMicroProgram NCC.Upper.CurrentProgram
set_option maxHeartbeats 3000000
variable {m n : Nat} {ell mu Delta L G eps : ℝ} {P : NCCInstance m n}
  {X : Set (EVec m)} {Y : Set (EVec n)}

/-- The numerical constructor contains no objective or class proof. -/
def program (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (initProgram : Program X Y (FeasibleSnapshot X Y))
    (T : Nat) (hT : 0 < T) (mu rho : ℝ) : Program X Y (Query m n) := do
  let out ← NCSCProgram.adaptProgram mu
    (NCSCProgram.fixedProgram (r := mu) hL projectX projectY hpX hpY initProgram T hT rho)
  GSProgram.readoutProgram L 0 projectX projectY hpX hpY out.1.1.z out.2

theorem program_actual_count (P : NCCInstance m n) (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (initProgram : Program X Y (FeasibleSnapshot X Y))
    (T : Nat) (hT : 0 < T) (mu rho : ℝ) :
    (queryTrace P (program hL projectX projectY hpX hpY initProgram T hT mu rho)).length ≤
      NCSCProgram.fixedCount L mu
        (queryTrace P (NCSCProgram.adaptProgram mu initProgram)).length T rho + 1 := by
  let p := NCSCProgram.adaptProgram mu
    (NCSCProgram.fixedProgram (r := mu) hL projectX projectY hpX hpY initProgram T hT rho)
  have hc := NCSCProgram.adapted_fixedProgram_actual_count (r := mu) P hL projectX projectY hpX hpY
    initProgram T hT rho mu
  have hr := (GSProgram.readoutProgram_depth L 0 projectX projectY hpX hpY
    (Program.eval P p).1.1.z (Program.eval P p).2).trace_length P
  rw [program, queryTrace_bind, List.length_append]
  change (queryTrace P p).length + (queryTrace P (GSProgram.readoutProgram L 0
    projectX projectY hpX hpY (Program.eval P p).1.1.z (Program.eval P p).2)).length ≤ _
  change (queryTrace P p).length ≤ _ at hc
  omega

theorem program_all_histories_feasible (hL : 0 < L)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hpX : IsEuclideanProjection X projectX) (hpY : IsEuclideanProjection Y projectY)
    (initProgram : Program X Y (FeasibleSnapshot X Y))
    (T : Nat) (hT : 0 < T) (mu rho : ℝ)
    (fallback : Query m n) (hfallback : fallback.1 ∈ X ∧ fallback.2 ∈ Y)
    (t : Nat) (history : ReplyHistory m n t) :
    let q := Program.queryAfterHistory
      (program hL projectX projectY hpX hpY initProgram T hT mu rho) fallback t history
    q.1 ∈ X ∧ q.2 ∈ Y :=
  Program.queryAfterHistory_mem _ fallback hfallback t history

theorem original_smooth_internal (h : NCSC.NCSCClass ell mu Delta P) :
    JointlySmoothWithin (NCSC.internalSmoothness ell mu) P := by
  intro x hx y hy u hu v hv
  have hs := h.jointly_smooth x hx y hy u hu v hv
  have hL := NCSCExecution.internalSmoothness_ge h
  have hell := h.ell_pos
  have hc : ell ^ 2 ≤ (NCSC.internalSmoothness ell mu) ^ 2 := by nlinarith only [hell, hL]
  exact hs.trans (mul_le_mul_of_nonneg_right hc
    (add_nonneg (Tracking.vecSq_nonneg _) (Tracking.vecSq_nonneg _)))

theorem horizon_observable_budget {q : ℝ} (hL : 0 < L) (hG : 0 < G) (heps : 0 < eps)
    (hq : q ≤ 4 * G / (Selection.outerIterations L G eps : ℝ)) : q < eps ^ 2 / L := by
  have hT : 0 < (Selection.outerIterations L G eps : ℝ) :=
    Nat.cast_pos.mpr (Selection.outerIterations_pos hL hG)
  have he2 := sq_pos_of_pos heps
  have hs := mul_le_mul_of_nonneg_right
    (Selection.outerIterations_lower (ell := L) (Delta := G) (eps := eps)) he2.le
  have heq : 4000 * (L * G / eps ^ 2 + 1) * eps ^ 2 = 4000 * (L * G + eps ^ 2) := by
    field_simp
  rw [heq] at hs
  have hq' := (le_div_iff₀ hT).1 hq
  have hm := mul_le_mul_of_nonneg_left hq' hL.le
  apply (lt_div_iff₀ hL).2
  apply (mul_lt_mul_iff_left₀ hT).1
  nlinarith only [hs, hm, mul_pos hL hG, he2]

/-- The whole intrinsic solver, refinement, and final original-gradient
query produce true normal-cone witnesses, with no dual radius. -/
theorem program_hasGSWitness (h : NCSC.NCSCClass ell mu Delta P)
    (initProgram : Program P.X P.Y (FeasibleSnapshot P.X P.Y))
    (hG : 0 < G) (heps : 0 < eps)
    (hE0 : snapshotEnergy (NCSCSystem.system h)
      (Program.eval (NCSC.auxiliary P mu) initProgram).1 ≤
        (Program.eval (NCSC.auxiliary P mu) initProgram).1.B)
    (hB0 : 0 ≤ (Program.eval (NCSC.auxiliary P mu) initProgram).1.B)
    (hgap : snapshotPotential (NCSCSystem.system h)
      (Program.eval (NCSC.auxiliary P mu) initProgram).1 -
        (ValueOn P.Y P.f 0 - Delta) ≤ G) :
    let out := Program.eval P (program (NCSC.internalSmoothness_pos h)
      (NCSCSystem.system h).projectX (NCSCExecution.projectY h)
      (NCSCSystem.system h).project_spec (NCSCExecution.projectY_spec h) initProgram
      (Selection.outerIterations (NCSC.internalSmoothness ell mu) G eps)
      (Selection.outerIterations_pos (NCSC.internalSmoothness_pos h) hG) mu
      (GSRun.refinementFactor (NCSC.internalSmoothness ell mu) mu))
    HasGSWitness P eps out.1 out.2 := by
  dsimp only
  let L := NCSC.internalSmoothness ell mu
  let sys := NCSCSystem.system h
  let T := Selection.outerIterations L G eps
  have hL : 0 < L := NCSC.internalSmoothness_pos h
  have hT : 0 < T := Selection.outerIterations_pos hL hG
  let R0 := (Program.eval (NCSC.auxiliary P mu) initProgram).1
  let R := NCSCProgram.selectedSnapshot sys R0 T hT
  let rho := GSRun.refinementFactor L mu
  let S := NCSCProgram.refinedState sys R rho
  let W := NCSCCanonical.originalSaddle h R.z
  let u := GSProgram.rawPair L sys.projectX S
  have hrho : 0 < rho := GSRun.refinementFactor_pos hL h.mu_pos
  have hrho1 : rho < 1 := GSRun.refinementFactor_lt_one hL (NCSC.intrinsic_parameter_le h)
  have hb := NCSCProgram.selectedSnapshot_bounds (f := (NCSC.auxiliary P mu).f)
    (show P.X.Nonempty from ⟨0, h.primal_origin⟩) hL h.mu_pos (NCSC.intrinsic_parameter_le h)
    (NCSCGeometry.CoreClass.regularizedValue_weaklyConvex (NCSCGeometry.ofNCSC h))
    sys R0 hE0 hB0 T hT (ValueOn P.Y P.f 0 - Delta) G
    (NCSCExecution.regularizedEnvelope_lower h) hgap
  have hg : vecSq (residualGradient (NCSCSystem.intrinsicProx h) R.z) < eps ^ 2 / 16 :=
    NCSCProgram.horizon_gradient_budget hL hG heps hb.2.2.2
  have hq : AnalyticBridge.observable sys R < eps ^ 2 / L :=
    horizon_observable_budget hL hG heps hb.2.2.1
  have he := NCSCProgram.refinedState_energy_le_observable (f := (NCSC.auxiliary P mu).f) hL h.mu_pos
    (NCSC.intrinsic_parameter_le h) sys R hb.1 hrho hrho1
  have hE : energyAt sys R.z S < mu * eps ^ 2 / (1000000 * L ^ 2) := by
    have hm := he.trans_lt (mul_lt_mul_of_pos_left hq hrho)
    have heq : rho * (eps ^ 2 / L) = mu * eps ^ 2 / (1000000 * L ^ 2) := by
      dsimp [rho, GSRun.refinementFactor]
      field_simp
    rwa [heq] at hm
  have hWx : W.x = selectedProx (NCSCSystem.intrinsicProx h) R.z :=
    NCSCCanonical.originalSaddle_x h R.z
  have hWy : W.y = (sys.stationary R.z).yStar.val :=
    NCSCCanonical.originalSaddle_y h R.z
  have hdist : vecSq (u - pack W.x W.y) ≤ 2 * energyAt sys R.z S / mu := by
    rw [hWx, hWy]
    change vecSq (pack (readout sys S) S.1.yFast -
      pack (selectedProx (NCSCSystem.intrinsicProx h) R.z) (sys.stationary R.z).yStar.1) ≤ _
    rw [← pack_sub, vecSq_pack]
    apply GSRun.fast_pair_distance_le_energy (f := (NCSC.auxiliary P mu).f) hL h.mu_pos
    have hh := NCSC.intrinsic_parameter_le h
    change mu ≤ L / 8 at hh
    linarith
  have hprecision : 50000 * L ^ 2 * vecSq (u - pack W.x W.y) ≤ eps ^ 2 := by
    have hd := (le_div_iff₀ h.mu_pos).1 hdist
    have he' := (lt_div_iff₀ (show 0 < 1000000 * L ^ 2 by positivity)).1 hE
    have hh := mul_le_mul_of_nonneg_left hd (show 0 ≤ 50000 * L ^ 2 by positivity)
    have : (50000 * L ^ 2 * vecSq (u - pack W.x W.y)) * mu ≤ eps ^ 2 * mu := by
      nlinarith only [hh, he', mul_nonneg h.mu_pos.le (sq_nonneg eps)]
    exact (mul_le_mul_iff_left₀ h.mu_pos).1 this
  have hanchor : 64 * L ^ 2 * vecSq (R.z - W.x) ≤ eps ^ 2 := by
    unfold residualGradient at hg
    rw [vecSq_smul] at hg
    rw [hWx]
    nlinarith only [hg]
  have heval := NCSCExecution.eval_program h initProgram T hT rho
  simp only [program, Program.eval_bind]
  change let out := Program.eval P (GSProgram.readoutProgram L 0 sys.projectX (NCSCExecution.projectY h)
      sys.project_spec (NCSCExecution.projectY_spec h)
      (Program.eval P (NCSCExecution.program h initProgram T hT rho)).1.1.z
      (Program.eval P (NCSCExecution.program h initProgram T hT rho)).2)
    HasGSWitness P eps out.1 out.2
  dsimp only
  simp only [heval.1, heval.2, GSProgram.eval_readoutProgram]
  apply NCSCGSReadout.readout_hasGSWitness hL heps (original_smooth_internal h)
    sys.project_spec (NCSCExecution.projectY_spec h) W
  · change u ∈ pairSet P.X P.Y
    simpa only [u, GSProgram.rawPair, pairSet, Set.mem_setOf_eq, unpackX_pack, unpackY_pack] using
      And.intro (sys.project_spec.mem ((-L⁻¹) • S.1.qFast)) S.2
  · exact hprecision
  · exact hanchor

end
end NCC.Extensions.NCSCGSProgram
