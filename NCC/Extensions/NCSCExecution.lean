import NCC.Extensions.NCSCSystem
import NCC.Extensions.NCSCProgram
import NCC.Extensions.NCSCMoreauComparison

/-!
# Executed intrinsic NC-SC solver and actual OS readout

The only initialization premise is a bound on the true energy of the actual
finite initializer. All local solver certificates are derived from NCSCClass.
-/
namespace NCC.Extensions.NCSCExecution
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open Oracle OuterTrajectoryConcrete ProjectionGeometry SharedOracle
open NCC.Upper
set_option maxHeartbeats 3000000

variable {m n : ℕ} {ell mu Delta : ℝ} {P : NCCInstance m n}

def projectY (h : NCSC.NCSCClass ell mu Delta P) : EVec n → EVec n :=
  NCSCSystem.chosenProjectY (NCSCGeometry.ofNCSC h)

theorem projectY_spec (h : NCSC.NCSCClass ell mu Delta P) :
    IsEuclideanProjection P.Y (projectY h) :=
  NCSCSystem.chosenProjectY_spec (NCSCGeometry.ofNCSC h)

/-- The abstract solver oracle is the value of the actual finite micro
program. This is a proved local identity, not a whole-run assumption. -/
theorem microRealizes (h : NCSC.NCSCClass ell mu Delta P) :
    NCSCProgram.MicroRealizes (NCSC.auxiliary P mu)
      (NCSC.internalSmoothness_pos h) (NCSCSystem.system h)
      (projectY h) (projectY_spec h) := by
  apply NCSCProgram.microRealizes_of_classOracle
  intro z S
  rfl

def program (h : NCSC.NCSCClass ell mu Delta P)
    (initProgram : Program P.X P.Y (FeasibleSnapshot P.X P.Y))
    (T : ℕ) (hT : 0 < T) (rho : ℝ) :=
  NCSCProgram.adaptProgram mu
    (NCSCProgram.fixedProgram (r := mu) (NCSC.internalSmoothness_pos h)
      (NCSCSystem.system h).projectX (projectY h)
      (NCSCSystem.system h).project_spec (projectY_spec h) initProgram T hT rho)

theorem eval_program (h : NCSC.NCSCClass ell mu Delta P)
    (initProgram : Program P.X P.Y (FeasibleSnapshot P.X P.Y))
    (T : ℕ) (hT : 0 < T) (rho : ℝ) :
    let R := NCSCProgram.selectedSnapshot (NCSCSystem.system h)
      (Program.eval (NCSC.auxiliary P mu) initProgram).1 T hT
    let out := Program.eval P (program h initProgram T hT rho)
    out.1.1 = R ∧ out.2 = NCSCProgram.refinedState (NCSCSystem.system h) R rho := by
  rw [program, NCSCProgram.eval_adaptProgram]
  exact NCSCProgram.eval_fixedProgram_of_micro (NCSC.auxiliary P mu)
    (NCSC.internalSmoothness_pos h) (NCSCSystem.system h) (projectY h)
    (projectY_spec h) (microRealizes h) initProgram T hT rho

theorem internalSmoothness_ge (h : NCSC.NCSCClass ell mu Delta P) :
    ell ≤ NCSC.internalSmoothness ell mu := by
  unfold NCSC.internalSmoothness
  linarith [h.ell_pos, h.mu_pos]

/-- A source-gradient bound follows from the genuine internal proximal point. -/
theorem gradient_le_internal (h : NCSC.NCSCClass ell mu Delta P) (z : EVec m) :
    vecSq (NCSC.gradient h z) ≤ 4 * vecSq (residualGradient (NCSCSystem.intrinsicProx h) z) := by
  have hp := selectedProx_spec (NCSCSystem.intrinsicProx h) z
  let v := selectedProx (NCSCSystem.intrinsicProx h) z
  change IsProxPoint P.X (DualRegularizedValueOn P.Y (NCSC.auxiliary P mu).f mu)
    (NCSC.internalSmoothness ell mu) z v at hp
  rw [NCSC.auxiliary_regularized_value] at hp
  exact NCSC.gradient_le_internal_residual h (internalSmoothness_ge h) hp

theorem regularizedEnvelope_lower (h : NCSC.NCSCClass ell mu Delta P) (z : EVec m) :
    ValueOn P.Y P.f 0 - Delta ≤
      regularizedEnvelope P.X P.Y (NCSC.auxiliary P mu).f
        (NCSC.internalSmoothness ell mu) mu (NCSCSystem.intrinsicProx h) z := by
  have hp := selectedProx_spec (NCSCSystem.intrinsicProx h) z
  have hl := h.initial_gap_pointwise _ hp.1
  have hq := mul_nonneg (NCSC.internalSmoothness_pos h).le
    (NCCLowerBoundVerification.vecSq_nonneg (selectedProx (NCSCSystem.intrinsicProx h) z - z))
  unfold regularizedEnvelope moreauEnvelope proxObjective
  rw [congrFun (NCSC.auxiliary_regularized_value P mu)
    (selectedProx (NCSCSystem.intrinsicProx h) z)]
  linarith

/-- The actual output anchor is OS once the true initializer budget and the
explicit horizon inequality are met. Local solver correctness is not a premise. -/
theorem program_isOS (h : NCSC.NCSCClass ell mu Delta P)
    (initProgram : Program P.X P.Y (FeasibleSnapshot P.X P.Y))
    {G eps : ℝ} (heps : 0 < eps)
    (hE0 : snapshotEnergy (NCSCSystem.system h)
      (Program.eval (NCSC.auxiliary P mu) initProgram).1 ≤
        (Program.eval (NCSC.auxiliary P mu) initProgram).1.B)
    (hB0 : 0 ≤ (Program.eval (NCSC.auxiliary P mu) initProgram).1.B)
    (hgap : snapshotPotential (NCSCSystem.system h)
      (Program.eval (NCSC.auxiliary P mu) initProgram).1 -
        (ValueOn P.Y P.f 0 - Delta) ≤ G)
    (T : ℕ) (hT : 0 < T) (rho : ℝ)
    (hbudget : 128 * NCSC.internalSmoothness ell mu * G / (T : ℝ) ≤ eps ^ 2) :
    NCSC.IsOS h eps (Program.eval P (program h initProgram T hT rho)).1.1.z := by
  let R0 := (Program.eval (NCSC.auxiliary P mu) initProgram).1
  let R := NCSCProgram.selectedSnapshot (NCSCSystem.system h) R0 T hT
  have hb := NCSCProgram.selectedSnapshot_bounds
    (X := P.X) (Y := P.Y) (f := (NCSC.auxiliary P mu).f)
    (L := NCSC.internalSmoothness ell mu) (r := mu)
    (hprox := NCSCSystem.intrinsicProx h)
    (show P.X.Nonempty from ⟨0, h.primal_origin⟩)
    (NCSC.internalSmoothness_pos h) h.mu_pos (NCSC.intrinsic_parameter_le h)
    (NCSCGeometry.CoreClass.regularizedValue_weaklyConvex
      (P := NCSC.auxiliary P mu) (NCSCGeometry.ofNCSC h))
    (NCSCSystem.system h) R0 hE0 hB0 T hT (ValueOn P.Y P.f 0 - Delta) G
    (regularizedEnvelope_lower h) hgap
  have hg := gradient_le_internal h R.z
  have heval := (eval_program h initProgram T hT rho).1
  refine ⟨heps, (Program.eval P (program h initProgram T hT rho)).1.2, ?_⟩
  rw [heval]
  change vecSq (NCSC.gradient h R.z) ≤ eps ^ 2
  have hmul := mul_le_mul_of_nonneg_left hb.2.2.2 (by norm_num : (0 : ℝ) ≤ 4)
  have heq : 4 * (32 * NCSC.internalSmoothness ell mu * G / (T : ℝ)) =
      128 * NCSC.internalSmoothness ell mu * G / (T : ℝ) := by ring
  rw [heq] at hmul
  exact hg.trans (hmul.trans hbudget)

theorem horizon_budget {L G eps : ℝ} (hL : 0 < L) (hG : 0 < G) (heps : 0 < eps) :
    128 * L * G / (Selection.outerIterations L G eps : ℝ) ≤ eps ^ 2 := by
  have hT := Selection.outerIterations_pos (eps := eps) hL hG
  have hTr : 0 < (Selection.outerIterations L G eps : ℝ) := Nat.cast_pos.mpr hT
  have he2 : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hs := mul_le_mul_of_nonneg_right
    (Selection.outerIterations_lower (ell := L) (Delta := G) (eps := eps)) he2.le
  have heq : 4000 * (L * G / eps ^ 2 + 1) * eps ^ 2 = 4000 * (L * G + eps ^ 2) := by
    field_simp
  rw [heq] at hs
  apply (div_le_iff₀ hTr).2
  nlinarith [mul_pos hL hG]

end
end NCC.Extensions.NCSCExecution
