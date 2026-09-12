import NCC.Extensions.NCSCSystem
import NCC.Extensions.NCSCGSReadout

/-! The saddle chosen in the intrinsic solver is the same proof witness
used in the GS conversion. Its coordinates are not supplied to the
algorithm, and the added dual quadratic cancels exactly. -/
namespace NCC.Extensions.NCSCCanonical
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open NCC.Model NCC.Upper

variable {m n : ℕ} {ell mu Delta : ℝ} {P : NCCInstance m n}

def auxiliarySaddle (h : NCSC.NCSCClass ell mu Delta P) (z : EVec m) :
    NCSCSystem.SaddleWitness (NCSC.auxiliary P mu) (NCSC.internalSmoothness ell mu) mu z :=
  Classical.choice (NCSCSystem.exists_saddleWitness (NCSCGeometry.ofNCSC h)
    h.mu_pos (NCSC.intrinsic_parameter_le h)
    (NCSCSystem.chosenProjectX_spec (NCSCGeometry.ofNCSC h))
    (NCSCSystem.chosenProjectY_spec (NCSCGeometry.ofNCSC h)) z)

theorem saddleX_eq (L : ℝ) (z x : EVec m) (y : EVec n) :
    NCSCSystem.saddleX (NCSC.auxiliary P mu) L z x y =
      WithinSystem.saddleX P L z x y := rfl

theorem saddleY_eq (x : EVec m) (y : EVec n) :
    NCSCSystem.saddleY (NCSC.auxiliary P mu) mu x y =
      WithinSystem.saddleY P 0 x y := by
  ext i
  simp only [NCSCSystem.saddleY, WithinSystem.saddleY, ClassOperator.gradYHat,
    NCSC.auxiliary, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

def originalSaddle (h : NCSC.NCSCClass ell mu Delta P) (z : EVec m) :
    WithinSystem.SaddleWitness P (NCSC.internalSmoothness ell mu) 0 z where
  x := (auxiliarySaddle h z).x
  y := (auxiliarySaddle h z).y
  x_mem := (auxiliarySaddle h z).x_mem
  y_mem := (auxiliarySaddle h z).y_mem
  normalX := by
    have hn := (auxiliarySaddle h z).normalX
    rwa [saddleX_eq] at hn
  normalY := by
    have hn := (auxiliarySaddle h z).normalY
    rwa [saddleY_eq] at hn

theorem originalSaddle_x (h : NCSC.NCSCClass ell mu Delta P) (z : EVec m) :
    (originalSaddle h z).x = selectedProx (NCSCSystem.intrinsicProx h) z := by
  symm
  exact selectedProx_unique (NCSC.internalSmoothness_pos h)
    (NCSCGeometry.CoreClass.regularizedValue_weaklyConvex (NCSCGeometry.ofNCSC h))
    (NCSCSystem.intrinsicProx h)
    ((auxiliarySaddle h z).isProxPoint (NCSCGeometry.ofNCSC h) h.mu_pos)

theorem originalSaddle_y (h : NCSC.NCSCClass ell mu Delta P) (z : EVec m) :
    (originalSaddle h z).y = ((NCSCSystem.system h).stationary z).yStar.val := rfl

theorem originalSaddle_isProxPoint (h : NCSC.NCSCClass ell mu Delta P) (z : EVec m) :
    IsProxPoint P.X (ValueOn P.Y P.f) (NCSC.internalSmoothness ell mu) z
      (originalSaddle h z).x := by
  have hp : IsProxPoint P.X
      (DualRegularizedValueOn P.Y (NCSC.auxiliary P mu).f mu)
      (NCSC.internalSmoothness ell mu) z (originalSaddle h z).x :=
    (auxiliarySaddle h z).isProxPoint (NCSCGeometry.ofNCSC h) h.mu_pos
  rwa [NCSC.auxiliary_regularized_value] at hp

end
end NCC.Extensions.NCSCCanonical
