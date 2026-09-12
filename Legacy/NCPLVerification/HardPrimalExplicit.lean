import NCPLVerification.HardBlockExplicit
import NCPLVerification.HardPrimalDifferentiability

/-!
# Explicit primal fields for the hard instance

This file rewrites one perspective block as a sum of globally differentiable
conic terminal and residual pieces.  It then identifies the two scalar
derivatives belonging to the predecessor and current outer coordinates.
-/

namespace NCPLVerification

noncomputable section

def hardResidualLocalValue {N : Nat} (p : ℝ) (u : EVec N) (j : Fin N) : ℝ :=
  if hj : j.1 = 0 then
    residualFirstProfileValue p (u j)
  else
    residualProfileValue p (u ⟨j.1 - 1, by omega⟩) (u j)

def hardResidualLocalGradP {N : Nat} (p : ℝ) (u : EVec N) (j : Fin N) : ℝ :=
  if hj : j.1 = 0 then
    residualFirstProfileGradP p (u j)
  else
    residualProfileGradP p (u ⟨j.1 - 1, by omega⟩) (u j)

def hardResidualLocalEnergy (N : Nat) (p : ℝ) (u : EVec N) : ℝ :=
  ∑ j : Fin N, innerAlpha N j * hardResidualLocalValue p u j

def hardResidualLocalGradPSum (N : Nat) (p : ℝ) (u : EVec N) : ℝ :=
  ∑ j : Fin N, innerAlpha N j * hardResidualLocalGradP p u j

def hardTerminalLocalValue (N : Nat) (p q : ℝ) (u : EVec N) : ℝ :=
  if hN : 0 < N then
    terminalPlusValue p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) +
      terminalMinusValue p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)
  else 0

def hardTerminalLocalGradP (N : Nat) (p q : ℝ) (u : EVec N) : ℝ :=
  if hN : 0 < N then
    terminalPlusGradP p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) +
      terminalMinusGradP p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)
  else 0

def hardTerminalLocalGradQ (N : Nat) (p q : ℝ) (u : EVec N) : ℝ :=
  if hN : 0 < N then
    terminalPlusGradQ p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩) +
      terminalMinusGradQ p q (u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)
  else 0

def hardLocalOuterA (p q : ℝ) : ℝ :=
  terminalPlusCoeff q * carmonSqrtPsi p ^ 2 +
    terminalMinusCoeff q * carmonSqrtPsi (-p) ^ 2

def hardLocalBlockValue (N : Nat) (lambdaWall eta p q : ℝ)
    (u : EVec N) : ℝ :=
  -carmonPhiCap * carmonRhoProfile p ^ 2 +
    hardTerminalLocalValue N p q u -
    eta * hardResidualLocalEnergy N p u -
    eta * lambdaWall * innerWallEnergy N u

def hardLocalBlockGradP (N : Nat) (eta p q : ℝ) (u : EVec N) : ℝ :=
  -carmonPhiCap * (2 * carmonRhoProfile p * carmonRhoProfileDeriv p) +
    hardTerminalLocalGradP N p q u -
    eta * hardResidualLocalGradPSum N p u

def hardLocalBlockGradQ (N : Nat) (p q : ℝ) (u : EVec N) : ℝ :=
  hardTerminalLocalGradQ N p q u

private theorem splitTerminalValue
    {a b c d u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b = 0) :
    c * sigmaConeValue a u + d * sigmaConeValue b u =
      if 0 < a + b then
        (c * a ^ 2 + d * b ^ 2) * sigma (u / (a + b))
      else 0 := by
  rcases mul_eq_zero.mp hab with haz | hbz
  · subst a
    rcases hb.eq_or_lt with rfl | hbpos
    · simp [sigmaConeValue]
    · simp [sigmaConeValue, hbpos]
      ring
  · subst b
    rcases ha.eq_or_lt with rfl | hapos
    · simp [sigmaConeValue]
    · simp [sigmaConeValue, hapos]
      ring

theorem hardTerminalLocalValue_eq {N : Nat} (hN : 0 < N)
    (p q : ℝ) (u : EVec N) :
    hardTerminalLocalValue N p q u =
      hardLocalOuterA p q *
        innerGamma (rescaleEVec (carmonRhoProfile p) u) := by
  let a := carmonSqrtPsi p
  let b := carmonSqrtPsi (-p)
  have hs := splitTerminalValue
    (c := terminalPlusCoeff q) (d := terminalMinusCoeff q)
    (u := u ⟨N - 1, Nat.sub_lt hN (by omega)⟩)
    (carmonSqrtPsi_nonneg p) (carmonSqrtPsi_nonneg (-p))
    (carmonSqrtPsi_mul_neg p)
  rw [innerGamma_eq hN]
  simp only [hardTerminalLocalValue, dif_pos hN, terminalPlusValue,
    terminalMinusValue, rescaleEVec]
  change terminalPlusCoeff q * sigmaConeValue a _ +
      terminalMinusCoeff q * sigmaConeValue b _ =
    hardLocalOuterA p q * sigma (_ / (a + b))
  by_cases hpos : 0 < a + b
  · rw [if_pos hpos] at hs
    simpa [hardLocalOuterA, a, b] using hs
  · rw [if_neg hpos] at hs
    have hab0 : a + b = 0 :=
      le_antisymm (le_of_not_gt hpos) (add_nonneg
        (carmonSqrtPsi_nonneg p) (carmonSqrtPsi_nonneg (-p)))
    have ha0 : a = 0 := by
      nlinarith [carmonSqrtPsi_nonneg p, carmonSqrtPsi_nonneg (-p)]
    have hb0 : b = 0 := by
      nlinarith [carmonSqrtPsi_nonneg p, carmonSqrtPsi_nonneg (-p)]
    simp [sigmaConeValue, hardLocalOuterA, a, b, ha0, hb0]

theorem hardResidualLocalValue_eq {N : Nat} (p : ℝ)
    (u : EVec N) (j : Fin N) :
    hardResidualLocalValue p u j =
      carmonRhoProfile p ^ 2 *
        residualSqKernel
          (innerPrev (rescaleEVec (carmonRhoProfile p) u) j)
          ((rescaleEVec (carmonRhoProfile p) u) j) := by
  have hrho : 0 ≤ carmonRhoProfile p := carmonRhoProfile_nonneg p
  by_cases hpos : 0 < carmonRhoProfile p
  · by_cases hj : j.1 = 0
    · simp only [hardResidualLocalValue, dif_pos hj,
        residualFirstProfileValue, residualFirstConeValue]
      rw [residualConeValue, if_pos hpos,
        div_self hpos.ne',
        show innerPrev (rescaleEVec (carmonRhoProfile p) u) j = 1 by
          simp [innerPrev, hj],
        show (rescaleEVec (carmonRhoProfile p) u) j =
          u j / carmonRhoProfile p by rfl]
    · simp only [hardResidualLocalValue, dif_neg hj,
        residualProfileValue]
      rw [residualConeValue, if_pos hpos,
        show innerPrev (rescaleEVec (carmonRhoProfile p) u) j =
          u ⟨j.1 - 1, by omega⟩ / carmonRhoProfile p by
        simp [innerPrev, rescaleEVec, hj],
        show (rescaleEVec (carmonRhoProfile p) u) j =
          u j / carmonRhoProfile p by rfl]
  · have hrho0 : carmonRhoProfile p = 0 :=
      le_antisymm (le_of_not_gt hpos) hrho
    by_cases hj : j.1 = 0
    · simp [hardResidualLocalValue, hj, residualFirstProfileValue,
        residualFirstConeValue, residualConeValue, hrho0]
    · simp [hardResidualLocalValue, hj, residualProfileValue,
        residualConeValue, hrho0]

theorem hardResidualLocalEnergy_eq (N : Nat) (p : ℝ) (u : EVec N) :
    hardResidualLocalEnergy N p u =
      carmonRhoProfile p ^ 2 *
        innerResidualEnergy N (rescaleEVec (carmonRhoProfile p) u) := by
  unfold hardResidualLocalEnergy innerResidualEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hardResidualLocalValue_eq]
  simp [innerResidual, residualSqKernel]
  ring

theorem hardLocalBlockValue_eq {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N)) (i : Fin T) :
    hardBlockValue N lambdaWall eta x y i =
      hardLocalBlockValue N lambdaWall eta
        (carmonBlockPrev x i) (x i) (hardDualWeightedBlock x y i) := by
  let p := carmonBlockPrev x i
  let u := hardDualWeightedBlock x y i
  change hardBlockValue N lambdaWall eta x y i =
    hardLocalBlockValue N lambdaWall eta p (x i) u
  have hrho := carmonRho_eq_blockProfile x i
  have hA0 := carmonOuterA_eq_terminalSplit x i
  have hA : carmonOuterA x i = hardLocalOuterA p (x i) := by
    simpa [hardLocalOuterA, p] using hA0
  have hterm := hardTerminalLocalValue_eq hN p (x i) u
  have hres := hardResidualLocalEnergy_eq N p u
  have hrhosq : carmonRhoSq x i = carmonRhoProfile p ^ 2 := by
    rw [← carmonRho_sq x i, hrho]
  unfold hardBlockValue hardLocalBlockValue
  rw [hrho, hA, hrhosq]
  by_cases hpos : 0 < carmonRhoProfile p
  · rw [perspectiveDelay_pos_decompose lambdaWall eta
      (hardLocalOuterA p (x i)) u hpos, ← hterm]
    rw [hres]
    ring
  · rw [perspectiveDelay, if_neg hpos]
    have hrho0 : carmonRhoProfile p = 0 :=
      le_antisymm (le_of_not_gt hpos) (carmonRhoProfile_nonneg p)
    have ha0 : carmonSqrtPsi p = 0 := by
      unfold carmonRhoProfile at hrho0
      nlinarith [carmonSqrtPsi_nonneg p, carmonSqrtPsi_nonneg (-p)]
    have hb0 : carmonSqrtPsi (-p) = 0 := by
      unfold carmonRhoProfile at hrho0
      nlinarith [carmonSqrtPsi_nonneg p, carmonSqrtPsi_nonneg (-p)]
    have hA0local : hardLocalOuterA p (x i) = 0 := by
      simp [hardLocalOuterA, ha0, hb0]
    have hterm0 : hardTerminalLocalValue N p (x i) u = 0 := by
      rw [hterm, hA0local]
      ring
    have hres0 : hardResidualLocalEnergy N p u = 0 := by
      rw [hres, hrho0]
      ring
    rw [hterm0, hres0]
    ring

theorem hasDerivAt_hardResidualLocalValue_p {N : Nat}
    (p : ℝ) (u : EVec N) (j : Fin N) :
    HasDerivAt (fun s ↦ hardResidualLocalValue s u j)
      (hardResidualLocalGradP p u j) p := by
  by_cases hj : j.1 = 0
  · simp only [hardResidualLocalValue, hardResidualLocalGradP, dif_pos hj]
    exact hasDerivAt_residualFirstProfileValue_p p (u j)
  · simp only [hardResidualLocalValue, hardResidualLocalGradP, dif_neg hj]
    exact hasDerivAt_residualProfileValue_p p (u ⟨j.1 - 1, by omega⟩) (u j)

theorem hasDerivAt_hardResidualLocalEnergy_p (N : Nat)
    (p : ℝ) (u : EVec N) :
    HasDerivAt (fun s ↦ hardResidualLocalEnergy N s u)
      (hardResidualLocalGradPSum N p u) p := by
  unfold hardResidualLocalEnergy hardResidualLocalGradPSum
  exact HasDerivAt.fun_sum fun j _ ↦
    (hasDerivAt_hardResidualLocalValue_p p u j).const_mul (innerAlpha N j)

theorem hasDerivAt_hardTerminalLocalValue_p {N : Nat} (hN : 0 < N)
    (p q : ℝ) (u : EVec N) :
    HasDerivAt (fun s ↦ hardTerminalLocalValue N s q u)
      (hardTerminalLocalGradP N p q u) p := by
  simp only [hardTerminalLocalValue, hardTerminalLocalGradP, dif_pos hN]
  exact (hasDerivAt_terminalPlusValue_p p q _).add
    (hasDerivAt_terminalMinusValue_p p q _)

theorem hasDerivAt_hardTerminalLocalValue_q {N : Nat} (hN : 0 < N)
    (p q : ℝ) (u : EVec N) :
    HasDerivAt (fun s ↦ hardTerminalLocalValue N p s u)
      (hardTerminalLocalGradQ N p q u) q := by
  simp only [hardTerminalLocalValue, hardTerminalLocalGradQ, dif_pos hN]
  exact (hasDerivAt_terminalPlusValue_q p q _).add
    (hasDerivAt_terminalMinusValue_q p q _)

theorem hasDerivAt_hardLocalBlockValue_p {N : Nat} (hN : 0 < N)
    (lambdaWall eta p q : ℝ) (u : EVec N) :
    HasDerivAt (fun s ↦ hardLocalBlockValue N lambdaWall eta s q u)
      (hardLocalBlockGradP N eta p q u) p := by
  have hbase := ((hasDerivAt_carmonRhoProfile p).pow 2).const_mul
    (-carmonPhiCap)
  have hterm := hasDerivAt_hardTerminalLocalValue_p hN p q u
  have hres := (hasDerivAt_hardResidualLocalEnergy_p N p u).const_mul eta
  have hwall := hasDerivAt_const p (eta * lambdaWall * innerWallEnergy N u)
  have h := (hbase.add hterm).sub hres |>.sub hwall
  change HasDerivAt
    (fun s : ℝ ↦ hardLocalBlockValue N lambdaWall eta s q u) _ p at h
  apply h.congr_deriv
  simp only [hardLocalBlockGradP, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

theorem hasDerivAt_hardLocalBlockValue_q {N : Nat} (hN : 0 < N)
    (lambdaWall eta p q : ℝ) (u : EVec N) :
    HasDerivAt (fun s ↦ hardLocalBlockValue N lambdaWall eta p s u)
      (hardLocalBlockGradQ N p q u) q := by
  have hbase := hasDerivAt_const q
    (-carmonPhiCap * carmonRhoProfile p ^ 2)
  have hterm := hasDerivAt_hardTerminalLocalValue_q hN p q u
  have hres := hasDerivAt_const q (eta * hardResidualLocalEnergy N p u)
  have hwall := hasDerivAt_const q (eta * lambdaWall * innerWallEnergy N u)
  have h := (hbase.add hterm).sub hres |>.sub hwall
  change HasDerivAt
    (fun s : ℝ ↦ hardLocalBlockValue N lambdaWall eta p s u) _ q at h
  apply h.congr_deriv
  simp [hardLocalBlockGradQ]

def hardBlockCoordGrad {T N : Nat} (eta : ℝ) (x : EVec T)
    (y : EVec (T * N)) (k i : Fin T) : ℝ :=
  if i = k then
    hardLocalBlockGradQ N (carmonBlockPrev x i) (x i)
      (hardDualWeightedBlock x y i)
  else if i.1 = k.1 + 1 then
    hardLocalBlockGradP N eta (x k) (x i)
      (hardDualWeightedBlock x y i)
  else 0

def hardExplicitGradX (T N : Nat) (eta : ℝ)
    (x : EVec T) (y : EVec (T * N)) : EVec T :=
  fun k ↦ ∑ i : Fin T, hardBlockCoordGrad eta x y k i

theorem carmonBlockPrev_update_self {T : Nat} (x : EVec T)
    (i : Fin T) (s : ℝ) :
    carmonBlockPrev (Function.update x i s) i = carmonBlockPrev x i := by
  unfold carmonBlockPrev
  by_cases hi : i.1 = 0
  · simp [hi]
  · simp only [dif_neg hi]
    apply Function.update_of_ne
    apply Fin.ne_of_val_ne
    simp only
    omega

theorem carmonBlockPrev_update_successor {T : Nat} (x : EVec T)
    (k i : Fin T) (s : ℝ) (hki : i.1 = k.1 + 1) :
    carmonBlockPrev (Function.update x k s) i = s := by
  unfold carmonBlockPrev
  have hi : i.1 ≠ 0 := by omega
  rw [dif_neg hi]
  have hbound : i.1 - 1 < T :=
    lt_of_le_of_lt (Nat.sub_le i.1 1) i.isLt
  have heq : (⟨i.1 - 1, hbound⟩ : Fin T) = k := by
    apply Fin.ext
    simp [hki]
  rw [heq]
  simp

theorem carmonBlockPrev_update_other {T : Nat} (x : EVec T)
    (k i : Fin T) (s : ℝ) (hki : i.1 ≠ k.1 + 1) :
    carmonBlockPrev (Function.update x k s) i = carmonBlockPrev x i := by
  unfold carmonBlockPrev
  by_cases hi : i.1 = 0
  · simp [hi]
  · simp only [dif_neg hi]
    have hbound : i.1 - 1 < T :=
      lt_of_le_of_lt (Nat.sub_le i.1 1) i.isLt
    have hne : (⟨i.1 - 1, hbound⟩ : Fin T) ≠ k := by
      intro h
      have hv := congrArg Fin.val h
      simp only at hv
      omega
    rw [Function.update_of_ne hne]

theorem hasDerivAt_hardBlockValue_update {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N))
    (k i : Fin T) :
    HasDerivAt
      (fun s ↦ hardBlockValue N lambdaWall eta (Function.update x k s) y i)
      (hardBlockCoordGrad eta x y k i) (x k) := by
  by_cases hik : i = k
  · subst i
    have h := hasDerivAt_hardLocalBlockValue_q hN lambdaWall eta
      (carmonBlockPrev x k) (x k) (hardDualWeightedBlock x y k)
    have hfun :
        (fun s ↦ hardBlockValue N lambdaWall eta (Function.update x k s) y k) =
          (fun s ↦ hardLocalBlockValue N lambdaWall eta
            (carmonBlockPrev x k) s (hardDualWeightedBlock x y k)) := by
      funext s
      rw [hardLocalBlockValue_eq hN]
      rw [carmonBlockPrev_update_self]
      simp [hardDualWeightedBlock]
    rw [hardBlockCoordGrad, if_pos rfl, hfun]
    exact h
  · by_cases hsucc : i.1 = k.1 + 1
    · have hik' : i ≠ k := hik
      have h := hasDerivAt_hardLocalBlockValue_p hN lambdaWall eta
        (x k) (x i) (hardDualWeightedBlock x y i)
      have hfun :
          (fun s ↦ hardBlockValue N lambdaWall eta (Function.update x k s) y i) =
            (fun s ↦ hardLocalBlockValue N lambdaWall eta
              s (x i) (hardDualWeightedBlock x y i)) := by
        funext s
        rw [hardLocalBlockValue_eq hN]
        rw [carmonBlockPrev_update_successor x k i s hsucc]
        rw [Function.update_of_ne hik]
        rfl
      rw [hardBlockCoordGrad, if_neg hik, if_pos hsucc, hfun]
      exact h
    · have hfun :
          (fun s ↦ hardBlockValue N lambdaWall eta (Function.update x k s) y i) =
            (fun _ ↦ hardLocalBlockValue N lambdaWall eta
              (carmonBlockPrev x i) (x i) (hardDualWeightedBlock x y i)) := by
        funext s
        rw [hardLocalBlockValue_eq hN]
        rw [carmonBlockPrev_update_other x k i s hsucc]
        rw [Function.update_of_ne hik]
        rfl
      rw [hardBlockCoordGrad, if_neg hik, if_neg hsucc, hfun]
      exact hasDerivAt_const (x k) _

theorem hasDerivAt_hardF_update {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N)) (k : Fin T) :
    HasDerivAt
      (fun s ↦ hardF T N lambdaWall eta (Function.update x k s) y)
      (hardExplicitGradX T N eta x y k) (x k) := by
  unfold hardF hardExplicitGradX
  exact HasDerivAt.fun_sum fun i _ ↦
    hasDerivAt_hardBlockValue_update hN lambdaWall eta x y k i

theorem hardGradX_eq_explicit {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (x : EVec T) (y : EVec (T * N)) :
    hardGradX T N lambdaWall eta x y = hardExplicitGradX T N eta x y := by
  funext k
  have hF := hasEVecFDerivAt_hardF_x_gradient hN lambdaWall eta x y
  unfold HasEVecFDerivAt at hF
  have hxup : Function.update x k (x k) = x := by
    funext j
    by_cases hj : j = k
    · subst j
      simp
    · rw [Function.update_of_ne hj]
  rw [← hxup] at hF
  have hcomp := hF.comp_hasDerivAt (x k) (hasDerivAt_update x k (x k))
  have hexp := hasDerivAt_hardF_update hN lambdaWall eta x y k
  have heq := hcomp.unique hexp
  simpa [evecDot_apply, Pi.single_apply] using heq

end

end NCPLVerification
