import NCPLVerification.HardPrimalExplicit
import NCPLVerification.HardJointSmoothness
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Dimension-free smoothness of the explicit primal field
-/

namespace NCPLVerification

noncomputable section

def hardResidualPrevAbs {N : Nat} (d : EVec N) (j : Fin N) : ℝ :=
  if hj : j.1 = 0 then 0 else |d ⟨j.1 - 1, by omega⟩|

def hardResidualInputL1 (N : Nat) (d : EVec N) : ℝ :=
  ∑ j : Fin N, innerAlpha N j * (|d j| + hardResidualPrevAbs d j)

theorem hardResidualPrev_sq_sum_le {N : Nat} (hN : 0 < N)
    (d : EVec N) :
    (∑ j : Fin N, innerAlpha N j * hardResidualPrevAbs d j ^ 2) ≤
      innerPrimalSq N d := by
  cases N with
  | zero => simp at hN
  | succ n =>
      rw [Fin.sum_univ_succ]
      have hzero :
          innerAlpha (n + 1) (0 : Fin (n + 1)) *
              hardResidualPrevAbs d 0 ^ 2 = 0 := by
        simp [hardResidualPrevAbs]
      rw [hzero, zero_add]
      unfold innerPrimalSq
      rw [Fin.sum_univ_castSucc]
      have hterm :
          0 ≤ innerD (n + 1) (Fin.last n) * d (Fin.last n) ^ 2 :=
        mul_nonneg (innerD_pos (by omega) _).le (sq_nonneg _)
      have heq (i : Fin n) :
          innerAlpha (n + 1) i.succ *
              hardResidualPrevAbs d i.succ ^ 2 =
            innerD (n + 1) i.castSucc * d i.castSucc ^ 2 := by
        have hprev : hardResidualPrevAbs d i.succ = |d i.castSucc| := by
          unfold hardResidualPrevAbs
          rw [dif_neg (by simp)]
          congr 2
        rw [hprev]
        have hi : i.castSucc.1 + 1 < n + 1 := by simp
        rw [innerD_castSucc (by omega) i.castSucc hi]
        have hfin : (⟨i.castSucc.1 + 1, hi⟩ : Fin (n + 1)) = i.succ := by
          ext
          rfl
        rw [hfin, sq_abs]
      have hsumEq :
          (∑ i : Fin n, innerAlpha (n + 1) i.succ *
              hardResidualPrevAbs d i.succ ^ 2) =
            ∑ i : Fin n, innerD (n + 1) i.castSucc * d i.castSucc ^ 2 := by
        apply Fintype.sum_congr
        exact heq
      rw [hsumEq]
      exact le_add_of_nonneg_right hterm

theorem hardResidualHere_sq_sum_le {N : Nat} (hN : 0 < N)
    (d : EVec N) :
    (∑ j : Fin N, innerAlpha N j * |d j| ^ 2) ≤ innerPrimalSq N d := by
  unfold innerPrimalSq
  apply Finset.sum_le_sum
  intro j _
  rw [sq_abs]
  exact mul_le_mul_of_nonneg_right (innerAlpha_le_innerD hN j) (sq_nonneg _)

theorem hardResidualInputL1_sq_le {N : Nat} (hN : 0 < N)
    (d : EVec N) :
    hardResidualInputL1 N d ^ 2 ≤ 12 * innerPrimalSq N d := by
  let r : Fin N → ℝ := fun j ↦
    innerAlpha N j * (|d j| + hardResidualPrevAbs d j)
  let f : Fin N → ℝ := fun j ↦ innerAlpha N j
  let g : Fin N → ℝ := fun j ↦
    innerAlpha N j * (|d j| + hardResidualPrevAbs d j) ^ 2
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset (Fin N))
    (r := r) (f := f) (g := g)
    (fun j _ ↦ (innerAlpha_pos hN j).le)
    (fun j _ ↦ mul_nonneg (innerAlpha_pos hN j).le (sq_nonneg _))
    (fun j _ ↦ by
      dsimp [r, f, g]
      exact le_of_eq (by ring))
  have hf : (∑ j : Fin N, f j) ≤ 3 := by
    simpa [f] using sum_innerAlpha_le_three hN
  have hg0 : 0 ≤ ∑ j : Fin N, g j :=
    Finset.sum_nonneg fun j _ ↦
      mul_nonneg (innerAlpha_pos hN j).le (sq_nonneg _)
  have hsplit :
      (∑ j : Fin N, g j) ≤
        2 * ((∑ j : Fin N, innerAlpha N j * |d j| ^ 2) +
          ∑ j : Fin N, innerAlpha N j * hardResidualPrevAbs d j ^ 2) := by
    calc
      (∑ j : Fin N, g j) ≤
          ∑ j : Fin N, 2 *
            (innerAlpha N j * |d j| ^ 2 +
              innerAlpha N j * hardResidualPrevAbs d j ^ 2) := by
        apply Finset.sum_le_sum
        intro j _
        dsimp [g]
        nlinarith [sq_nonneg (|d j| - hardResidualPrevAbs d j),
          (innerAlpha_pos hN j).le]
      _ = 2 * ((∑ j : Fin N, innerAlpha N j * |d j| ^ 2) +
          ∑ j : Fin N, innerAlpha N j * hardResidualPrevAbs d j ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hhere := hardResidualHere_sq_sum_le hN d
  have hprev := hardResidualPrev_sq_sum_le hN d
  have hg : (∑ j : Fin N, g j) ≤ 4 * innerPrimalSq N d := by
    nlinarith
  have hprod :
      (∑ j : Fin N, f j) * (∑ j : Fin N, g j) ≤
        3 * (4 * innerPrimalSq N d) := by
    exact mul_le_mul hf hg hg0 (by norm_num)
  dsimp [hardResidualInputL1]
  change (∑ j : Fin N, r j) ^ 2 ≤ 12 * innerPrimalSq N d
  exact hcs.trans (hprod.trans_eq (by ring))

theorem hardResidualLocalGradP_abs_sub_le {N : Nat}
    (p p' : ℝ) (u u' : EVec N) (j : Fin N) :
    |hardResidualLocalGradP p u j - hardResidualLocalGradP p' u' j| ≤
      4 * residualProfileSmoothC *
        (|p - p'| + |u j - u' j| +
          hardResidualPrevAbs (u - u') j) := by
  by_cases hj : j.1 = 0
  · simp only [hardResidualLocalGradP, dif_pos hj,
      hardResidualPrevAbs, Pi.sub_apply]
    have h := residualFirstProfileGradP_abs_sub_le p (u j) p' (u' j)
    nlinarith [residualProfileSmoothC_nonneg]
  · simp only [hardResidualLocalGradP, dif_neg hj,
      hardResidualPrevAbs, Pi.sub_apply]
    have h := residualProfileGradP_abs_sub_le p
      (u ⟨j.1 - 1, by omega⟩) (u j) p'
      (u' ⟨j.1 - 1, by omega⟩) (u' j)
    have hC := residualProfileSmoothC_nonneg
    nlinarith [abs_nonneg (p - p'), abs_nonneg (u j - u' j),
      abs_nonneg (u ⟨j.1 - 1, by omega⟩ - u' ⟨j.1 - 1, by omega⟩)]

theorem hardResidualLocalGradPSum_abs_sub_le {N : Nat} (hN : 0 < N)
    (p p' : ℝ) (u u' : EVec N) :
    |hardResidualLocalGradPSum N p u - hardResidualLocalGradPSum N p' u'| ≤
      4 * residualProfileSmoothC *
        (3 * |p - p'| + hardResidualInputL1 N (u - u')) := by
  unfold hardResidualLocalGradPSum
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j : Fin N,
        |innerAlpha N j * hardResidualLocalGradP p u j -
          innerAlpha N j * hardResidualLocalGradP p' u' j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin N, innerAlpha N j *
        (4 * residualProfileSmoothC *
          (|p - p'| + |u j - u' j| +
            hardResidualPrevAbs (u - u') j)) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul,
        abs_of_nonneg (innerAlpha_pos hN j).le]
      exact mul_le_mul_of_nonneg_left
        (hardResidualLocalGradP_abs_sub_le p p' u u' j)
        (innerAlpha_pos hN j).le
    _ ≤ 4 * residualProfileSmoothC *
        (3 * |p - p'| + hardResidualInputL1 N (u - u')) := by
      have ha := sum_innerAlpha_le_three hN
      unfold hardResidualInputL1
      have heq :
          (∑ j : Fin N, innerAlpha N j *
            (4 * residualProfileSmoothC *
              (|p - p'| + |u j - u' j| +
                hardResidualPrevAbs (u - u') j))) =
          4 * residualProfileSmoothC *
            (|p - p'| * (∑ j : Fin N, innerAlpha N j) +
              ∑ j : Fin N, innerAlpha N j *
                (|(u - u') j| + hardResidualPrevAbs (u - u') j)) := by
        calc
          _ = ∑ j : Fin N, 4 * residualProfileSmoothC *
              (innerAlpha N j * |p - p'| +
                innerAlpha N j *
                  (|(u - u') j| + hardResidualPrevAbs (u - u') j)) := by
            apply Finset.sum_congr rfl
            intro j _
            simp only [Pi.sub_apply]
            ring
          _ = _ := by
            rw [← Finset.mul_sum]
            congr 1
            rw [Finset.sum_add_distrib, ← Finset.sum_mul]
            ring
      rw [heq]
      exact mul_le_mul_of_nonneg_left (by
        have hp := abs_nonneg (p - p')
        nlinarith) (mul_nonneg (by norm_num) residualProfileSmoothC_nonneg)

def hardPrimalBlockC : ℝ :=
  20 * (terminalConeSmoothC + residualProfileSmoothC)

theorem hardPrimalBlockC_nonneg : 0 ≤ hardPrimalBlockC := by
  unfold hardPrimalBlockC
  exact mul_nonneg (by norm_num)
    (add_nonneg terminalConeSmoothC_nonneg residualProfileSmoothC_nonneg)

theorem hardBaseGradP_abs_sub_le (p p' : ℝ) :
    |-carmonPhiCap * (2 * carmonRhoProfile p * carmonRhoProfileDeriv p) -
        -carmonPhiCap * (2 * carmonRhoProfile p' * carmonRhoProfileDeriv p')| ≤
      terminalConeSmoothC * |p - p'| := by
  have heq :
      carmonRhoProfile p * carmonRhoProfileDeriv p -
          carmonRhoProfile p' * carmonRhoProfileDeriv p' =
        (carmonRhoProfile p - carmonRhoProfile p') *
            carmonRhoProfileDeriv p +
          carmonRhoProfile p' *
            (carmonRhoProfileDeriv p - carmonRhoProfileDeriv p') := by ring
  have htri := abs_add_le
    ((carmonRhoProfile p - carmonRhoProfile p') * carmonRhoProfileDeriv p)
    (carmonRhoProfile p' *
      (carmonRhoProfileDeriv p - carmonRhoProfileDeriv p'))
  repeat' rw [abs_mul] at htri
  have hr := carmonRhoProfile_abs_sub_le p p'
  have hdr := carmonRhoProfileDeriv_abs_sub_le p p'
  have hda := abs_carmonRhoProfileDeriv_le_sixtyFour p
  have hrp : |carmonRhoProfile p'| ≤ 2 := by
    rw [abs_of_nonneg (carmonRhoProfile_nonneg p')]
    exact carmonRhoProfile_le_two p'
  have h1 :
      |carmonRhoProfile p - carmonRhoProfile p'| *
          |carmonRhoProfileDeriv p| ≤ (64 * |p - p'|) * 64 := by gcongr
  have h2 :
      |carmonRhoProfile p'| *
          |carmonRhoProfileDeriv p - carmonRhoProfileDeriv p'| ≤
        2 * (1152 * |p - p'|) := by gcongr
  have hprod :
      |carmonRhoProfile p * carmonRhoProfileDeriv p -
          carmonRhoProfile p' * carmonRhoProfileDeriv p'| ≤
        6400 * |p - p'| := by
    rw [heq]
    exact htri.trans (by nlinarith)
  have hcap : |carmonPhiCap| = carmonPhiCap :=
    abs_of_nonneg carmonPhiCap_nonneg
  rw [show -carmonPhiCap * (2 * carmonRhoProfile p * carmonRhoProfileDeriv p) -
        -carmonPhiCap * (2 * carmonRhoProfile p' * carmonRhoProfileDeriv p') =
      (-2 * carmonPhiCap) *
        (carmonRhoProfile p * carmonRhoProfileDeriv p -
          carmonRhoProfile p' * carmonRhoProfileDeriv p') by ring,
    abs_mul]
  have hcoef : |(-2 : ℝ) * carmonPhiCap| = 2 * carmonPhiCap := by
    rw [abs_mul, abs_neg, hcap]
    norm_num
  rw [hcoef]
  have hm := mul_le_mul_of_nonneg_left hprod
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) carmonPhiCap_nonneg)
  calc
    2 * carmonPhiCap *
        |carmonRhoProfile p * carmonRhoProfileDeriv p -
          carmonRhoProfile p' * carmonRhoProfileDeriv p'| ≤
      2 * carmonPhiCap * (6400 * |p - p'|) := hm
    _ ≤ terminalConeSmoothC * |p - p'| := by
      unfold terminalConeSmoothC
      nlinarith [carmonPhiCap_nonneg, abs_nonneg (p - p'),
        mul_nonneg carmonPhiCap_nonneg (abs_nonneg (p - p'))]

theorem hardTerminalLocalGradP_abs_sub_le {N : Nat} (hN : 0 < N)
    (p q p' q' : ℝ) (u u' : EVec N) :
    |hardTerminalLocalGradP N p q u - hardTerminalLocalGradP N p' q' u'| ≤
      2 * terminalConeSmoothC *
        (|p - p'| + |q - q'| +
          |u ⟨N - 1, Nat.sub_lt hN (by omega)⟩ -
            u' ⟨N - 1, Nat.sub_lt hN (by omega)⟩|) := by
  let l : Fin N := ⟨N - 1, Nat.sub_lt hN (by omega)⟩
  simp only [hardTerminalLocalGradP, dif_pos hN]
  change |terminalPlusGradP p q (u l) + terminalMinusGradP p q (u l) -
      (terminalPlusGradP p' q' (u' l) + terminalMinusGradP p' q' (u' l))| ≤
    2 * terminalConeSmoothC * (|p - p'| + |q - q'| + |u l - u' l|)
  have hp := terminalPlusGradP_abs_sub_le p q (u l) p' q' (u' l)
  have hm := terminalMinusGradP_abs_sub_le p q (u l) p' q' (u' l)
  have htri := abs_add_le
    (terminalPlusGradP p q (u l) - terminalPlusGradP p' q' (u' l))
    (terminalMinusGradP p q (u l) - terminalMinusGradP p' q' (u' l))
  rw [show
      terminalPlusGradP p q (u l) + terminalMinusGradP p q (u l) -
        (terminalPlusGradP p' q' (u' l) + terminalMinusGradP p' q' (u' l)) =
      (terminalPlusGradP p q (u l) - terminalPlusGradP p' q' (u' l)) +
        (terminalMinusGradP p q (u l) - terminalMinusGradP p' q' (u' l)) by ring]
  exact htri.trans (by linarith)

theorem hardTerminalLocalGradQ_abs_sub_le {N : Nat} (hN : 0 < N)
    (p q p' q' : ℝ) (u u' : EVec N) :
    |hardTerminalLocalGradQ N p q u - hardTerminalLocalGradQ N p' q' u'| ≤
      2 * terminalConeSmoothC *
        (|p - p'| + |q - q'| +
          |u ⟨N - 1, Nat.sub_lt hN (by omega)⟩ -
            u' ⟨N - 1, Nat.sub_lt hN (by omega)⟩|) := by
  let l : Fin N := ⟨N - 1, Nat.sub_lt hN (by omega)⟩
  simp only [hardTerminalLocalGradQ, dif_pos hN]
  change |terminalPlusGradQ p q (u l) + terminalMinusGradQ p q (u l) -
      (terminalPlusGradQ p' q' (u' l) + terminalMinusGradQ p' q' (u' l))| ≤
    2 * terminalConeSmoothC * (|p - p'| + |q - q'| + |u l - u' l|)
  have hp := terminalPlusGradQ_abs_sub_le p q (u l) p' q' (u' l)
  have hm := terminalMinusGradQ_abs_sub_le p q (u l) p' q' (u' l)
  have htri := abs_add_le
    (terminalPlusGradQ p q (u l) - terminalPlusGradQ p' q' (u' l))
    (terminalMinusGradQ p q (u l) - terminalMinusGradQ p' q' (u' l))
  rw [show
      terminalPlusGradQ p q (u l) + terminalMinusGradQ p q (u l) -
        (terminalPlusGradQ p' q' (u' l) + terminalMinusGradQ p' q' (u' l)) =
      (terminalPlusGradQ p q (u l) - terminalPlusGradQ p' q' (u' l)) +
        (terminalMinusGradQ p q (u l) - terminalMinusGradQ p' q' (u' l)) by ring]
  exact htri.trans (by linarith)

theorem hardLocalBlockGradP_abs_sub_le {N : Nat} (hN : 0 < N)
    (eta : ℝ) (heta : |eta| ≤ 1) (p q p' q' : ℝ) (u u' : EVec N) :
    |hardLocalBlockGradP N eta p q u - hardLocalBlockGradP N eta p' q' u'| ≤
      hardPrimalBlockC *
        (|p - p'| + |q - q'| +
          |(u - u') ⟨N - 1, Nat.sub_lt hN (by omega)⟩| +
          hardResidualInputL1 N (u - u')) := by
  let B : ℝ → ℝ := fun s ↦
    -carmonPhiCap * (2 * carmonRhoProfile s * carmonRhoProfileDeriv s)
  let TP := hardTerminalLocalGradP N
  let R := hardResidualLocalGradPSum N
  have heq :
      hardLocalBlockGradP N eta p q u -
          hardLocalBlockGradP N eta p' q' u' =
        (B p - B p') + (TP p q u - TP p' q' u') -
          eta * (R p u - R p' u') := by
    simp [hardLocalBlockGradP, B, TP, R]
    ring
  rw [heq]
  have htri1 := abs_sub ((B p - B p') + (TP p q u - TP p' q' u'))
    (eta * (R p u - R p' u'))
  have htri2 := abs_add_le (B p - B p') (TP p q u - TP p' q' u')
  have hb := hardBaseGradP_abs_sub_le p p'
  have ht := hardTerminalLocalGradP_abs_sub_le hN p q p' q' u u'
  have hr := hardResidualLocalGradPSum_abs_sub_le hN p p' u u'
  have hres : |eta * (R p u - R p' u')| ≤
      4 * residualProfileSmoothC *
        (3 * |p - p'| + hardResidualInputL1 N (u - u')) := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right heta (abs_nonneg _)).trans <| by
      simpa [R] using hr
  have hlast :
      |u ⟨N - 1, Nat.sub_lt hN (by omega)⟩ -
        u' ⟨N - 1, Nat.sub_lt hN (by omega)⟩| =
      |(u - u') ⟨N - 1, Nat.sub_lt hN (by omega)⟩| := by rfl
  rw [hlast] at ht
  unfold hardPrimalBlockC
  have ht0 := terminalConeSmoothC_nonneg
  have hr0 := residualProfileSmoothC_nonneg
  nlinarith [abs_nonneg (p - p'), abs_nonneg (q - q'),
    abs_nonneg ((u - u') ⟨N - 1, Nat.sub_lt hN (by omega)⟩),
    show 0 ≤ hardResidualInputL1 N (u - u') by
      exact Finset.sum_nonneg fun j _ ↦ mul_nonneg
        (innerAlpha_pos hN j).le (add_nonneg (abs_nonneg _)
          (by unfold hardResidualPrevAbs; split <;> positivity))]

theorem hardLocalBlockGradQ_abs_sub_le {N : Nat} (hN : 0 < N)
    (p q p' q' : ℝ) (u u' : EVec N) :
    |hardLocalBlockGradQ N p q u - hardLocalBlockGradQ N p' q' u'| ≤
      hardPrimalBlockC *
        (|p - p'| + |q - q'| +
          |(u - u') ⟨N - 1, Nat.sub_lt hN (by omega)⟩| +
          hardResidualInputL1 N (u - u')) := by
  unfold hardLocalBlockGradQ
  have ht := hardTerminalLocalGradQ_abs_sub_le hN p q p' q' u u'
  have hlast :
      |u ⟨N - 1, Nat.sub_lt hN (by omega)⟩ -
        u' ⟨N - 1, Nat.sub_lt hN (by omega)⟩| =
      |(u - u') ⟨N - 1, Nat.sub_lt hN (by omega)⟩| := by rfl
  rw [hlast] at ht
  unfold hardPrimalBlockC
  have hr0 := residualProfileSmoothC_nonneg
  have hL0 : 0 ≤ hardResidualInputL1 N (u - u') :=
    Finset.sum_nonneg fun j _ ↦ mul_nonneg (innerAlpha_pos hN j).le
      (add_nonneg (abs_nonneg _)
        (by unfold hardResidualPrevAbs; split <;> positivity))
  nlinarith [terminalConeSmoothC_nonneg, abs_nonneg (p - p'),
    abs_nonneg (q - q'),
    abs_nonneg ((u - u') ⟨N - 1, Nat.sub_lt hN (by omega)⟩)]

theorem last_sq_le_innerPrimalSq {N : Nat} (hN : 0 < N) (d : EVec N) :
    d ⟨N - 1, Nat.sub_lt hN (by omega)⟩ ^ 2 ≤ innerPrimalSq N d := by
  unfold innerPrimalSq
  have hsingle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun i : Fin N ↦ innerD N i * d i ^ 2)
    (fun i _ ↦ mul_nonneg (innerD_pos hN i).le (sq_nonneg _))
    (Finset.mem_univ ⟨N - 1, Nat.sub_lt hN (by omega)⟩)
  rw [innerD_terminal hN, one_mul] at hsingle
  exact hsingle

theorem hardLocalBlockGradP_sq_sub_le {N : Nat} (hN : 0 < N)
    (eta : ℝ) (heta : |eta| ≤ 1) (p q p' q' : ℝ) (u u' : EVec N) :
    (hardLocalBlockGradP N eta p q u -
        hardLocalBlockGradP N eta p' q' u') ^ 2 ≤
      52 * hardPrimalBlockC ^ 2 *
        ((p - p') ^ 2 + (q - q') ^ 2 + innerPrimalSq N (u - u')) := by
  let a := |p - p'|
  let b := |q - q'|
  let c := |(u - u') ⟨N - 1, Nat.sub_lt hN (by omega)⟩|
  let l := hardResidualInputL1 N (u - u')
  let S := a + b + c + l
  have habs := hardLocalBlockGradP_abs_sub_le hN eta heta p q p' q' u u'
  change |hardLocalBlockGradP N eta p q u -
      hardLocalBlockGradP N eta p' q' u'| ≤ hardPrimalBlockC * S at habs
  have hS0 : 0 ≤ S := by
    dsimp [S, a, b, c, l]
    exact add_nonneg (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (abs_nonneg _)) (Finset.sum_nonneg fun j _ ↦ mul_nonneg
        (innerAlpha_pos hN j).le (add_nonneg (abs_nonneg _)
          (by unfold hardResidualPrevAbs; split <;> positivity)))
  have hsq :
      (hardLocalBlockGradP N eta p q u -
        hardLocalBlockGradP N eta p' q' u') ^ 2 ≤
          (hardPrimalBlockC * S) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hardPrimalBlockC_nonneg hS0)).2 habs
  have hc := last_sq_le_innerPrimalSq hN (u - u')
  have hl := hardResidualInputL1_sq_le hN (u - u')
  have hfour : S ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + l ^ 2) := by
    dsimp [S]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - l),
      sq_nonneg (b - c), sq_nonneg (b - l), sq_nonneg (c - l)]
  have hS : S ^ 2 ≤ 52 *
      ((p - p') ^ 2 + (q - q') ^ 2 + innerPrimalSq N (u - u')) := by
    have ha : a ^ 2 = (p - p') ^ 2 := by dsimp [a]; exact sq_abs _
    have hb : b ^ 2 = (q - q') ^ 2 := by dsimp [b]; exact sq_abs _
    have hc' : c ^ 2 =
        (u - u') ⟨N - 1, Nat.sub_lt hN (by omega)⟩ ^ 2 := by
      dsimp [c]
      exact sq_abs _
    rw [ha, hb, hc'] at hfour
    nlinarith [innerPrimalSq_nonneg hN (u - u')]
  calc
    _ ≤ (hardPrimalBlockC * S) ^ 2 := hsq
    _ = hardPrimalBlockC ^ 2 * S ^ 2 := by ring
    _ ≤ hardPrimalBlockC ^ 2 *
        (52 * ((p - p') ^ 2 + (q - q') ^ 2 +
          innerPrimalSq N (u - u'))) :=
      mul_le_mul_of_nonneg_left hS (sq_nonneg _)
    _ = _ := by ring

theorem hardLocalBlockGradQ_sq_sub_le {N : Nat} (hN : 0 < N)
    (p q p' q' : ℝ) (u u' : EVec N) :
    (hardLocalBlockGradQ N p q u - hardLocalBlockGradQ N p' q' u') ^ 2 ≤
      52 * hardPrimalBlockC ^ 2 *
        ((p - p') ^ 2 + (q - q') ^ 2 + innerPrimalSq N (u - u')) := by
  have habs := hardLocalBlockGradQ_abs_sub_le hN p q p' q' u u'
  let a := |p - p'|
  let b := |q - q'|
  let c := |(u - u') ⟨N - 1, Nat.sub_lt hN (by omega)⟩|
  let l := hardResidualInputL1 N (u - u')
  let S := a + b + c + l
  change |hardLocalBlockGradQ N p q u - hardLocalBlockGradQ N p' q' u'| ≤
    hardPrimalBlockC * S at habs
  have hp := hardLocalBlockGradP_sq_sub_le hN (0 : ℝ) (by simp)
    p q p' q' u u'
  have hS0 : 0 ≤ S := by
    dsimp [S, a, b, c, l]
    exact add_nonneg (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
      (abs_nonneg _)) (Finset.sum_nonneg fun j _ ↦ mul_nonneg
        (innerAlpha_pos hN j).le (add_nonneg (abs_nonneg _)
          (by unfold hardResidualPrevAbs; split <;> positivity)))
  have hsq :
      (hardLocalBlockGradQ N p q u - hardLocalBlockGradQ N p' q' u') ^ 2 ≤
        (hardPrimalBlockC * S) ^ 2 := by
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hardPrimalBlockC_nonneg hS0)).2 habs
  have hc := last_sq_le_innerPrimalSq hN (u - u')
  have hl := hardResidualInputL1_sq_le hN (u - u')
  have hfour : S ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + l ^ 2) := by
    dsimp [S]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - l),
      sq_nonneg (b - c), sq_nonneg (b - l), sq_nonneg (c - l)]
  have hS : S ^ 2 ≤ 52 *
      ((p - p') ^ 2 + (q - q') ^ 2 + innerPrimalSq N (u - u')) := by
    have ha : a ^ 2 = (p - p') ^ 2 := by dsimp [a]; exact sq_abs _
    have hb : b ^ 2 = (q - q') ^ 2 := by dsimp [b]; exact sq_abs _
    have hc' : c ^ 2 =
        (u - u') ⟨N - 1, Nat.sub_lt hN (by omega)⟩ ^ 2 := by
      dsimp [c]
      exact sq_abs _
    rw [ha, hb, hc'] at hfour
    nlinarith [innerPrimalSq_nonneg hN (u - u')]
  calc
    _ ≤ (hardPrimalBlockC * S) ^ 2 := hsq
    _ = hardPrimalBlockC ^ 2 * S ^ 2 := by ring
    _ ≤ hardPrimalBlockC ^ 2 *
        (52 * ((p - p') ^ 2 + (q - q') ^ 2 +
          innerPrimalSq N (u - u'))) :=
      mul_le_mul_of_nonneg_left hS (sq_nonneg _)
    _ = _ := by ring

def hardExplicitQ {T N : Nat} (x : EVec T) (y : EVec (T * N))
    (k : Fin T) : ℝ :=
  hardLocalBlockGradQ N (carmonBlockPrev x k) (x k)
    (hardDualWeightedBlock x y k)

def hardExplicitP {T N : Nat} (eta : ℝ) (x : EVec T)
    (y : EVec (T * N)) (k : Fin T) : ℝ :=
  if hk : k.1 + 1 < T then
    hardLocalBlockGradP N eta (x k) (x ⟨k.1 + 1, hk⟩)
      (hardDualWeightedBlock x y ⟨k.1 + 1, hk⟩)
  else 0

theorem hardExplicitGradX_eq_Q_add_P {T N : Nat} (eta : ℝ)
    (x : EVec T) (y : EVec (T * N)) (k : Fin T) :
    hardExplicitGradX T N eta x y k =
      hardExplicitQ x y k + hardExplicitP eta x y k := by
  unfold hardExplicitGradX
  by_cases hk : k.1 + 1 < T
  · let s : Fin T := ⟨k.1 + 1, hk⟩
    have hsk : s ≠ k := by
      intro h
      have hv := congrArg Fin.val h
      simp [s] at hv
    have hcond (i : Fin T) : i.1 = k.1 + 1 ↔ i = s := by
      constructor
      · intro hi
        apply Fin.ext
        simpa [s] using hi
      · intro hi
        subst i
        simp [s]
    have hpoint (i : Fin T) :
        hardBlockCoordGrad eta x y k i =
          (if i = k then hardExplicitQ x y k else 0) +
            (if i = s then
              hardLocalBlockGradP N eta (x k) (x s)
                (hardDualWeightedBlock x y s)
            else 0) := by
      by_cases hik : i = k
      · subst i
        simp [hardBlockCoordGrad, hardExplicitQ, hsk.symm]
      · rw [hardBlockCoordGrad, if_neg hik]
        by_cases his : i = s
        · subst i
          simp [s, hsk]
        · have hnot : i.1 ≠ k.1 + 1 := by
            intro hi
            exact his ((hcond i).mp hi)
          simp [hnot, hik, his]
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    simp [hardExplicitP, hk, s]
  · have hnone (i : Fin T) : i.1 ≠ k.1 + 1 := by
      intro hi
      have := i.isLt
      omega
    have hpoint (i : Fin T) :
        hardBlockCoordGrad eta x y k i =
          if i = k then hardExplicitQ x y k else 0 := by
      by_cases hik : i = k
      · subst i
        simp [hardBlockCoordGrad, hardExplicitQ]
      · simp [hardBlockCoordGrad, hik, hnone i]
    simp_rw [hpoint]
    simp [hardExplicitP, hk]

theorem hardDualWeightedBlock_metric {T N : Nat} (hN : 0 < N)
    (x x' : EVec T) (y y' : EVec (T * N)) (i : Fin T) :
    innerPrimalSq N
        (hardDualWeightedBlock x y i - hardDualWeightedBlock x' y' i) =
      vecSq (dualBlock y i - dualBlock y' i) := by
  unfold hardDualWeightedBlock
  exact innerPrimalSq_toWeighted_sub hN (dualBlock y i) (dualBlock y' i)

theorem hardExplicitQ_sq_sub_le {T N : Nat} (hN : 0 < N)
    (x x' : EVec T) (y y' : EVec (T * N)) (k : Fin T) :
    (hardExplicitQ x y k - hardExplicitQ x' y' k) ^ 2 ≤
      52 * hardPrimalBlockC ^ 2 *
        (carmonPrevDiff x x' k ^ 2 + (x k - x' k) ^ 2 +
          vecSq (dualBlock y k - dualBlock y' k)) := by
  unfold hardExplicitQ
  have h := hardLocalBlockGradQ_sq_sub_le hN
    (carmonBlockPrev x k) (x k) (carmonBlockPrev x' k) (x' k)
    (hardDualWeightedBlock x y k) (hardDualWeightedBlock x' y' k)
  rw [hardDualWeightedBlock_metric hN x x' y y' k,
    carmonBlockPrev_sq_sub_eq] at h
  exact h

theorem hardExplicitP_sq_sub_le {T N : Nat} (hN : 0 < N)
    (eta : ℝ) (heta : |eta| ≤ 1)
    (x x' : EVec T) (y y' : EVec (T * N)) (k : Fin T) :
    (hardExplicitP eta x y k - hardExplicitP eta x' y' k) ^ 2 ≤
      if hk : k.1 + 1 < T then
        52 * hardPrimalBlockC ^ 2 *
          ((x k - x' k) ^ 2 +
            (x ⟨k.1 + 1, hk⟩ - x' ⟨k.1 + 1, hk⟩) ^ 2 +
            vecSq (dualBlock y ⟨k.1 + 1, hk⟩ -
              dualBlock y' ⟨k.1 + 1, hk⟩))
      else 0 := by
  by_cases hk : k.1 + 1 < T
  · simp only [hardExplicitP, dif_pos hk]
    have h := hardLocalBlockGradP_sq_sub_le hN eta heta
      (x k) (x ⟨k.1 + 1, hk⟩) (x' k) (x' ⟨k.1 + 1, hk⟩)
      (hardDualWeightedBlock x y ⟨k.1 + 1, hk⟩)
      (hardDualWeightedBlock x' y' ⟨k.1 + 1, hk⟩)
    rw [hardDualWeightedBlock_metric hN x x' y y' ⟨k.1 + 1, hk⟩] at h
    exact h
  · simp [hardExplicitP, hk]

theorem sum_if_successor_le_sum {T : Nat} (f : Fin T → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    (∑ k : Fin T, if hk : k.1 + 1 < T then f ⟨k.1 + 1, hk⟩ else 0) ≤
      ∑ i : Fin T, f i := by
  cases T with
  | zero => simp
  | succ n =>
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
      have hcast (i : Fin n) :
          (if hk : i.castSucc.1 + 1 < n + 1 then
              f ⟨i.castSucc.1 + 1, hk⟩ else 0) = f i.succ := by
        have hk : i.castSucc.1 + 1 < n + 1 := by simp
        rw [dif_pos hk]
        congr 2
      simp_rw [hcast]
      have hlast :
          (if hk : (Fin.last n).1 + 1 < n + 1 then
              f ⟨(Fin.last n).1 + 1, hk⟩ else 0) = 0 := by
        rw [dif_neg (by simp)]
      rw [hlast, add_zero]
      exact le_add_of_nonneg_left (hf 0)

theorem vecSq_hardExplicitQ_sub_le {T N : Nat} (hN : 0 < N)
    (x x' : EVec T) (y y' : EVec (T * N)) :
    vecSq (fun k ↦ hardExplicitQ x y k - hardExplicitQ x' y' k) ≤
      52 * hardPrimalBlockC ^ 2 *
        (2 * vecSq (x - x') + vecSq (y - y')) := by
  unfold vecSq
  have hsum :
      (∑ k : Fin T, (hardExplicitQ x y k - hardExplicitQ x' y' k) ^ 2) ≤
        ∑ k : Fin T, 52 * hardPrimalBlockC ^ 2 *
          (carmonPrevDiff x x' k ^ 2 + (x k - x' k) ^ 2 +
            vecSq (dualBlock y k - dualBlock y' k)) := by
    apply Finset.sum_le_sum
    intro k _
    exact hardExplicitQ_sq_sub_le hN x x' y y' k
  have hprev := sum_carmonPrevDiff_sq_le x x'
  have hx : (∑ k : Fin T, (x k - x' k) ^ 2) = vecSq (x - x') := rfl
  have hy :
      (∑ k : Fin T, vecSq (dualBlock y k - dualBlock y' k)) =
        vecSq (y - y') := by
    simp_rw [← dualBlock_sub]
    exact (vecSq_eq_sum_dualBlock (y - y')).symm
  calc
    _ ≤ ∑ k : Fin T, 52 * hardPrimalBlockC ^ 2 *
        (carmonPrevDiff x x' k ^ 2 + (x k - x' k) ^ 2 +
          vecSq (dualBlock y k - dualBlock y' k)) := hsum
    _ = 52 * hardPrimalBlockC ^ 2 *
        ((∑ k : Fin T, carmonPrevDiff x x' k ^ 2) +
          (∑ k : Fin T, (x k - x' k) ^ 2) +
          ∑ k : Fin T, vecSq (dualBlock y k - dualBlock y' k)) := by
      simp [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 52 * hardPrimalBlockC ^ 2 *
        (vecSq (x - x') + vecSq (x - x') + vecSq (y - y')) := by
      rw [hx, hy]
      apply mul_le_mul_of_nonneg_left _
        (mul_nonneg (by norm_num) (sq_nonneg _))
      linarith
    _ = _ := by
      unfold vecSq
      ring

theorem vecSq_hardExplicitP_sub_le {T N : Nat} (hN : 0 < N)
    (eta : ℝ) (heta : |eta| ≤ 1)
    (x x' : EVec T) (y y' : EVec (T * N)) :
    vecSq (fun k ↦ hardExplicitP eta x y k - hardExplicitP eta x' y' k) ≤
      52 * hardPrimalBlockC ^ 2 *
        (2 * vecSq (x - x') + vecSq (y - y')) := by
  unfold vecSq
  let dx : EVec T := x - x'
  let byBlock : Fin T → ℝ := fun i ↦
    vecSq (dualBlock y i - dualBlock y' i)
  have hpoint (k : Fin T) :
      (hardExplicitP eta x y k - hardExplicitP eta x' y' k) ^ 2 ≤
        52 * hardPrimalBlockC ^ 2 *
          (if hk : k.1 + 1 < T then
            dx k ^ 2 + dx ⟨k.1 + 1, hk⟩ ^ 2 + byBlock ⟨k.1 + 1, hk⟩
          else 0) := by
    have h := hardExplicitP_sq_sub_le hN eta heta x x' y y' k
    by_cases hk : k.1 + 1 < T
    · rw [dif_pos hk] at h ⊢
      simpa [dx, byBlock] using h
    · rw [dif_neg hk] at h ⊢
      simpa using h
  have hsum :
      (∑ k : Fin T, (hardExplicitP eta x y k -
          hardExplicitP eta x' y' k) ^ 2) ≤
        ∑ k : Fin T, 52 * hardPrimalBlockC ^ 2 *
          (if hk : k.1 + 1 < T then
            dx k ^ 2 + dx ⟨k.1 + 1, hk⟩ ^ 2 + byBlock ⟨k.1 + 1, hk⟩
          else 0) := by
    apply Finset.sum_le_sum
    intro k _
    exact hpoint k
  have hcurr :
      (∑ k : Fin T, if hk : k.1 + 1 < T then dx k ^ 2 else 0) ≤
        ∑ k : Fin T, dx k ^ 2 := by
    apply Finset.sum_le_sum
    intro k _
    split
    · exact le_rfl
    · exact sq_nonneg _
  have hsuccX := sum_if_successor_le_sum (fun i : Fin T ↦ dx i ^ 2)
    (fun i ↦ sq_nonneg _)
  have hsuccY := sum_if_successor_le_sum byBlock
    (fun i ↦ by unfold byBlock vecSq; positivity)
  have hinside :
      (∑ k : Fin T, if hk : k.1 + 1 < T then
          dx k ^ 2 + dx ⟨k.1 + 1, hk⟩ ^ 2 + byBlock ⟨k.1 + 1, hk⟩
        else 0) ≤
      2 * vecSq (x - x') + vecSq (y - y') := by
    have heq :
        (∑ k : Fin T, if hk : k.1 + 1 < T then
            dx k ^ 2 + dx ⟨k.1 + 1, hk⟩ ^ 2 + byBlock ⟨k.1 + 1, hk⟩
          else 0) =
        (∑ k : Fin T, if hk : k.1 + 1 < T then dx k ^ 2 else 0) +
        (∑ k : Fin T, if hk : k.1 + 1 < T then
          dx ⟨k.1 + 1, hk⟩ ^ 2 else 0) +
        (∑ k : Fin T, if hk : k.1 + 1 < T then
          byBlock ⟨k.1 + 1, hk⟩ else 0) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k.1 + 1 < T
      · simp [hk]
      · simp [hk]
    rw [heq]
    have hx : (∑ k : Fin T, dx k ^ 2) = vecSq (x - x') := by rfl
    have hy : (∑ k : Fin T, byBlock k) = vecSq (y - y') := by
      unfold byBlock
      simp_rw [← dualBlock_sub]
      exact (vecSq_eq_sum_dualBlock (y - y')).symm
    rw [hx] at hcurr hsuccX
    rw [hy] at hsuccY
    linarith
  calc
    _ ≤ ∑ k : Fin T, 52 * hardPrimalBlockC ^ 2 *
        (if hk : k.1 + 1 < T then
          dx k ^ 2 + dx ⟨k.1 + 1, hk⟩ ^ 2 + byBlock ⟨k.1 + 1, hk⟩
        else 0) := hsum
    _ = 52 * hardPrimalBlockC ^ 2 *
        (∑ k : Fin T, if hk : k.1 + 1 < T then
          dx k ^ 2 + dx ⟨k.1 + 1, hk⟩ ^ 2 + byBlock ⟨k.1 + 1, hk⟩
        else 0) := by rw [Finset.mul_sum]
    _ ≤ 52 * hardPrimalBlockC ^ 2 *
        (2 * vecSq (x - x') + vecSq (y - y')) :=
      mul_le_mul_of_nonneg_left hinside
        (mul_nonneg (by norm_num) (sq_nonneg _))

theorem hardGradX_joint_lipschitz {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (heta : |eta| ≤ 1)
    (x x' : EVec T) (y y' : EVec (T * N)) :
    vecSq (hardGradX T N lambdaWall eta x y -
        hardGradX T N lambdaWall eta x' y') ≤
      416 * hardPrimalBlockC ^ 2 *
        (vecSq (x - x') + vecSq (y - y')) := by
  rw [hardGradX_eq_explicit hN, hardGradX_eq_explicit hN]
  let a : EVec T := fun k ↦ hardExplicitQ x y k - hardExplicitQ x' y' k
  let b : EVec T := fun k ↦
    hardExplicitP eta x y k - hardExplicitP eta x' y' k
  have heq :
      hardExplicitGradX T N eta x y - hardExplicitGradX T N eta x' y' =
        a + b := by
    funext k
    change hardExplicitGradX T N eta x y k -
        hardExplicitGradX T N eta x' y' k = (a + b) k
    rw [hardExplicitGradX_eq_Q_add_P, hardExplicitGradX_eq_Q_add_P]
    simp [a, b]
    ring
  rw [heq]
  have hab := vecSq_add_le_two a b
  have ha := vecSq_hardExplicitQ_sub_le hN x x' y y'
  have hb := vecSq_hardExplicitP_sub_le hN eta heta x x' y y'
  change vecSq a ≤ _ at ha
  change vecSq b ≤ _ at hb
  have hx : 0 ≤ vecSq (x - x') := by
    unfold vecSq
    positivity
  have hy : 0 ≤ vecSq (y - y') := by
    unfold vecSq
    positivity
  have hC := sq_nonneg hardPrimalBlockC
  nlinarith

/-- A numerical squared smoothness coefficient for the full primal-dual
gradient.  For fixed numerical `lambdaWall` and `eta` it is independent of
both the outer length `T` and the inner block width `N`. -/
def hardJointSmoothSqCoeff (lambdaWall eta : ℝ) : ℝ :=
  416 * hardPrimalBlockC ^ 2 + 32 * hardBlockDualParamC ^ 2 +
    2 * perspectiveDualSmoothCoeff lambdaWall eta carmonAmax

theorem hardJointSmoothSqCoeff_nonneg (lambdaWall eta : ℝ) :
    0 ≤ hardJointSmoothSqCoeff lambdaWall eta := by
  unfold hardJointSmoothSqCoeff
  have hp := perspectiveDualSmoothCoeff_nonneg lambdaWall eta carmonAmax
  positivity

def hardJointSmoothL (lambdaWall eta : ℝ) : ℝ :=
  Real.sqrt (hardJointSmoothSqCoeff lambdaWall eta)

theorem hardJointSmoothL_nonneg (lambdaWall eta : ℝ) :
    0 ≤ hardJointSmoothL lambdaWall eta := by
  exact Real.sqrt_nonneg _

theorem hardJointSmoothL_pos (lambdaWall eta : ℝ) :
    0 < hardJointSmoothL lambdaWall eta := by
  have hr : 0 < residualProfileSmoothC := by
    norm_num [residualProfileSmoothC]
  have hb : 0 < hardPrimalBlockC := by
    unfold hardPrimalBlockC
    have ht := terminalConeSmoothC_nonneg
    positivity
  unfold hardJointSmoothL
  apply Real.sqrt_pos.2
  unfold hardJointSmoothSqCoeff
  have hd := sq_nonneg hardBlockDualParamC
  have hp := perspectiveDualSmoothCoeff_nonneg lambdaWall eta carmonAmax
  nlinarith [sq_pos_of_pos hb]

theorem hardF_isJointlySmooth {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (heta : |eta| ≤ 1) :
    IsJointlySmooth (hardJointSmoothL lambdaWall eta)
      (hardGradX T N lambdaWall eta) (hardGradY T N lambdaWall eta) := by
  intro x y x' y'
  have hp := hardGradX_joint_lipschitz hN lambdaWall eta heta x x' y y'
  have hd := hardGradY_joint_lipschitz hN lambdaWall eta heta x x' y y'
  have hx : 0 ≤ vecSq (x - x') := by
    unfold vecSq
    positivity
  have hy : 0 ≤ vecSq (y - y') := by
    unfold vecSq
    positivity
  have hdualC : 0 ≤ perspectiveDualSmoothCoeff lambdaWall eta carmonAmax :=
    perspectiveDualSmoothCoeff_nonneg _ _ _
  have hcoeff := hardJointSmoothSqCoeff_nonneg lambdaWall eta
  unfold jointSq hardJointSmoothL
  rw [Real.sq_sqrt hcoeff]
  unfold hardJointSmoothSqCoeff
  nlinarith [sq_nonneg hardPrimalBlockC, sq_nonneg hardBlockDualParamC,
    mul_nonneg hdualC hy, mul_nonneg hdualC hx]

end

end NCPLVerification
