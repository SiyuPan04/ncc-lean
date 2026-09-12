import NCPLVerification.CarmonActivation

/-!
# Derivative certificates for the outer activation data

This file formalizes the derivative-size part of Lemma 6.2.  Both `rho_i`
and `A_i` have sparse genuine Fréchet derivatives; the first derivative of
`A_i` is proportional to `rho_i`, uniformly in the outer dimension.
-/

namespace NCPLVerification

noncomputable section

theorem carmonRho_eq_profile {T : Nat} (x : EVec T) (i : Fin T) :
    carmonRho x i = if hi : i.1 = 0 then 1 else
      carmonRhoProfile (x ⟨i.1 - 1, by omega⟩) := by
  rw [carmonRho_eq_explicit]
  unfold carmonRhoExplicit carmonRhoProfile
  rfl

theorem carmonRho_le_two {T : Nat} (x : EVec T) (i : Fin T) :
    carmonRho x i ≤ 2 := by
  rw [carmonRho_eq_profile]
  split
  · norm_num
  · exact carmonRhoProfile_le_two _

def carmonRhoSqPrevDeriv {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  if hi : i.1 = 0 then 0 else
    carmonPsiDeriv (x ⟨i.1 - 1, by omega⟩) -
      carmonPsiDeriv (-x ⟨i.1 - 1, by omega⟩)

theorem abs_carmonRhoSqPrevDeriv_le {T : Nat} (x : EVec T) (i : Fin T) :
    |carmonRhoSqPrevDeriv x i| ≤ 64 * carmonRho x i := by
  by_cases hi : i.1 = 0
  · simp [carmonRhoSqPrevDeriv, hi, carmonRho_nonneg x i]
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    rw [carmonRhoSqPrevDeriv, dif_neg hi, carmonRho_eq_profile, dif_neg hi]
    unfold carmonRhoProfile
    have htri := abs_sub (carmonPsiDeriv (x p)) (carmonPsiDeriv (-x p))
    have hp := abs_carmonPsiDeriv_le_sqrt (x p)
    have hn := abs_carmonPsiDeriv_le_sqrt (-x p)
    nlinarith [carmonSqrtPsi_nonneg (x p), carmonSqrtPsi_nonneg (-x p)]

theorem carmonRhoSqPrevDeriv_abs_sub_le {T : Nat}
    (x x' : EVec T) (i : Fin T) :
    |carmonRhoSqPrevDeriv x i - carmonRhoSqPrevDeriv x' i| ≤
      864 * carmonPrevDiff x x' i := by
  by_cases hi : i.1 = 0
  · simp [carmonRhoSqPrevDeriv, carmonPrevDiff, hi]
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    rw [carmonRhoSqPrevDeriv, dif_neg hi,
      carmonRhoSqPrevDeriv, dif_neg hi]
    have hp := carmonPsiDeriv_abs_sub_le (x p) (x' p)
    have hn := carmonPsiDeriv_abs_sub_le (-x p) (-x' p)
    have hn' : |carmonPsiDeriv (-x p) - carmonPsiDeriv (-x' p)| ≤
        432 * |x p - x' p| := by
      simpa only [neg_sub_neg, abs_neg, abs_sub_comm] using hn
    have htri := abs_sub
      (carmonPsiDeriv (x p) - carmonPsiDeriv (x' p))
      (carmonPsiDeriv (-x p) - carmonPsiDeriv (-x' p))
    rw [carmonPrevDiff, dif_neg hi]
    rw [show
      carmonPsiDeriv (x p) - carmonPsiDeriv (-x p) -
          (carmonPsiDeriv (x' p) - carmonPsiDeriv (-x' p)) =
        (carmonPsiDeriv (x p) - carmonPsiDeriv (x' p)) -
          (carmonPsiDeriv (-x p) - carmonPsiDeriv (-x' p)) by ring]
    nlinarith

theorem abs_carmonTermPrevCoeff_le {T : Nat} (x : EVec T) (i : Fin T) :
    |carmonTermPrevCoeff x i| ≤ 64 * carmonPhiCap * carmonRho x i := by
  by_cases hi : i.1 = 0
  · rw [carmonTermPrevCoeff, dif_pos hi]
    simp only [abs_zero]
    exact mul_nonneg
      (mul_nonneg (by norm_num) carmonPhiCap_nonneg) (carmonRho_nonneg x i)
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    rw [carmonTermPrevCoeff, dif_neg hi, abs_neg,
      carmonRho_eq_profile, dif_neg hi]
    unfold carmonRhoProfile
    have htri := abs_add_le
      (carmonPsiDeriv (-x p) * carmonPhi (-x i))
      (carmonPsiDeriv (x p) * carmonPhi (x i))
    rw [abs_mul, abs_mul] at htri
    have hpsiN := abs_carmonPsiDeriv_le_sqrt (-x p)
    have hpsiP := abs_carmonPsiDeriv_le_sqrt (x p)
    have hphiN := abs_carmonPhi_le_cap (-x i)
    have hphiP := abs_carmonPhi_le_cap (x i)
    have hprodN : |carmonPsiDeriv (-x p)| * |carmonPhi (-x i)| ≤
        (64 * carmonSqrtPsi (-x p)) * carmonPhiCap := by
      exact mul_le_mul hpsiN hphiN (abs_nonneg _)
        (mul_nonneg (by norm_num) (carmonSqrtPsi_nonneg (-x p)))
    have hprodP : |carmonPsiDeriv (x p)| * |carmonPhi (x i)| ≤
        (64 * carmonSqrtPsi (x p)) * carmonPhiCap := by
      exact mul_le_mul hpsiP hphiP (abs_nonneg _)
        (mul_nonneg (by norm_num) (carmonSqrtPsi_nonneg (x p)))
    nlinarith

theorem carmonTermPrevCoeff_abs_sub_le {T : Nat}
    (x x' : EVec T) (i : Fin T) :
    |carmonTermPrevCoeff x i - carmonTermPrevCoeff x' i| ≤
      864 * carmonPhiCap * carmonPrevDiff x x' i +
        96 * |x i - x' i| := by
  by_cases hi : i.1 = 0
  · simp [carmonTermPrevCoeff, carmonPrevDiff, hi]
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    have hpnext : p.1 + 1 < T := by
      simp only [p]
      omega
    have hpi : (⟨p.1 + 1, hpnext⟩ : Fin T) = i := by
      apply Fin.ext
      simp only [p]
      omega
    have hfx : carmonTermPrevCoeff x i = -carmonForward x p := by
      rw [carmonTermPrevCoeff, dif_neg hi, carmonForward, dif_pos hpnext]
      rw [hpi]
    have hfx' : carmonTermPrevCoeff x' i = -carmonForward x' p := by
      rw [carmonTermPrevCoeff, dif_neg hi, carmonForward, dif_pos hpnext]
      rw [hpi]
    rw [hfx, hfx', neg_sub_neg, abs_sub_comm]
    have h := carmonForward_abs_sub_le x x' p
    rw [carmonPrevDiff, dif_neg hi]
    change _ ≤ 864 * carmonPhiCap * |x p - x' p| + 96 * |x i - x' i|
    simpa [carmonNextDiff, hpnext, hpi] using h

def carmonOuterAPrevCoeff {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  carmonPhiCap * carmonRhoSqPrevDeriv x i + carmonTermPrevCoeff x i

theorem abs_carmonOuterAPrevCoeff_le {T : Nat} (x : EVec T) (i : Fin T) :
    |carmonOuterAPrevCoeff x i| ≤
      128 * carmonPhiCap * carmonRho x i := by
  unfold carmonOuterAPrevCoeff
  have htri := abs_add_le
    (carmonPhiCap * carmonRhoSqPrevDeriv x i) (carmonTermPrevCoeff x i)
  rw [abs_mul, abs_of_nonneg carmonPhiCap_nonneg] at htri
  have hr := abs_carmonRhoSqPrevDeriv_le x i
  have ht := abs_carmonTermPrevCoeff_le x i
  nlinarith [carmonPhiCap_nonneg, carmonRho_nonneg x i]

theorem carmonOuterAPrevCoeff_abs_sub_le {T : Nat}
    (x x' : EVec T) (i : Fin T) :
    |carmonOuterAPrevCoeff x i - carmonOuterAPrevCoeff x' i| ≤
      1728 * carmonPhiCap * carmonPrevDiff x x' i +
        96 * |x i - x' i| := by
  unfold carmonOuterAPrevCoeff
  have hr := carmonRhoSqPrevDeriv_abs_sub_le x x' i
  have ht := carmonTermPrevCoeff_abs_sub_le x x' i
  have htri := abs_add_le
    (carmonPhiCap * carmonRhoSqPrevDeriv x i -
      carmonPhiCap * carmonRhoSqPrevDeriv x' i)
    (carmonTermPrevCoeff x i - carmonTermPrevCoeff x' i)
  have heq :
      (carmonPhiCap * carmonRhoSqPrevDeriv x i + carmonTermPrevCoeff x i) -
        (carmonPhiCap * carmonRhoSqPrevDeriv x' i + carmonTermPrevCoeff x' i) =
      (carmonPhiCap * carmonRhoSqPrevDeriv x i -
        carmonPhiCap * carmonRhoSqPrevDeriv x' i) +
      (carmonTermPrevCoeff x i - carmonTermPrevCoeff x' i) := by ring
  have hcap :
      |carmonPhiCap * carmonRhoSqPrevDeriv x i -
        carmonPhiCap * carmonRhoSqPrevDeriv x' i| ≤
        864 * carmonPhiCap * carmonPrevDiff x x' i := by
    rw [← mul_sub, abs_mul, abs_of_nonneg carmonPhiCap_nonneg]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_left hr carmonPhiCap_nonneg
  rw [heq]
  nlinarith [carmonPhiCap_nonneg, carmonPrevDiff_nonneg x x' i]

theorem abs_carmonIncoming_le_four_rho {T : Nat} (x : EVec T) (i : Fin T) :
    |carmonIncoming x i| ≤ 4 * carmonRho x i := by
  rw [carmonIncoming_eq_rho_mul, abs_mul,
    abs_of_nonneg (carmonRhoSq_nonneg x i)]
  have hphi := abs_carmonPhiDeriv_le_two (x i)
  have hrho := carmonRho_le_two x i
  rw [← carmonRho_sq]
  nlinarith [carmonRho_nonneg x i]

def carmonOuterAGradient {T : Nat} (x : EVec T) (i : Fin T) : EVec T :=
  fun j ↦ if hji : j = i then -carmonIncoming x i else
    if hi : i.1 = 0 then 0 else
      if hjp : j = ⟨i.1 - 1, by omega⟩ then carmonOuterAPrevCoeff x i else 0

def carmonOuterCA : ℝ := 10 + 256 * carmonPhiCap

theorem carmonOuterCA_nonneg : 0 ≤ carmonOuterCA := by
  unfold carmonOuterCA
  nlinarith [carmonPhiCap_nonneg]

def carmonOuterASmoothC : ℝ := 200 + 1800 * carmonPhiCap

theorem carmonOuterASmoothC_nonneg : 0 ≤ carmonOuterASmoothC := by
  unfold carmonOuterASmoothC
  nlinarith [carmonPhiCap_nonneg]

theorem abs_carmonOuterAGradient_le {T : Nat} (x : EVec T)
    (i j : Fin T) :
    |carmonOuterAGradient x i j| ≤ carmonOuterCA * carmonRho x i := by
  unfold carmonOuterAGradient
  split
  · rw [abs_neg]
    have h := abs_carmonIncoming_le_four_rho x i
    unfold carmonOuterCA
    nlinarith [carmonPhiCap_nonneg, carmonRho_nonneg x i]
  · split
    · simp [mul_nonneg carmonOuterCA_nonneg (carmonRho_nonneg x i)]
    · split
      · have h := abs_carmonOuterAPrevCoeff_le x i
        unfold carmonOuterCA
        nlinarith [carmonPhiCap_nonneg, carmonRho_nonneg x i]
      · simp [mul_nonneg carmonOuterCA_nonneg (carmonRho_nonneg x i)]

theorem carmonOuterAGradient_component_abs_sub_le {T : Nat}
    (x x' : EVec T) (i j : Fin T) :
    |carmonOuterAGradient x i j - carmonOuterAGradient x' i j| ≤
      carmonOuterASmoothC *
        (carmonPrevDiff x x' i + |x i - x' i|) := by
  unfold carmonOuterAGradient
  split
  · rw [neg_sub_neg, abs_sub_comm]
    have h := carmonIncoming_abs_sub_le x x' i
    unfold carmonOuterASmoothC
    nlinarith [carmonPhiCap_nonneg, carmonPrevDiff_nonneg x x' i,
      abs_nonneg (x i - x' i)]
  · split
    · simpa only [sub_self, abs_zero] using
        mul_nonneg carmonOuterASmoothC_nonneg
          (add_nonneg (carmonPrevDiff_nonneg x x' i)
            (abs_nonneg (x i - x' i)))
    · split
      · have h := carmonOuterAPrevCoeff_abs_sub_le x x' i
        unfold carmonOuterASmoothC
        nlinarith [carmonPhiCap_nonneg, carmonPrevDiff_nonneg x x' i,
          abs_nonneg (x i - x' i)]
      · simpa only [sub_self, abs_zero] using
          mul_nonneg carmonOuterASmoothC_nonneg
            (add_nonneg (carmonPrevDiff_nonneg x x' i)
              (abs_nonneg (x i - x' i)))

/-- Squared Euclidean Hessian/gradient-Lipschitz form of the second-derivative
part of the outer activation lemma. -/
theorem vecSq_carmonOuterAGradient_sub_le {T : Nat}
    (x x' : EVec T) (i : Fin T) :
    vecSq (carmonOuterAGradient x i - carmonOuterAGradient x' i) ≤
      4 * carmonOuterASmoothC ^ 2 *
        (carmonPrevDiff x x' i ^ 2 + |x i - x' i| ^ 2) := by
  let B := carmonOuterASmoothC *
    (carmonPrevDiff x x' i + |x i - x' i|)
  have hB0 : 0 ≤ B := mul_nonneg carmonOuterASmoothC_nonneg
    (add_nonneg (carmonPrevDiff_nonneg x x' i) (abs_nonneg _))
  have hsq (j : Fin T) :
      (carmonOuterAGradient x i - carmonOuterAGradient x' i) j ^ 2 ≤ B ^ 2 := by
    have h := carmonOuterAGradient_component_abs_sub_le x x' i j
    change |(carmonOuterAGradient x i - carmonOuterAGradient x' i) j| ≤ B at h
    calc
      (carmonOuterAGradient x i - carmonOuterAGradient x' i) j ^ 2 =
          |(carmonOuterAGradient x i - carmonOuterAGradient x' i) j| ^ 2 := by
        rw [sq_abs]
      _ ≤ B ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
  by_cases hi : i.1 = 0
  · have hsum : vecSq
        (carmonOuterAGradient x i - carmonOuterAGradient x' i) =
        (carmonOuterAGradient x i - carmonOuterAGradient x' i) i ^ 2 := by
      unfold vecSq
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [carmonOuterAGradient, hji, hi]
      · simp
    rw [hsum]
    have h := hsq i
    have hp0 : carmonPrevDiff x x' i = 0 := by simp [carmonPrevDiff, hi]
    unfold B at h
    rw [hp0, zero_add] at h
    nlinarith [sq_nonneg (carmonOuterASmoothC * |x i - x' i|)]
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    have hpi : p ≠ i := by
      intro hbad
      have := Fin.ext_iff.mp hbad
      simp only [p] at this
      omega
    have hsum : vecSq
        (carmonOuterAGradient x i - carmonOuterAGradient x' i) =
        (carmonOuterAGradient x i - carmonOuterAGradient x' i) i ^ 2 +
          (carmonOuterAGradient x i - carmonOuterAGradient x' i) p ^ 2 := by
      unfold vecSq
      calc
        (∑ j : Fin T,
            (carmonOuterAGradient x i - carmonOuterAGradient x' i) j ^ 2) =
            ∑ j ∈ ({i, p} : Finset (Fin T)),
              (carmonOuterAGradient x i - carmonOuterAGradient x' i) j ^ 2 := by
          symm
          apply Finset.sum_subset
          · simp
          · intro j _ hj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            have hji : j ≠ i := fun h ↦ hj (Or.inl h)
            have hjp : j ≠ p := fun h ↦ hj (Or.inr h)
            simp [carmonOuterAGradient, hi, hji, hjp, p]
        _ = _ := Finset.sum_pair hpi.symm
    rw [hsum]
    have hii := hsq i
    have hip := hsq p
    have hab := sq_nonneg (carmonPrevDiff x x' i - |x i - x' i|)
    unfold B at hii hip
    nlinarith [carmonOuterASmoothC_nonneg,
      carmonPrevDiff_nonneg x x' i, abs_nonneg (x i - x' i)]

/-- Squared Euclidean form of the article's uniform
`‖∇ A_i(x)‖ ≤ C_A ρ_i(x)` estimate.  Only the current and predecessor
coordinates can occur, so the constant is independent of `T`. -/
theorem vecSq_carmonOuterAGradient_le {T : Nat} (x : EVec T) (i : Fin T) :
    vecSq (carmonOuterAGradient x i) ≤
      2 * carmonOuterCA ^ 2 * carmonRho x i ^ 2 := by
  have hbound (j : Fin T) :
      carmonOuterAGradient x i j ^ 2 ≤
        (carmonOuterCA * carmonRho x i) ^ 2 := by
    have h := abs_carmonOuterAGradient_le x i j
    have hnonneg : 0 ≤ carmonOuterCA * carmonRho x i :=
      mul_nonneg carmonOuterCA_nonneg (carmonRho_nonneg x i)
    calc
      carmonOuterAGradient x i j ^ 2 =
          |carmonOuterAGradient x i j| ^ 2 := by rw [sq_abs]
      _ ≤ (carmonOuterCA * carmonRho x i) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h 2
  by_cases hi : i.1 = 0
  · have hsum : vecSq (carmonOuterAGradient x i) =
        carmonOuterAGradient x i i ^ 2 := by
      unfold vecSq
      apply Finset.sum_eq_single i
      · intro j _ hji
        simp [carmonOuterAGradient, hji, hi]
      · simp
    rw [hsum]
    have h := hbound i
    nlinarith [sq_nonneg (carmonOuterCA * carmonRho x i)]
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    have hpi : p ≠ i := by
      intro hbad
      have := Fin.ext_iff.mp hbad
      simp only [p] at this
      omega
    have hsum : vecSq (carmonOuterAGradient x i) =
        carmonOuterAGradient x i i ^ 2 +
          carmonOuterAGradient x i p ^ 2 := by
      unfold vecSq
      calc
        (∑ j : Fin T, carmonOuterAGradient x i j ^ 2) =
            ∑ j ∈ ({i, p} : Finset (Fin T)),
              carmonOuterAGradient x i j ^ 2 := by
          symm
          apply Finset.sum_subset
          · simp
          · intro j _ hj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            have hji : j ≠ i := fun h => hj (Or.inl h)
            have hjp : j ≠ p := fun h => hj (Or.inr h)
            simp [carmonOuterAGradient, hi, hji, hjp, p]
        _ = carmonOuterAGradient x i i ^ 2 +
            carmonOuterAGradient x i p ^ 2 := Finset.sum_pair hpi.symm
    rw [hsum]
    have hii := hbound i
    have hip := hbound p
    nlinarith

def carmonRhoFDeriv {T : Nat} (x : EVec T) (i : Fin T) :
    EVec T →L[ℝ] ℝ :=
  if hi : i.1 = 0 then 0 else
    carmonRhoProfileDeriv (x ⟨i.1 - 1, by omega⟩) •
      evecProj ⟨i.1 - 1, by omega⟩

theorem hasCarmonFDerivAt_carmonRho {T : Nat} (x : EVec T) (i : Fin T) :
    HasCarmonFDerivAt (fun w : EVec T ↦ carmonRho w i)
      (carmonRhoFDeriv x i) x := by
  letI : AddCommGroup (EVec T) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec T) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec T) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasCarmonFDerivAt
  by_cases hi : i.1 = 0
  · have hconst : HasFDerivAt (fun _ : EVec T ↦ (1 : ℝ)) 0 x :=
      hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x
    simpa [carmonRho_eq_profile, carmonRhoFDeriv, hi] using hconst
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    have hp : HasFDerivAt (fun w : EVec T ↦ w p) (evecProj p) x :=
      (evecProj p).hasFDerivAt
    have hprofile := (hasDerivAt_carmonRhoProfile (x p)).hasFDerivAt.comp x hp
    convert hprofile using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    · funext w
      rw [carmonRho_eq_profile]
      simp [hi, p]
    · apply ContinuousLinearMap.ext
      intro h
      simp [carmonRhoFDeriv, hi, p]
      ring

def carmonRhoSqFDeriv {T : Nat} (x : EVec T) (i : Fin T) :
    EVec T →L[ℝ] ℝ :=
  if hi : i.1 = 0 then 0 else
    carmonRhoSqPrevDeriv x i • evecProj ⟨i.1 - 1, by omega⟩

theorem hasCarmonFDerivAt_carmonRhoSq {T : Nat} (x : EVec T) (i : Fin T) :
    HasCarmonFDerivAt (fun w : EVec T ↦ carmonRhoSq w i)
      (carmonRhoSqFDeriv x i) x := by
  letI : AddCommGroup (EVec T) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec T) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec T) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasCarmonFDerivAt
  by_cases hi : i.1 = 0
  · have hconst : HasFDerivAt (fun _ : EVec T ↦ (1 : ℝ)) 0 x :=
      hasFDerivAt_const (𝕜 := ℝ) (1 : ℝ) x
    simpa [carmonRhoSq, carmonRhoSqFDeriv, hi] using hconst
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    have hp : HasFDerivAt (fun w : EVec T ↦ w p) (evecProj p) x :=
      (evecProj p).hasFDerivAt
    have hpos := (differentiable_carmonPsi (x p)).hasDerivAt
    rw [deriv_carmonPsi] at hpos
    have hneg := (differentiable_carmonPsi (-x p)).hasDerivAt
    rw [deriv_carmonPsi] at hneg
    have hposComp := hpos.hasFDerivAt.comp x hp
    have hnegComp := hneg.hasFDerivAt.comp x hp.neg
    have hsum := hposComp.add hnegComp
    convert hsum using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    · funext w
      simp [carmonRhoSq, hi, p]
    · ext h
      simp [carmonRhoSqFDeriv, carmonRhoSqPrevDeriv, hi, p]
      ring

def carmonOuterAFDeriv {T : Nat} (x : EVec T) (i : Fin T) :
    EVec T →L[ℝ] ℝ :=
  carmonPhiCap • carmonRhoSqFDeriv x i + carmonTermFDeriv x i

theorem hasCarmonFDerivAt_carmonOuterA {T : Nat} (x : EVec T) (i : Fin T) :
    HasCarmonFDerivAt (fun w : EVec T ↦ carmonOuterA w i)
      (carmonOuterAFDeriv x i) x := by
  letI : AddCommGroup (EVec T) := Pi.normedAddCommGroup.toAddCommGroup
  letI : Module ℝ (EVec T) := Pi.normedSpace.toModule
  letI : TopologicalSpace (EVec T) :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  letI : AddCommGroup ℝ := Real.normedCommRing.toAddCommGroup
  letI : Module ℝ ℝ := (NormedAlgebra.toNormedSpace ℝ).toModule
  letI : TopologicalSpace ℝ :=
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
  unfold HasCarmonFDerivAt carmonOuterA carmonOuterAFDeriv
  have hr : HasFDerivAt (fun w : EVec T ↦ carmonRhoSq w i)
      (carmonRhoSqFDeriv x i) x := by
    simpa only [HasCarmonFDerivAt] using hasCarmonFDerivAt_carmonRhoSq x i
  have ht : HasFDerivAt (fun w : EVec T ↦ carmonTerm w i)
      (carmonTermFDeriv x i) x := by
    simpa only [HasCarmonFDerivAt] using hasEVecFDerivAt_carmonTerm x i
  exact (hr.const_mul carmonPhiCap).add ht

theorem carmonOuterAFDeriv_apply_eq_gradient {T : Nat}
    (x h : EVec T) (i : Fin T) :
    carmonOuterAFDeriv x i h =
      ∑ j : Fin T, carmonOuterAGradient x i j * h j := by
  unfold carmonOuterAFDeriv
  rw [add_apply]
  by_cases hi : i.1 = 0
  · simp [carmonRhoSqFDeriv, carmonTermFDeriv, carmonOuterAGradient,
      hi, carmonIncoming]
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    have hpi : p ≠ i := by
      intro hbad
      have := Fin.ext_iff.mp hbad
      simp only [p] at this
      omega
    rw [show (∑ j : Fin T, carmonOuterAGradient x i j * h j) =
        carmonOuterAGradient x i i * h i +
          carmonOuterAGradient x i p * h p by
      calc
        (∑ j : Fin T, carmonOuterAGradient x i j * h j) =
            ∑ j ∈ ({i, p} : Finset (Fin T)),
              carmonOuterAGradient x i j * h j := by
          symm
          apply Finset.sum_subset
          · simp
          · intro j _ hj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            have hji : j ≠ i := fun h => hj (Or.inl h)
            have hjp : j ≠ p := fun h => hj (Or.inr h)
            simp [carmonOuterAGradient, hi, hji, hjp, p]
        _ = carmonOuterAGradient x i i * h i +
            carmonOuterAGradient x i p * h p :=
          Finset.sum_pair hpi.symm]
    simp [carmonRhoSqFDeriv, carmonTermFDeriv_apply,
      carmonOuterAGradient, carmonOuterAPrevCoeff, hi, p, hpi]
    ring

end

end NCPLVerification
