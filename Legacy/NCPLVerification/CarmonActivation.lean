import NCPLVerification.CarmonSmoothness

/-!
# Smooth square-root activation gate

The article uses `rho_i = sqrt (psi(t) + psi(-t))`.  The two summands have
disjoint supports.  We expose the equivalent sum of two flat half-exponential
gates, which makes its genuine first and second derivatives transparent.
-/

namespace NCPLVerification

noncomputable section

def expNegHalfInvSqGlue (x : ℝ) : ℝ :=
  expNegInvSqGlue (Real.sqrt 2 * x)

def expNegHalfInvSqGlueDeriv (x : ℝ) : ℝ :=
  Real.sqrt 2 * expNegInvSqGlueDeriv (Real.sqrt 2 * x)

def expNegHalfInvSqGlueSecond (x : ℝ) : ℝ :=
  2 * expNegInvSqGlueSecond (Real.sqrt 2 * x)

theorem sqrt_two_pos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)

theorem sqrt_two_sq : Real.sqrt (2 : ℝ) ^ 2 = 2 := by norm_num

theorem hasDerivAt_expNegHalfInvSqGlue (x : ℝ) :
    HasDerivAt expNegHalfInvSqGlue (expNegHalfInvSqGlueDeriv x) x := by
  unfold expNegHalfInvSqGlue expNegHalfInvSqGlueDeriv
  have harg : HasDerivAt (fun t : ℝ ↦ Real.sqrt 2 * t) (Real.sqrt 2) x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (Real.sqrt 2)
  have h := (hasDerivAt_expNegInvSqGlue (Real.sqrt 2 * x)).comp x harg
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    rfl
  · ring

theorem hasDerivAt_expNegHalfInvSqGlueDeriv (x : ℝ) :
    HasDerivAt expNegHalfInvSqGlueDeriv (expNegHalfInvSqGlueSecond x) x := by
  unfold expNegHalfInvSqGlueDeriv expNegHalfInvSqGlueSecond
  have harg : HasDerivAt (fun t : ℝ ↦ Real.sqrt 2 * t) (Real.sqrt 2) x :=
    by simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul (Real.sqrt 2)
  have hcomp := (hasDerivAt_expNegInvSqGlueDeriv (Real.sqrt 2 * x)).comp x harg
  have h := hcomp.const_mul (Real.sqrt 2)
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext t
    rfl
  · nth_rewrite 1 [← sqrt_two_sq]
    ring

theorem expNegHalfInvSqGlue_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    expNegHalfInvSqGlue x = 0 := by
  unfold expNegHalfInvSqGlue
  apply expNegInvSqGlue_of_nonpos
  exact mul_nonpos_of_nonneg_of_nonpos (Real.sqrt_nonneg _) hx

theorem expNegHalfInvSqGlue_nonneg (x : ℝ) :
    0 ≤ expNegHalfInvSqGlue x := expNegInvSqGlue_nonneg _

theorem expNegHalfInvSqGlue_sq (x : ℝ) :
    expNegHalfInvSqGlue x ^ 2 = expNegInvSqGlue x := by
  by_cases hx : x ≤ 0
  · simp [expNegHalfInvSqGlue_of_nonpos hx, expNegInvSqGlue_of_nonpos hx]
  · have hxpos : 0 < x := lt_of_not_ge hx
    have hsx : 0 < Real.sqrt 2 * x := mul_pos sqrt_two_pos hxpos
    unfold expNegHalfInvSqGlue expNegInvSqGlue
    rw [if_neg hsx.not_ge, if_neg hx]
    rw [pow_two, ← Real.exp_add]
    congr 1
    field_simp [sqrt_two_pos.ne', hxpos.ne']
    nlinarith [sqrt_two_sq]

def carmonSqrtPsi (t : ℝ) : ℝ :=
  Real.sqrt (Real.exp 1) * expNegHalfInvSqGlue (2 * t - 1)

def carmonSqrtPsiDeriv (t : ℝ) : ℝ :=
  2 * Real.sqrt (Real.exp 1) * expNegHalfInvSqGlueDeriv (2 * t - 1)

def carmonSqrtPsiSecond (t : ℝ) : ℝ :=
  4 * Real.sqrt (Real.exp 1) * expNegHalfInvSqGlueSecond (2 * t - 1)

theorem carmonSqrtPsi_nonneg (t : ℝ) : 0 ≤ carmonSqrtPsi t :=
  mul_nonneg (Real.sqrt_nonneg _) (expNegHalfInvSqGlue_nonneg _)

theorem carmonSqrtPsi_of_le_half {t : ℝ} (ht : t ≤ 1 / 2) :
    carmonSqrtPsi t = 0 := by
  unfold carmonSqrtPsi
  rw [expNegHalfInvSqGlue_of_nonpos (by linarith)]
  ring

@[simp] theorem carmonSqrtPsi_zero : carmonSqrtPsi 0 = 0 := by
  apply carmonSqrtPsi_of_le_half
  norm_num

theorem carmonSqrtPsi_sq (t : ℝ) : carmonSqrtPsi t ^ 2 = carmonPsi t := by
  unfold carmonSqrtPsi carmonPsi
  rw [mul_pow, Real.sq_sqrt (Real.exp_pos 1).le,
    expNegHalfInvSqGlue_sq]

theorem carmonSqrtPsi_mul_neg (t : ℝ) :
    carmonSqrtPsi t * carmonSqrtPsi (-t) = 0 := by
  by_cases ht : t ≤ 1 / 2
  · rw [carmonSqrtPsi_of_le_half ht]
    ring
  · have hneg : -t ≤ 1 / 2 := by linarith
    rw [carmonSqrtPsi_of_le_half hneg]
    ring

theorem hasDerivAt_carmonSqrtPsi (t : ℝ) :
    HasDerivAt carmonSqrtPsi (carmonSqrtPsiDeriv t) t := by
  unfold carmonSqrtPsi carmonSqrtPsiDeriv
  have harg : HasDerivAt (fun s : ℝ ↦ 2 * s - 1) 2 t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul 2 |>.sub_const 1)
  have hcomp := (hasDerivAt_expNegHalfInvSqGlue (2 * t - 1)).comp t harg
  have h := hcomp.const_mul (Real.sqrt (Real.exp 1))
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · ring

theorem hasDerivAt_carmonSqrtPsiDeriv (t : ℝ) :
    HasDerivAt carmonSqrtPsiDeriv (carmonSqrtPsiSecond t) t := by
  unfold carmonSqrtPsiDeriv carmonSqrtPsiSecond
  have harg : HasDerivAt (fun s : ℝ ↦ 2 * s - 1) 2 t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul 2 |>.sub_const 1)
  have hcomp := (hasDerivAt_expNegHalfInvSqGlueDeriv (2 * t - 1)).comp t harg
  have h := hcomp.const_mul (2 * Real.sqrt (Real.exp 1))
  convert h using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · ring

theorem sqrt_two_le_two : Real.sqrt (2 : ℝ) ≤ 2 := by
  nlinarith [sqrt_two_sq, Real.sqrt_nonneg (2 : ℝ)]

theorem abs_expNegHalfInvSqGlueDeriv_le_eight (x : ℝ) :
    |expNegHalfInvSqGlueDeriv x| ≤ 8 := by
  unfold expNegHalfInvSqGlueDeriv
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := abs_expNegInvSqGlueDeriv_le_four (Real.sqrt 2 * x)
  nlinarith [sqrt_two_le_two, Real.sqrt_nonneg (2 : ℝ)]

theorem abs_expNegHalfInvSqGlueSecond_le_seventyTwo (x : ℝ) :
    |expNegHalfInvSqGlueSecond x| ≤ 72 := by
  unfold expNegHalfInvSqGlueSecond
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  nlinarith [abs_expNegInvSqGlueSecond_le_thirtySix (Real.sqrt 2 * x)]

theorem abs_carmonSqrtPsiDeriv_le_thirtyTwo (t : ℝ) :
    |carmonSqrtPsiDeriv t| ≤ 32 := by
  unfold carmonSqrtPsiDeriv
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := abs_expNegHalfInvSqGlueDeriv_le_eight (2 * t - 1)
  nlinarith [sqrt_exp_one_le_two, Real.sqrt_nonneg (Real.exp 1)]

theorem abs_carmonSqrtPsiSecond_le_fiveSeventySix (t : ℝ) :
    |carmonSqrtPsiSecond t| ≤ 576 := by
  unfold carmonSqrtPsiSecond
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := abs_expNegHalfInvSqGlueSecond_le_seventyTwo (2 * t - 1)
  nlinarith [sqrt_exp_one_le_two, Real.sqrt_nonneg (Real.exp 1)]

theorem carmonPsiDeriv_eq_sqrt (t : ℝ) :
    carmonPsiDeriv t = 2 * carmonSqrtPsi t * carmonSqrtPsiDeriv t := by
  have hleft := (differentiable_carmonPsi t).hasDerivAt
  rw [deriv_carmonPsi] at hleft
  have hright := (hasDerivAt_carmonSqrtPsi t).pow 2
  have hright' : HasDerivAt carmonPsi
      (2 * carmonSqrtPsi t * carmonSqrtPsiDeriv t) t := by
    have h := hright.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s ↦ (carmonSqrtPsi_sq s).symm)
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using h
  exact HasDerivAt.unique hleft hright'

theorem abs_carmonPsiDeriv_le_sqrt (t : ℝ) :
    |carmonPsiDeriv t| ≤ 64 * carmonSqrtPsi t := by
  rw [carmonPsiDeriv_eq_sqrt, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (carmonSqrtPsi_nonneg t)]
  have h := abs_carmonSqrtPsiDeriv_le_thirtyTwo t
  nlinarith [carmonSqrtPsi_nonneg t]

def carmonRhoProfile (t : ℝ) : ℝ :=
  carmonSqrtPsi t + carmonSqrtPsi (-t)

def carmonRhoProfileDeriv (t : ℝ) : ℝ :=
  carmonSqrtPsiDeriv t - carmonSqrtPsiDeriv (-t)

def carmonRhoProfileSecond (t : ℝ) : ℝ :=
  carmonSqrtPsiSecond t + carmonSqrtPsiSecond (-t)

theorem hasDerivAt_carmonRhoProfile (t : ℝ) :
    HasDerivAt carmonRhoProfile (carmonRhoProfileDeriv t) t := by
  unfold carmonRhoProfile carmonRhoProfileDeriv
  have hp := hasDerivAt_carmonSqrtPsi t
  have hn := (hasDerivAt_carmonSqrtPsi (-t)).comp t (hasDerivAt_id t).neg
  convert hp.add hn using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · ring

theorem hasDerivAt_carmonRhoProfileDeriv (t : ℝ) :
    HasDerivAt carmonRhoProfileDeriv (carmonRhoProfileSecond t) t := by
  unfold carmonRhoProfileDeriv carmonRhoProfileSecond
  have hp := hasDerivAt_carmonSqrtPsiDeriv t
  have hn := (hasDerivAt_carmonSqrtPsiDeriv (-t)).comp t (hasDerivAt_id t).neg
  convert hp.sub hn using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext s
    rfl
  · ring

theorem carmonRhoProfile_nonneg (t : ℝ) : 0 ≤ carmonRhoProfile t :=
  add_nonneg (carmonSqrtPsi_nonneg t) (carmonSqrtPsi_nonneg (-t))

theorem carmonRhoProfile_le_two (t : ℝ) : carmonRhoProfile t ≤ 2 := by
  have hsquares : carmonRhoProfile t ^ 2 =
      carmonPsi t + carmonPsi (-t) := by
    unfold carmonRhoProfile
    rw [add_sq, carmonSqrtPsi_sq, carmonSqrtPsi_sq]
    have hz := carmonSqrtPsi_mul_neg t
    nlinarith
  have hpsi : carmonPsi t + carmonPsi (-t) ≤ 3 := by
    by_cases ht : t ≤ 1 / 2
    · rw [carmonPsi_of_le_half ht]
      simpa [abs_of_nonneg (carmonPsi_nonneg (-t))] using
        abs_carmonPsi_le_three (-t)
    · have hneg : -t ≤ 1 / 2 := by linarith
      rw [carmonPsi_of_le_half hneg]
      simpa [abs_of_nonneg (carmonPsi_nonneg t)] using
        abs_carmonPsi_le_three t
  nlinarith [carmonRhoProfile_nonneg t]

theorem abs_carmonRhoProfileDeriv_le_sixtyFour (t : ℝ) :
    |carmonRhoProfileDeriv t| ≤ 64 := by
  unfold carmonRhoProfileDeriv
  exact (abs_sub _ _).trans (by
    nlinarith [abs_carmonSqrtPsiDeriv_le_thirtyTwo t,
      abs_carmonSqrtPsiDeriv_le_thirtyTwo (-t)])

theorem abs_carmonRhoProfileSecond_le_elevenFiftyTwo (t : ℝ) :
    |carmonRhoProfileSecond t| ≤ 1152 := by
  unfold carmonRhoProfileSecond
  exact (abs_add_le _ _).trans (by
    nlinarith [abs_carmonSqrtPsiSecond_le_fiveSeventySix t,
      abs_carmonSqrtPsiSecond_le_fiveSeventySix (-t)])

def carmonRhoExplicit {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  if hi : i.1 = 0 then 1 else
    carmonSqrtPsi (x ⟨i.1 - 1, by omega⟩) +
      carmonSqrtPsi (-x ⟨i.1 - 1, by omega⟩)

theorem carmonRhoExplicit_nonneg {T : Nat} (x : EVec T) (i : Fin T) :
    0 ≤ carmonRhoExplicit x i := by
  unfold carmonRhoExplicit
  split
  · norm_num
  · exact add_nonneg (carmonSqrtPsi_nonneg _) (carmonSqrtPsi_nonneg _)

theorem carmonRhoExplicit_sq {T : Nat} (x : EVec T) (i : Fin T) :
    carmonRhoExplicit x i ^ 2 = carmonRhoSq x i := by
  by_cases hi : i.1 = 0
  · simp [carmonRhoExplicit, carmonRhoSq, hi]
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    rw [carmonRhoExplicit, dif_neg hi, carmonRhoSq, dif_neg hi]
    rw [add_sq, carmonSqrtPsi_sq, carmonSqrtPsi_sq]
    have hz := carmonSqrtPsi_mul_neg (x ⟨i.1 - 1, by omega⟩)
    nlinarith

theorem carmonRho_eq_explicit {T : Nat} (x : EVec T) (i : Fin T) :
    carmonRho x i = carmonRhoExplicit x i := by
  have hs1 := carmonRho_sq x i
  have hs2 := carmonRhoExplicit_sq x i
  have h1 := carmonRho_nonneg x i
  have h2 := carmonRhoExplicit_nonneg x i
  nlinarith

def carmonRhoPrevDeriv {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  if hi : i.1 = 0 then 0 else
    carmonSqrtPsiDeriv (x ⟨i.1 - 1, by omega⟩) -
      carmonSqrtPsiDeriv (-x ⟨i.1 - 1, by omega⟩)

def carmonRhoPrevSecond {T : Nat} (x : EVec T) (i : Fin T) : ℝ :=
  if hi : i.1 = 0 then 0 else
    carmonSqrtPsiSecond (x ⟨i.1 - 1, by omega⟩) +
      carmonSqrtPsiSecond (-x ⟨i.1 - 1, by omega⟩)

theorem hasDerivAt_carmonRho_predecessor {T : Nat} (x : EVec T) (i : Fin T) :
    HasDerivAt
      (fun t : ℝ ↦ if hi : i.1 = 0 then 1 else
        carmonRho (Function.update x ⟨i.1 - 1, by omega⟩ t) i)
      (carmonRhoPrevDeriv x i)
      (if hi : i.1 = 0 then 0 else x ⟨i.1 - 1, by omega⟩) := by
  by_cases hi : i.1 = 0
  · simp only [hi, ↓reduceDIte, carmonRhoPrevDeriv]
    simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ)))
  · let p : Fin T := ⟨i.1 - 1, by omega⟩
    simp only [hi, ↓reduceDIte]
    have hp := hasDerivAt_carmonSqrtPsi (x p)
    have hn := (hasDerivAt_carmonSqrtPsi (-x p)).comp (x p) (hasDerivAt_id _).neg
    have hsum := hp.add hn
    have hfun : (fun t : ℝ ↦ carmonRho (Function.update x p t) i) =
        fun t ↦ carmonSqrtPsi t + carmonSqrtPsi (-t) := by
      funext t
      rw [carmonRho_eq_explicit]
      simp [carmonRhoExplicit, hi, p]
    rw [hfun]
    unfold carmonRhoPrevDeriv
    rw [dif_neg hi]
    convert hsum using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      rfl
    · ring

end

end NCPLVerification
