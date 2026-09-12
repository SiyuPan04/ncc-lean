import NCPLVerification.GateCalculus

/-!
# Analytic derivatives of the scalar gates

The piecewise formulas in `GateCalculus` are not merely symbolic: this file
proves that they are the actual derivatives, including at every splice point.
-/

namespace NCPLVerification

noncomputable section

private def sigmaPoly (x : ℝ) : ℝ := 3 * x ^ 2 - 2 * x ^ 3

private theorem hasDerivAt_sigmaPoly (x : ℝ) :
    HasDerivAt sigmaPoly (6 * x - 6 * x ^ 2) x := by
  unfold sigmaPoly
  have h2 := ((hasDerivAt_id x).pow 2).const_mul 3
  have h3 := ((hasDerivAt_id x).pow 3).const_mul 2
  have h := h2.sub h3
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one] at h
  change HasDerivAt (fun y : ℝ ↦ 3 * y ^ 2 - 2 * y ^ 3) _ x at h
  exact h.congr_deriv (by ring)

private theorem sigma_eq_poly {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    sigma x = sigmaPoly x := by
  rcases hx.1.eq_or_lt with hzero | hpos
  · subst x
    norm_num [sigma, sigmaPoly]
  · simp [sigma, sigmaPoly, not_le.mpr hpos, hx.2]

private theorem hasDerivWithinAt_sigma_left_zero :
    HasDerivWithinAt sigma 0 (Set.Iic (0 : ℝ)) 0 := by
  refine (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))).hasDerivWithinAt.congr ?_ ?_
  · intro x hx
    exact sigma_of_nonpos hx
  · exact sigma_zero

private theorem hasDerivWithinAt_sigma_middle (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt sigma (6 * x - 6 * x ^ 2) (Set.Icc (0 : ℝ) 1) x := by
  refine (hasDerivAt_sigmaPoly x).hasDerivWithinAt.congr ?_ ?_
  · intro y hy
    exact sigma_eq_poly hy
  · exact sigma_eq_poly hx

private theorem hasDerivWithinAt_sigma_right_one :
    HasDerivWithinAt sigma 0 (Set.Ici (1 : ℝ)) 1 := by
  refine (hasDerivAt_const (x := (1 : ℝ)) (c := (1 : ℝ))).hasDerivWithinAt.congr ?_ ?_
  · intro x hx
    exact sigma_of_one_le hx
  · exact sigma_one

private theorem hasDerivAt_sigma_zero : HasDerivAt sigma 0 0 := by
  have hm : HasDerivWithinAt sigma 0 (Set.Icc (0 : ℝ) 1) 0 := by
    simpa using hasDerivWithinAt_sigma_middle 0 (by norm_num)
  have hu := hasDerivWithinAt_sigma_left_zero.union hm
  have hset : Set.Iic (0 : ℝ) ∪ Set.Icc 0 1 = Set.Iic 1 := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
    constructor <;> intro h
    · rcases h with h | h <;> linarith
    · by_cases hx : x ≤ 0
      · exact Or.inl hx
      · exact Or.inr ⟨le_of_not_ge hx, h⟩
  rw [hset] at hu
  exact hu.hasDerivAt (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1))

private theorem hasDerivAt_sigma_one : HasDerivAt sigma 0 1 := by
  have hm : HasDerivWithinAt sigma 0 (Set.Icc (0 : ℝ) 1) 1 := by
    simpa using hasDerivWithinAt_sigma_middle 1 (by norm_num)
  have hu := hm.union hasDerivWithinAt_sigma_right_one
  have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Ici 1 = Set.Ici 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor <;> intro h
    · rcases h with h | h <;> linarith
    · by_cases hx : x ≤ 1
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (le_of_not_ge hx)
  rw [hset] at hu
  exact hu.hasDerivAt (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1))

/-- `sigmaDeriv` is the actual derivative of `sigma` at every real point. -/
theorem hasDerivAt_sigma (s : ℝ) : HasDerivAt sigma (sigmaDeriv s) s := by
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · have hc : HasDerivWithinAt sigma 0 (Set.Iic (0 : ℝ)) s := by
      refine (hasDerivAt_const (x := s) (c := (0 : ℝ))).hasDerivWithinAt.congr ?_ ?_
      · intro x hx
        exact sigma_of_nonpos hx
      · exact sigma_of_nonpos hs.le
    have hd := hc.hasDerivAt (Iic_mem_nhds hs)
    simpa [sigmaDeriv, hs.le] using hd
  · simpa using hasDerivAt_sigma_zero
  · rcases lt_trichotomy s 1 with hs1 | rfl | hs1
    · have hm := hasDerivWithinAt_sigma_middle s ⟨hs.le, hs1.le⟩
      have hmem : Set.Icc (0 : ℝ) 1 ∈ nhds s := Icc_mem_nhds hs hs1
      have hd := hm.hasDerivAt hmem
      simpa [sigmaDeriv, not_le.mpr hs, hs1.le] using hd
    · simpa using hasDerivAt_sigma_one
    · have hc : HasDerivWithinAt sigma 0 (Set.Ici (1 : ℝ)) s := by
        refine (hasDerivAt_const (x := s) (c := (1 : ℝ))).hasDerivWithinAt.congr ?_ ?_
        · intro x hx
          exact sigma_of_one_le hx
        · exact sigma_of_one_le hs1.le
      have hd := hc.hasDerivAt (Ici_mem_nhds hs1)
      simpa [sigmaDeriv, not_le.mpr hs, not_le.mpr hs1] using hd

theorem differentiable_sigma : Differentiable ℝ sigma :=
  fun s ↦ (hasDerivAt_sigma s).differentiableAt

theorem deriv_sigma (s : ℝ) : deriv sigma s = sigmaDeriv s :=
  (hasDerivAt_sigma s).deriv

private def betaNegPoly (x : ℝ) : ℝ :=
  -1 + 2 * (x + 1) ^ 2 - (x + 1) ^ 3

private def betaPosPoly (x : ℝ) : ℝ :=
  1 + (x - 1) + (x - 1) ^ 2 - (x - 1) ^ 3

private theorem hasDerivAt_betaNegPoly (x : ℝ) :
    HasDerivAt betaNegPoly (4 * (x + 1) - 3 * (x + 1) ^ 2) x := by
  unfold betaNegPoly
  have hu := (hasDerivAt_id x).add_const 1
  have h2 := (hu.pow 2).const_mul 2
  have h3 := hu.pow 3
  have h := (hasDerivAt_const x (-1 : ℝ)).add h2 |>.sub h3
  simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    mul_one] at h
  change HasDerivAt (fun y : ℝ ↦ -1 + 2 * (y + 1) ^ 2 - (y + 1) ^ 3) _ x at h
  exact h.congr_deriv (by ring)

private theorem hasDerivAt_betaPosPoly (x : ℝ) :
    HasDerivAt betaPosPoly (1 + 2 * (x - 1) - 3 * (x - 1) ^ 2) x := by
  unfold betaPosPoly
  have hu := (hasDerivAt_id x).sub_const 1
  have h2 := hu.pow 2
  have h3 := hu.pow 3
  have h := (hasDerivAt_const x (1 : ℝ)).add hu |>.add h2 |>.sub h3
  simp only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    mul_one] at h
  change HasDerivAt
    (fun y : ℝ ↦ 1 + (y - 1) + (y - 1) ^ 2 - (y - 1) ^ 3) _ x at h
  exact h.congr_deriv (by ring)

private theorem beta_eq_negPoly {x : ℝ} (hx : x ∈ Set.Icc (-1 : ℝ) 0) :
    beta x = betaNegPoly x := by
  rcases hx.1.eq_or_lt with h | h
  · subst x
    norm_num [beta, betaNegPoly]
  · simp [beta, betaNegPoly, not_le.mpr h, hx.2]

private theorem beta_eq_posPoly {x : ℝ} (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    beta x = betaPosPoly x := by
  rcases hx.1.eq_or_lt with h | h
  · subst x
    norm_num [beta, betaPosPoly]
  · simp [beta, betaPosPoly, not_le.mpr (by linarith : -1 < x),
      not_le.mpr (by linarith : 0 < x), not_le.mpr h, hx.2]

private theorem hasDerivWithinAt_beta_left :
    HasDerivWithinAt beta 0 (Set.Iic (-1 : ℝ)) (-1) := by
  refine (hasDerivAt_const (x := (-1 : ℝ)) (c := (-1 : ℝ))).hasDerivWithinAt.congr ?_ ?_
  · intro x hx
    have hx' : x ≤ (-1 : ℝ) := hx
    simp [beta, hx']
  · norm_num [beta]

private theorem hasDerivWithinAt_beta_neg (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 0) :
    HasDerivWithinAt beta (4 * (x + 1) - 3 * (x + 1) ^ 2)
      (Set.Icc (-1 : ℝ) 0) x := by
  refine (hasDerivAt_betaNegPoly x).hasDerivWithinAt.congr ?_ ?_
  · intro y hy
    exact beta_eq_negPoly hy
  · exact beta_eq_negPoly hx

private theorem hasDerivWithinAt_beta_mid (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt beta 1 (Set.Icc (0 : ℝ) 1) x := by
  refine (hasDerivAt_id x).hasDerivWithinAt.congr ?_ ?_
  · intro y hy
    exact beta_eq_self hy.1 hy.2
  · exact beta_eq_self hx.1 hx.2

private theorem hasDerivWithinAt_beta_pos (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    HasDerivWithinAt beta (1 + 2 * (x - 1) - 3 * (x - 1) ^ 2)
      (Set.Icc (1 : ℝ) 2) x := by
  refine (hasDerivAt_betaPosPoly x).hasDerivWithinAt.congr ?_ ?_
  · intro y hy
    exact beta_eq_posPoly hy
  · exact beta_eq_posPoly hx

private theorem hasDerivWithinAt_beta_right :
    HasDerivWithinAt beta 0 (Set.Ici (2 : ℝ)) 2 := by
  refine (hasDerivAt_const (x := (2 : ℝ)) (c := (2 : ℝ))).hasDerivWithinAt.congr ?_ ?_
  · intro x hx
    exact beta_of_two_le hx
  · norm_num [beta]

private theorem hasDerivAt_beta_neg_one : HasDerivAt beta 0 (-1) := by
  have hr : HasDerivWithinAt beta 0 (Set.Icc (-1 : ℝ) 0) (-1) := by
    simpa using hasDerivWithinAt_beta_neg (-1) (by norm_num)
  have hu := hasDerivWithinAt_beta_left.union hr
  have hset : Set.Iic (-1 : ℝ) ∪ Set.Icc (-1) 0 = Set.Iic 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Iic, Set.mem_Icc]
    constructor <;> intro h
    · rcases h with h | h <;> linarith
    · by_cases hx : x ≤ -1
      · exact Or.inl hx
      · exact Or.inr ⟨le_of_not_ge hx, h⟩
  rw [hset] at hu
  exact hu.hasDerivAt (Iic_mem_nhds (by norm_num : (-1 : ℝ) < 0))

private theorem hasDerivAt_beta_zero : HasDerivAt beta 1 0 := by
  have hl : HasDerivWithinAt beta 1 (Set.Icc (-1 : ℝ) 0) 0 := by
    convert hasDerivWithinAt_beta_neg 0 (by norm_num) using 1 <;> norm_num
  have hr := hasDerivWithinAt_beta_mid 0 (by norm_num)
  have hu := hl.union hr
  have hset : Set.Icc (-1 : ℝ) 0 ∪ Set.Icc 0 1 = Set.Icc (-1) 1 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc]
    constructor <;> intro h
    · rcases h with h | h <;> constructor <;> linarith
    · by_cases hx : x ≤ 0
      · exact Or.inl ⟨h.1, hx⟩
      · exact Or.inr ⟨le_of_not_ge hx, h.2⟩
  rw [hset] at hu
  exact hu.hasDerivAt (Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1))

private theorem hasDerivAt_beta_one : HasDerivAt beta 1 1 := by
  have hl := hasDerivWithinAt_beta_mid 1 (by norm_num)
  have hr : HasDerivWithinAt beta 1 (Set.Icc (1 : ℝ) 2) 1 := by
    simpa using hasDerivWithinAt_beta_pos 1 (by norm_num)
  have hu := hl.union hr
  have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Icc 1 2 = Set.Icc 0 2 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc]
    constructor <;> intro h
    · rcases h with h | h <;> constructor <;> linarith
    · by_cases hx : x ≤ 1
      · exact Or.inl ⟨h.1, hx⟩
      · exact Or.inr ⟨le_of_not_ge hx, h.2⟩
  rw [hset] at hu
  exact hu.hasDerivAt (Icc_mem_nhds (by norm_num : (0 : ℝ) < 1)
    (by norm_num : (1 : ℝ) < 2))

private theorem hasDerivAt_beta_two : HasDerivAt beta 0 2 := by
  have hl : HasDerivWithinAt beta 0 (Set.Icc (1 : ℝ) 2) 2 := by
    convert hasDerivWithinAt_beta_pos 2 (by norm_num) using 1 <;> norm_num
  have hu := hl.union hasDerivWithinAt_beta_right
  have hset : Set.Icc (1 : ℝ) 2 ∪ Set.Ici 2 = Set.Ici 1 := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor <;> intro h
    · rcases h with h | h <;> linarith
    · by_cases hx : x ≤ 2
      · exact Or.inl ⟨h, hx⟩
      · exact Or.inr (le_of_not_ge hx)
  rw [hset] at hu
  exact hu.hasDerivAt (Ici_mem_nhds (by norm_num : (1 : ℝ) < 2))

/-- `betaDeriv` is the actual derivative of `beta` at every real point. -/
theorem hasDerivAt_beta (t : ℝ) : HasDerivAt beta (betaDeriv t) t := by
  rcases lt_trichotomy t (-1) with ht | rfl | ht
  · have hc : HasDerivWithinAt beta 0 (Set.Iic (-1 : ℝ)) t := by
      refine (hasDerivAt_const (x := t) (c := (-1 : ℝ))).hasDerivWithinAt.congr ?_ ?_
      · intro x hx
        have hx' : x ≤ (-1 : ℝ) := hx
        simp [beta, hx']
      · simp [beta, ht.le]
    have hd := hc.hasDerivAt (Iic_mem_nhds ht)
    simpa [betaDeriv, ht.le] using hd
  · convert hasDerivAt_beta_neg_one using 1 <;> norm_num [betaDeriv]
  · rcases lt_trichotomy t 0 with ht0 | rfl | ht0
    · have hm := hasDerivWithinAt_beta_neg t ⟨ht.le, ht0.le⟩
      have hd := hm.hasDerivAt (Icc_mem_nhds ht ht0)
      simpa [betaDeriv, not_le.mpr ht, ht0.le] using hd
    · convert hasDerivAt_beta_zero using 1 <;> norm_num [betaDeriv]
    · rcases lt_trichotomy t 1 with ht1 | rfl | ht1
      · have hm := hasDerivWithinAt_beta_mid t ⟨ht0.le, ht1.le⟩
        have hd := hm.hasDerivAt (Icc_mem_nhds ht0 ht1)
        have hm1 : ¬t ≤ (-1 : ℝ) := by linarith
        have h0 : ¬t ≤ 0 := by linarith
        simpa [betaDeriv, hm1, h0, ht1.le] using hd
      · convert hasDerivAt_beta_one using 1 <;> norm_num [betaDeriv]
      · rcases lt_trichotomy t 2 with ht2 | rfl | ht2
        · have hm := hasDerivWithinAt_beta_pos t ⟨ht1.le, ht2.le⟩
          have hd := hm.hasDerivAt (Icc_mem_nhds ht1 ht2)
          have hm1 : ¬t ≤ (-1 : ℝ) := by linarith
          have h0 : ¬t ≤ 0 := by linarith
          have h1 : ¬t ≤ 1 := by linarith
          simpa [betaDeriv, hm1, h0, h1, ht2.le] using hd
        · convert hasDerivAt_beta_two using 1 <;> norm_num [betaDeriv]
        · have hc : HasDerivWithinAt beta 0 (Set.Ici (2 : ℝ)) t := by
            refine (hasDerivAt_const (x := t) (c := (2 : ℝ))).hasDerivWithinAt.congr ?_ ?_
            · intro x hx
              exact beta_of_two_le hx
            · exact beta_of_two_le ht2.le
          have hd := hc.hasDerivAt (Ici_mem_nhds ht2)
          have hm1 : ¬t ≤ (-1 : ℝ) := by linarith
          have h0 : ¬t ≤ 0 := by linarith
          have h1 : ¬t ≤ 1 := by linarith
          have h2 : ¬t ≤ 2 := by linarith
          simpa [betaDeriv, hm1, h0, h1, h2] using hd

theorem differentiable_beta : Differentiable ℝ beta :=
  fun t ↦ (hasDerivAt_beta t).differentiableAt

theorem deriv_beta (t : ℝ) : deriv beta t = betaDeriv t :=
  (hasDerivAt_beta t).deriv

/-- Squaring removes the kink of the positive part. -/
theorem hasDerivAt_posPart_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ posPart y ^ 2) (2 * posPart x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hc : HasDerivWithinAt (fun y : ℝ ↦ posPart y ^ 2) 0
        (Set.Iic (0 : ℝ)) x := by
      refine (hasDerivAt_const (x := x) (c := (0 : ℝ))).hasDerivWithinAt.congr ?_ ?_
      · intro y hy
        have hy' : y ≤ 0 := hy
        simp [posPart, hy']
      · simp [posPart, hx.le]
    have hd := hc.hasDerivAt (Iic_mem_nhds hx)
    simpa [posPart, hx.le] using hd
  · have hl : HasDerivWithinAt (fun y : ℝ ↦ posPart y ^ 2) 0
        (Set.Iic (0 : ℝ)) 0 := by
      refine (hasDerivAt_const (x := (0 : ℝ)) (c := (0 : ℝ))).hasDerivWithinAt.congr ?_ ?_
      · intro y hy
        have hy' : y ≤ 0 := hy
        simp [posPart, hy']
      · simp [posPart]
    have hr : HasDerivWithinAt (fun y : ℝ ↦ posPart y ^ 2) 0
        (Set.Ici (0 : ℝ)) 0 := by
      have hp : HasDerivWithinAt (fun y : ℝ ↦ y ^ 2) 0
          (Set.Ici (0 : ℝ)) 0 := by
        simpa using (hasDerivWithinAt_pow (s := Set.Ici (0 : ℝ)) 2 (0 : ℝ))
      refine hp.congr ?_ ?_
      · intro y hy
        have hy' : 0 ≤ y := hy
        rw [posPart, max_eq_left hy']
      · simp [posPart]
    have hu := hl.union hr
    have hset : Set.Iic (0 : ℝ) ∪ Set.Ici 0 = Set.univ := by
      ext y
      simp only [Set.mem_union, Set.mem_Iic, Set.mem_Ici, Set.mem_univ, iff_true]
      exact le_total y 0
    rw [hset, hasDerivWithinAt_univ] at hu
    simpa [posPart] using hu
  · have hp : HasDerivWithinAt (fun y : ℝ ↦ posPart y ^ 2) (2 * x)
        (Set.Ici (0 : ℝ)) x := by
      have hs : HasDerivWithinAt (fun y : ℝ ↦ y ^ 2) (2 * x)
          (Set.Ici (0 : ℝ)) x := by
        simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
          (hasDerivWithinAt_pow (s := Set.Ici (0 : ℝ)) 2 x)
      refine hs.congr ?_ ?_
      · intro y hy
        have hy' : 0 ≤ y := hy
        rw [posPart, max_eq_left hy']
      · simp [posPart, hx.le]
    have hd := hp.hasDerivAt (Ici_mem_nhds hx)
    simpa [posPart, hx.le] using hd

/-- Derivative of the squared lower wall. -/
theorem hasDerivAt_negPart_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ negPart y ^ 2) (-2 * negPart x) x := by
  have ho := hasDerivAt_posPart_sq (-x)
  have hi := (hasDerivAt_id x).neg
  have hc := ho.comp x hi
  have hc' : HasDerivAt ((fun y : ℝ ↦ posPart y ^ 2) ∘ fun y ↦ -y)
      (-2 * negPart x) x := by
    exact hc.congr_deriv (by simp [negPart, posPart])
  refine hc'.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_)
  simp [negPart, posPart]

end

end NCPLVerification
