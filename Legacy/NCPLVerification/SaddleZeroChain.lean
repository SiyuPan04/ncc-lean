import NCPLVerification.ScaledHardClass

/-!
# The interleaved saddle zero-chain

Coordinates are ordered blockwise as
`y⁽ⁱ⁾₀, …, y⁽ⁱ⁾_{N-1}, xᵢ`.  The definitions below flatten that order to
`Fin (T * (N + 1))`, exactly matching Definition 1.2 of the article.
-/

namespace NCPLVerification

noncomputable section

def orderedPrimal {T N : Nat} (z : EVec (T * (N + 1))) : EVec T :=
  fun i ↦ z (finProdFinEquiv (i, Fin.last N))

def orderedDual {T N : Nat} (z : EVec (T * (N + 1))) : EVec (T * N) :=
  fun k ↦
    let p := finProdFinEquiv.symm k
    z (finProdFinEquiv (p.1, p.2.castSucc))

def hardOrderedSaddleField (T N : Nat) (lambdaWall eta : ℝ)
    (z : EVec (T * (N + 1))) : EVec (T * (N + 1)) := fun k ↦
  let p := finProdFinEquiv.symm k
  if hdual : p.2.1 < N then
    -hardGradY T N lambdaWall eta (orderedPrimal z) (orderedDual z)
      (finProdFinEquiv (p.1, ⟨p.2.1, hdual⟩))
  else
    hardGradX T N lambdaWall eta (orderedPrimal z) (orderedDual z) p.1

theorem finProdFinEquiv_val {a b : Nat} (i : Fin a) (j : Fin b) :
    (finProdFinEquiv (i, j)).1 = i.1 * b + j.1 := by
  change j.1 + b * i.1 = i.1 * b + j.1
  ac_rfl

theorem hardLocalBlockGradQ_zero_of_terminal_zero {N : Nat} (hN : 0 < N)
    (p q : ℝ) (u : EVec N)
    (hu : u ⟨N - 1, Nat.sub_lt hN (by omega)⟩ = 0) :
    hardLocalBlockGradQ N p q u = 0 := by
  unfold hardLocalBlockGradQ hardTerminalLocalGradQ
  rw [dif_pos hN, hu]
  simp [terminalPlusGradQ, terminalMinusGradQ, terminalConeGradQ,
    sigmaConeValue, sigma_zero]

theorem hardLocalBlockGradP_zero_at_closed {N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) (u : EVec N) (hu : u = 0) :
    hardLocalBlockGradP N eta 0 0 u = 0 := by
  subst u
  unfold hardLocalBlockGradP hardTerminalLocalGradP
    hardResidualLocalGradPSum hardResidualLocalGradP
  rw [dif_pos hN]
  simp [terminalPlusGradP, terminalMinusGradP, terminalConeGradP,
    sigmaConeGradRho, carmonRhoProfile, carmonRhoProfileDeriv,
    residualFirstProfileGradP, residualProfileGradP,
    residualFirstConeGradRho, residualConeGradRho, twoConeGradient]

theorem orderedPrimal_apply {T N : Nat} (z : EVec (T * (N + 1)))
    (i : Fin T) :
    orderedPrimal z i = z (finProdFinEquiv (i, Fin.last N)) := rfl

theorem orderedDual_block_apply {T N : Nat} (z : EVec (T * (N + 1)))
    (i : Fin T) (j : Fin N) :
    dualBlock (orderedDual z) i j =
      z (finProdFinEquiv (i, j.castSucc)) := by
  simp [dualBlock, orderedDual]

theorem hardDualWeightedBlock_ordered_apply {T N : Nat}
    (z : EVec (T * (N + 1))) (i : Fin T) (j : Fin N) :
    hardDualWeightedBlock (orderedPrimal z) (orderedDual z) i j =
      z (finProdFinEquiv (i, j.castSucc)) / Real.sqrt (innerD N j) := by
  simp [hardDualWeightedBlock, toWeightedCoordinates,
    orderedDual_block_apply]

theorem orderedPrimal_eq_zero_of_supported {T N r : Nat}
    {z : EVec (T * (N + 1))} (hz : SupportedBelow r z) (i : Fin T)
    (hi : r ≤ i.1 * (N + 1) + N) :
    orderedPrimal z i = 0 := by
  apply hz
  rw [finProdFinEquiv_val]
  simpa using hi

theorem orderedDualBlock_eq_zero_of_supported {T N r : Nat}
    {z : EVec (T * (N + 1))} (hz : SupportedBelow r z)
    (i : Fin T) (j : Fin N) (hij : r ≤ i.1 * (N + 1) + j.1) :
    dualBlock (orderedDual z) i j = 0 := by
  rw [orderedDual_block_apply]
  apply hz
  rw [finProdFinEquiv_val]
  exact hij

theorem hardDualWeightedBlock_eq_zero_of_supported {T N r : Nat}
    {z : EVec (T * (N + 1))} (hz : SupportedBelow r z)
    (i : Fin T) (hblock : ∀ j : Fin N, r ≤ i.1 * (N + 1) + j.1) :
    hardDualWeightedBlock (orderedPrimal z) (orderedDual z) i = 0 := by
  funext j
  rw [hardDualWeightedBlock_ordered_apply,
    hz (finProdFinEquiv (i, j.castSucc))]
  · simp
  · rw [finProdFinEquiv_val]
    exact hblock j

theorem carmonRho_ordered_eq_zero_of_prev_zero {T N : Nat}
    (z : EVec (T * (N + 1))) (i : Fin T) (hi : i.1 ≠ 0)
    (hprev : orderedPrimal z ⟨i.1 - 1, by omega⟩ = 0) :
    carmonRho (orderedPrimal z) i = 0 := by
  rw [carmonRho_eq_blockProfile]
  simp [carmonBlockPrev, hi, hprev, carmonRhoProfile,
    carmonSqrtPsi_zero]

theorem hardBlockGradY_ordered_zero {T N r : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) {z : EVec (T * (N + 1))}
    (hz : SupportedBelow r z) (i : Fin T) (j : Fin N)
    (hreveal : r + 1 ≤ i.1 * (N + 1) + j.1) :
    hardBlockGradY T N lambdaWall eta (orderedPrimal z) (orderedDual z) i j = 0 := by
  by_cases hj : j.1 = 0
  · have hi : i.1 ≠ 0 := by
      intro hi0
      rw [hi0, hj] at hreveal
      simp at hreveal
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hi
    have hprevBound : r ≤ (i.1 - 1) * (N + 1) + N := by
      rw [hn] at hreveal ⊢
      simp only [Nat.succ_sub_one, Nat.succ_mul] at hreveal ⊢
      omega
    have hprev : orderedPrimal z ⟨i.1 - 1, by omega⟩ = 0 :=
      orderedPrimal_eq_zero_of_supported hz _ hprevBound
    have hrho : carmonRho (orderedPrimal z) i = 0 :=
      carmonRho_ordered_eq_zero_of_prev_zero z i hi hprev
    have hu : hardDualWeightedBlock (orderedPrimal z) (orderedDual z) i = 0 := by
      apply hardDualWeightedBlock_eq_zero_of_supported hz i
      intro l
      omega
    unfold hardBlockGradY toEuclideanGradient
    rw [hrho, hu]
    simp [perspectiveGradient, negPart]
  · have hjpos : 0 < j.1 := Nat.pos_of_ne_zero hj
    let u := hardDualWeightedBlock (orderedPrimal z) (orderedDual z) i
    have hu : SupportedBelow (j.1 - 1) u := by
      intro l hl
      unfold u
      rw [hardDualWeightedBlock_ordered_apply]
      have hzero : z (finProdFinEquiv (i, l.castSucc)) = 0 := by
        apply hz
        rw [finProdFinEquiv_val]
        simp only [Fin.val_castSucc]
        omega
      rw [hzero]
      simp
    have hchain := perspectiveGradient_is_zeroChain N lambdaWall eta
      (carmonOuterA (orderedPrimal z) i)
      (carmonRho_nonneg (orderedPrimal z) i)
      (j.1 - 1) u hu
    have hcomponent := hchain j (by omega)
    unfold hardBlockGradY toEuclideanGradient
    change perspectiveGradient N lambdaWall eta
        (carmonRho (orderedPrimal z) i)
        (carmonOuterA (orderedPrimal z) i) u j /
        Real.sqrt (innerD N j) = 0
    rw [hcomponent]
    simp

theorem hardGradX_ordered_zero {T N r : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) {z : EVec (T * (N + 1))}
    (hz : SupportedBelow r z) (i : Fin T)
    (hreveal : r + 1 ≤ i.1 * (N + 1) + N) :
    hardGradX T N lambdaWall eta (orderedPrimal z) (orderedDual z) i = 0 := by
  let x := orderedPrimal z
  let y := orderedDual z
  have hlastBound : r ≤ i.1 * (N + 1) + (N - 1) := by
    omega
  let last : Fin N := ⟨N - 1, Nat.sub_lt hN (by omega)⟩
  have hulast : hardDualWeightedBlock x y i last = 0 := by
    unfold x y last
    rw [hardDualWeightedBlock_ordered_apply]
    have hzlast : z (finProdFinEquiv
        (i, (⟨N - 1, Nat.sub_lt hN (by omega)⟩ : Fin N).castSucc)) = 0 := by
      apply hz
      rw [finProdFinEquiv_val]
      simpa using hlastBound
    rw [hzlast]
    simp
  have hQ : hardExplicitQ x y i = 0 := by
    unfold hardExplicitQ
    exact hardLocalBlockGradQ_zero_of_terminal_zero hN _ _ _ hulast
  have hP : hardExplicitP eta x y i = 0 := by
    by_cases hi : i.1 + 1 < T
    · let s : Fin T := ⟨i.1 + 1, hi⟩
      have hxi : x i = 0 := by
        unfold x
        apply orderedPrimal_eq_zero_of_supported hz
        omega
      have hxs : x s = 0 := by
        unfold x s
        apply orderedPrimal_eq_zero_of_supported hz
        simp only
        rw [Nat.add_mul]
        omega
      have hus : hardDualWeightedBlock x y s = 0 := by
        unfold x y s
        apply hardDualWeightedBlock_eq_zero_of_supported hz
        intro j
        rw [Nat.add_mul]
        omega
      unfold hardExplicitP
      rw [dif_pos hi]
      change hardLocalBlockGradP N eta (x i) (x s)
        (hardDualWeightedBlock x y s) = 0
      rw [hxi, hxs, hus]
      exact hardLocalBlockGradP_zero_at_closed hN lambdaWall eta 0 rfl
    · simp [hardExplicitP, hi]
  rw [hardGradX_eq_explicit hN,
    hardExplicitGradX_eq_Q_add_P, hQ, hP, add_zero]

/-- Proposition 7.3: the complete saddle vector field is a zero-chain in the
article's exact interleaved order. -/
theorem hardOrderedSaddleField_is_zeroChain {T N : Nat} (hN : 0 < N)
    (lambdaWall eta : ℝ) :
    IsFirstOrderZeroChain (hardOrderedSaddleField T N lambdaWall eta) := by
  intro r z hz k hk
  rcases hp : finProdFinEquiv.symm k with ⟨i, s⟩
  have hkEq : k = finProdFinEquiv (i, s) := by
    rw [← hp]
    exact (finProdFinEquiv.apply_symm_apply k).symm
  subst k
  have hreveal : r + 1 ≤ i.1 * (N + 1) + s.1 := by
    rw [finProdFinEquiv_val] at hk
    exact hk
  unfold hardOrderedSaddleField
  simp only [finProdFinEquiv.symm_apply_apply]
  by_cases hs : s.1 < N
  · rw [dif_pos hs]
    let j : Fin N := ⟨s.1, hs⟩
    have hj : hardBlockGradY T N lambdaWall eta
        (orderedPrimal z) (orderedDual z) i j = 0 :=
      hardBlockGradY_ordered_zero hN lambdaWall eta hz i j (by
        simpa [j] using hreveal)
    rw [hardGradY_eq_assemble]
    change -assembleDualBlocks
      (fun a ↦ hardBlockGradY T N lambdaWall eta
        (orderedPrimal z) (orderedDual z) a)
      (finProdFinEquiv (i, j)) = 0
    simp [assembleDualBlocks, hj]
  · have hsN : s.1 = N := by omega
    rw [dif_neg hs]
    apply hardGradX_ordered_zero hN lambdaWall eta hz i
    simpa [hsN] using hreveal

def scaledHardOrderedSaddleField (T N : Nat)
    (lambdaWall eta scale amp : ℝ) (z : EVec (T * (N + 1))) :
    EVec (T * (N + 1)) := fun k ↦
  let p := finProdFinEquiv.symm k
  if hdual : p.2.1 < N then
    -scaledHardGradY T N lambdaWall eta scale amp
      (orderedPrimal z) (orderedDual z)
      (finProdFinEquiv (p.1, ⟨p.2.1, hdual⟩))
  else
    scaledHardGradX T N lambdaWall eta scale amp
      (orderedPrimal z) (orderedDual z) p.1

theorem orderedPrimal_rescale {T N : Nat} (scale : ℝ)
    (z : EVec (T * (N + 1))) :
    orderedPrimal (rescaleEVec scale z) =
      rescaleEVec scale (orderedPrimal z) := by
  rfl

theorem orderedDual_rescale {T N : Nat} (scale : ℝ)
    (z : EVec (T * (N + 1))) :
    orderedDual (rescaleEVec scale z) =
      rescaleEVec scale (orderedDual z) := by
  funext k
  simp [orderedDual, rescaleEVec]

theorem scaledHardOrderedSaddleField_eq (T N : Nat)
    (lambdaWall eta scale amp : ℝ) (z : EVec (T * (N + 1))) :
    scaledHardOrderedSaddleField T N lambdaWall eta scale amp z =
      scaleEVec (amp / scale)
        (hardOrderedSaddleField T N lambdaWall eta
          (rescaleEVec scale z)) := by
  funext k
  rcases hp : finProdFinEquiv.symm k with ⟨i, s⟩
  unfold scaledHardOrderedSaddleField hardOrderedSaddleField
  simp only [hp]
  simp only [scaledHardGradX, scaledHardGradY, scaleEVec]
  rw [orderedPrimal_rescale, orderedDual_rescale]
  by_cases hs : s.1 < N
  · rw [dif_pos hs]
    simp only [hp, dif_pos hs]
    ring
  · rw [dif_neg hs]
    simp only [hp, dif_neg hs]

theorem scaledHardOrderedSaddleField_is_zeroChain {T N : Nat}
    (hN : 0 < N) (lambdaWall eta scale amp : ℝ) :
    IsFirstOrderZeroChain
      (scaledHardOrderedSaddleField T N lambdaWall eta scale amp) := by
  intro r z hz
  have hz' : SupportedBelow r (rescaleEVec scale z) := by
    intro i hi
    simp [rescaleEVec, hz i hi]
  have hbase := hardOrderedSaddleField_is_zeroChain hN lambdaWall eta
    r (rescaleEVec scale z) hz'
  intro k hk
  rw [scaledHardOrderedSaddleField_eq]
  unfold scaleEVec
  rw [hbase k hk]
  ring

end

end NCPLVerification
