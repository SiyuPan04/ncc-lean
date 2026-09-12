import NCPLVerification.GateCalculus
import NCPLVerification.Weights
import NCPLVerification.ZeroChain

/-!
# The terminal-amplified inner chain

This file gives the exact finite-dimensional definitions from Section 3 of
the paper and formalizes the displayed coordinate-gradient formula.  The
formula is then used to prove the first-order zero-chain property.
-/

namespace NCPLVerification

noncomputable section

/-- The frozen predecessor `z₀ = 1` in the paper's one-based notation. -/
def innerPrev {N : ℕ} (z : EVec N) (i : Fin N) : ℝ :=
  if hi : i.1 = 0 then 1 else z ⟨i.1 - 1, by omega⟩

/-- Residual `rᵢ(z) = (1 - σ(zᵢ₋₁) β(zᵢ))₊`. -/
def innerResidual {N : ℕ} (z : EVec N) (i : Fin N) : ℝ :=
  gateResidual (innerPrev z i) (z i)

/-- The exact inner objective `H_N`, with wall coefficient `dᵢ` rather than
`αᵢ`. -/
def innerH (N : ℕ) (lambdaWall : ℝ) (z : EVec N) : ℝ :=
  (∑ i : Fin N, innerAlpha N i * innerResidual z i ^ 2) +
    lambdaWall * ∑ i : Fin N, innerD N i * negPart (z i) ^ 2

/-- Nonnegative incoming contribution in coordinate `i`. -/
def innerIncoming (N : ℕ) (z : EVec N) (i : Fin N) : ℝ :=
  innerAlpha N i * sigma (innerPrev z i) * betaDeriv (z i) * innerResidual z i

/-- Forward contribution in coordinate `i`, absent at the terminal
coordinate.  Unlike `innerIncoming`, this term contains the signed `β`. -/
def innerForward (N : ℕ) (z : EVec N) (i : Fin N) : ℝ :=
  if hi : i.1 + 1 < N then
    innerAlpha N ⟨i.1 + 1, hi⟩ * sigmaDeriv (z i) * beta (z ⟨i.1 + 1, hi⟩) *
      innerResidual z ⟨i.1 + 1, hi⟩
  else 0

/-- Coordinate formula displayed in the inner-chain proof.  A later calculus
lemma identifies this vector with the Fréchet gradient of `innerH`. -/
def innerGradient (N : ℕ) (lambdaWall : ℝ) (z : EVec N) : EVec N :=
  fun i ↦ -2 * innerIncoming N z i - 2 * innerForward N z i -
    2 * lambdaWall * innerD N i * negPart (z i)

theorem innerPrev_zero_of_supported {N r : ℕ} {z : EVec N}
    (hz : SupportedBelow r z) (i : Fin N) (hi : r + 1 ≤ i.1) :
    innerPrev z i = 0 := by
  have hi0 : i.1 ≠ 0 := by omega
  have hiprev : r ≤ i.1 - 1 := by omega
  simp [innerPrev, hi0, hz ⟨i.1 - 1, by omega⟩ hiprev]

theorem innerIncoming_zero_of_supported {N r : ℕ} {z : EVec N}
    (hz : SupportedBelow r z) (i : Fin N) (hi : r + 1 ≤ i.1) :
    innerIncoming N z i = 0 := by
  have hp := innerPrev_zero_of_supported hz i hi
  simp [innerIncoming, hp, sigma_zero]

theorem innerForward_zero_of_supported {N r : ℕ} {z : EVec N}
    (hz : SupportedBelow r z) (i : Fin N) (hi : r + 1 ≤ i.1) :
    innerForward N z i = 0 := by
  have hzi : z i = 0 := hz i (by omega)
  simp [innerForward, hzi, sigmaDeriv_zero]

/-- Part (c) of the inner-chain lemma: the explicit gradient field reveals at
most the next coordinate. -/
theorem innerGradient_is_zeroChain (N : ℕ) (lambdaWall : ℝ) :
    IsFirstOrderZeroChain (innerGradient N lambdaWall) := by
  intro r z hz i hi
  have hzi : z i = 0 := hz i (by omega)
  rw [innerGradient]
  simp [innerIncoming_zero_of_supported hz i hi,
    innerForward_zero_of_supported hz i hi, hzi]

@[simp] theorem innerResidual_nonneg {N : ℕ} (z : EVec N) (i : Fin N) :
    0 ≤ innerResidual z i := gateResidual_nonneg _ _

theorem innerResidual_le_two {N : ℕ} (z : EVec N) (i : Fin N) :
    innerResidual z i ≤ 2 := gateResidual_le_two _ _

theorem innerH_nonneg {N : ℕ} (hN : 0 < N) {lambdaWall : ℝ}
    (hlambda : 0 ≤ lambdaWall) (z : EVec N) : 0 ≤ innerH N lambdaWall z := by
  unfold innerH
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (innerAlpha_pos hN i).le (sq_nonneg _)
  · apply mul_nonneg hlambda
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (innerD_pos hN i).le (sq_nonneg _)

end

end NCPLVerification
