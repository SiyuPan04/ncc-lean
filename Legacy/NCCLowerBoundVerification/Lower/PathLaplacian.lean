import NCCLowerBoundVerification.Basic

/-!
# The regularized path Laplacian

This module gives a matrix-free formalization of the quadratic forms of
`Aₙ` and `Mₙ = n⁻² I + Aₙ` from Definition `def:concrete-inner` in
`Upper+Lower_unified_lower.tex`.
-/

namespace NCCLowerBoundVerification

noncomputable section

/-- The path-Laplacian quadratic form
`∑_{j=1}^{n-1} (w_j - w_{j+1})²`. -/
def pathEnergy : (n : Nat) → EVec n → ℝ
  | 0, _ => 0
  | n + 1, w => ∑ j : Fin n, (w j.castSucc - w j.succ) ^ 2

/-- The scalar coefficient `n⁻²`, written so that it is total also at `n = 0`. -/
def pathRegularization (n : Nat) : ℝ :=
  1 / (n : ℝ) ^ 2

/-- The quadratic form `wᵀ Mₙ w = n⁻² ‖w‖² + wᵀ Aₙ w`. -/
def regularizedPathQuad (n : Nat) (w : EVec n) : ℝ :=
  pathRegularization n * vecSq w + pathEnergy n w

theorem pathRegularization_nonneg (n : Nat) : 0 ≤ pathRegularization n := by
  unfold pathRegularization
  positivity

theorem pathRegularization_pos {n : Nat} (hn : 0 < n) :
    0 < pathRegularization n := by
  unfold pathRegularization
  positivity

theorem pathEnergy_nonneg (n : Nat) (w : EVec n) : 0 ≤ pathEnergy n w := by
  cases n with
  | zero => simp [pathEnergy]
  | succ n =>
      simp only [pathEnergy]
      exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

private theorem vecSq_nonneg {n : Nat} (w : EVec n) : 0 ≤ vecSq w := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _

theorem regularizedPathQuad_nonneg (n : Nat) (w : EVec n) :
    0 ≤ regularizedPathQuad n w := by
  unfold regularizedPathQuad
  exact add_nonneg
    (mul_nonneg (pathRegularization_nonneg n) (vecSq_nonneg w))
    (pathEnergy_nonneg n w)

/-- The Loewner lower bound `n⁻² I ≼ Mₙ`, in quadratic-form form. -/
theorem regularizedPathQuad_lower (n : Nat) (w : EVec n) :
    pathRegularization n * vecSq w ≤ regularizedPathQuad n w := by
  unfold regularizedPathQuad
  exact le_add_of_nonneg_right (pathEnergy_nonneg n w)

/-- For positive dimension, the lower coefficient in the preceding bound is strict. -/
theorem regularizedPathQuad_strong_lower {n : Nat} (hn : 0 < n) (w : EVec n) :
    0 < pathRegularization n ∧
      pathRegularization n * vecSq w ≤ regularizedPathQuad n w := by
  exact ⟨pathRegularization_pos hn, regularizedPathQuad_lower n w⟩

/-- Each path edge contributes at most twice the squared norm of its endpoints. -/
private theorem edge_sq_le (a b : ℝ) : (a - b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a + b)]

/-- The standard dimension-free spectral estimate `wᵀ Aₙ w ≤ 4 ‖w‖²`. -/
theorem pathEnergy_le_four_vecSq (n : Nat) (w : EVec n) :
    pathEnergy n w ≤ 4 * vecSq w := by
  cases n with
  | zero => simp [pathEnergy, vecSq, NCPLVerification.vecSq]
  | succ n =>
      simp only [pathEnergy]
      have hedge :
          (∑ j : Fin n, (w j.castSucc - w j.succ) ^ 2) ≤
            ∑ j : Fin n, (2 * (w j.castSucc) ^ 2 + 2 * (w j.succ) ^ 2) := by
        apply Finset.sum_le_sum
        intro j _
        exact edge_sq_le (w j.castSucc) (w j.succ)
      have hleft :
          (∑ j : Fin n, (w j.castSucc) ^ 2) ≤
            ∑ i : Fin (n + 1), (w i) ^ 2 := by
        rw [Fin.sum_univ_castSucc]
        exact le_add_of_nonneg_right (sq_nonneg _)
      have hright :
          (∑ j : Fin n, (w j.succ) ^ 2) ≤
            ∑ i : Fin (n + 1), (w i) ^ 2 := by
        rw [Fin.sum_univ_succ]
        exact le_add_of_nonneg_left (sq_nonneg _)
      unfold vecSq NCPLVerification.vecSq
      calc
        (∑ j : Fin n, (w j.castSucc - w j.succ) ^ 2) ≤
            ∑ j : Fin n, (2 * (w j.castSucc) ^ 2 + 2 * (w j.succ) ^ 2) := hedge
        _ = 2 * (∑ j : Fin n, (w j.castSucc) ^ 2) +
              2 * (∑ j : Fin n, (w j.succ) ^ 2) := by
                rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
        _ ≤ 4 * ∑ i : Fin (n + 1), (w i) ^ 2 := by linarith

/-- The Loewner upper bound `Mₙ ≼ (4 + n⁻²) I`. -/
theorem regularizedPathQuad_upper (n : Nat) (w : EVec n) :
    regularizedPathQuad n w ≤
      (4 + pathRegularization n) * vecSq w := by
  unfold regularizedPathQuad
  have h := pathEnergy_le_four_vecSq n w
  nlinarith

/-- One coordinate of the path-Laplacian action.  It refers only to the
coordinate itself and its immediate predecessor and successor. -/
def pathLaplacianCoord {n : Nat} (w : EVec n) (i : Fin n) : ℝ :=
  (if hprev : 0 < i.val then
      w i - w ⟨i.val - 1, by omega⟩
    else 0) +
  (if hnext : i.val + 1 < n then
      w i - w ⟨i.val + 1, hnext⟩
    else 0)

/-- One coordinate of `Mₙ w`. -/
def regularizedPathCoord {n : Nat} (w : EVec n) (i : Fin n) : ℝ :=
  pathRegularization n * w i + pathLaplacianCoord w i

/-- Local-coordinate certificate for the tridiagonal path action. -/
theorem pathLaplacianCoord_eq_of_local {n : Nat} {w v : EVec n} (i : Fin n)
    (hself : w i = v i)
    (hprev : ∀ h : 0 < i.val,
      w ⟨i.val - 1, by omega⟩ = v ⟨i.val - 1, by omega⟩)
    (hnext : ∀ h : i.val + 1 < n,
      w ⟨i.val + 1, h⟩ = v ⟨i.val + 1, h⟩) :
    pathLaplacianCoord w i = pathLaplacianCoord v i := by
  unfold pathLaplacianCoord
  split <;> split <;> simp_all

theorem regularizedPathCoord_eq_of_local {n : Nat} {w v : EVec n} (i : Fin n)
    (hself : w i = v i)
    (hprev : ∀ h : 0 < i.val,
      w ⟨i.val - 1, by omega⟩ = v ⟨i.val - 1, by omega⟩)
    (hnext : ∀ h : i.val + 1 < n,
      w ⟨i.val + 1, h⟩ = v ⟨i.val + 1, h⟩) :
    regularizedPathCoord w i = regularizedPathCoord v i := by
  unfold regularizedPathCoord
  rw [hself, pathLaplacianCoord_eq_of_local i hself hprev hnext]

/-- Zero-chain certificate: if `w` vanishes from coordinate `k` onward,
then `Mₙ w` vanishes from coordinate `k+1` onward. -/
theorem regularizedPathCoord_zero_of_zero_tail {n k : Nat} {w : EVec n}
    (hw : ∀ i : Fin n, k ≤ i.val → w i = 0)
    (i : Fin n) (hi : k + 1 ≤ i.val) : regularizedPathCoord w i = 0 := by
  have hself : w i = 0 := hw i (by omega)
  have hipos : 0 < i.val := by omega
  let iprev : Fin n := ⟨i.val - 1, by omega⟩
  have hprevtail : k ≤ iprev.val := by
    dsimp [iprev]
    omega
  have hp : w iprev = 0 := hw iprev hprevtail
  by_cases hnext : i.val + 1 < n
  · let inext : Fin n := ⟨i.val + 1, hnext⟩
    have hnexttail : k ≤ inext.val := by
      dsimp [inext]
      omega
    have hn : w inext = 0 := hw inext hnexttail
    unfold regularizedPathCoord pathLaplacianCoord
    simp [hipos, hnext, hself, hp, hn, iprev, inext]
  · unfold regularizedPathCoord pathLaplacianCoord
    simp [hipos, hnext, hself, hp, iprev]

end

end NCCLowerBoundVerification
