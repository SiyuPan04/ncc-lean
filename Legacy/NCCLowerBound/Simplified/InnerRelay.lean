import NCCLowerBoundVerification.Lower.GreenMatrix

/-!
# The symmetrically normalised inner dual relay

This file formalises the block in lines 900--949 and 1553--1656 of
`NC_C_Lower_Bound_simplified.tex`.  The dependency project already constructs
the regularised path matrix and proves its Green-kernel estimates, but its
older relay uses the asymmetric source `a e₁ - (b / 2) e_N`.  Consequently we
reuse only the path operator and its inverse here and define the symmetric
source `a e₁ - b e_N` afresh.

The dependency API supplies only coarse Green-column bounds.  We derive the
sharp estimates `6/5 <= rho` and `rho <= 8/5` here from the same endpoint
profile as the TeX hyperbolic-cosine calculation, using its rational
second-order recurrence instead of transcendental functions.
-/

namespace NCCLowerBound
namespace Simplified
namespace InnerRelay

noncomputable section

open scoped BigOperators
open NCCLowerBoundVerification

abbrev EVec := NCCLowerBoundVerification.EVec

/-! ## The path matrix and its inverse -/

/-- The path matrix `M_N = N^{-2} I + A_N`. -/
abbrev pathM (N : Nat) : Matrix (Fin N) (Fin N) ℝ :=
  innerM N

/-- The inverse matrix `B_N`. -/
abbrev pathB (N : Nat) : Matrix (Fin N) (Fin N) ℝ :=
  innerB N

/-- The path-Laplacian matrix, extracted from the already verified path
matrix by removing the diagonal regularisation. -/
def pathA (N : Nat) : Matrix (Fin N) (Fin N) ℝ :=
  pathM N - pathRegularization N • (1 : Matrix (Fin N) (Fin N) ℝ)

/-- Literal matrix equality corresponding to `M_N = N^{-2} I + A_N`. -/
theorem pathM_eq_regularization_add_pathA (N : Nat) :
    pathM N =
      pathRegularization N • (1 : Matrix (Fin N) (Fin N) ℝ) + pathA N := by
  ext i j
  simp [pathA]

/-- The matrix action agrees coordinatewise with the regularised path
Laplacian action.  This pins down the correspondence with the symmetric
normalisation, rather than merely identifying two quadratic values. -/
theorem pathM_mulVec_eq_coord {N : Nat} (w : EVec N) (i : Fin N) :
    (pathM N).mulVec w i = regularizedPathCoord w i :=
  innerM_mulVec_eq_coord w i

/-- The extracted `A_N` acts as the ordinary path Laplacian. -/
theorem pathA_mulVec_eq_coord {N : Nat} (w : EVec N) (i : Fin N) :
    (pathA N).mulVec w i = pathLaplacianCoord w i := by
  rw [pathA, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  change (pathM N).mulVec w i - pathRegularization N * w i = _
  rw [pathM_mulVec_eq_coord]
  simp [regularizedPathCoord]

private theorem regularizedPathBilinear_sum_right {N : Nat} (u : EVec N)
    (s : Finset (Fin N)) (f : Fin N → EVec N) :
    regularizedPathBilinear N u (∑ j ∈ s, f j) =
      ∑ j ∈ s, regularizedPathBilinear N u (f j) := by
  induction s using Finset.induction_on with
  | empty =>
      simpa using regularizedPathBilinear_smul_right N 0 u u
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [regularizedPathBilinear_add_right, ih]

private theorem basis_sum (N : Nat) (w : EVec N) :
    (∑ j : Fin N, w j • Pi.single j (1 : ℝ)) = w := by
  funext i
  classical
  simp [Pi.single_apply]

/-- Matrix quadratic form equals the matrix-free regularised path form. -/
theorem pathM_quadratic_eq (N : Nat) (w : EVec N) :
    (∑ i : Fin N, w i * (pathM N).mulVec w i) =
      regularizedPathQuad N w := by
  rw [← regularizedPathBilinear_self]
  calc
    (∑ i : Fin N, w i * (pathM N).mulVec w i) =
        ∑ i : Fin N,
          regularizedPathBilinear N w (w i • Pi.single i (1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [regularizedPathBilinear_smul_right,
        regularizedPathBilinear_comm,
        innerM_mulVec_eq_bilinear]
    _ = regularizedPathBilinear N w
          (∑ i : Fin N, w i • Pi.single i (1 : ℝ)) := by
      symm
      simpa using regularizedPathBilinear_sum_right
        (N := N) w Finset.univ (fun i ↦ w i • Pi.single i (1 : ℝ))
    _ = regularizedPathBilinear N w w := by rw [basis_sum]

/-- In quadratic-form language, the extracted `A_N` is exactly the edge
energy `sum_j (w_j-w_{j+1})^2`. -/
theorem pathA_quadratic_eq (N : Nat) (w : EVec N) :
    (∑ i : Fin N, w i * (pathA N).mulVec w i) = pathEnergy N w := by
  calc
    (∑ i : Fin N, w i * (pathA N).mulVec w i) =
        ∑ i : Fin N,
          w i * ((pathM N).mulVec w i - pathRegularization N * w i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [pathA_mulVec_eq_coord, pathM_mulVec_eq_coord]
      simp [regularizedPathCoord]
    _ = (∑ i : Fin N, w i * (pathM N).mulVec w i) -
          pathRegularization N * vecSq w := by
      unfold vecSq NCPLVerification.vecSq
      calc
        _ = ∑ i : Fin N,
            (w i * (pathM N).mulVec w i -
              pathRegularization N * w i ^ 2) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = pathEnergy N w := by
      rw [pathM_quadratic_eq]
      unfold regularizedPathQuad
      ring

theorem pathM_isUnit {N : Nat} (hN : 0 < N) : IsUnit (pathM N) :=
  innerM_isUnit hN

theorem pathM_mul_pathB {N : Nat} (hN : 0 < N) :
    pathM N * pathB N = 1 :=
  innerM_mul_innerB hN

private theorem vecSq_pos_of_ne_zero {N : Nat} {w : EVec N} (hw : w ≠ 0) :
    0 < vecSq w := by
  have hex : ∃ i : Fin N, w i ≠ 0 := by
    by_contra h
    push Not at h
    apply hw
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  have hisq : 0 < w i ^ 2 := sq_pos_of_ne_zero hi
  have hle : w i ^ 2 ≤ vecSq w := by
    unfold vecSq NCPLVerification.vecSq
    exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (w j))
      (Finset.mem_univ i)
  exact lt_of_lt_of_le hisq hle

/-- Positive definiteness of `M_N`. -/
theorem pathM_posDef {N : Nat} (hN : 0 < N) {w : EVec N} (hw : w ≠ 0) :
    0 < ∑ i : Fin N, w i * (pathM N).mulVec w i := by
  rw [pathM_quadratic_eq]
  have hreg := pathRegularization_pos hN
  have hlower := regularizedPathQuad_lower N w
  have hsq := vecSq_pos_of_ne_zero hw
  nlinarith

/-! ## Symmetric endpoint normalisation -/

def first {N : Nat} (hN : 0 < N) : Fin N := innerFirst hN

def last {N : Nat} (hN : 0 < N) : Fin N := innerLast hN

/-- `sigma = (B_N)_{1N}`. -/
def sigma {N : Nat} (hN : 0 < N) : ℝ :=
  pathB N (first hN) (last hN)

/-- `rho = (B_N)_{11} / sigma`. -/
def rho {N : Nat} (hN : 0 < N) : ℝ :=
  pathB N (first hN) (first hN) / sigma hN

theorem sigma_eq_reverse_cross {N : Nat} (hN : 0 < N) :
    sigma hN = pathB N (last hN) (first hN) := by
  unfold sigma first last pathB
  exact innerB_apply_comm N _ _

theorem sigma_bounds {N : Nat} (hN : 10 ≤ N) :
    (N : ℝ) / 10 ≤ sigma (by omega : 0 < N) ∧
      sigma (by omega : 0 < N) ≤ 20 * (N : ℝ) := by
  let hNpos : 0 < N := by omega
  rw [sigma_eq_reverse_cross hNpos]
  exact innerB_first_column_bounds hN (last hNpos)

theorem sigma_pos {N : Nat} (hN : 10 ≤ N) :
    0 < sigma (by omega : 0 < N) := by
  have hs := (sigma_bounds hN).1
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  nlinarith

theorem endpoint_diagonal_eq {N : Nat} (hN : 0 < N) :
    pathB N (last hN) (last hN) =
      pathB N (first hN) (first hN) := by
  exact innerB_endpoint_diagonal_eq hN

/-- The currently available Green estimates imply this honest coarse ratio
bound.  It is deliberately not presented as the sharper paper estimate. -/
theorem rho_coarse_bounds {N : Nat} (hN : 10 ≤ N) :
    (1 / 200 : ℝ) ≤ rho (by omega : 0 < N) ∧
      rho (by omega : 0 < N) ≤ 200 := by
  let hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hs := sigma_bounds hN
  have hspos := sigma_pos hN
  have hd := innerB_first_column_bounds hN (first hNpos)
  have hd' :
      (N : ℝ) / 10 ≤ pathB N (first hNpos) (first hNpos) ∧
        pathB N (first hNpos) (first hNpos) ≤ 20 * (N : ℝ) := by
    simpa [first, pathB] using hd
  unfold rho
  constructor
  · rw [le_div_iff₀ hspos]
    nlinarith [hd'.1, hs.2]
  · rw [div_le_iff₀ hspos]
    nlinarith [hd'.2, hs.1]

theorem rho_pos {N : Nat} (hN : 10 ≤ N) :
    0 < rho (by omega : 0 < N) := by
  have h := (rho_coarse_bounds hN).1
  norm_num at h ⊢
  linarith

/-! ### A recurrence proof of the sharp endpoint ratio

The TeX writes the following sequence as a quotient of hyperbolic cosines.
For formal purposes its second-order recurrence is both exact and more
convenient: it avoids importing any numerical transcendental estimates.
The index is distance from the right endpoint. -/

def endpointProfileSeq (N : Nat) : Nat → ℝ
  | 0 => 1
  | 1 => 1 + pathRegularization N
  | m + 2 =>
      (2 + pathRegularization N) * endpointProfileSeq N (m + 1) -
        endpointProfileSeq N m

@[simp] theorem endpointProfileSeq_zero (N : Nat) :
    endpointProfileSeq N 0 = 1 := rfl

@[simp] theorem endpointProfileSeq_one (N : Nat) :
    endpointProfileSeq N 1 = 1 + pathRegularization N := rfl

theorem endpointProfileSeq_diff_succ (N m : Nat) :
    endpointProfileSeq N (m + 2) - endpointProfileSeq N (m + 1) =
      (endpointProfileSeq N (m + 1) - endpointProfileSeq N m) +
        pathRegularization N * endpointProfileSeq N (m + 1) := by
  rw [endpointProfileSeq]
  ring

theorem endpointProfileSeq_one_le_mono (N m : Nat) :
    1 ≤ endpointProfileSeq N m ∧
      endpointProfileSeq N m ≤ endpointProfileSeq N (m + 1) := by
  induction m with
  | zero =>
      simp [endpointProfileSeq, pathRegularization_nonneg]
  | succ m ih =>
      have hp : 0 ≤ pathRegularization N * endpointProfileSeq N (m + 1) :=
        mul_nonneg (pathRegularization_nonneg N) (by linarith [ih.1, ih.2])
      constructor
      · linarith [ih.1, ih.2]
      · have hd := endpointProfileSeq_diff_succ N m
        linarith

theorem endpointProfileSeq_diff_lower (N m : Nat) :
    (m + 1 : ℝ) * pathRegularization N ≤
      endpointProfileSeq N (m + 1) - endpointProfileSeq N m := by
  induction m with
  | zero => simp [endpointProfileSeq]
  | succ m ih =>
      rw [show m + 1 + 1 = m + 2 by omega,
        endpointProfileSeq_diff_succ]
      have hp := (endpointProfileSeq_one_le_mono N (m + 1)).1
      have hreg := pathRegularization_nonneg N
      have hmul := mul_le_mul_of_nonneg_left hp hreg
      push_cast
      nlinarith

theorem endpointProfileSeq_lower (N m : Nat) :
    1 + ((m : ℝ) * (m + 1) / 2) * pathRegularization N ≤
      endpointProfileSeq N m := by
  induction m with
  | zero => simp [endpointProfileSeq]
  | succ m ih =>
      have hd := endpointProfileSeq_diff_lower N m
      push_cast at hd ⊢
      nlinarith

/-- A bootstrap bound used only to control the second-order correction in
the sharp upper estimate. -/
theorem endpointProfileSeq_coarse_upper {N m : Nat} (hN : 0 < N) (hm : m < N) :
    endpointProfileSeq N m ≤ 2 ∧
      endpointProfileSeq N (m + 1) - endpointProfileSeq N m ≤
        2 * (m + 1 : ℝ) * pathRegularization N ∧
      endpointProfileSeq N m ≤
        1 + pathRegularization N * (m : ℝ) * (m + 1) := by
  induction m with
  | zero =>
      have hr := pathRegularization_nonneg N
      simp [endpointProfileSeq]
      nlinarith
  | succ m ih =>
      have hm' : m < N := by omega
      have ih' := ih hm'
      have hd := endpointProfileSeq_diff_succ N m
      have hC : endpointProfileSeq N (m + 1) ≤
          1 + pathRegularization N * (m + 1 : ℝ) * (m + 2) := by
        nlinarith [ih'.2.1, ih'.2.2]
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hm1 : (0 : ℝ) ≤ m + 1 := by positivity
      have hm2 : (0 : ℝ) ≤ m + 2 := by positivity
      have hm1N : (m + 1 : ℝ) ≤ N := by exact_mod_cast (by omega : m + 1 ≤ N)
      have hm2N : (m + 2 : ℝ) ≤ N := by exact_mod_cast (by omega : m + 2 ≤ N)
      have hprod : (m + 1 : ℝ) * (m + 2) ≤ (N : ℝ) ^ 2 := by
        calc
          (m + 1 : ℝ) * (m + 2) ≤ (N : ℝ) * N :=
            mul_le_mul hm1N hm2N hm2 hNr.le
          _ = (N : ℝ) ^ 2 := by ring
      have hregprod :
          pathRegularization N * (m + 1 : ℝ) * (m + 2) ≤ 1 := by
        unfold pathRegularization
        rw [show 1 / (N : ℝ) ^ 2 * (m + 1 : ℝ) * (m + 2) =
          ((m + 1 : ℝ) * (m + 2)) / (N : ℝ) ^ 2 by ring]
        rw [div_le_iff₀ (sq_pos_of_pos hNr)]
        simpa using hprod
      have htwo : endpointProfileSeq N (m + 1) ≤ 2 := by linarith
      have hr := pathRegularization_nonneg N
      have hdiff : endpointProfileSeq N (m + 2) - endpointProfileSeq N (m + 1) ≤
          2 * (m + 2 : ℝ) * pathRegularization N := by
        nlinarith [ih'.2.1, mul_le_mul_of_nonneg_left htwo hr]
      refine ⟨htwo, ?_, ?_⟩
      · rw [show m + 1 + 1 = m + 2 by omega]
        push_cast
        convert hdiff using 1
        all_goals ring
      · push_cast
        convert hC using 1
        all_goals ring

theorem endpointProfileSeq_diff_upper {N m : Nat} (hN : 0 < N) (hm : m < N) :
    endpointProfileSeq N (m + 1) - endpointProfileSeq N m ≤
      (m + 1 : ℝ) * pathRegularization N +
        ((m : ℝ) * (m + 1) * (m + 2) / 3) *
          pathRegularization N ^ 2 := by
  induction m with
  | zero => simp [endpointProfileSeq]
  | succ m ih =>
      have hm' : m < N := by omega
      have ih' := ih hm'
      have hd := endpointProfileSeq_diff_succ N m
      have hc := endpointProfileSeq_coarse_upper hN hm
      have hr := pathRegularization_nonneg N
      have hmul := mul_le_mul_of_nonneg_left hc.2.2 hr
      rw [show m + 1 + 1 = m + 2 by omega]
      push_cast at ih' hmul ⊢
      nlinarith

/-- A two-term discrete Taylor bound for the endpoint profile. -/
theorem endpointProfileSeq_upper_succ {N m : Nat} (hN : 0 < N)
    (hm : m + 1 < N) :
    endpointProfileSeq N (m + 1) ≤
      1 + ((m + 1 : ℝ) * (m + 2) / 2) * pathRegularization N +
        ((m : ℝ) * (m + 1) * (m + 2) * (m + 3) / 12) *
          pathRegularization N ^ 2 := by
  induction m with
  | zero =>
      simp [endpointProfileSeq]
  | succ m ih =>
      have hm' : m + 1 < N := by omega
      have ih' := ih hm'
      have hd := endpointProfileSeq_diff_upper (m := m + 1) hN (by omega)
      rw [show m + 1 + 1 = m + 2 by omega]
      push_cast at ih' hd ⊢
      nlinarith

/-- The recurrence profile placed on the path, with index zero at the right
endpoint. -/
def endpointProfile {N : Nat} (_hN : 0 < N) : EVec N := fun i ↦
  endpointProfileSeq N (N - 1 - i.val)

@[simp] theorem endpointProfile_last {N : Nat} (hN : 0 < N) :
    endpointProfile hN (last hN) = 1 := by
  simp [endpointProfile, last, innerLast]

@[simp] theorem endpointProfile_first {N : Nat} (hN : 0 < N) :
    endpointProfile hN (first hN) = endpointProfileSeq N (N - 1) := by
  simp [endpointProfile, first, innerFirst]

private theorem regularizedPathCoord_smul {N : Nat} (c : ℝ)
    (w : EVec N) (i : Fin N) :
    regularizedPathCoord (c • w) i = c * regularizedPathCoord w i := by
  unfold regularizedPathCoord pathLaplacianCoord
  split <;> split <;> simp [Pi.smul_apply] <;> ring

/-- Away from the first coordinate, the recurrence profile is harmonic for
the regularised path operator. -/
theorem endpointProfile_coord_zero_of_ne_first {N : Nat} (hN : 0 < N)
    (i : Fin N) (hi : i ≠ first hN) :
    regularizedPathCoord (endpointProfile hN) i = 0 := by
  have hipos : 0 < i.val := by
    by_contra hz
    have hiz : i = first hN := by
      apply Fin.ext
      simp [first, innerFirst]
      omega
    exact hi hiz
  by_cases hnext : i.val + 1 < N
  · let d : Nat := N - 1 - i.val
    have hdpos : 0 < d := by
      dsimp [d]
      omega
    have hself : endpointProfile hN i = endpointProfileSeq N d := by rfl
    have hprev :
        endpointProfile hN ⟨i.val - 1, by omega⟩ =
          endpointProfileSeq N (d + 1) := by
      unfold endpointProfile
      congr 1
      dsimp [d]
      omega
    have hnextv :
        endpointProfile hN ⟨i.val + 1, hnext⟩ =
          endpointProfileSeq N (d - 1) := by
      unfold endpointProfile
      congr 1
    have hrec := endpointProfileSeq_diff_succ N (d - 1)
    have hd1 : d - 1 + 1 = d := by omega
    have hd2 : d - 1 + 2 = d + 1 := by omega
    rw [hd1, hd2] at hrec
    unfold regularizedPathCoord pathLaplacianCoord
    rw [dif_pos hipos, dif_pos hnext, hself, hprev, hnextv]
    nlinarith
  · have hilast : i = last hN := by
      apply Fin.ext
      simp [last, innerLast]
      omega
    subst i
    unfold regularizedPathCoord pathLaplacianCoord
    have hp : 0 < (last hN).val := by simp [last, innerLast]; omega
    have hnxt : ¬((last hN).val + 1 < N) := by
      simp [last, innerLast]
      omega
    rw [dif_pos hp, dif_neg hnxt]
    have hNtwo : 1 < N := by
      by_contra hle
      have hNone : N = 1 := by omega
      subst N
      apply hi
      apply Fin.ext
      simp [first, last, innerFirst, innerLast]
    have hidx : N - 1 - (N - 1 - 1) = 1 := by omega
    simp [endpointProfile, last, innerLast, hidx]

/-- The sole nonzero coordinate of `M_N` applied to the recurrence profile. -/
def endpointProfileCoeff {N : Nat} (hN : 0 < N) : ℝ :=
  regularizedPathCoord (endpointProfile hN) (first hN)

theorem endpointProfileCoeff_pos {N : Nat} (hN10 : 10 ≤ N) :
    0 < endpointProfileCoeff (by omega : 0 < N) := by
  let hN : 0 < N := by omega
  let q := endpointProfile hN
  have hqne : q ≠ 0 := by
    intro hzero
    have hz := congrFun hzero (last hN)
    simp [q] at hz
  have hpd := pathM_posDef hN hqne
  have hsum :
      (∑ i : Fin N, q i * (pathM N).mulVec q i) =
        q (first hN) * endpointProfileCoeff hN := by
    classical
    calc
      _ = q (first hN) * (pathM N).mulVec q (first hN) := by
        apply Finset.sum_eq_single_of_mem (first hN) (Finset.mem_univ _)
        intro i _ hi
        rw [pathM_mulVec_eq_coord,
          endpointProfile_coord_zero_of_ne_first hN i hi]
        ring
      _ = q (first hN) * endpointProfileCoeff hN := by
        rw [pathM_mulVec_eq_coord]
        simp [endpointProfileCoeff, q]
  rw [hsum] at hpd
  have hqfirst := (endpointProfileSeq_one_le_mono N (N - 1)).1
  simp only [q, endpointProfile_first] at hpd
  by_contra hc
  have hc' : endpointProfileCoeff hN ≤ 0 := le_of_not_gt hc
  have hp0 : 0 ≤ endpointProfileSeq N (N - 1) := by linarith
  have hprod := mul_nonpos_of_nonneg_of_nonpos hp0 hc'
  exact (not_lt_of_ge hprod) hpd

def normalizedEndpointProfile {N : Nat} (hN : 0 < N) : EVec N :=
  (endpointProfileCoeff hN)⁻¹ • endpointProfile hN

theorem normalizedEndpointProfile_equation {N : Nat} (hN10 : 10 ≤ N)
    (i : Fin N) :
    regularizedPathCoord
        (normalizedEndpointProfile (by omega : 0 < N)) i =
      (Pi.single (first (by omega : 0 < N)) (1 : ℝ) : EVec N) i := by
  let hN : 0 < N := by omega
  have hc := endpointProfileCoeff_pos hN10
  unfold normalizedEndpointProfile
  rw [regularizedPathCoord_smul]
  by_cases hi : i = first hN
  · subst i
    change (endpointProfileCoeff hN)⁻¹ * endpointProfileCoeff hN = 1
    exact inv_mul_cancel₀ (ne_of_gt hc)
  · rw [endpointProfile_coord_zero_of_ne_first hN i hi]
    simp [hi]

theorem normalizedEndpointProfile_eq_green {N : Nat} (hN10 : 10 ≤ N) :
    normalizedEndpointProfile (by omega : 0 < N) =
      innerGreenColumn N (first (by omega : 0 < N)) := by
  let hN : 0 < N := by omega
  apply Matrix.mulVec_injective_iff_isUnit.mpr (pathM_isUnit hN)
  funext i
  rw [pathM_mulVec_eq_coord, pathM_mulVec_eq_coord,
    normalizedEndpointProfile_equation hN10,
    innerGreenColumn_equation hN (first hN) i]

/-- Identification of the inverse endpoint ratio with the elementary
recurrence profile. -/
theorem rho_eq_endpointProfileSeq {N : Nat} (hN10 : 10 ≤ N) :
    rho (by omega : 0 < N) = endpointProfileSeq N (N - 1) := by
  let hN : 0 < N := by omega
  have heq := normalizedEndpointProfile_eq_green hN10
  have hf := congrFun heq (first hN)
  have hl := congrFun heq (last hN)
  have hc := endpointProfileCoeff_pos hN10
  simp only [normalizedEndpointProfile, Pi.smul_apply, smul_eq_mul,
    endpointProfile_first, endpointProfile_last, innerGreenColumn] at hf hl
  have hf' :
      (endpointProfileCoeff hN)⁻¹ * endpointProfileSeq N (N - 1) =
        pathB N (first hN) (first hN) := by
    simpa [pathB] using hf
  have hl' :
      (endpointProfileCoeff hN)⁻¹ * 1 =
        pathB N (last hN) (first hN) := by
    simpa [pathB] using hl
  unfold rho
  change pathB N (first hN) (first hN) / sigma hN = _
  rw [sigma_eq_reverse_cross hN]
  rw [← hf', ← hl']
  field_simp [ne_of_gt hc]

theorem endpointProfileSeq_sharp_bounds {N : Nat} (hN10 : 10 ≤ N) :
    (6 / 5 : ℝ) ≤ endpointProfileSeq N (N - 1) ∧
      endpointProfileSeq N (N - 1) ≤ 8 / 5 := by
  let hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN10r : (10 : ℝ) ≤ N := by exact_mod_cast hN10
  have hNm1 : (((N - 1 : Nat) : ℝ)) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  constructor
  · have hl := endpointProfileSeq_lower N (N - 1)
    rw [hNm1] at hl
    have hbase :
        (6 / 5 : ℝ) ≤
          1 + (((N : ℝ) - 1) * N / 2) * pathRegularization N := by
      unfold pathRegularization
      field_simp [ne_of_gt hNr]
      nlinarith
    have hl' :
        1 + (((N : ℝ) - 1) * N / 2) * pathRegularization N ≤
          endpointProfileSeq N (N - 1) := by
      convert hl using 1
      all_goals ring
    exact hbase.trans hl'
  · have hu := endpointProfileSeq_upper_succ
        (N := N) (m := N - 2) hN (by omega)
    have hidx : N - 2 + 1 = N - 1 := by omega
    rw [hidx] at hu
    have hNm2 : (((N - 2 : Nat) : ℝ)) = (N : ℝ) - 2 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hNm2] at hu
    have hfirstTerm :
        ((((N : ℝ) - 2) + 1) * (((N : ℝ) - 2) + 2) / 2) *
            pathRegularization N ≤ 1 / 2 := by
      unfold pathRegularization
      field_simp [ne_of_gt hNr]
      nlinarith
    have hpoly0 :
        0 ≤ (N : ℝ) * (2 * (N : ℝ) ^ 2 + N - 2) := by
      have : 0 ≤ 2 * (N : ℝ) ^ 2 + N - 2 := by
        nlinarith [sq_nonneg (N : ℝ)]
      exact mul_nonneg hNr.le this
    have hprod :
        (((N : ℝ) - 2) * ((N : ℝ) - 1) * N * ((N : ℝ) + 1)) ≤
          (N : ℝ) ^ 4 := by
      nlinarith
    have hsecondTerm :
        (((N : ℝ) - 2) * (((N : ℝ) - 2) + 1) *
              (((N : ℝ) - 2) + 2) * (((N : ℝ) - 2) + 3) / 12) *
            pathRegularization N ^ 2 ≤ 1 / 12 := by
      unfold pathRegularization
      have hN4 : 0 < (N : ℝ) ^ 4 := by positivity
      rw [show (1 / (N : ℝ) ^ 2) ^ 2 = 1 / (N : ℝ) ^ 4 by ring]
      rw [show (((N : ℝ) - 2) * (((N : ℝ) - 2) + 1) *
              (((N : ℝ) - 2) + 2) * (((N : ℝ) - 2) + 3) / 12) *
            (1 / (N : ℝ) ^ 4) =
          ((((N : ℝ) - 2) * ((N : ℝ) - 1) * N * ((N : ℝ) + 1)) /
            ((N : ℝ) ^ 4)) / 12 by field_simp; ring]
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 12)]
      rw [div_le_iff₀ hN4]
      simpa using hprod
    nlinarith

/-- A named certificate for the sharp endpoint estimate. -/
def HasSharpEndpointRatio {N : Nat} (hN : 0 < N) : Prop :=
  (6 / 5 : ℝ) ≤ rho hN ∧ rho hN ≤ 8 / 5

/-- The endpoint Green ratio obeys the two sharp constants used in the TeX
correction argument.  This is unconditional once `N ≥ 10`. -/
theorem sharp_endpoint_ratio {N : Nat} (hN10 : 10 ≤ N) :
    HasSharpEndpointRatio (by omega : 0 < N) := by
  unfold HasSharpEndpointRatio
  rw [rho_eq_endpointProfileSeq hN10]
  exact endpointProfileSeq_sharp_bounds hN10

theorem correction_bounds {N : Nat} {hN : 0 < N}
    (hrho : HasSharpEndpointRatio hN) :
    (2 / 5 : ℝ) ≤ 2 - rho hN ∧ 2 - rho hN ≤ 4 / 5 := by
  unfold HasSharpEndpointRatio at hrho
  constructor <;> linarith

/-- In particular, the endpoint ratio cannot exceed the correction diagonal. -/
theorem rho_le_two {N : Nat} (hN10 : 10 ≤ N) :
    rho (by omega : 0 < N) ≤ 2 := by
  have h := (sharp_endpoint_ratio hN10).2
  linarith

/-- The correction coefficient lies in `[2/5,4/5]`, with no auxiliary
endpoint-ratio assumption. -/
theorem correction_bounds_unconditional {N : Nat} (hN10 : 10 ≤ N) :
    (2 / 5 : ℝ) ≤ 2 - rho (by omega : 0 < N) ∧
      2 - rho (by omega : 0 < N) ≤ 4 / 5 :=
  correction_bounds (sharp_endpoint_ratio hN10)

/-- The symmetric endpoint source `a e_1 - b e_N`. -/
def endpointSource {N : Nat} (hN : 0 < N) (a b : ℝ) : EVec N :=
  Pi.single (first hN) a - Pi.single (last hN) b

def endpointForcing {N : Nat} (hN : 0 < N) (a b : ℝ) (w : EVec N) : ℝ :=
  a * w (first hN) - b * w (last hN)

/-- `sigma^{-1/2}`. -/
def relayScale {N : Nat} (hN : 0 < N) : ℝ :=
  (Real.sqrt (sigma hN))⁻¹

theorem relayScale_pos {N : Nat} (hN10 : 10 ≤ N) :
    0 < relayScale (by omega : 0 < N) := by
  unfold relayScale
  exact inv_pos.mpr (Real.sqrt_pos.2 (sigma_pos hN10))

theorem relayScale_sq {N : Nat} (hN10 : 10 ≤ N) :
    relayScale (by omega : 0 < N) ^ 2 =
      1 / sigma (by omega : 0 < N) := by
  let hNpos : 0 < N := by omega
  have hs := sigma_pos hN10
  unfold relayScale
  rw [inv_pow, Real.sq_sqrt hs.le]
  simp [div_eq_mul_inv]

/-- The uncorrected symmetric relay `h(a,b;w)`. -/
def relayH {N : Nat} (hN : 0 < N) (a b : ℝ) (w : EVec N) : ℝ :=
  -(1 / 2 : ℝ) * regularizedPathQuad N w +
    relayScale hN * endpointForcing hN a b w

/-- The diagonally corrected relay. -/
def correctedH {N : Nat} (hN : 0 < N) (a b : ℝ) (w : EVec N) : ℝ :=
  relayH hN a b w + (2 - rho hN) / 2 * (a ^ 2 + b ^ 2)

/-- `w^star = sigma^{-1/2} B_N (a e_1-b e_N)`. -/
def wStar {N : Nat} (hN : 0 < N) (a b : ℝ) : EVec N := fun i ↦
  relayScale hN *
    (pathB N i (first hN) * a - pathB N i (last hN) * b)

theorem wStar_eq_matrix_mulVec {N : Nat} (hN : 0 < N) (a b : ℝ) :
    wStar hN a b =
      relayScale hN • (pathB N).mulVec (endpointSource hN a b) := by
  classical
  unfold endpointSource
  rw [Matrix.mulVec_sub, Matrix.mulVec_single, Matrix.mulVec_single]
  funext i
  unfold wStar
  simp only [Pi.smul_apply, Pi.sub_apply, Matrix.col_apply, smul_eq_mul,
    op_smul_eq_mul]

/-! ## Stationarity, maximisation, and the effective link -/

def IsRelayStationary {N : Nat} (hN : 0 < N) (a b : ℝ)
    (wstar : EVec N) : Prop :=
  ∀ d : EVec N,
    regularizedPathBilinear N wstar d =
      relayScale hN * endpointForcing hN a b d

private theorem bilinear_eq_weighted_action {N : Nat} (u v : EVec N) :
    regularizedPathBilinear N u v =
      ∑ i : Fin N, v i * (pathM N).mulVec u i := by
  classical
  calc
    regularizedPathBilinear N u v =
        regularizedPathBilinear N u
          (∑ i : Fin N, v i • Pi.single i (1 : ℝ)) := by rw [basis_sum]
    _ = ∑ i : Fin N, regularizedPathBilinear N u
          (v i • Pi.single i (1 : ℝ)) := by
      simpa using regularizedPathBilinear_sum_right
        (N := N) u Finset.univ (fun i ↦ v i • Pi.single i (1 : ℝ))
    _ = ∑ i : Fin N, v i * (pathM N).mulVec u i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [regularizedPathBilinear_smul_right,
        regularizedPathBilinear_comm,
        innerM_mulVec_eq_bilinear]

private theorem bilinear_greenColumn {N : Nat} (hN : 0 < N)
    (j : Fin N) (d : EVec N) :
    regularizedPathBilinear N (innerGreenColumn N j) d = d j := by
  rw [bilinear_eq_weighted_action]
  have haction : (pathM N).mulVec (innerGreenColumn N j) =
      Pi.single j (1 : ℝ) := by
    funext i
    rw [pathM_mulVec_eq_coord, innerGreenColumn_equation hN]
  rw [haction]
  simp [Pi.single_apply]

theorem wStar_stationary {N : Nat} (hN : 0 < N) (a b : ℝ) :
    IsRelayStationary hN a b (wStar hN a b) := by
  intro d
  have hw : wStar hN a b =
      relayScale hN •
        (a • innerGreenColumn N (first hN) +
          (-b) • innerGreenColumn N (last hN)) := by
    funext i
    unfold wStar innerGreenColumn
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [hw, regularizedPathBilinear_smul_left,
    regularizedPathBilinear_add_left,
    regularizedPathBilinear_smul_left,
    regularizedPathBilinear_smul_left,
    bilinear_greenColumn hN, bilinear_greenColumn hN]
  unfold endpointForcing
  ring

private theorem endpointForcing_sub {N : Nat} (hN : 0 < N) (a b : ℝ)
    (u v : EVec N) :
    endpointForcing hN a b (u - v) =
      endpointForcing hN a b u - endpointForcing hN a b v := by
  simp [endpointForcing, Pi.sub_apply]
  ring

private theorem endpointForcing_add {N : Nat} (hN : 0 < N) (a b : ℝ)
    (u v : EVec N) :
    endpointForcing hN a b (u + v) =
      endpointForcing hN a b u + endpointForcing hN a b v := by
  simp [endpointForcing, Pi.add_apply]
  ring

private theorem endpointForcing_smul {N : Nat} (hN : 0 < N) (a b c : ℝ)
    (u : EVec N) :
    endpointForcing hN a b (c • u) = c * endpointForcing hN a b u := by
  simp [endpointForcing, Pi.smul_apply]
  ring

private theorem regularizedPathBilinear_sub_right (N : Nat)
    (u v w : EVec N) :
    regularizedPathBilinear N u (v - w) =
      regularizedPathBilinear N u v - regularizedPathBilinear N u w := by
  rw [sub_eq_add_neg, regularizedPathBilinear_add_right,
    ← neg_one_smul ℝ w, regularizedPathBilinear_smul_right]
  ring

/-- Exact completion of the square. -/
theorem relayH_completion {N : Nat} (hN : 0 < N) (a b : ℝ)
    {wstar : EVec N} (hstar : IsRelayStationary hN a b wstar)
    (w : EVec N) :
    relayH hN a b wstar - relayH hN a b w =
      (1 / 2 : ℝ) * regularizedPathQuad N (w - wstar) := by
  have hs := hstar (w - wstar)
  rw [regularizedPathBilinear_sub_right,
    regularizedPathBilinear_self, endpointForcing_sub] at hs
  have hq := regularizedPathQuad_sub_expansion N w wstar
  rw [regularizedPathBilinear_comm N w wstar] at hq
  unfold relayH
  nlinarith

theorem correctedH_completion {N : Nat} (hN : 0 < N) (a b : ℝ)
    {wstar : EVec N} (hstar : IsRelayStationary hN a b wstar)
    (w : EVec N) :
    correctedH hN a b wstar - correctedH hN a b w =
      (1 / 2 : ℝ) * regularizedPathQuad N (w - wstar) := by
  have h := relayH_completion hN a b hstar w
  unfold correctedH
  linarith

theorem correctedH_le_at_wStar {N : Nat} (hN : 0 < N) (a b : ℝ)
    (w : EVec N) :
    correctedH hN a b w ≤ correctedH hN a b (wStar hN a b) := by
  have hcomp := correctedH_completion hN a b (wStar_stationary hN a b) w
  have hq := regularizedPathQuad_nonneg N (w - wStar hN a b)
  nlinarith

/-- Quantitative uniqueness/strong-concavity gap. -/
theorem correctedH_strong_gap {N : Nat} (hN : 0 < N) (a b : ℝ)
    (w : EVec N) :
    correctedH hN a b (wStar hN a b) - correctedH hN a b w ≥
      (pathRegularization N / 2) * vecSq (w - wStar hN a b) := by
  rw [correctedH_completion hN a b (wStar_stationary hN a b)]
  have hq := regularizedPathQuad_lower N (w - wStar hN a b)
  nlinarith

theorem wStar_unique_maximizer {N : Nat} (hN : 0 < N) (a b : ℝ)
    {w : EVec N}
    (hw : correctedH hN a b w = correctedH hN a b (wStar hN a b)) :
    w = wStar hN a b := by
  have hcomp := correctedH_completion hN a b (wStar_stationary hN a b) w
  have hlower := regularizedPathQuad_lower N (w - wStar hN a b)
  have hreg := pathRegularization_pos hN
  have hsq0 : vecSq (w - wStar hN a b) = 0 := by
    have hnonneg : 0 ≤ vecSq (w - wStar hN a b) := by
      unfold vecSq NCPLVerification.vecSq
      positivity
    nlinarith
  have hz : w - wStar hN a b = 0 := by
    by_contra hne
    have hp := vecSq_pos_of_ne_zero hne
    linarith
  exact sub_eq_zero.mp hz

theorem relayH_value_at_stationary {N : Nat} (hN : 0 < N) (a b : ℝ)
    {wstar : EVec N} (hstar : IsRelayStationary hN a b wstar) :
    relayH hN a b wstar =
      (1 / 2 : ℝ) * relayScale hN * endpointForcing hN a b wstar := by
  have hs := hstar wstar
  rw [regularizedPathBilinear_self] at hs
  unfold relayH
  nlinarith

/-- Exact value of the uncorrected relay at its maximiser. -/
theorem relayH_wStar_value {N : Nat} (hN10 : 10 ≤ N) (a b : ℝ) :
    relayH (by omega : 0 < N) a b (wStar (by omega : 0 < N) a b) =
      (1 / 2 : ℝ) *
        (rho (by omega : 0 < N) * (a ^ 2 + b ^ 2) - 2 * a * b) := by
  let hN : 0 < N := by omega
  have hcross : pathB N (last hN) (first hN) = sigma hN := by
    rw [← sigma_eq_reverse_cross hN]
  have hforward : pathB N (first hN) (last hN) = sigma hN := rfl
  have hdiag := endpoint_diagonal_eq hN
  calc
    relayH hN a b (wStar hN a b) =
        (1 / 2 : ℝ) * relayScale hN *
          endpointForcing hN a b (wStar hN a b) :=
      relayH_value_at_stationary hN a b (wStar_stationary hN a b)
    _ = (1 / 2 : ℝ) * relayScale hN ^ 2 *
          (pathB N (first hN) (first hN) * (a ^ 2 + b ^ 2) -
            2 * sigma hN * a * b) := by
      unfold endpointForcing wStar
      rw [hcross, hdiag, hforward]
      ring
    _ = (1 / 2 : ℝ) *
          (rho hN * (a ^ 2 + b ^ 2) - 2 * a * b) := by
      rw [relayScale_sq hN10]
      have hs0 : sigma hN ≠ 0 := ne_of_gt (sigma_pos hN10)
      unfold rho
      field_simp [hs0]

/-- The corrected effective link is exactly `Q(a,b)=a^2-ab+b^2`. -/
theorem correctedH_wStar_value {N : Nat} (hN10 : 10 ≤ N) (a b : ℝ) :
    correctedH (by omega : 0 < N) a b
        (wStar (by omega : 0 < N) a b) =
      a ^ 2 - a * b + b ^ 2 := by
  unfold correctedH
  rw [relayH_wStar_value hN10]
  ring

theorem correctedH_argmax_and_value {N : Nat} (hN10 : 10 ≤ N) (a b : ℝ) :
    (∀ w : EVec N,
      correctedH (by omega : 0 < N) a b w ≤
        correctedH (by omega : 0 < N) a b
          (wStar (by omega : 0 < N) a b)) ∧
    correctedH (by omega : 0 < N) a b
        (wStar (by omega : 0 < N) a b) = a ^ 2 - a * b + b ^ 2 := by
  exact ⟨fun w ↦ correctedH_le_at_wStar (by omega) a b w,
    correctedH_wStar_value hN10 a b⟩

/-! ## Global strong concavity in the dual variable -/

private theorem regularizedPathQuad_convex_combo (N : Nat)
    (u v : EVec N) (t : ℝ) :
    regularizedPathQuad N (t • u + (1 - t) • v) =
      t * regularizedPathQuad N u + (1 - t) * regularizedPathQuad N v -
        t * (1 - t) * regularizedPathQuad N (u - v) := by
  rw [regularizedPathQuad_add_expansion,
    regularizedPathQuad_smul, regularizedPathQuad_smul,
    regularizedPathBilinear_smul_left,
    regularizedPathBilinear_smul_right,
    regularizedPathQuad_sub_expansion]
  ring

private theorem endpointForcing_convex_combo {N : Nat} (hN : 0 < N)
    (a b : ℝ) (u v : EVec N) (t : ℝ) :
    endpointForcing hN a b (t • u + (1 - t) • v) =
      t * endpointForcing hN a b u +
        (1 - t) * endpointForcing hN a b v := by
  rw [endpointForcing_add, endpointForcing_smul, endpointForcing_smul]

/-- Exact Jensen gap of the corrected relay. -/
theorem correctedH_jensen_identity {N : Nat} (hN : 0 < N) (a b : ℝ)
    (u v : EVec N) (t : ℝ) :
    correctedH hN a b (t • u + (1 - t) • v) =
      t * correctedH hN a b u + (1 - t) * correctedH hN a b v +
        (1 / 2 : ℝ) * t * (1 - t) * regularizedPathQuad N (u - v) := by
  unfold correctedH relayH
  rw [regularizedPathQuad_convex_combo,
    endpointForcing_convex_combo]
  ring

/-- `correctedH(a,b;·)` is `N^{-2}`-strongly concave, expressed by its
defining Jensen inequality. -/
theorem correctedH_strongConcave {N : Nat} (hN : 0 < N) (a b : ℝ)
    (u v : EVec N) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * correctedH hN a b u + (1 - t) * correctedH hN a b v +
        (pathRegularization N / 2) * t * (1 - t) * vecSq (u - v) ≤
      correctedH hN a b (t • u + (1 - t) • v) := by
  rw [correctedH_jensen_identity]
  have hcoef : 0 ≤ (1 / 2 : ℝ) * t * (1 - t) := by positivity
  have hq := regularizedPathQuad_lower N (u - v)
  have hmul := mul_le_mul_of_nonneg_left hq hcoef
  nlinarith

/-! ## Origin signs and one-coordinate causality -/

theorem correctedH_zero_dual (hN : 0 < N) (a b : ℝ) :
    correctedH hN a b (0 : EVec N) =
      (2 - rho hN) / 2 * (a ^ 2 + b ^ 2) := by
  have he : pathEnergy N (0 : EVec N) = 0 := by
    cases N <;> simp [pathEnergy]
  simp [correctedH, relayH, endpointForcing, regularizedPathQuad,
    he, vecSq, NCPLVerification.vecSq]

theorem correctedH_zero_dual_nonneg (hN : 0 < N)
    (hrho : rho hN ≤ 2) (a b : ℝ) :
    0 ≤ correctedH hN a b (0 : EVec N) := by
  rw [correctedH_zero_dual]
  positivity

/-- The origin sign required by the composite construction, discharged from
`N ≥ 10` rather than an externally supplied ratio bound. -/
theorem correctedH_zero_dual_nonneg_of_ten {N : Nat} (hN10 : 10 ≤ N)
    (a b : ℝ) :
    0 ≤ correctedH (by omega : 0 < N) a b (0 : EVec N) :=
  correctedH_zero_dual_nonneg (by omega) (rho_le_two hN10) a b

theorem correctedH_zero_primal_nonpos (hN : 0 < N) (w : EVec N) :
    correctedH hN 0 0 w ≤ 0 := by
  simp only [correctedH, relayH, endpointForcing, zero_mul, zero_sub]
  have hq := regularizedPathQuad_nonneg N w
  nlinarith

def relayGradA {N : Nat} (hN : 0 < N) (a : ℝ) (w : EVec N) : ℝ :=
  relayScale hN * w (first hN) + (2 - rho hN) * a

def relaySaddleGradW {N : Nat} (hN : 0 < N) (a b : ℝ)
    (w : EVec N) (i : Fin N) : ℝ :=
  regularizedPathCoord w i - relayScale hN * endpointSource hN a b i

def relayGradB {N : Nat} (hN : 0 < N) (b : ℝ) (w : EVec N) : ℝ :=
  -relayScale hN * w (last hN) + (2 - rho hN) * b

theorem relayGradA_zero (hN : 0 < N) {a : ℝ} {w : EVec N}
    (ha : a = 0) (hw : w (first hN) = 0) : relayGradA hN a w = 0 := by
  simp [relayGradA, ha, hw]

theorem relayGradB_zero (hN : 0 < N) {b : ℝ} {w : EVec N}
    (hb : b = 0) (hw : w (last hN) = 0) : relayGradB hN b w = 0 := by
  simp [relayGradB, hb, hw]

/-- Tridiagonal one-step causality of the middle saddle coordinates. -/
theorem relaySaddleGradW_zero_of_zero_tail {N k : Nat} (hN : 0 < N)
    (a b : ℝ) {w : EVec N} (hb : b = 0)
    (hw : ∀ i : Fin N, k ≤ i.val → w i = 0)
    (i : Fin N) (hi : k + 1 ≤ i.val) :
    relaySaddleGradW hN a b w i = 0 := by
  have hreg : regularizedPathCoord w i = 0 :=
    regularizedPathCoord_zero_of_zero_tail hw i hi
  have hfirst : i ≠ first hN := by
    intro h
    have hv := congrArg Fin.val h
    simp [first, innerFirst] at hv
    omega
  have hsource : endpointSource hN a b i = 0 := by
    simp [endpointSource, hfirst, hb]
  unfold relaySaddleGradW
  rw [hreg, hsource]
  ring

/-- Read the primal entry `a` from the joint coordinate order
`(a,w_1,...,w_N,b)`. -/
def jointA {N : Nat} (q : EVec (N + 2)) : ℝ := q ⟨0, by omega⟩

/-- Read the path block from the joint coordinate order. -/
def jointW {N : Nat} (q : EVec (N + 2)) : EVec N :=
  fun i ↦ q ⟨i.val + 1, by omega⟩

/-- Read the final primal entry `b` from the joint coordinate order. -/
def jointB {N : Nat} (q : EVec (N + 2)) : ℝ := q ⟨N + 1, by omega⟩

/-- The saddle vector field of the corrected relay, in the literal order
`(a,w_1,...,w_N,b)`. -/
def relayField {N : Nat} (hN : 0 < N) (q : EVec (N + 2)) : EVec (N + 2) :=
  fun r ↦
    if hA : r.val = 0 then
      relayGradA hN (jointA q) (jointW q)
    else if hW : r.val ≤ N then
      relaySaddleGradW hN (jointA q) (jointB q) (jointW q)
        ⟨r.val - 1, by omega⟩
    else
      relayGradB hN (jointB q) (jointW q)

/-- Prefix-support formulation of a first-order zero-chain. -/
def IsPrefixZeroChain {d : Nat} (F : EVec d → EVec d) : Prop :=
  ∀ (k : Nat) (q : EVec d),
    (∀ i : Fin d, k ≤ i.val → q i = 0) →
      ∀ r : Fin d, k + 1 ≤ r.val → F q r = 0

/-- The diagonal correction preserves support, and the tridiagonal path
operator can reveal at most one new joint coordinate.  Hence the actual
saddle field is a zero-chain in the claimed order. -/
theorem relayField_isPrefixZeroChain {N : Nat} (hN : 0 < N) :
    IsPrefixZeroChain (relayField hN) := by
  intro k q hq r hr
  unfold relayField
  split
  · omega
  · rename_i hA
    split
    · rename_i hW
      let j : Fin N := ⟨r.val - 1, by omega⟩
      change relaySaddleGradW hN (jointA q) (jointB q) (jointW q) j = 0
      by_cases hk : k = 0
      · subst k
        have ha : jointA q = 0 := by
          apply hq ⟨0, by omega⟩
          omega
        have hb : jointB q = 0 := by
          apply hq ⟨N + 1, by omega⟩
          omega
        have hw : jointW q = 0 := by
          funext i
          apply hq ⟨i.val + 1, by omega⟩
          omega
        rw [hw]
        simp [relaySaddleGradW, endpointSource, ha, hb,
          regularizedPathCoord, pathLaplacianCoord]
      · have hb : jointB q = 0 := by
          apply hq ⟨N + 1, by omega⟩
          change k ≤ N + 1
          omega
        have hw : ∀ i : Fin N, k - 1 ≤ i.val → jointW q i = 0 := by
          intro i hi
          apply hq ⟨i.val + 1, by omega⟩
          change k ≤ i.val + 1
          omega
        apply relaySaddleGradW_zero_of_zero_tail
          (k := k - 1) hN (jointA q) (jointB q) hb hw j
        dsimp [j]
        omega
    · rename_i hW
      apply relayGradB_zero hN
      · apply hq ⟨N + 1, by omega⟩
        change k ≤ N + 1
        omega
      · apply hq ⟨(last hN).val + 1, by omega⟩
        change k ≤ (last hN).val + 1
        simp [last, innerLast]
        omega

/-! ## Maximiser growth and independent block assembly -/

theorem relayScale_sq_le_ten_div {N : Nat} (hN10 : 10 ≤ N) :
    relayScale (by omega : 0 < N) ^ 2 ≤ 10 / (N : ℝ) := by
  let hN : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hspos := sigma_pos hN10
  have hslow := (sigma_bounds hN10).1
  rw [relayScale_sq hN10]
  rw [div_le_div_iff₀ hspos hNr]
  nlinarith

/-- Squared form of
`||w^star(a,b)|| <= 20 sqrt(20) N sqrt(a^2+b^2)`. -/
theorem wStar_vecSq_le {N : Nat} (hN10 : 10 ≤ N) (a b : ℝ) :
    vecSq (wStar (by omega : 0 < N) a b) ≤
      8000 * (N : ℝ) ^ 2 * (a ^ 2 + b ^ 2) := by
  let hN : 0 < N := by omega
  let NR : ℝ := N
  have hNR : 0 < NR := by
    dsimp [NR]
    exact_mod_cast hN
  have hsbound := relayScale_sq_le_ten_div hN10
  unfold vecSq NCPLVerification.vecSq
  calc
    ∑ i : Fin N, wStar hN a b i ^ 2 ≤
        ∑ _i : Fin N, 8000 * NR * (a ^ 2 + b ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      let X := pathB N i (first hN)
      let Y := pathB N i (last hN)
      have hX := innerB_first_column_bounds hN10 i
      have hY := innerB_last_column_bounds hN10 i
      have hX' :
          (N : ℝ) / 10 ≤ X ∧ X ≤ 20 * (N : ℝ) := by
        simpa [X, first, pathB] using hX
      have hY' :
          (N : ℝ) / 10 ≤ Y ∧ Y ≤ 20 * (N : ℝ) := by
        simpa [Y, last, pathB] using hY
      have h20 : 0 ≤ 20 * NR := by positivity
      have hXabs : |X| ≤ 20 * NR := by
        have hX0 : 0 ≤ X := by
          have hNr' : (0 : ℝ) < N := by exact_mod_cast hN
          nlinarith [hX'.1]
        rw [abs_of_nonneg hX0]
        simpa [NR] using hX'.2
      have hYabs : |Y| ≤ 20 * NR := by
        have hY0 : 0 ≤ Y := by
          have hNr' : (0 : ℝ) < N := by exact_mod_cast hN
          nlinarith [hY'.1]
        rw [abs_of_nonneg hY0]
        simpa [NR] using hY'.2
      have hXsq : X ^ 2 ≤ (20 * NR) ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg h20] using hXabs
      have hYsq : Y ^ 2 ≤ (20 * NR) ^ 2 := by
        rw [sq_le_sq]
        simpa [abs_of_nonneg h20] using hYabs
      have hXa := mul_le_mul_of_nonneg_right hXsq (sq_nonneg a)
      have hYb := mul_le_mul_of_nonneg_right hYsq (sq_nonneg b)
      have hsource : (X * a - Y * b) ^ 2 ≤
          800 * NR ^ 2 * (a ^ 2 + b ^ 2) := by
        have hsplit : (X * a - Y * b) ^ 2 ≤
            2 * (X * a) ^ 2 + 2 * (Y * b) ^ 2 := by
          nlinarith [sq_nonneg (X * a + Y * b)]
        nlinarith
      change (relayScale hN *
          (pathB N i (first hN) * a - pathB N i (last hN) * b)) ^ 2 ≤ _
      dsimp [X, Y] at hsource ⊢
      calc
        _ = relayScale hN ^ 2 *
            (pathB N i (first hN) * a - pathB N i (last hN) * b) ^ 2 := by
          ring
        _ ≤ (10 / NR) * (800 * NR ^ 2 * (a ^ 2 + b ^ 2)) := by
          exact mul_le_mul hsbound hsource (sq_nonneg _)
            (by positivity : 0 ≤ (10 / NR : ℝ))
        _ = 8000 * NR * (a ^ 2 + b ^ 2) := by
          field_simp
          ring
    _ = 8000 * NR ^ 2 * (a ^ 2 + b ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      dsimp [NR]
      ring

def innerComponent {m N : Nat} (hN : 0 < N)
    (a b : Fin m → ℝ) (y : Fin m → EVec N) : ℝ :=
  ∑ i : Fin m, correctedH hN (a i) (b i) (y i)

def blockWStar {m N : Nat} (hN : 0 < N)
    (a b : Fin m → ℝ) : Fin m → EVec N :=
  fun i ↦ wStar hN (a i) (b i)

theorem innerComponent_le_at_blockWStar {m N : Nat} (hN : 0 < N)
    (a b : Fin m → ℝ) (y : Fin m → EVec N) :
    innerComponent hN a b y ≤
      innerComponent hN a b (blockWStar hN a b) := by
  unfold innerComponent blockWStar
  exact Finset.sum_le_sum fun i _ ↦ correctedH_le_at_wStar hN (a i) (b i) (y i)

theorem innerComponent_blockWStar_value {m N : Nat} (hN10 : 10 ≤ N)
    (a b : Fin m → ℝ) :
    innerComponent (by omega : 0 < N) a b
        (blockWStar (by omega : 0 < N) a b) =
      ∑ i : Fin m, ((a i) ^ 2 - a i * b i + (b i) ^ 2) := by
  unfold innerComponent blockWStar
  apply Finset.sum_congr rfl
  intro i _
  exact correctedH_wStar_value hN10 (a i) (b i)

theorem blockWStar_growth {m N : Nat} (hN10 : 10 ≤ N)
    (a b : Fin m → ℝ) :
    (∑ i : Fin m, vecSq (blockWStar (by omega : 0 < N) a b i)) ≤
      8000 * (N : ℝ) ^ 2 *
        ∑ i : Fin m, ((a i) ^ 2 + (b i) ^ 2) := by
  unfold blockWStar
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ ↦ wStar_vecSq_le hN10 (a i) (b i)

end

end InnerRelay
end Simplified
end NCCLowerBound
