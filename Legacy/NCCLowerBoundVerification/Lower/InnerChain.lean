import NCCLowerBoundVerification.Lower.PathLaplacian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The concrete inner-chain block

This module formalizes the explicit quadratic block from
`def:concrete-inner` and the algebraic, local-dependence, causality, transfer,
and size portions of `lem:inner-interface` in
`Upper+Lower_unified_lower.tex`.
-/

namespace NCCLowerBoundVerification

noncomputable section

private def eDot {n : Nat} (u v : EVec n) : ℝ :=
  ∑ i : Fin n, u i * v i

/-- Polarization of `regularizedPathQuad`; this is `uᵀ Mₙ v`. -/
def regularizedPathBilinear : (n : Nat) → EVec n → EVec n → ℝ
  | 0, _, _ => 0
  | n + 1, u, v =>
      pathRegularization (n + 1) * eDot u v +
        ∑ j : Fin n,
          (u j.castSucc - u j.succ) * (v j.castSucc - v j.succ)

theorem regularizedPathBilinear_self (n : Nat) (w : EVec n) :
    regularizedPathBilinear n w w = regularizedPathQuad n w := by
  cases n with
  | zero => simp [regularizedPathBilinear, regularizedPathQuad, pathEnergy,
      vecSq, NCPLVerification.vecSq]
  | succ n =>
      simp only [regularizedPathBilinear, regularizedPathQuad, pathEnergy]
      congr 1
      · unfold eDot vecSq NCPLVerification.vecSq
        apply congrArg (pathRegularization (n + 1) * ·)
        apply Finset.sum_congr rfl
        intro i _
        ring
      · apply Finset.sum_congr rfl
        intro i _
        ring

theorem regularizedPathBilinear_comm (n : Nat) (u v : EVec n) :
    regularizedPathBilinear n u v = regularizedPathBilinear n v u := by
  cases n with
  | zero => simp [regularizedPathBilinear]
  | succ n =>
      simp only [regularizedPathBilinear]
      unfold eDot
      congr 1
      · apply congrArg (pathRegularization (n + 1) * ·)
        apply Finset.sum_congr rfl
        intro i _
        ring
      · apply Finset.sum_congr rfl
        intro i _
        ring

theorem regularizedPathBilinear_add_left (n : Nat) (u v w : EVec n) :
    regularizedPathBilinear n (u + v) w =
      regularizedPathBilinear n u w + regularizedPathBilinear n v w := by
  cases n with
  | zero => simp [regularizedPathBilinear]
  | succ n =>
      simp only [regularizedPathBilinear]
      unfold eDot
      have hdot :
          (∑ i : Fin (n + 1), (u + v) i * w i) =
            (∑ i : Fin (n + 1), u i * w i) + ∑ i : Fin (n + 1), v i * w i := by
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      have hedge :
          (∑ j : Fin n,
              ((u + v) j.castSucc - (u + v) j.succ) *
                (w j.castSucc - w j.succ)) =
            (∑ j : Fin n, (u j.castSucc - u j.succ) *
              (w j.castSucc - w j.succ)) +
            ∑ j : Fin n, (v j.castSucc - v j.succ) *
              (w j.castSucc - w j.succ) := by
        calc
          _ = ∑ j : Fin n,
              ((u j.castSucc - u j.succ) * (w j.castSucc - w j.succ) +
                (v j.castSucc - v j.succ) * (w j.castSucc - w j.succ)) := by
                  apply Finset.sum_congr rfl
                  intro j _
                  simp only [Pi.add_apply]
                  ring
          _ = _ := Finset.sum_add_distrib
      rw [hdot, hedge]
      ring

theorem regularizedPathBilinear_smul_left (n : Nat) (c : ℝ) (u v : EVec n) :
    regularizedPathBilinear n (c • u) v =
      c * regularizedPathBilinear n u v := by
  cases n with
  | zero => simp [regularizedPathBilinear]
  | succ n =>
      simp only [regularizedPathBilinear]
      unfold eDot
      have hdot :
          (∑ i : Fin (n + 1), (c • u) i * v i) =
            c * ∑ i : Fin (n + 1), u i * v i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      have hedge :
          (∑ j : Fin n,
              ((c • u) j.castSucc - (c • u) j.succ) *
                (v j.castSucc - v j.succ)) =
            c * ∑ j : Fin n, (u j.castSucc - u j.succ) *
              (v j.castSucc - v j.succ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      rw [hdot, hedge]
      ring

theorem regularizedPathBilinear_add_right (n : Nat) (u v w : EVec n) :
    regularizedPathBilinear n u (v + w) =
      regularizedPathBilinear n u v + regularizedPathBilinear n u w := by
  rw [regularizedPathBilinear_comm, regularizedPathBilinear_add_left]
  rw [regularizedPathBilinear_comm n v u, regularizedPathBilinear_comm n w u]

theorem regularizedPathBilinear_smul_right (n : Nat) (c : ℝ) (u v : EVec n) :
    regularizedPathBilinear n u (c • v) =
      c * regularizedPathBilinear n u v := by
  rw [regularizedPathBilinear_comm, regularizedPathBilinear_smul_left]
  rw [regularizedPathBilinear_comm n v u]

private theorem regularizedPathBilinear_sub_left (n : Nat) (u v w : EVec n) :
    regularizedPathBilinear n (u - v) w =
      regularizedPathBilinear n u w - regularizedPathBilinear n v w := by
  rw [sub_eq_add_neg, regularizedPathBilinear_add_left,
    ← neg_one_smul ℝ v, regularizedPathBilinear_smul_left]
  ring

private theorem regularizedPathBilinear_sub_right (n : Nat) (u v w : EVec n) :
    regularizedPathBilinear n u (v - w) =
      regularizedPathBilinear n u v - regularizedPathBilinear n u w := by
  rw [regularizedPathBilinear_comm, regularizedPathBilinear_sub_left]
  rw [regularizedPathBilinear_comm n v u, regularizedPathBilinear_comm n w u]

/-- The exact quadratic expansion used in the strong-concavity proof. -/
theorem regularizedPathQuad_sub_expansion (n : Nat) (u v : EVec n) :
    regularizedPathQuad n (u - v) =
      regularizedPathQuad n u + regularizedPathQuad n v -
        2 * regularizedPathBilinear n u v := by
  rw [← regularizedPathBilinear_self,
    regularizedPathBilinear_sub_left,
    regularizedPathBilinear_sub_right n u u v,
    regularizedPathBilinear_sub_right n v u v,
    regularizedPathBilinear_self, regularizedPathBilinear_self,
    regularizedPathBilinear_comm n v u]
  ring

theorem regularizedPathQuad_add_expansion (n : Nat) (u v : EVec n) :
    regularizedPathQuad n (u + v) =
      regularizedPathQuad n u + regularizedPathQuad n v +
        2 * regularizedPathBilinear n u v := by
  rw [← regularizedPathBilinear_self, regularizedPathBilinear_add_left,
    regularizedPathBilinear_add_right n u u v,
    regularizedPathBilinear_add_right n v u v, regularizedPathBilinear_self,
    regularizedPathBilinear_self, regularizedPathBilinear_comm n v u]
  ring

theorem regularizedPathQuad_smul (n : Nat) (c : ℝ) (u : EVec n) :
    regularizedPathQuad n (c • u) = c ^ 2 * regularizedPathQuad n u := by
  rw [← regularizedPathBilinear_self, regularizedPathBilinear_smul_left,
    regularizedPathBilinear_smul_right, regularizedPathBilinear_self]
  ring

/-- First and last coordinate indices, with positivity carried explicitly. -/
def innerFirst {n : Nat} (hn : 0 < n) : Fin n := ⟨0, hn⟩

def innerLast {n : Nat} (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

/-- The forcing `a e₁ - b/2 eₙ`, represented coordinatewise. -/
def innerSource {n : Nat} (hn : 0 < n) (a b : ℝ) : EVec n :=
  Pi.single (innerFirst hn) a - Pi.single (innerLast hn) (b / 2)

/-- The paper's factor `sqrt (Cₙ / n)`. -/
def innerScale (n : Nat) (C : ℝ) : ℝ :=
  Real.sqrt (C / (n : ℝ))

/-- Pairing with the endpoint forcing `a e₁ - b/2 eₙ`. -/
def innerForcing {n : Nat} (hn : 0 < n) (a b : ℝ) (w : EVec n) : ℝ :=
  a * w (innerFirst hn) - b / 2 * w (innerLast hn)

/-- Definition `def:concrete-inner`, in the matrix-free quadratic-form form. -/
def innerChain {n : Nat} (hn : 0 < n) (C a b : ℝ) (w : EVec n) : ℝ :=
  -(1 / 2 : ℝ) * regularizedPathQuad n w +
    innerScale n C * innerForcing hn a b w

/-- The displayed `a` component of the saddle vector field. -/
def innerGradA {n : Nat} (hn : 0 < n) (C : ℝ) (w : EVec n) : ℝ :=
  innerScale n C * w (innerFirst hn)

/-- The displayed `b` component of the saddle vector field. -/
def innerGradB {n : Nat} (hn : 0 < n) (C : ℝ) (w : EVec n) : ℝ :=
  -(1 / 2 : ℝ) * innerScale n C * w (innerLast hn)

/-- The coordinate formula for `-∇_w h`. -/
def innerSaddleGradW {n : Nat} (hn : 0 < n) (C a b : ℝ)
    (w : EVec n) (i : Fin n) : ℝ :=
  regularizedPathCoord w i - innerScale n C * innerSource hn a b i

theorem innerChain_zero_dual {n : Nat} (hn : 0 < n) (C a b : ℝ) :
    innerChain hn C a b 0 = 0 := by
  have henergy : pathEnergy n (0 : EVec n) = 0 := by
    cases n <;> simp [pathEnergy]
  simp [innerChain, innerForcing, regularizedPathQuad, henergy, vecSq,
    NCPLVerification.vecSq]

theorem innerChain_zero_primal_nonpos {n : Nat} (hn : 0 < n)
    (C : ℝ) (w : EVec n) : innerChain hn C 0 0 w ≤ 0 := by
  simp only [innerChain, innerForcing, zero_mul]
  have hq := regularizedPathQuad_nonneg n w
  nlinarith

theorem hasDerivAt_innerChain_a {n : Nat} (hn : 0 < n)
    (C a b : ℝ) (w : EVec n) :
    HasDerivAt (fun q : ℝ ↦ innerChain hn C q b w) (innerGradA hn C w) a := by
  unfold innerChain innerGradA
  unfold innerForcing
  convert (hasDerivAt_const a (-(1 / 2 : ℝ) * regularizedPathQuad n w)).add
    ((((hasDerivAt_id a).mul_const (w (innerFirst hn))).sub
      (hasDerivAt_const a (b / 2 * w (innerLast hn)))).const_mul
        (innerScale n C)) using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext q
    simp only [Pi.add_apply, Pi.sub_apply, id_eq]
  · ring

theorem hasDerivAt_innerChain_b {n : Nat} (hn : 0 < n)
    (C a b : ℝ) (w : EVec n) :
    HasDerivAt (fun q : ℝ ↦ innerChain hn C a q w) (innerGradB hn C w) b := by
  unfold innerChain innerGradB
  unfold innerForcing
  convert (hasDerivAt_const b (-(1 / 2 : ℝ) * regularizedPathQuad n w)).add
    (((hasDerivAt_const b (a * w (innerFirst hn))).sub
      (((hasDerivAt_id b).div_const 2).mul_const (w (innerLast hn)))).const_mul
        (innerScale n C)) using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext q
    simp only [Pi.add_apply, Pi.sub_apply, id_eq]
  · ring

private theorem innerForcing_sub {n : Nat} (hn : 0 < n) (a b : ℝ)
    (u v : EVec n) :
    innerForcing hn a b (u - v) =
      innerForcing hn a b u - innerForcing hn a b v := by
  unfold innerForcing
  simp only [Pi.sub_apply]
  ring

private theorem innerForcing_add {n : Nat} (hn : 0 < n) (a b : ℝ)
    (u v : EVec n) :
    innerForcing hn a b (u + v) =
      innerForcing hn a b u + innerForcing hn a b v := by
  unfold innerForcing
  simp only [Pi.add_apply]
  ring

private theorem innerForcing_smul {n : Nat} (hn : 0 < n) (a b c : ℝ)
    (u : EVec n) :
    innerForcing hn a b (c • u) = c * innerForcing hn a b u := by
  unfold innerForcing
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Exact quadratic expansion along an arbitrary dual direction. -/
theorem innerChain_line_expansion {n : Nat} (hn : 0 < n) (C a b : ℝ)
    (w d : EVec n) (t : ℝ) :
    innerChain hn C a b (w + t • d) =
      innerChain hn C a b w +
        t * (-regularizedPathBilinear n w d +
          innerScale n C * innerForcing hn a b d) -
        (1 / 2 : ℝ) * t ^ 2 * regularizedPathQuad n d := by
  rw [innerChain, regularizedPathQuad_add_expansion,
    regularizedPathQuad_smul, regularizedPathBilinear_smul_right,
    innerForcing_add, innerForcing_smul]
  unfold innerChain
  ring

/-- Actual directional derivative of the concrete block in every dual
direction. -/
theorem hasDerivAt_innerChain_dual_line_zero {n : Nat} (hn : 0 < n)
    (C a b : ℝ) (w d : EVec n) :
    HasDerivAt (fun t : ℝ ↦ innerChain hn C a b (w + t • d))
      (-regularizedPathBilinear n w d +
        innerScale n C * innerForcing hn a b d) 0 := by
  let A := -regularizedPathBilinear n w d +
    innerScale n C * innerForcing hn a b d
  let Q := regularizedPathQuad n d
  have hpoly : HasDerivAt
      (fun t : ℝ ↦ innerChain hn C a b w + t * A - (1 / 2 : ℝ) * t ^ 2 * Q)
      A 0 := by
    convert ((hasDerivAt_const (0 : ℝ) (innerChain hn C a b w)).add
      ((hasDerivAt_id (0 : ℝ)).mul_const A)).sub
        ((((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (1 / 2 : ℝ)).mul_const Q) using 1
    all_goals try { apply AddCommGroup.ext <;> rfl }
    all_goals try { apply Module.ext <;> rfl }
    · funext t
      simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp [A, Q]
  have heq : (fun t : ℝ ↦ innerChain hn C a b (w + t • d)) =
      (fun t : ℝ ↦ innerChain hn C a b w + t * A - (1 / 2 : ℝ) * t ^ 2 * Q) := by
    funext t
    exact innerChain_line_expansion hn C a b w d t
  rw [heq]
  exact hpoly

/-- First-order equation for the unique unconstrained dual maximizer.  This
is the matrix-free form of `Mₙ w⋆ = sqrt(Cₙ/n) (a e₁ - b/2 eₙ)`. -/
def IsInnerStationary {n : Nat} (hn : 0 < n) (C a b : ℝ)
    (wstar : EVec n) : Prop :=
  ∀ d : EVec n,
    regularizedPathBilinear n wstar d =
      innerScale n C * innerForcing hn a b d

/-- Exact completion of the square around any solution of the first-order
equation. -/
theorem innerChain_completion {n : Nat} (hn : 0 < n) (C a b : ℝ)
    {wstar : EVec n} (hstar : IsInnerStationary hn C a b wstar)
    (w : EVec n) :
    innerChain hn C a b wstar - innerChain hn C a b w =
      (1 / 2 : ℝ) * regularizedPathQuad n (w - wstar) := by
  have hs := hstar (w - wstar)
  rw [regularizedPathBilinear_sub_right, regularizedPathBilinear_self,
    innerForcing_sub] at hs
  have hq := regularizedPathQuad_sub_expansion n w wstar
  rw [regularizedPathBilinear_comm n w wstar] at hq
  unfold innerChain
  nlinarith

/-- The stationary point is a global maximizer. -/
theorem innerChain_le_at_stationary {n : Nat} (hn : 0 < n) (C a b : ℝ)
    {wstar : EVec n} (hstar : IsInnerStationary hn C a b wstar)
    (w : EVec n) :
    innerChain hn C a b w ≤ innerChain hn C a b wstar := by
  have hcomp := innerChain_completion hn C a b hstar w
  have hq := regularizedPathQuad_nonneg n (w - wstar)
  nlinarith

/-- Quantitative `n⁻²` strong-concavity gap from item (i). -/
theorem innerChain_strong_concavity_gap {n : Nat} (hn : 0 < n)
    (C a b : ℝ) {wstar : EVec n}
    (hstar : IsInnerStationary hn C a b wstar) (w : EVec n) :
    innerChain hn C a b wstar - innerChain hn C a b w ≥
      (pathRegularization n / 2) * vecSq (w - wstar) := by
  rw [innerChain_completion hn C a b hstar]
  have hq := regularizedPathQuad_lower n (w - wstar)
  nlinarith

/-- Dimension-explicit curvature bounds for the dual Hessian block. -/
theorem inner_dual_curvature_bounds (n : Nat) (w : EVec n) :
    pathRegularization n * vecSq w ≤ regularizedPathQuad n w ∧
      regularizedPathQuad n w ≤ (4 + pathRegularization n) * vecSq w := by
  exact ⟨regularizedPathQuad_lower n w, regularizedPathQuad_upper n w⟩

/-- In the paper's regime `n ≥ 10`, the upper curvature coefficient is at
most `4.01`, hence numerical and dimension-independent. -/
theorem inner_dual_curvature_upper_of_ten_le {n : Nat} (hn : 10 ≤ n)
    (w : EVec n) :
    regularizedPathQuad n w ≤ (401 / 100 : ℝ) * vecSq w := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 10) hn)
  have hreg : pathRegularization n ≤ (1 / 100 : ℝ) := by
    unfold pathRegularization
    rw [div_le_iff₀ (sq_pos_of_pos hnpos)]
    have hnreal : (10 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [sq_nonneg ((n : ℝ) - 10)]
  have hq := regularizedPathQuad_upper n w
  have hvec : 0 ≤ vecSq w := by
    unfold vecSq NCPLVerification.vecSq
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  nlinarith

/-- Quadratic form of the full joint Hessian in a direction `(da,db,dw)`. -/
def innerJointHessianQuad {n : Nat} (hn : 0 < n) (C da db : ℝ)
    (dw : EVec n) : ℝ :=
  -regularizedPathQuad n dw +
    2 * innerScale n C * da * dw (innerFirst hn) -
      innerScale n C * db * dw (innerLast hn)

private theorem coordinate_sq_le_vecSq {n : Nat} (w : EVec n) (i : Fin n) :
    w i ^ 2 ≤ vecSq w := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (w j)) (Finset.mem_univ i)

private theorem two_abs_mul_le_sq_add_sq (x y : ℝ) :
    2 * |x * y| ≤ x ^ 2 + y ^ 2 := by
  rw [abs_mul]
  nlinarith [sq_nonneg (|x| - |y|), sq_abs x, sq_abs y]

/-- Numerical joint-Hessian bound corresponding to item (i).  It is stated
as the symmetric quadratic-form estimate equivalent to the operator bound. -/
theorem inner_joint_hessian_bound {n : Nat} (hn : 10 ≤ n) {C : ℝ}
    (hC : 0 ≤ C) (hCupper : C ≤ 120) (da db : ℝ) (dw : EVec n) :
    |innerJointHessianQuad (by omega : 0 < n) C da db dw| ≤
      12 * (da ^ 2 + db ^ 2 + vecSq dw) := by
  let hnpos : 0 < n := by omega
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsquare : innerScale n C ^ 2 = C / (n : ℝ) := by
    unfold innerScale
    rw [Real.sq_sqrt]
    exact div_nonneg hC hnreal.le
  have hsbound : innerScale n C ^ 2 ≤ 12 := by
    rw [hsquare, div_le_iff₀ hnreal]
    have hn10 : (10 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hq0 := regularizedPathQuad_nonneg n dw
  have hq := inner_dual_curvature_upper_of_ten_le hn dw
  have hw0 : 0 ≤ vecSq dw := by
    unfold vecSq NCPLVerification.vecSq
    exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hwfirst := coordinate_sq_le_vecSq dw (innerFirst hnpos)
  have hwlast := coordinate_sq_le_vecSq dw (innerLast hnpos)
  have ha0 := sq_nonneg da
  have hb0 := sq_nonneg db
  have hA0 := two_abs_mul_le_sq_add_sq (innerScale n C * da)
    (dw (innerFirst hnpos))
  have hB0 := two_abs_mul_le_sq_add_sq (innerScale n C * db)
    (dw (innerLast hnpos))
  have hA : |2 * innerScale n C * da * dw (innerFirst hnpos)| ≤
      12 * da ^ 2 + vecSq dw := by
    rw [show 2 * innerScale n C * da * dw (innerFirst hnpos) =
      2 * ((innerScale n C * da) * dw (innerFirst hnpos)) by ring,
      abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hscaleA := mul_le_mul_of_nonneg_right hsbound ha0
    nlinarith
  have hB : |innerScale n C * db * dw (innerLast hnpos)| ≤
      6 * db ^ 2 + (1 / 2 : ℝ) * vecSq dw := by
    have hscaleB := mul_le_mul_of_nonneg_right hsbound hb0
    rw [show innerScale n C * db * dw (innerLast hnpos) =
      (innerScale n C * db) * dw (innerLast hnpos) by ring]
    nlinarith
  unfold innerJointHessianQuad
  calc
    |-regularizedPathQuad n dw +
        2 * innerScale n C * da * dw (innerFirst hnpos) -
          innerScale n C * db * dw (innerLast hnpos)| ≤
      |-regularizedPathQuad n dw +
          2 * innerScale n C * da * dw (innerFirst hnpos)| +
        |innerScale n C * db * dw (innerLast hnpos)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (-regularizedPathQuad n dw +
          2 * innerScale n C * da * dw (innerFirst hnpos)) 0
          (innerScale n C * db * dw (innerLast hnpos))
    _ ≤ (|-regularizedPathQuad n dw| +
          |2 * innerScale n C * da * dw (innerFirst hnpos)|) +
        |innerScale n C * db * dw (innerLast hnpos)| := by
      simpa only [add_comm, add_left_comm, add_assoc] using
        add_le_add_right
          (abs_add_le (-regularizedPathQuad n dw)
            (2 * innerScale n C * da * dw (innerFirst hnpos)))
          |innerScale n C * db * dw (innerLast hnpos)|
    _ ≤ 12 * (da ^ 2 + db ^ 2 + vecSq dw) := by
      rw [abs_neg, abs_of_nonneg hq0]
      nlinarith

private theorem vecSq_eq_zero_iff {n : Nat} (w : EVec n) :
    vecSq w = 0 ↔ w = 0 := by
  constructor
  · intro hw
    funext i
    have hterm : w i ^ 2 ≤ vecSq w := by
      unfold vecSq NCPLVerification.vecSq
      exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (w j)) (Finset.mem_univ i)
    have : w i ^ 2 = 0 := by nlinarith [sq_nonneg (w i)]
    exact sq_eq_zero_iff.mp this
  · rintro rfl
    simp [vecSq, NCPLVerification.vecSq]

/-- Positivity of the regularization makes the maximizer unique. -/
theorem innerChain_unique_maximizer {n : Nat} (hn : 0 < n) (C a b : ℝ)
    {wstar : EVec n} (hstar : IsInnerStationary hn C a b wstar)
    {w : EVec n} (hw : innerChain hn C a b wstar = innerChain hn C a b w) :
    w = wstar := by
  have hcomp := innerChain_completion hn C a b hstar w
  have hreg := regularizedPathQuad_lower n (w - wstar)
  have hregpos := pathRegularization_pos hn
  have hqzero : regularizedPathQuad n (w - wstar) = 0 := by nlinarith
  have hvec : vecSq (w - wstar) = 0 := by
    have hnonneg : 0 ≤ vecSq (w - wstar) := by
      unfold vecSq NCPLVerification.vecSq
      exact Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    nlinarith
  have hzero := (vecSq_eq_zero_iff (w - wstar)).mp hvec
  exact sub_eq_zero.mp hzero

/-- At a stationary point the maximized value is one half of the endpoint
forcing pairing, as in the substitution step of item (ii). -/
theorem innerChain_value_at_stationary {n : Nat} (hn : 0 < n) (C a b : ℝ)
    {wstar : EVec n} (hstar : IsInnerStationary hn C a b wstar) :
    innerChain hn C a b wstar =
      (1 / 2 : ℝ) * innerScale n C * innerForcing hn a b wstar := by
  have hs := hstar wstar
  rw [regularizedPathBilinear_self] at hs
  unfold innerChain
  nlinarith

/-- The first saddle component vanishes at the full origin. -/
theorem innerGradA_zero (n : Nat) (hn : 0 < n) (C : ℝ) :
    innerGradA hn C (0 : EVec n) = 0 := by
  simp [innerGradA]

/-- The last saddle component vanishes whenever the last dual coordinate has
not yet been revealed. -/
theorem innerGradB_eq_zero_of_last_eq_zero {n : Nat} (hn : 0 < n) (C : ℝ)
    {w : EVec n} (hw : w (innerLast hn) = 0) : innerGradB hn C w = 0 := by
  simp [innerGradB, hw]

/-- Local dependence of the dual saddle field: coordinate `i` reads only
itself and its two path neighbors (the endpoint forcing is independent of
`w`). -/
theorem innerSaddleGradW_eq_of_local {n : Nat} (hn : 0 < n) (C a b : ℝ)
    {w v : EVec n} (i : Fin n)
    (hself : w i = v i)
    (hprev : ∀ h : 0 < i.val,
      w ⟨i.val - 1, by omega⟩ = v ⟨i.val - 1, by omega⟩)
    (hnext : ∀ h : i.val + 1 < n,
      w ⟨i.val + 1, h⟩ = v ⟨i.val + 1, h⟩) :
    innerSaddleGradW hn C a b w i = innerSaddleGradW hn C a b v i := by
  unfold innerSaddleGradW
  rw [regularizedPathCoord_eq_of_local i hself hprev hnext]

/-- Tail causality: if dual coordinates from `k` onward and the unrevealed
exit coordinate `b` vanish, then field coordinates from `k+1` onward vanish.
This is the tridiagonal certificate behind the order
`(a,w₁,…,wₙ,b)`. -/
theorem innerSaddleGradW_zero_of_zero_tail {n k : Nat} (hn : 0 < n)
    (C a b : ℝ) {w : EVec n} (hb : b = 0)
    (hw : ∀ i : Fin n, k ≤ i.val → w i = 0)
    (i : Fin n) (hi : k + 1 ≤ i.val) :
    innerSaddleGradW hn C a b w i = 0 := by
  have hreg : regularizedPathCoord w i = 0 :=
    regularizedPathCoord_zero_of_zero_tail hw i hi
  have hfirst : i ≠ innerFirst hn := by
    intro h
    have hval := congrArg Fin.val h
    simp [innerFirst] at hval
    omega
  have hsource : innerSource hn a b i = 0 := by
    simp [innerSource, hfirst, hb]
  unfold innerSaddleGradW
  rw [hreg, hsource]
  ring

/-- The concrete matrix `Mₙ`, defined from the verified bilinear form. -/
def innerM (n : Nat) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ regularizedPathBilinear n (Pi.single i 1) (Pi.single j 1)

/-- `Bₙ = Mₙ⁻¹` from `def:concrete-inner`. -/
def innerB (n : Nat) : Matrix (Fin n) (Fin n) ℝ :=
  (innerM n)⁻¹

theorem innerM_symmetric (n : Nat) : Matrix.transpose (innerM n) = innerM n := by
  ext i j
  simp only [Matrix.transpose_apply, innerM]
  exact regularizedPathBilinear_comm n _ _

theorem innerB_symmetric (n : Nat) : Matrix.transpose (innerB n) = innerB n := by
  unfold innerB
  rw [Matrix.transpose_nonsing_inv, innerM_symmetric]

theorem innerB_apply_comm (n : Nat) (i j : Fin n) :
    innerB n i j = innerB n j i := by
  have h := congrFun (congrFun (innerB_symmetric n) j) i
  simpa only [Matrix.transpose_apply] using h

/-- `Cₙ = 12 n / (Bₙ)_{n1}`. -/
def innerC {n : Nat} (hn : 0 < n) : ℝ :=
  12 * (n : ℝ) / innerB n (innerLast hn) (innerFirst hn)

def innerC1 {n : Nat} (hn : 0 < n) : ℝ :=
  innerC hn *
    (innerB n (innerLast hn) (innerFirst hn) -
      innerB n (innerFirst hn) (innerFirst hn)) / (2 * (n : ℝ))

def innerC2 {n : Nat} (hn : 0 < n) : ℝ :=
  innerC hn *
    (innerB n (innerLast hn) (innerFirst hn) -
      innerB n (innerFirst hn) (innerFirst hn)) / (8 * (n : ℝ))

/-- The quadratic value obtained by substituting
`w⋆ = sqrt(Cₙ/n) Bₙ(a e₁-b eₙ/2)`. -/
def innerInverseValue {n : Nat} (hn : 0 < n) (a b : ℝ) : ℝ :=
  innerC hn / (2 * (n : ℝ)) *
    (innerB n (innerFirst hn) (innerFirst hn) * a ^ 2 -
      (innerB n (innerFirst hn) (innerLast hn) +
        innerB n (innerLast hn) (innerFirst hn)) / 2 * a * b +
      innerB n (innerLast hn) (innerLast hn) / 4 * b ^ 2)

/-- The explicit unconstrained candidate
`sqrt(Cₙ/n) Bₙ(a e₁-b eₙ/2)`. -/
def innerMaximizer {n : Nat} (hn : 0 < n) (a b : ℝ) : EVec n :=
  fun i ↦ innerScale n (innerC hn) *
    (innerB n i (innerFirst hn) * a -
      innerB n i (innerLast hn) * (b / 2))

theorem innerMaximizer_zero {n : Nat} (hn : 0 < n) :
    innerMaximizer hn 0 0 = 0 := by
  funext i
  simp [innerMaximizer]

/-- Substitution of the explicit candidate gives the inverse quadratic value.
The nonnegativity premise is discharged by the endpoint Green-function
lower bound below. -/
theorem innerChain_value_at_explicit_maximizer {n : Nat} (hn : 0 < n)
    (hC : 0 ≤ innerC hn) (a b : ℝ)
    (hstationary : IsInnerStationary hn (innerC hn) a b
      (innerMaximizer hn a b)) :
    innerChain hn (innerC hn) a b (innerMaximizer hn a b) =
      innerInverseValue hn a b := by
  rw [innerChain_value_at_stationary hn (innerC hn) a b hstationary]
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsquare : innerScale n (innerC hn) ^ 2 = innerC hn / (n : ℝ) := by
    unfold innerScale
    rw [Real.sq_sqrt]
    exact div_nonneg hC hnreal.le
  unfold innerForcing innerMaximizer innerInverseValue
  rw [innerB_apply_comm n (innerFirst hn) (innerLast hn)]
  calc
    (1 / 2 : ℝ) * innerScale n (innerC hn) *
        (a * (innerScale n (innerC hn) *
            (innerB n (innerFirst hn) (innerFirst hn) * a -
              innerB n (innerLast hn) (innerFirst hn) * (b / 2))) -
          b / 2 * (innerScale n (innerC hn) *
            (innerB n (innerLast hn) (innerFirst hn) * a -
              innerB n (innerLast hn) (innerLast hn) * (b / 2)))) =
      (1 / 2 : ℝ) * innerScale n (innerC hn) ^ 2 *
        (innerB n (innerFirst hn) (innerFirst hn) * a ^ 2 -
          (innerB n (innerLast hn) (innerFirst hn) +
            innerB n (innerLast hn) (innerFirst hn)) / 2 * a * b +
          innerB n (innerLast hn) (innerLast hn) / 4 * b ^ 2) := by ring
    _ = innerC hn / (2 * (n : ℝ)) *
        (innerB n (innerFirst hn) (innerFirst hn) * a ^ 2 -
          (innerB n (innerLast hn) (innerFirst hn) +
            innerB n (innerLast hn) (innerFirst hn)) / 2 * a * b +
          innerB n (innerLast hn) (innerLast hn) / 4 * b ^ 2) := by
      rw [hsquare]
      ring

/-- Pure normalization algebra for item (ii).  The three hypotheses isolate
the inverse-matrix facts used in the TeX proof: nonzero endpoint Green entry,
symmetry, and reversal symmetry. -/
theorem inner_coefficients_transfer {n : Nat} (hn : 0 < n)
    (hcross : innerB n (innerLast hn) (innerFirst hn) ≠ 0)
    (hsymDiag : innerB n (innerLast hn) (innerLast hn) =
      innerB n (innerFirst hn) (innerFirst hn))
    (a b : ℝ) :
    innerInverseValue hn a b + innerC1 hn * a ^ 2 + innerC2 hn * b ^ 2 =
      6 * (a - b / 2) ^ 2 := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  unfold innerInverseValue innerC1 innerC2 innerC
  rw [innerB_apply_comm n (innerFirst hn) (innerLast hn), hsymDiag]
  field_simp [hn0, hcross]
  ring

/-- Full algebraic transfer once the explicit inverse candidate is certified
as solving the first-order equation. -/
theorem innerChain_explicit_transfer {n : Nat} (hn : 0 < n)
    (hC : 0 ≤ innerC hn)
    (hstationary : ∀ a b,
      IsInnerStationary hn (innerC hn) a b (innerMaximizer hn a b))
    (hcross : innerB n (innerLast hn) (innerFirst hn) ≠ 0)
    (hsymDiag : innerB n (innerLast hn) (innerLast hn) =
      innerB n (innerFirst hn) (innerFirst hn))
    (a b : ℝ) :
    innerChain hn (innerC hn) a b (innerMaximizer hn a b) +
        innerC1 hn * a ^ 2 + innerC2 hn * b ^ 2 =
      6 * (a - b / 2) ^ 2 := by
  rw [innerChain_value_at_explicit_maximizer hn hC a b (hstationary a b)]
  exact inner_coefficients_transfer hn hcross hsymDiag a b

/-- The cited lower/upper endpoint Green-function estimates immediately make
`Cₙ` a positive numerical constant. -/
theorem innerC_bounds_of_endpoint_bounds {n : Nat} (hn : 0 < n)
    (hlower : (n : ℝ) / 10 ≤ innerB n (innerLast hn) (innerFirst hn))
    (hupper : innerB n (innerLast hn) (innerFirst hn) ≤ 20 * (n : ℝ)) :
    (3 / 5 : ℝ) ≤ innerC hn ∧ innerC hn ≤ 120 := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hcrosspos : 0 < innerB n (innerLast hn) (innerFirst hn) := by
    nlinarith
  constructor
  · unfold innerC
    rw [le_div_iff₀ hcrosspos]
    nlinarith
  · unfold innerC
    rw [div_le_iff₀ hcrosspos]
    nlinarith

/-- Item (iii), reduced to the two inverse-column bounds quoted in the TeX.
The numerical constant `96000` is deliberately coarse but uniform in `n`. -/
theorem innerMaximizer_size_of_column_bounds {n : Nat} (hn : 0 < n)
    (hC : 0 ≤ innerC hn ∧ innerC hn ≤ 120)
    (hfirst : ∀ i : Fin n,
      |innerB n i (innerFirst hn)| ≤ 20 * (n : ℝ))
    (hlast : ∀ i : Fin n,
      |innerB n i (innerLast hn)| ≤ 20 * (n : ℝ))
    (a b : ℝ) :
    vecSq (innerMaximizer hn a b) ≤
      96000 * (n : ℝ) ^ 2 * (a ^ 2 + b ^ 2) := by
  let N : ℝ := n
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast hn
  have hsquare : innerScale n (innerC hn) ^ 2 = innerC hn / N := by
    unfold innerScale N
    rw [Real.sq_sqrt]
    exact div_nonneg hC.1 hN.le
  have hsbound : innerScale n (innerC hn) ^ 2 ≤ 120 / N := by
    rw [hsquare]
    exact (div_le_div_iff_of_pos_right hN).2 hC.2
  unfold vecSq NCPLVerification.vecSq
  calc
    ∑ i : Fin n, innerMaximizer hn a b i ^ 2 ≤
        ∑ _i : Fin n, 96000 * N * (a ^ 2 + b ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      let X := innerB n i (innerFirst hn)
      let Y := innerB n i (innerLast hn)
      have hN20 : 0 ≤ 20 * N := by positivity
      have hXsq : X ^ 2 ≤ (20 * N) ^ 2 := by
        rw [sq_le_sq]
        simpa [X, abs_of_nonneg hN20] using hfirst i
      have hYsq : Y ^ 2 ≤ (20 * N) ^ 2 := by
        rw [sq_le_sq]
        simpa [Y, abs_of_nonneg hN20] using hlast i
      have hXa := mul_le_mul_of_nonneg_right hXsq (sq_nonneg a)
      have hYb := mul_le_mul_of_nonneg_right hYsq (sq_nonneg b)
      have hsource : (X * a - Y * (b / 2)) ^ 2 ≤
          800 * N ^ 2 * (a ^ 2 + b ^ 2) := by
        have hsplit : (X * a - Y * (b / 2)) ^ 2 ≤
            2 * (X * a) ^ 2 + 2 * (Y * (b / 2)) ^ 2 := by
          nlinarith [sq_nonneg (X * a + Y * (b / 2))]
        nlinarith
      have hmul := mul_le_mul hsbound hsource (sq_nonneg _)
        (by positivity : 0 ≤ (120 / N : ℝ))
      change (innerScale n (innerC hn) *
          (innerB n i (innerFirst hn) * a -
            innerB n i (innerLast hn) * (b / 2))) ^ 2 ≤ _
      dsimp [X, Y] at hsource ⊢
      calc
        _ = innerScale n (innerC hn) ^ 2 *
            (innerB n i (innerFirst hn) * a -
              innerB n i (innerLast hn) * (b / 2)) ^ 2 := by ring
        _ ≤ (120 / N) * (800 * N ^ 2 * (a ^ 2 + b ^ 2)) := by
          exact mul_le_mul hsbound hsource (sq_nonneg _)
            (by positivity : 0 ≤ (120 / N : ℝ))
        _ = 96000 * N * (a ^ 2 + b ^ 2) := by
          field_simp
          ring
    _ = 96000 * N ^ 2 * (a ^ 2 + b ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      dsimp [N]
      ring

end

end NCCLowerBoundVerification
