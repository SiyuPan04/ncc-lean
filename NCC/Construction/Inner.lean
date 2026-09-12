import NCCLowerBound.Simplified.InnerFiniteBall
import NCCLowerBound.Simplified.CompositeSmoothnessAssembly

/-!
# Current manuscript: the exact inner chain

This file restates the definitions of `A_N`, `M_N`, `B_N`, `k_N`, `c_N`,
`H`, and the finite-ball value from `main.tex` in the current namespace.
The correspondence to the vendored proofs is proved as equality of the
actual functions, before any analytic theorem is transported. No property
of the inner chain is taken as an assumption.

Euclidean norms below are `sqrt (sum coordinates squared)`. The inherited
function-space norm is not used for dimension-free estimates. The sharp
numerical choice `c_H = 6` is established below by weighted square estimates.
-/

namespace NCC.Construction.Inner

noncomputable section

open scoped BigOperators
open NCCLowerBoundVerification

namespace Old
export NCCLowerBound.Simplified.InnerRelay
  (pathA pathM pathB first last sigma rho relayScale endpointSource endpointForcing
   correctedH wStar jointA jointW jointB relayField IsPrefixZeroChain)
end Old

abbrev Vec (n : ℕ) := NCCLowerBoundVerification.EVec n

/-- Euclidean norm, explicitly distinguished from the function-space norm. -/
def norm₂ {n : ℕ} (w : Vec n) : ℝ := Real.sqrt (vecSq w)

/-- The path Laplacian. The action and quadratic-form correspondence are below. -/
def A (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := Old.pathA N

/-- `M_N = N⁻² I + A_N`. -/
def M (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (1 / (N : ℝ) ^ 2) • (1 : Matrix (Fin N) (Fin N) ℝ) + A N

/-- `B_N = M_N⁻¹`. -/
def B (N : ℕ) : Matrix (Fin N) (Fin N) ℝ := (M N)⁻¹

def k {N : ℕ} (hN : 0 < N) : ℝ := B N (Old.first hN) (Old.last hN)

def c {N : ℕ} (hN : 0 < N) : ℝ :=
  B N (Old.first hN) (Old.first hN) / k hN

def source {N : ℕ} (hN : 0 < N) (a b : ℝ) : Vec N :=
  Pi.single (Old.first hN) a - Pi.single (Old.last hN) b

/-- Literal matrix expression for the manuscript's `H`. -/
def H {N : ℕ} (hN : 0 < N) (a b : ℝ) (w : Vec N) : ℝ :=
  -(1 / 2 : ℝ) * (∑ i : Fin N, w i * (M N).mulVec w i) +
    (Real.sqrt (k hN))⁻¹ * (∑ i : Fin N, source hN a b i * w i) +
    (2 - c hN) / 2 * (a ^ 2 + b ^ 2)

def maximizer {N : ℕ} (hN : 0 < N) (a b : ℝ) : Vec N :=
  (Real.sqrt (k hN))⁻¹ • (B N).mulVec (source hN a b)

def Q (a b : ℝ) : ℝ := a ^ 2 - a * b + b ^ 2

theorem A_action {N : ℕ} (w : Vec N) (i : Fin N) :
    (A N).mulVec w i = pathLaplacianCoord w i :=
  NCCLowerBound.Simplified.InnerRelay.pathA_mulVec_eq_coord w i

theorem A_energy (N : ℕ) (w : Vec N) :
    (∑ i : Fin N, w i * (A N).mulVec w i) = pathEnergy N w :=
  NCCLowerBound.Simplified.InnerRelay.pathA_quadratic_eq N w

theorem M_eq_old (N : ℕ) : M N = Old.pathM N := by
  exact (NCCLowerBound.Simplified.InnerRelay.pathM_eq_regularization_add_pathA N).symm

theorem B_eq_old (N : ℕ) : B N = Old.pathB N := by
  rw [B, M_eq_old]
  rfl

theorem k_eq_old {N : ℕ} (hN : 0 < N) : k hN = Old.sigma hN := by
  simp only [k, B_eq_old, NCCLowerBound.Simplified.InnerRelay.sigma]

theorem c_eq_old {N : ℕ} (hN : 0 < N) : c hN = Old.rho hN := by
  simp only [c, B_eq_old, k_eq_old, NCCLowerBound.Simplified.InnerRelay.rho]

theorem source_eq_old {N : ℕ} (hN : 0 < N) (a b : ℝ) :
    source hN a b = Old.endpointSource hN a b := rfl

theorem source_dot {N : ℕ} (hN : 0 < N) (a b : ℝ) (w : Vec N) :
    (∑ i : Fin N, source hN a b i * w i) =
      a * w (Old.first hN) - b * w (Old.last hN) := by
  classical
  simp [source, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, Pi.single_apply]

/-- Exact equality of the current matrix formula and the proved relay. -/
theorem H_eq_old {N : ℕ} (hN : 0 < N) (a b : ℝ) (w : Vec N) :
    H hN a b w = Old.correctedH hN a b w := by
  rw [H, M_eq_old, NCCLowerBound.Simplified.InnerRelay.pathM_quadratic_eq,
    source_dot, k_eq_old, c_eq_old]
  rfl

theorem maximizer_eq_old {N : ℕ} (hN : 0 < N) (a b : ℝ) :
    maximizer hN a b = Old.wStar hN a b := by
  rw [maximizer, k_eq_old, B_eq_old, source_eq_old]
  exact (NCCLowerBound.Simplified.InnerRelay.wStar_eq_matrix_mulVec hN a b).symm

theorem M_positive_definite {N : ℕ} (hN : 0 < N) {w : Vec N} (hw : w ≠ 0) :
    0 < ∑ i : Fin N, w i * (M N).mulVec w i := by
  rw [M_eq_old]
  exact NCCLowerBound.Simplified.InnerRelay.pathM_posDef hN hw

theorem M_mul_B {N : ℕ} (hN : 0 < N) : M N * B N = 1 := by
  rw [M_eq_old, B_eq_old]
  exact NCCLowerBound.Simplified.InnerRelay.pathM_mul_pathB hN

theorem k_bounds {N : ℕ} (hN : 10 ≤ N) :
    (N : ℝ) / 10 ≤ k (by omega : 0 < N) ∧
      k (by omega : 0 < N) ≤ 20 * (N : ℝ) := by
  simpa only [k_eq_old] using NCCLowerBound.Simplified.InnerRelay.sigma_bounds hN

theorem k_pos {N : ℕ} (hN : 10 ≤ N) : 0 < k (by omega : 0 < N) := by
  simpa only [k_eq_old] using NCCLowerBound.Simplified.InnerRelay.sigma_pos hN

/-- The sharp endpoint ratio is proved from `N ≥ 10`, with no ratio premise. -/
theorem c_bounds {N : ℕ} (hN : 10 ≤ N) :
    (6 / 5 : ℝ) ≤ c (by omega : 0 < N) ∧ c (by omega : 0 < N) ≤ 8 / 5 := by
  simpa only [c_eq_old, NCCLowerBound.Simplified.InnerRelay.HasSharpEndpointRatio] using
    NCCLowerBound.Simplified.InnerRelay.sharp_endpoint_ratio hN

theorem H_maximum {N : ℕ} (hN : 0 < N) (a b : ℝ) (w : Vec N) :
    H hN a b w ≤ H hN a b (maximizer hN a b) := by
  simpa only [H_eq_old, maximizer_eq_old] using
    NCCLowerBound.Simplified.InnerRelay.correctedH_le_at_wStar hN a b w

theorem H_maximizer_unique {N : ℕ} (hN : 0 < N) (a b : ℝ) {w : Vec N}
    (hw : H hN a b w = H hN a b (maximizer hN a b)) :
    w = maximizer hN a b := by
  simp only [H_eq_old, maximizer_eq_old] at hw ⊢
  exact NCCLowerBound.Simplified.InnerRelay.wStar_unique_maximizer hN a b hw

theorem H_maximum_value {N : ℕ} (hN : 10 ≤ N) (a b : ℝ) :
    H (by omega : 0 < N) a b (maximizer (by omega : 0 < N) a b) = Q a b := by
  simpa only [H_eq_old, maximizer_eq_old, Q] using
    NCCLowerBound.Simplified.InnerRelay.correctedH_wStar_value hN a b

/-- The effective link is the actual supremum of the image of `H`. -/
theorem H_supremum {N : ℕ} (hN : 10 ≤ N) (a b : ℝ) :
    IsGreatest (Set.range (H (by omega : 0 < N) a b)) (Q a b) := by
  refine ⟨⟨maximizer (by omega) a b, H_maximum_value hN a b⟩, ?_⟩
  rintro _ ⟨w, rfl⟩
  rw [← H_maximum_value hN a b]
  exact H_maximum (by omega) a b w

theorem maximizer_growth_squared {N : ℕ} (hN : 10 ≤ N) (a b : ℝ) :
    vecSq (maximizer (by omega : 0 < N) a b) ≤
      8000 * (N : ℝ) ^ 2 * (a ^ 2 + b ^ 2) := by
  simpa only [maximizer_eq_old] using
    NCCLowerBound.Simplified.InnerRelay.wStar_vecSq_le hN a b

/-- The paper's actual constant `c_y = 20 sqrt 20`. -/
theorem maximizer_growth {N : ℕ} (hN : 10 ≤ N) (a b : ℝ) :
    norm₂ (maximizer (by omega : 0 < N) a b) ≤
      20 * Real.sqrt 20 * (N : ℝ) * Real.sqrt (a ^ 2 + b ^ 2) := by
  have hb := maximizer_growth_squared hN a b
  have hsq : 0 ≤ vecSq (maximizer (by omega : 0 < N) a b) := by
    unfold vecSq NCPLVerification.vecSq
    positivity
  have h1 := Real.sq_sqrt hsq
  have h2 := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 20)
  have h3 := Real.sq_sqrt (by positivity : 0 ≤ a ^ 2 + b ^ 2)
  have hleft : 0 ≤ norm₂ (maximizer (by omega : 0 < N) a b) :=
    Real.sqrt_nonneg _
  have hright : 0 ≤ 20 * Real.sqrt 20 * (N : ℝ) * Real.sqrt (a ^ 2 + b ^ 2) := by
    positivity
  apply (sq_le_sq₀ hleft hright).mp
  unfold norm₂
  rw [h1]
  norm_num only [mul_pow, h2, h3, Nat.reducePow, Nat.reduceMul]
  exact hb

/-- Strong concavity in its defining Euclidean Jensen form. -/
theorem H_strongly_concave {N : ℕ} (hN : 0 < N) (a b : ℝ)
    (u v : Vec N) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * H hN a b u + (1 - t) * H hN a b v +
      ((1 / (N : ℝ) ^ 2) / 2) * t * (1 - t) * vecSq (u - v) ≤
      H hN a b (t • u + (1 - t) • v) := by
  simpa only [H_eq_old, pathRegularization] using
    NCCLowerBound.Simplified.InnerRelay.correctedH_strongConcave hN a b u v ht0 ht1

theorem H_origin_signs {N : ℕ} (hN : 10 ≤ N) (a b : ℝ) (w : Vec N) :
    0 ≤ H (by omega : 0 < N) a b 0 ∧ H (by omega : 0 < N) 0 0 w ≤ 0 := by
  simp only [H_eq_old]
  exact ⟨NCCLowerBound.Simplified.InnerRelay.correctedH_zero_dual_nonneg_of_ten hN a b,
    NCCLowerBound.Simplified.InnerRelay.correctedH_zero_primal_nonpos (by omega) w⟩

/-- `H` expressed in the claimed coordinate order `(a,w₁,...,w_N,b)`. -/
def jointH {N : ℕ} (hN : 0 < N) (q : Vec (N + 2)) : ℝ :=
  H hN (Old.jointA q) (Old.jointB q) (Old.jointW q)

def gradient {N : ℕ} (hN : 0 < N) : Vec (N + 2) → Vec (N + 2) :=
  NCCLowerBound.Simplified.CompositeSmoothnessAssembly.relayTrueGradient hN

theorem jointH_hasFDerivAt {N : ℕ} (hN : 0 < N) (q : Vec (N + 2)) :
    HasFDerivAt (jointH hN) (NCPLVerification.evecDot (gradient hN q)) q := by
  have heq : jointH hN =
      NCCLowerBound.Simplified.CompositeSmoothnessAssembly.relayObjective hN := by
    funext q
    exact H_eq_old hN _ _ _
  rw [heq]
  exact NCCLowerBound.Simplified.CompositeSmoothnessAssembly.hasFDerivAt_relayObjective hN q

/-- The actual gradient is a zero-chain; dual sign reversal preserves support. -/
theorem gradient_zero_chain {N : ℕ} (hN : 0 < N) :
    Old.IsPrefixZeroChain (gradient hN) := by
  intro k q hq r hr
  have hz := NCCLowerBound.Simplified.InnerRelay.relayField_isPrefixZeroChain hN k q hq r hr
  unfold gradient NCCLowerBound.Simplified.CompositeSmoothnessAssembly.relayTrueGradient
  unfold NCCLowerBound.Simplified.InnerRelay.relayField at hz
  by_cases h0 : r.val = 0 <;> by_cases hm : r.val ≤ N <;> simp_all

private theorem gradient_difference_energy {N : ℕ} (hN : 0 < N)
    (q r : Vec (N + 2)) :
    vecSq (gradient hN q - gradient hN r) =
      vecSq (Old.relayField hN q - Old.relayField hN r) := by
  unfold vecSq NCPLVerification.vecSq
  apply Finset.sum_congr rfl
  intro i _
  change (gradient hN q i - gradient hN r i) ^ 2 = _
  unfold gradient NCCLowerBound.Simplified.CompositeSmoothnessAssembly.relayTrueGradient
    NCCLowerBound.Simplified.InnerRelay.relayField
  by_cases h0 : i.val = 0 <;> by_cases hm : i.val ≤ N <;>
    simp only [Pi.sub_apply, h0, hm, ↓reduceDIte]
  all_goals ring

/-- A dimension-free bound for the true gradient, with numerical constant 10. -/
theorem gradient_lipschitz {N : ℕ} (hN : 10 ≤ N) (q r : Vec (N + 2)) :
    norm₂ (gradient (by omega : 0 < N) q - gradient (by omega : 0 < N) r) ≤
      10 * norm₂ (q - r) := by
  unfold norm₂
  rw [gradient_difference_energy]
  exact NCCLowerBound.Simplified.CompositeSmoothness.relayField_euclidean_lipschitz hN q r

private theorem energy_nonneg {n : ℕ} (w : Vec n) : 0 ≤ vecSq w := by
  unfold vecSq NCPLVerification.vecSq
  positivity

private theorem coordinate_energy_le {n : ℕ} (w : Vec n) (i : Fin n) :
    w i ^ 2 ≤ vecSq w := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.single_le_sum (fun j _ => sq_nonneg (w j)) (Finset.mem_univ i)

/-- Squared operator bound 25 for the actual regularized path action. -/
theorem M_action_squared_le {N : ℕ} (hN : 10 ≤ N) (w : Vec N) :
    vecSq (regularizedPathVector w) ≤ 25 * vecSq w := by
  let r := pathRegularization N
  have hr0 : 0 ≤ r := pathRegularization_nonneg N
  have hr1 : r ≤ 1 := by
    dsimp [r, pathRegularization]
    have hNr : (10 : ℝ) ≤ N := by exact_mod_cast hN
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) ^ 2)]
    nlinarith
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hcoord : vecSq (regularizedPathVector w) ≤
      5 * r ^ 2 * vecSq w + (5 / 4 : ℝ) * vecSq (pathLaplacianVector w) := by
    unfold vecSq NCPLVerification.vecSq
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    change (r * w i + pathLaplacianVector w i) ^ 2 ≤ _
    nlinarith [sq_nonneg (2 * (r * w i) - pathLaplacianVector w i / 2)]
  have hL := pathLaplacianVector_vecSq_le w
  have hE := pathEnergy_le_four_vecSq N w
  have hrw := mul_le_mul_of_nonneg_right hr2 (energy_nonneg w)
  nlinarith

private theorem weighted_sub_energy {n : ℕ} (u v : Vec n) :
    vecSq (u - v) ≤ (6 / 5 : ℝ) * vecSq u + 6 * vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (u i + 5 * v i)]

/-- Numerical bound 6, including the exact endpoint normalization. -/
theorem relay_field_squared_le_six {N : ℕ} (hN10 : 10 ≤ N) (q : Vec (N + 2)) :
    vecSq (Old.relayField (by omega : 0 < N) q) ≤ 36 * vecSq q := by
  let hN : 0 < N := by omega
  let a := Old.jointA q
  let b := Old.jointB q
  let w := Old.jointW q
  let s := Old.relayScale hN
  let d := 2 - Old.rho hN
  have hs : s ^ 2 ≤ 1 :=
    NCCLowerBound.Simplified.CompositeSmoothness.relayScale_sq_le_one hN10
  have hd : d ^ 2 ≤ 1 :=
    NCCLowerBound.Simplified.CompositeSmoothness.correction_sq_le_one hN10
  have hsa := mul_le_mul_of_nonneg_right hs (sq_nonneg (w (Old.first hN)))
  have hsb := mul_le_mul_of_nonneg_right hs (sq_nonneg (w (Old.last hN)))
  have hda := mul_le_mul_of_nonneg_right hd (sq_nonneg a)
  have hdb := mul_le_mul_of_nonneg_right hd (sq_nonneg b)
  have hf := coordinate_energy_le w (Old.first hN)
  have hl := coordinate_energy_le w (Old.last hN)
  have ha : NCCLowerBound.Simplified.InnerRelay.relayGradA hN a w ^ 2 ≤
      2 * vecSq w + 2 * a ^ 2 := by
    change (s * w (Old.first hN) + d * a) ^ 2 ≤ _
    nlinarith [sq_nonneg (s * w (Old.first hN) - d * a)]
  have hb : NCCLowerBound.Simplified.InnerRelay.relayGradB hN b w ^ 2 ≤
      2 * vecSq w + 2 * b ^ 2 := by
    change (-s * w (Old.last hN) + d * b) ^ 2 ≤ _
    nlinarith [sq_nonneg (-s * w (Old.last hN) - d * b)]
  have hsource : vecSq (s • Old.endpointSource hN a b) ≤ 2 * (a ^ 2 + b ^ 2) := by
    have heq : vecSq (s • Old.endpointSource hN a b) =
        s ^ 2 * vecSq (Old.endpointSource hN a b) := by
      unfold vecSq NCPLVerification.vecSq
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
    rw [heq]
    have hmul := mul_le_mul_of_nonneg_right hs (energy_nonneg (Old.endpointSource hN a b))
    have hsrc := NCCLowerBound.Simplified.CompositeSmoothness.endpointSource_vecSq_le hN a b
    nlinarith
  have hmidEq :
      (fun i => NCCLowerBound.Simplified.InnerRelay.relaySaddleGradW hN a b w i) =
        regularizedPathVector w - s • Old.endpointSource hN a b := by rfl
  have hm := weighted_sub_energy (regularizedPathVector w) (s • Old.endpointSource hN a b)
  have hp := M_action_squared_le hN10 w
  have hw0 := energy_nonneg w
  have hab0 : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  rw [NCCLowerBound.Simplified.CompositeSmoothness.vecSq_relayField_decomposition,
    NCCLowerBound.Simplified.CompositeSmoothness.vecSq_joint_decomposition]
  change _ ≤ 36 * (a ^ 2 + vecSq w + b ^ 2)
  rw [hmidEq]
  nlinarith

theorem gradient_lipschitz_six {N : ℕ} (hN : 10 ≤ N) (q r : Vec (N + 2)) :
    norm₂ (gradient (by omega : 0 < N) q - gradient (by omega : 0 < N) r) ≤
      6 * norm₂ (q - r) := by
  have hb : vecSq (gradient (by omega : 0 < N) q - gradient (by omega : 0 < N) r) ≤
      36 * vecSq (q - r) := by
    rw [gradient_difference_energy, ← NCCLowerBound.Simplified.CompositeSmoothness.relayField_sub]
    exact relay_field_squared_le_six hN (q - r)
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by unfold norm₂; positivity)).mp
  unfold norm₂
  rw [mul_pow, Real.sq_sqrt (energy_nonneg _), Real.sq_sqrt (energy_nonneg _)]
  norm_num
  exact hb

private theorem gradient_add {N : ℕ} (hN : 0 < N) (u v : Vec (N + 2)) :
    gradient hN (u + v) = gradient hN u + gradient hN v := by
  funext i
  unfold gradient NCCLowerBound.Simplified.CompositeSmoothnessAssembly.relayTrueGradient
  by_cases h0 : i.val = 0 <;> by_cases hm : i.val ≤ N <;>
    simp only [Pi.add_apply, h0, hm, ↓reduceDIte]
  all_goals
    simp only [NCCLowerBound.Simplified.InnerRelay.relayGradA,
      NCCLowerBound.Simplified.InnerRelay.relayGradB,
      NCCLowerBound.Simplified.InnerRelay.relaySaddleGradW,
      NCCLowerBound.Simplified.InnerRelay.jointA,
      NCCLowerBound.Simplified.InnerRelay.jointB,
      NCCLowerBound.Simplified.InnerRelay.jointW,
      NCCLowerBound.Simplified.InnerRelay.endpointSource,
      regularizedPathCoord, pathLaplacianCoord, Pi.single_apply,
      Pi.add_apply, Pi.sub_apply]
    (try split_ifs) <;> simp_all <;> ring

private theorem gradient_smul {N : ℕ} (hN : 0 < N) (s : ℝ) (u : Vec (N + 2)) :
    gradient hN (s • u) = s • gradient hN u := by
  funext i
  unfold gradient NCCLowerBound.Simplified.CompositeSmoothnessAssembly.relayTrueGradient
  by_cases h0 : i.val = 0 <;> by_cases hm : i.val ≤ N <;>
    simp only [Pi.smul_apply, h0, hm, ↓reduceDIte]
  all_goals
    simp only [NCCLowerBound.Simplified.InnerRelay.relayGradA,
      NCCLowerBound.Simplified.InnerRelay.relayGradB,
      NCCLowerBound.Simplified.InnerRelay.relaySaddleGradW,
      NCCLowerBound.Simplified.InnerRelay.jointA,
      NCCLowerBound.Simplified.InnerRelay.jointB,
      NCCLowerBound.Simplified.InnerRelay.jointW,
      NCCLowerBound.Simplified.InnerRelay.endpointSource,
      regularizedPathCoord, pathLaplacianCoord, Pi.single_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    (try split_ifs) <;> simp_all <;> ring

def hessianLinear {N : ℕ} (hN : 0 < N) : Vec (N + 2) →ₗ[ℝ] Vec (N + 2) where
  toFun := gradient hN
  map_add' := gradient_add hN
  map_smul' := gradient_smul hN

/-- The constant Hessian, as a continuous linear map on coordinate vectors. -/
def hessian {N : ℕ} (hN : 0 < N) : Vec (N + 2) →L[ℝ] Vec (N + 2) :=
  (hessianLinear hN).toContinuousLinearMap

/-- This operator is the actual derivative of the actual gradient of `jointH`. -/
theorem gradient_hasFDerivAt {N : ℕ} (hN : 0 < N) (q : Vec (N + 2)) :
    HasFDerivAt (gradient hN) (hessian hN) q :=
  (hessian hN).hasFDerivAt

/-- The manuscript's Euclidean Hessian norm bound, equivalently as an
operator bound on every direction. -/
theorem hessian_euclidean_bound {N : ℕ} (hN : 10 ≤ N) (q : Vec (N + 2)) :
    norm₂ (hessian (by omega : 0 < N) q) ≤ 6 * norm₂ q := by
  change norm₂ (gradient (by omega : 0 < N) q) ≤ 6 * norm₂ q
  have hz : gradient (by omega : 0 < N) 0 = 0 := (hessianLinear (by omega : 0 < N)).map_zero
  simpa only [hz, sub_zero] using gradient_lipschitz_six hN q 0

/-- Serialized `(a_i,b_i)` primal pulse. -/
abbrev Pulse (blocks : ℕ) := Vec (blocks * 2)
abbrev Dual (blocks N : ℕ) := Vec (blocks * N)

def objective {blocks N : ℕ} (hN : 0 < N) (p : Pulse blocks) (y : Dual blocks N) : ℝ :=
  ∑ i : Fin blocks,
    H hN (p (finProdFinEquiv (i, ⟨0, by omega⟩)))
      (p (finProdFinEquiv (i, ⟨1, by omega⟩)))
      (fun j => y (finProdFinEquiv (i, j)))

def dualBall (blocks N : ℕ) (D : ℝ) : Set (Dual blocks N) :=
  {y | vecSq y ≤ (D / 2) ^ 2}

/-- Literal finite-ball value from item (iv). -/
def V {blocks N : ℕ} (hN : 0 < N) (D : ℝ) : Pulse blocks → ℝ :=
  ValueOn (dualBall blocks N D) (objective hN)

theorem objective_eq_old {blocks N : ℕ} (hN : 0 < N) :
    objective (blocks := blocks) hN =
      NCCLowerBound.Simplified.InnerFiniteBall.innerObjective hN := by
  funext p y
  unfold objective NCCLowerBound.Simplified.InnerFiniteBall.innerObjective
    NCCLowerBound.Simplified.InnerRelay.innerComponent
  apply Finset.sum_congr rfl
  intro i _
  exact H_eq_old hN _ _ _

theorem V_eq_old {blocks N : ℕ} (hN : 0 < N) (D : ℝ) :
    V (blocks := blocks) hN D =
      NCCLowerBound.Simplified.InnerFiniteBall.finiteValue hN D := by
  rw [V, objective_eq_old]
  rfl

/-- Full differentiability of the actual constrained maximum, not a hypothesis. -/
theorem V_differentiable {blocks N : ℕ} (hN : 0 < N) {D : ℝ} (hD : 0 ≤ D) :
    Differentiable ℝ (V (blocks := blocks) hN D) := by
  rw [V_eq_old]
  exact NCCLowerBound.Simplified.InnerFiniteBall.finiteValue_differentiable hN hD

/-- Item (iv), stated with the genuine Fréchet derivative of `V_D`. -/
theorem V_radial_lower {blocks N : ℕ} (hN : 10 ≤ N) {D : ℝ} (hD : 0 ≤ D)
    (p : Pulse blocks) :
    (2 / 5 : ℝ) * vecSq p ≤ (fderiv ℝ (V (by omega : 0 < N) D) p) p := by
  rw [V_eq_old]
  exact NCCLowerBound.Simplified.InnerFiniteBall.finiteValue_radial hN hD p

end

end NCC.Construction.Inner
