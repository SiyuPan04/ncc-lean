import NCCLowerBound.Simplified.RestrictedBall
import NCCLowerBoundVerification.Lower.UniformInner
import NCCLowerBoundVerification.PaperClass

/-!
# Dimension-free smoothness estimates for the simplified hard instance

This file begins with the genuinely dimension-free part of the joint
smoothness argument: the corrected inner relay.  All norms below are the
Euclidean norms encoded by `vecSq`; in particular none of the constants is
obtained by comparing with the dimension-dependent sup norm on a function
space.
-/

namespace NCCLowerBound
namespace Simplified
namespace CompositeSmoothness

noncomputable section

open scoped BigOperators
open Set
open NCCLowerBoundVerification
open InnerRelay
open CompositeProperties RestrictedBall

abbrev EVec := NCCLowerBoundVerification.EVec

/-! ## The actual Fréchet gradient of the flattened objective -/

/-- Joint, uncurried form of the genuine flattened five-component saddle. -/
def flatJointObjective {M N : Nat} (hN : 0 < N) (K : ℝ) :
    FlatPrimal M × FlatDual M N → ℝ :=
  Function.uncurry (flatHardObjective hN K)

/-- The coordinate decoders used by `flatHardObjective` are smooth linear
reindexings, hence the flattened objective is genuinely `C^∞`. -/
theorem flatJointObjective_contDiff {M N : Nat} (hN : 0 < N) (K : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (flatJointObjective (M := M) hN K) := by
  have hdecode : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : FlatPrimal M × FlatDual M N =>
        ((decodePrimal z.1, unflattenBlocks z.2) : SaddlePoint M N)) := by
    unfold decodePrimal flatState flatEntrance flatExit unflattenBlocks
    fun_prop
  convert (saddleObjective_contDiff (M := M) hN K).comp hdecode using 1
  funext z
  rfl

/-- Actual primal Fréchet-gradient coordinates of `flatHardObjective`.
This is the Riesz-coordinate extraction of its joint Fréchet derivative,
not a postulated certificate. -/
def flatPrimalGradient {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : FlatPrimal M) (y : FlatDual M N) : FlatPrimal M :=
  ambientGradX (flatJointObjective hN K) x y

/-- Actual dual Fréchet-gradient coordinates of `flatHardObjective`. -/
def flatDualGradient {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : FlatPrimal M) (y : FlatDual M N) : FlatDual M N :=
  ambientGradY (flatJointObjective hN K) x y

/-- The two vectors above represent the whole joint Fréchet derivative in
every direction. -/
theorem flatGradient_represents_fderiv {M N : Nat} (hN : 0 < N) (K : ℝ) :
    NCPLVerification.RepresentsJointGradient (flatHardObjective (M := M) hN K)
      (flatPrimalGradient hN K) (flatDualGradient hN K) := by
  have hd : Differentiable ℝ (flatJointObjective (M := M) hN K) :=
    (flatJointObjective_contDiff (M := M) hN K).differentiable (by simp)
  unfold flatPrimalGradient flatDualGradient
  simpa [flatJointObjective] using
    (representsJointGradient_ambient (flatJointObjective (M := M) hN K) hd)

/-- The signed saddle field associated with the genuine Fréchet gradient. -/
def flatSignedGradient {M N : Nat} (hN : 0 < N) (K : ℝ)
    (x : FlatPrimal M) (y : FlatDual M N) :
    FlatPrimal M × FlatDual M N :=
  (flatPrimalGradient hN K x y, -flatDualGradient hN K x y)

private theorem vecSq_nonneg {n : Nat} (v : EVec n) : 0 ≤ vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  positivity

private theorem coordinate_sq_le_vecSq {n : Nat} (v : EVec n) (i : Fin n) :
    v i ^ 2 ≤ vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.single_le_sum (fun j _ => sq_nonneg (v j))
    (Finset.mem_univ i)

private theorem vecSq_single {n : Nat} (i : Fin n) (c : ℝ) :
    vecSq (Pi.single i c : EVec n) = c ^ 2 := by
  classical
  unfold vecSq NCPLVerification.vecSq
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

private theorem vecSq_sub_le_two {n : Nat} (u v : EVec n) :
    vecSq (u - v) ≤ 2 * vecSq u + 2 * vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  calc
    (∑ i, (u - v) i ^ 2) ≤
        ∑ i, (2 * u i ^ 2 + 2 * v i ^ 2) := by
      exact Finset.sum_le_sum fun i _ => by
        simp only [Pi.sub_apply]
        nlinarith [sq_nonneg (u i + v i)]
    _ = 2 * (∑ i, u i ^ 2) + 2 * (∑ i, v i ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

private theorem vecSq_smul {n : Nat} (c : ℝ) (v : EVec n) :
    vecSq (c • v) = c ^ 2 * vecSq v := by
  unfold vecSq NCPLVerification.vecSq
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- The symmetric two-endpoint source has a dimension-free Euclidean norm.
The estimate remains valid without using that the endpoints are distinct. -/
theorem endpointSource_vecSq_le {N : Nat} (hN : 0 < N) (a b : ℝ) :
    vecSq (endpointSource hN a b) ≤ 2 * (a ^ 2 + b ^ 2) := by
  unfold endpointSource
  have h := vecSq_sub_le_two
    (Pi.single (first hN) a : EVec N)
    (Pi.single (last hN) b : EVec N)
  rw [vecSq_single, vecSq_single] at h
  nlinarith

/-- The relay normalisation is at most one for every `N >= 10`. -/
theorem relayScale_sq_le_one {N : Nat} (hN10 : 10 ≤ N) :
    relayScale (by omega : 0 < N) ^ 2 ≤ 1 := by
  have hs := relayScale_sq_le_ten_div hN10
  have hNr : (10 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN10
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hdiv : (10 : ℝ) / (N : ℝ) ≤ 1 := by
    exact (div_le_one hNpos).2 hNr
  exact hs.trans hdiv

/-- The diagonal correction coefficient has square at most one. -/
theorem correction_sq_le_one {N : Nat} (hN10 : 10 ≤ N) :
    (2 - rho (by omega : 0 < N)) ^ 2 ≤ 1 := by
  have hc := correction_bounds_unconditional hN10
  nlinarith [sq_nonneg (2 - rho (by omega : 0 < N) - 1)]

/-- The actual signed-gradient field of one corrected relay has a numerical
Euclidean operator bound independent of the path length. -/
theorem relay_block_field_sq_le {N : Nat} (hN10 : 10 ≤ N)
    (a b : ℝ) (w : EVec N) :
    relayGradA (by omega : 0 < N) a w ^ 2 +
        relayGradB (by omega : 0 < N) b w ^ 2 +
        vecSq (fun i => relaySaddleGradW (by omega : 0 < N) a b w i) ≤
      100 * (a ^ 2 + b ^ 2 + vecSq w) := by
  let hN : 0 < N := by omega
  let scale := relayScale hN
  let correction := 2 - rho hN
  let path : EVec N := regularizedPathVector w
  let source : EVec N := scale • endpointSource hN a b
  let middle : EVec N :=
    fun i => relaySaddleGradW hN a b w i
  have hs : scale ^ 2 ≤ 1 := by
    simpa [scale, hN] using relayScale_sq_le_one hN10
  have hs0 : 0 ≤ scale ^ 2 := sq_nonneg scale
  have hc : correction ^ 2 ≤ 1 := by
    simpa [correction, hN] using correction_sq_le_one hN10
  have hc0 : 0 ≤ correction ^ 2 := sq_nonneg correction
  have hw0 : 0 ≤ vecSq w := vecSq_nonneg w
  have hab0 : 0 ≤ a ^ 2 + b ^ 2 :=
    add_nonneg (sq_nonneg a) (sq_nonneg b)
  have hfirst := coordinate_sq_le_vecSq w (first hN)
  have hlast := coordinate_sq_le_vecSq w (last hN)
  have hA : relayGradA hN a w ^ 2 ≤ 2 * vecSq w + 2 * a ^ 2 := by
    unfold relayGradA
    change (scale * w (first hN) + correction * a) ^ 2 ≤ _
    have hsw : scale ^ 2 * w (first hN) ^ 2 ≤ vecSq w := by
      calc
        scale ^ 2 * w (first hN) ^ 2 ≤ 1 * vecSq w :=
          mul_le_mul hs hfirst (sq_nonneg _) zero_le_one
        _ = vecSq w := one_mul _
    have hca : correction ^ 2 * a ^ 2 ≤ a ^ 2 := by
      calc
        correction ^ 2 * a ^ 2 ≤ 1 * a ^ 2 :=
          mul_le_mul hc le_rfl (sq_nonneg _) zero_le_one
        _ = a ^ 2 := one_mul _
    nlinarith [sq_nonneg (scale * w (first hN) - correction * a)]
  have hB : relayGradB hN b w ^ 2 ≤ 2 * vecSq w + 2 * b ^ 2 := by
    unfold relayGradB
    change (-scale * w (last hN) + correction * b) ^ 2 ≤ _
    have hsw : scale ^ 2 * w (last hN) ^ 2 ≤ vecSq w := by
      calc
        scale ^ 2 * w (last hN) ^ 2 ≤ 1 * vecSq w :=
          mul_le_mul hs hlast (sq_nonneg _) zero_le_one
        _ = vecSq w := one_mul _
    have hcb : correction ^ 2 * b ^ 2 ≤ b ^ 2 := by
      calc
        correction ^ 2 * b ^ 2 ≤ 1 * b ^ 2 :=
          mul_le_mul hc le_rfl (sq_nonneg _) zero_le_one
        _ = b ^ 2 := one_mul _
    nlinarith [sq_nonneg (-scale * w (last hN) - correction * b)]
  have hpath : vecSq path ≤ 33 * vecSq w := by
    exact regularizedPathVector_vecSq_le_of_ten hN10 w
  have hsourceEq : vecSq source = scale ^ 2 * vecSq (endpointSource hN a b) := by
    exact vecSq_smul scale (endpointSource hN a b)
  have hsource : vecSq source ≤ 2 * (a ^ 2 + b ^ 2) := by
    rw [hsourceEq]
    have he := endpointSource_vecSq_le hN a b
    nlinarith [mul_nonneg (sub_nonneg.mpr hs)
      (vecSq_nonneg (endpointSource hN a b)),
      mul_nonneg hs0 (sub_nonneg.mpr he)]
  have hmiddleEq : middle = path - source := by
    funext i
    simp [middle, path, source, relaySaddleGradW,
      regularizedPathVector, scale]
  have hmiddle : vecSq middle ≤
      66 * vecSq w + 4 * (a ^ 2 + b ^ 2) := by
    rw [hmiddleEq]
    exact (vecSq_sub_le_two path source).trans (by nlinarith)
  change relayGradA hN a w ^ 2 + relayGradB hN b w ^ 2 +
      vecSq middle ≤ 100 * (a ^ 2 + b ^ 2 + vecSq w)
  nlinarith

@[simp] theorem relayField_first {N : Nat} (hN : 0 < N)
    (q : EVec (N + 2)) :
    relayField hN q ⟨0, by omega⟩ =
      relayGradA hN (jointA q) (jointW q) := by
  simp [relayField]

@[simp] theorem relayField_middle {N : Nat} (hN : 0 < N)
    (q : EVec (N + 2)) (i : Fin N) :
    relayField hN q ⟨i.val + 1, by omega⟩ =
      relaySaddleGradW hN (jointA q) (jointB q) (jointW q) i := by
  simp [relayField]

@[simp] theorem relayField_last {N : Nat} (hN : 0 < N)
    (q : EVec (N + 2)) :
    relayField hN q ⟨N + 1, by omega⟩ =
      relayGradB hN (jointB q) (jointW q) := by
  simp [relayField]

/-- Euclidean squared norm decomposition in the relay coordinate order
`(a,w_1,...,w_N,b)`. -/
theorem vecSq_joint_decomposition {N : Nat} (q : EVec (N + 2)) :
    vecSq q = jointA q ^ 2 + vecSq (jointW q) + jointB q ^ 2 := by
  unfold vecSq NCPLVerification.vecSq jointA jointW jointB
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hmiddle :
      (∑ i : Fin N, q i.castSucc.succ ^ 2) =
        ∑ i : Fin N, q ⟨i.val + 1, by omega⟩ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    congr 2
  have hlast : q (Fin.last N).succ = q ⟨N + 1, by omega⟩ := by
    congr 1
  have hzero : q 0 = q ⟨0, by omega⟩ := by
    congr 1
  rw [hmiddle, hlast, hzero]
  ring

/-- The same coordinate decomposition for the actual relay field. -/
theorem vecSq_relayField_decomposition {N : Nat} (hN : 0 < N)
    (q : EVec (N + 2)) :
    vecSq (relayField hN q) =
      relayGradA hN (jointA q) (jointW q) ^ 2 +
        vecSq (fun i =>
          relaySaddleGradW hN (jointA q) (jointB q) (jointW q) i) +
        relayGradB hN (jointB q) (jointW q) ^ 2 := by
  unfold vecSq NCPLVerification.vecSq
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hfirst : relayField hN q 0 =
      relayGradA hN (jointA q) (jointW q) := by
    have hi : (0 : Fin (N + 2)) = ⟨0, by omega⟩ := by
      apply Fin.ext
      rfl
    rw [hi, relayField_first]
  have hmiddle :
      (∑ i : Fin N, relayField hN q i.castSucc.succ ^ 2) =
        ∑ i : Fin N,
          relaySaddleGradW hN (jointA q) (jointB q) (jointW q) i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    have hi : i.castSucc.succ = (⟨i.val + 1, by omega⟩ : Fin (N + 2)) := by
      apply Fin.ext
      simp
    rw [hi, relayField_middle]
  have hlast : relayField hN q (Fin.last N).succ =
      relayGradB hN (jointB q) (jointW q) := by
    have hi : (Fin.last N).succ = (⟨N + 1, by omega⟩ : Fin (N + 2)) := by
      apply Fin.ext
      simp
    rw [hi, relayField_last]
  rw [hfirst, hmiddle, hlast]
  ring

/-- A literal dimension-free bound for the serialized relay field. -/
theorem relayField_vecSq_le {N : Nat} (hN10 : 10 ≤ N)
    (q : EVec (N + 2)) :
    vecSq (relayField (by omega : 0 < N) q) ≤ 100 * vecSq q := by
  rw [vecSq_relayField_decomposition, vecSq_joint_decomposition]
  have h := relay_block_field_sq_le hN10
    (jointA q) (jointB q) (jointW q)
  nlinarith

private theorem regularizedPathCoord_sub {N : Nat} (u v : EVec N)
    (i : Fin N) :
    regularizedPathCoord (u - v) i =
      regularizedPathCoord u i - regularizedPathCoord v i := by
  unfold regularizedPathCoord pathLaplacianCoord
  simp only [Pi.sub_apply]
  split <;> split <;> ring

/-- The corrected relay field is linear (the diagonal correction introduces
no affine offset). -/
theorem relayField_sub {N : Nat} (hN : 0 < N)
    (q r : EVec (N + 2)) :
    relayField hN (q - r) = relayField hN q - relayField hN r := by
  funext k
  by_cases hk0 : k.val = 0
  · have hk : k = (⟨0, by omega⟩ : Fin (N + 2)) := by
      apply Fin.ext
      exact hk0
    rw [hk]
    simp only [Pi.sub_apply]
    rw [relayField_first, relayField_first, relayField_first]
    unfold relayGradA jointA jointW
    simp only [Pi.sub_apply]
    ring
  · by_cases hkN : k.val ≤ N
    · let i : Fin N := ⟨k.val - 1, by omega⟩
      have hk : k = (⟨i.val + 1, by omega⟩ : Fin (N + 2)) := by
        apply Fin.ext
        dsimp [i]
        omega
      rw [hk]
      simp only [Pi.sub_apply]
      rw [relayField_middle, relayField_middle, relayField_middle]
      have hw : jointW (q - r) = jointW q - jointW r := by
        funext j
        rfl
      unfold relaySaddleGradW
      rw [hw, regularizedPathCoord_sub]
      unfold jointA jointB endpointSource
      simp only [Pi.sub_apply]
      classical
      simp only [Pi.single_apply]
      split <;> split <;> ring
    · have hkval : k.val = N + 1 := by omega
      have hk : k = (⟨N + 1, by omega⟩ : Fin (N + 2)) := by
        apply Fin.ext
        exact hkval
      rw [hk]
      simp only [Pi.sub_apply]
      rw [relayField_last, relayField_last, relayField_last]
      unfold relayGradB jointB jointW
      simp only [Pi.sub_apply]
      ring

/-- Squared Euclidean Lipschitz estimate for the actual signed relay field.
The numerical constant `100` is independent of `N`. -/
theorem relayField_sub_vecSq_le {N : Nat} (hN10 : 10 ≤ N)
    (q r : EVec (N + 2)) :
    vecSq (relayField (by omega : 0 < N) q -
        relayField (by omega : 0 < N) r) ≤
      100 * vecSq (q - r) := by
  rw [← relayField_sub]
  exact relayField_vecSq_le hN10 (q - r)

/-- The Euclidean norm used in the manuscript, stated without relying on the
sup norm inherited by a finite function type. -/
def euclideanNorm {n : Nat} (v : EVec n) : ℝ := Real.sqrt (vecSq v)

theorem euclideanNorm_nonneg {n : Nat} (v : EVec n) :
    0 ≤ euclideanNorm v := Real.sqrt_nonneg _

/-- Unsquared `10`-Lipschitz form of `relayField_sub_vecSq_le`. -/
theorem relayField_euclidean_lipschitz {N : Nat} (hN10 : 10 ≤ N)
    (q r : EVec (N + 2)) :
    euclideanNorm (relayField (by omega : 0 < N) q -
        relayField (by omega : 0 < N) r) ≤
      10 * euclideanNorm (q - r) := by
  have h := relayField_sub_vecSq_le hN10 q r
  have hout0 := vecSq_nonneg
    (relayField (by omega : 0 < N) q - relayField (by omega : 0 < N) r)
  have hin0 := vecSq_nonneg (q - r)
  have hsout := Real.sq_sqrt hout0
  have hsin := Real.sq_sqrt hin0
  have hrout := euclideanNorm_nonneg
    (relayField (by omega : 0 < N) q - relayField (by omega : 0 < N) r)
  have hrin := euclideanNorm_nonneg (q - r)
  unfold euclideanNorm at hrout hrin ⊢
  nlinarith

/-- A single numerical witness for uniform inner-relay smoothness over every
admissible path length. -/
theorem exists_uniform_relay_lipschitz :
    ∃ ell0 : ℝ, 0 < ell0 ∧
      ∀ (N : Nat) (hN : 10 ≤ N) (q r : EVec (N + 2)),
        euclideanNorm (relayField (by omega : 0 < N) q -
            relayField (by omega : 0 < N) r) ≤
          ell0 * euclideanNorm (q - r) := by
  exact ⟨10, by norm_num, fun N hN q r =>
    relayField_euclidean_lipschitz hN q r⟩

/-! ## Scalar second-derivative bounds used by the outer components -/

/-- The state clip has a globally bounded actual second derivative. -/
theorem stateClip_second_deriv_bounded :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, |deriv (deriv stateClip) t| ≤ C := by
  obtain ⟨C, hC0, hC⟩ :=
    clipIntegrandDeriv_bounded (R := (2 : ℝ)) (width := (1 : ℝ))
      (by norm_num) (by norm_num)
  refine ⟨C, hC0, ?_⟩
  intro t
  rw [show deriv (deriv stateClip) t =
      saturationTemplateSecond 2 1 t by
    simpa [stateClip] using
      (secondDeriv_saturationTemplate (R := (2 : ℝ)) (width := (1 : ℝ))
        (t := t))]
  exact hC t

/-- The pulse clip has a globally bounded actual second derivative. -/
theorem pulseClip_second_deriv_bounded :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, |deriv (deriv pulseClip) t| ≤ C := by
  obtain ⟨C, hC0, hC⟩ :=
    clipIntegrandDeriv_bounded (R := (21 : ℝ)) (width := (1 : ℝ))
      (by norm_num) (by norm_num)
  refine ⟨C, hC0, ?_⟩
  intro t
  rw [show deriv (deriv pulseClip) t =
      saturationTemplateSecond 21 1 t by
    simpa [pulseClip] using
      (secondDeriv_saturationTemplate (R := (21 : ℝ)) (width := (1 : ℝ))
        (t := t))]
  exact hC t

private theorem frontierSwitch_second_deriv_eq_zero_of_not_mem
    {t : ℝ} (ht : t ∉ Set.Icc (-(1 : ℝ)) 2) :
    deriv (deriv frontierSwitch) t = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · have hfirst : Set.EqOn (deriv frontierSwitch) (fun _ : ℝ => 0)
        (Set.Iio (1 / 5 : ℝ)) := by
      intro x hx
      exact frontierSwitch_deriv_eq_zero_of_le_fifth hx.le
    have ht' : t ∈ Set.Iio (1 / 5 : ℝ) := by
      show t < (1 / 5 : ℝ)
      linarith
    simpa using hfirst.deriv isOpen_Iio ht'
  · have hvalue : Set.EqOn frontierSwitch (fun _ : ℝ => 1)
        (Set.Ioi (1 : ℝ)) := by
      intro x hx
      exact frontierSwitch_eq_one_of_one_le hx.le
    have hfirst : Set.EqOn (deriv frontierSwitch) (fun _ : ℝ => 0)
        (Set.Ioi (1 : ℝ)) := by
      intro x hx
      simpa using hvalue.deriv isOpen_Ioi hx
    have ht' : t ∈ Set.Ioi (1 : ℝ) := by
      show (1 : ℝ) < t
      linarith
    simpa using hfirst.deriv isOpen_Ioi ht'

/-- The composed frontier switch also has a globally bounded actual second
derivative.  The proof uses its literal constant tails, not merely smoothness
on a noncompact domain. -/
theorem frontierSwitch_second_deriv_bounded :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, |deriv (deriv frontierSwitch) t| ≤ C := by
  have hcont : Continuous (fun t : ℝ =>
      |deriv (deriv frontierSwitch) t|) := by
    have hf : ContDiff ℝ (2 : ℕ∞) frontierSwitch :=
      frontierSwitch_contDiff.of_le (by
        exact_mod_cast (show (2 : ℕ∞) ≤ ⊤ from le_top))
    have h := hf.continuous_iteratedDeriv' 2
    simpa [iteratedDeriv_succ] using h.abs
  obtain ⟨C, hC⟩ := bddAbove_def.mp
    (isCompact_Icc.bddAbove_image hcont.continuousOn)
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro t
  by_cases ht : t ∈ Set.Icc (-(1 : ℝ)) 2
  · exact (hC _ ⟨t, ht, rfl⟩).trans (le_max_left _ _)
  · rw [frontierSwitch_second_deriv_eq_zero_of_not_mem ht, abs_zero]
    exact le_max_right _ _

/-- The phase potential bound already proved for the concrete scalar
construction, restated directly for its actual second derivative. -/
theorem phasePotential_actual_second_deriv_bounded (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ t : ℝ, |deriv (deriv (phasePotential K)) t| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := phasePotential_second_bounded K
  refine ⟨C, hC0, ?_⟩
  intro t
  rw [phasePotential_second_deriv_eq]
  exact hC t

/-- One common finite second-derivative bound for every scalar interface in
the five-component construction (for the fixed phase parameter `K`). -/
theorem scalar_interfaces_common_second_deriv_bound (K : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      |deriv (deriv stateClip) t| ≤ C ∧
      |deriv (deriv pulseClip) t| ≤ C ∧
      |deriv (deriv frontierSwitch) t| ≤ C ∧
      |deriv (deriv (phasePotential K)) t| ≤ C := by
  obtain ⟨Cs, hCs0, hCs⟩ := stateClip_second_deriv_bounded
  obtain ⟨Cp, hCp0, hCp⟩ := pulseClip_second_deriv_bounded
  obtain ⟨Ca, hCa0, hCa⟩ := frontierSwitch_second_deriv_bounded
  obtain ⟨Cu, hCu0, hCu⟩ := phasePotential_actual_second_deriv_bounded K
  refine ⟨Cs + Cp + Ca + Cu, by positivity, ?_⟩
  intro t
  have hs := hCs t
  have hp := hCp t
  have ha := hCa t
  have hu := hCu t
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end
end CompositeSmoothness
end Simplified
end NCCLowerBound
