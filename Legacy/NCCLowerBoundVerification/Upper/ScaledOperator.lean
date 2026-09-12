import NCCLowerBoundVerification.Upper.ProjectedMicro
import NCCLowerBoundVerification.Upper.ProjectedVIExistence

/-!
# The scaled operator in the feasible micro-solver

This file formalizes the change of variables in TeX 1021--1160.  In the
paper's notation `mu = ell`, `gamma = theta = 8 / mu`, and the saddle-gradient
part is `2 * mu`-Lipschitz.  These values are important: replacing the paper's
`mu = ell` by `mu = 1 / (2 * ell)` does *not* give a dimension-free constant
`M0 = 32` from a `2 * ell` source Lipschitz bound.

The source hypotheses below are deliberately stated as predicates rather than
assuming the final strong-monotonicity/Lipschitz conclusions for the scaled
operator.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace ScaledOperator

noncomputable section

open ProjectionGeometry
open RelativeFOAM
open ProjectedMicro
open ProjectedVIExistence

abbrev Pair (m n : Nat) := EVec (m + n)

def pack {m n : Nat} (x : EVec m) (y : EVec n) : Pair m n :=
  Fin.append x y

def unpackX {m n : Nat} (u : Pair m n) : EVec m :=
  fun i => u (Fin.castAdd n i)

def unpackY {m n : Nat} (u : Pair m n) : EVec n :=
  fun j => u (Fin.natAdd m j)

@[simp] theorem unpackX_pack {m n : Nat} (x : EVec m) (y : EVec n) :
    unpackX (pack x y) = x := by
  funext i
  simp [unpackX, pack]

@[simp] theorem unpackY_pack {m n : Nat} (x : EVec m) (y : EVec n) :
    unpackY (pack x y) = y := by
  funext j
  simp [unpackY, pack]

@[simp] theorem pack_unpack {m n : Nat} (u : Pair m n) :
    pack (unpackX u) (unpackY u) = u := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [pack, unpackX, unpackY]

@[simp] theorem pack_zero {m n : Nat} :
    pack (0 : EVec m) (0 : EVec n) = 0 := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [pack]

@[simp] theorem pack_add {m n : Nat} (x x' : EVec m) (y y' : EVec n) :
    pack (x + x') (y + y') = pack x y + pack x' y' := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [pack]

@[simp] theorem pack_sub {m n : Nat} (x x' : EVec m) (y y' : EVec n) :
    pack (x - x') (y - y') = pack x y - pack x' y' := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [pack]

@[simp] theorem pack_smul {m n : Nat} (a : ℝ) (x : EVec m) (y : EVec n) :
    pack (a • x) (a • y) = a • pack x y := by
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j <;> simp [pack]

theorem vecSq_pack {m n : Nat} (x : EVec m) (y : EVec n) :
    vecSq (pack x y) = vecSq x + vecSq y := by
  unfold vecSq NCPLVerification.vecSq pack
  rw [Fin.sum_univ_add]
  simp

theorem vecDot_pack {m n : Nat} (x x' : EVec m) (y y' : EVec n) :
    vecDot (pack x y) (pack x' y') = vecDot x x' + vecDot y y' := by
  unfold vecDot pack
  rw [Fin.sum_univ_add]
  simp

def gamma (mu : ℝ) : ℝ := 8 / mu

def scaleRoot (mu : ℝ) : ℝ := Real.sqrt (gamma mu)

theorem gamma_pos {mu : ℝ} (hmu : 0 < mu) : 0 < gamma mu := by
  unfold gamma
  positivity

theorem scaleRoot_pos {mu : ℝ} (hmu : 0 < mu) : 0 < scaleRoot mu := by
  exact Real.sqrt_pos.2 (gamma_pos hmu)

theorem scaleRoot_sq {mu : ℝ} (hmu : 0 < mu) :
    scaleRoot mu ^ 2 = gamma mu := by
  exact Real.sq_sqrt (gamma_pos hmu).le

def scalePair {m n : Nat} (mu : ℝ) (x : EVec m) (y : EVec n) : Pair m n :=
  pack ((scaleRoot mu)⁻¹ • x) ((scaleRoot mu)⁻¹ • y)

def unscaleX {m n : Nat} (mu : ℝ) (u : Pair m n) : EVec m :=
  scaleRoot mu • unpackX u

def unscaleY {m n : Nat} (mu : ℝ) (u : Pair m n) : EVec n :=
  scaleRoot mu • unpackY u

@[simp] theorem unscaleX_scalePair {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (x : EVec m) (y : EVec n) : unscaleX mu (scalePair mu x y) = x := by
  unfold unscaleX scalePair
  rw [unpackX_pack]
  simp [ne_of_gt (scaleRoot_pos hmu)]

@[simp] theorem unscaleY_scalePair {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (x : EVec m) (y : EVec n) : unscaleY mu (scalePair mu x y) = y := by
  unfold unscaleY scalePair
  rw [unpackY_pack]
  simp [ne_of_gt (scaleRoot_pos hmu)]

theorem scalePair_unscale {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (u : Pair m n) : scalePair mu (unscaleX mu u) (unscaleY mu u) = u := by
  unfold scalePair unscaleX unscaleY
  have hs : scaleRoot mu ≠ 0 := ne_of_gt (scaleRoot_pos hmu)
  simp [smul_smul, hs, pack_unpack]

def scaledSet {m n : Nat} (mu : ℝ) (X : Set (EVec m)) (Y : Set (EVec n)) :
    Set (Pair m n) :=
  {u | unscaleX mu u ∈ X ∧ unscaleY mu u ∈ Y}

@[simp] theorem scalePair_mem_scaledSet_iff {m n : Nat} {mu : ℝ}
    (hmu : 0 < mu) {X : Set (EVec m)} {Y : Set (EVec n)}
    (x : EVec m) (y : EVec n) :
    scalePair mu x y ∈ scaledSet mu X Y ↔ x ∈ X ∧ y ∈ Y := by
  simp [scaledSet, hmu]

def scaledCenter {m n : Nat} (mu : ℝ) (qg : EVec m) (yg : EVec n) : Pair m n :=
  scalePair mu (-mu⁻¹ • qg) yg

/-- Monotonicity of the saddle-gradient map `(gradXHat, -gradYHat)`. -/
def SaddleGradientMonotone {m n : Nat}
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n) : Prop :=
  ∀ x y x' y',
    0 ≤ vecDot (gradXHat x y - gradXHat x' y') (x - x') -
      vecDot (gradYHat x y - gradYHat x' y') (y - y')

/-- Joint Euclidean Lipschitzness, in squared form. -/
def JointGradientLipschitz
    {m n : Nat} (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n) (L : ℝ) : Prop :=
  ∀ x y x' y',
    vecSq (gradXHat x y - gradXHat x' y') +
        vecSq (gradYHat x y - gradYHat x' y') ≤
      L ^ 2 * (vecSq (x - x') + vecSq (y - y'))

/-- The class-level saddle monotonicity assumption, only on `X × Y`. -/
def SaddleGradientMonotoneOn {m n : Nat}
    (X : Set (EVec m)) (Y : Set (EVec n))
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ x' ∈ X, ∀ y' ∈ Y,
    0 ≤ vecDot (gradXHat x y - gradXHat x' y') (x - x') -
      vecDot (gradYHat x y - gradYHat x' y') (y - y')

/-- The class-level joint Lipschitz assumption, only on `X × Y`. -/
def JointGradientLipschitzOn {m n : Nat}
    (X : Set (EVec m)) (Y : Set (EVec n))
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n) (L : ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, ∀ x' ∈ X, ∀ y' ∈ Y,
    vecSq (gradXHat x y - gradXHat x' y') +
        vecSq (gradYHat x y - gradYHat x' y') ≤
      L ^ 2 * (vecSq (x - x') + vecSq (y - y'))

/-- The operator `A_g` displayed in the TeX, in packed coordinates. -/
def scaledOperator {m n : Nat} (mu r : ℝ) (qg : EVec m) (yg : EVec n)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n) (u : Pair m n) : Pair m n :=
  let x := unscaleX mu u
  let y := unscaleY mu u
  pack
    (scaleRoot mu •
      (gradXHat x y + (mu / 2) • (x - mu⁻¹ • qg)))
    (scaleRoot mu •
      (-gradYHat x y + r • y + (gamma mu)⁻¹ • (y - yg)))

theorem gamma_inv {mu : ℝ} (hmu : 0 < mu) :
    (gamma mu)⁻¹ = mu / 8 := by
  unfold gamma
  field_simp

theorem vecSq_scalePair {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (x : EVec m) (y : EVec n) :
    vecSq (scalePair mu x y) =
      (gamma mu)⁻¹ * (vecSq x + vecSq y) := by
  rw [scalePair, vecSq_pack, vecSq_smul, vecSq_smul,
    ]
  have hs : scaleRoot mu ≠ 0 := ne_of_gt (scaleRoot_pos hmu)
  have hinvSq : (scaleRoot mu)⁻¹ ^ 2 = (gamma mu)⁻¹ := by
    rw [inv_pow, scaleRoot_sq hmu]
  rw [hinvSq]
  ring

theorem pair_difference {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (u v : Pair m n) :
    u - v = scalePair mu
      (unscaleX mu u - unscaleX mu v)
      (unscaleY mu u - unscaleY mu v) := by
  have hs : scaleRoot mu ≠ 0 := ne_of_gt (scaleRoot_pos hmu)
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro j
  · simp [scalePair, unscaleX, unpackX, pack, hs, smul_sub, smul_smul]
  · simp [scalePair, unscaleY, unpackY, pack, hs, smul_sub, smul_smul]

theorem scaledOperator_difference {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (r : ℝ) (qg : EVec m) (yg : EVec n)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n) (u v : Pair m n) :
    scaledOperator mu r qg yg gradXHat gradYHat u -
        scaledOperator mu r qg yg gradXHat gradYHat v =
      pack
        (scaleRoot mu •
          ((gradXHat (unscaleX mu u) (unscaleY mu u) -
              gradXHat (unscaleX mu v) (unscaleY mu v)) +
            (mu / 2) • (unscaleX mu u - unscaleX mu v)))
        (scaleRoot mu •
          (-(gradYHat (unscaleX mu u) (unscaleY mu u) -
              gradYHat (unscaleX mu v) (unscaleY mu v)) +
            (r + (gamma mu)⁻¹) •
              (unscaleY mu u - unscaleY mu v))) := by
  unfold scaledOperator
  rw [← pack_sub]
  congr 1 <;> funext i <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  · ring
  · ring

theorem scaledOperator_pairing {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (r : ℝ) (qg : EVec m) (yg : EVec n)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n) (u v : Pair m n) :
    vecDot
        (scaledOperator mu r qg yg gradXHat gradYHat u -
          scaledOperator mu r qg yg gradXHat gradYHat v)
        (u - v) =
      vecDot
          (gradXHat (unscaleX mu u) (unscaleY mu u) -
            gradXHat (unscaleX mu v) (unscaleY mu v))
          (unscaleX mu u - unscaleX mu v) -
      vecDot
          (gradYHat (unscaleX mu u) (unscaleY mu u) -
            gradYHat (unscaleX mu v) (unscaleY mu v))
          (unscaleY mu u - unscaleY mu v) +
      (mu / 2) * vecSq (unscaleX mu u - unscaleX mu v) +
      (r + (gamma mu)⁻¹) *
        vecSq (unscaleY mu u - unscaleY mu v) := by
  rw [scaledOperator_difference hmu, pair_difference hmu,
    show scalePair mu
      (unscaleX mu u - unscaleX mu v)
      (unscaleY mu u - unscaleY mu v) =
      pack ((scaleRoot mu)⁻¹ • (unscaleX mu u - unscaleX mu v))
        ((scaleRoot mu)⁻¹ • (unscaleY mu u - unscaleY mu v)) from rfl,
    vecDot_pack]
  unfold vecDot vecSq NCPLVerification.vecSq
  simp only [unpackX_pack, unpackY_pack, Pi.add_apply, Pi.sub_apply,
    Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  have hs : scaleRoot mu ≠ 0 := ne_of_gt (scaleRoot_pos hmu)
  have hx :
      (∑ i : Fin m,
        scaleRoot mu *
            ((gradXHat (unscaleX mu u) (unscaleY mu u) i -
                gradXHat (unscaleX mu v) (unscaleY mu v) i) +
              mu / 2 * (unscaleX mu u i - unscaleX mu v i)) *
          ((scaleRoot mu)⁻¹ * (unscaleX mu u i - unscaleX mu v i))) =
        (∑ i : Fin m,
          (gradXHat (unscaleX mu u) (unscaleY mu u) i -
            gradXHat (unscaleX mu v) (unscaleY mu v) i) *
              (unscaleX mu u i - unscaleX mu v i)) +
        mu / 2 * ∑ i : Fin m, (unscaleX mu u i - unscaleX mu v i) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hy :
      (∑ i : Fin n,
        scaleRoot mu *
            (-(gradYHat (unscaleX mu u) (unscaleY mu u) i -
                gradYHat (unscaleX mu v) (unscaleY mu v) i) +
              (r + (gamma mu)⁻¹) *
                (unscaleY mu u i - unscaleY mu v i)) *
          ((scaleRoot mu)⁻¹ * (unscaleY mu u i - unscaleY mu v i))) =
        -(∑ i : Fin n,
          (gradYHat (unscaleX mu u) (unscaleY mu u) i -
            gradYHat (unscaleX mu v) (unscaleY mu v) i) *
              (unscaleY mu u i - unscaleY mu v i)) +
        (r + (gamma mu)⁻¹) *
          ∑ i : Fin n, (unscaleY mu u i - unscaleY mu v i) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  rw [hx, hy]
  ring

/-- The scaled operator is one-strongly monotone.  This is derived from the
source saddle-gradient monotonicity and the paper's affine regularizers. -/
theorem scaledOperator_stronglyMonotone {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r) (qg : EVec m) (yg : EVec n)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n)
    (hmon : SaddleGradientMonotone gradXHat gradYHat) :
    IsStronglyMonotone (scaledOperator mu r qg yg gradXHat gradYHat) 1 := by
  intro u v
  let dx := unscaleX mu u - unscaleX mu v
  let dy := unscaleY mu u - unscaleY mu v
  have hm := hmon (unscaleX mu u) (unscaleY mu u)
    (unscaleX mu v) (unscaleY mu v)
  have hx := ProjectionGeometry.vecSq_nonneg dx
  have hy := ProjectionGeometry.vecSq_nonneg dy
  rw [one_mul, scaledOperator_pairing hmu]
  rw [pair_difference hmu, vecSq_scalePair hmu, gamma_inv hmu]
  dsimp [dx, dy] at hm hx hy ⊢
  nlinarith

theorem scaledOperator_stronglyMonotoneOn {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (qg : EVec m) (yg : EVec n)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n)
    (hmon : SaddleGradientMonotoneOn X Y gradXHat gradYHat) :
    IsStronglyMonotoneOn (scaledSet mu X Y)
      (scaledOperator mu r qg yg gradXHat gradYHat) 1 := by
  intro u hu v hv
  let dx := unscaleX mu u - unscaleX mu v
  let dy := unscaleY mu u - unscaleY mu v
  have hm := hmon (unscaleX mu u) hu.1 (unscaleY mu u) hu.2
    (unscaleX mu v) hv.1 (unscaleY mu v) hv.2
  have hx := ProjectionGeometry.vecSq_nonneg dx
  have hy := ProjectionGeometry.vecSq_nonneg dy
  rw [one_mul, scaledOperator_pairing hmu]
  rw [pair_difference hmu, vecSq_scalePair hmu, gamma_inv hmu]
  dsimp [dx, dy] at hm hx hy ⊢
  nlinarith

theorem vecSq_add_le_two {d : Nat} (a b : EVec d) :
    vecSq (a + b) ≤ 2 * vecSq a + 2 * vecSq b := by
  unfold vecSq NCPLVerification.vecSq
  calc
    (∑ i, (a + b) i ^ 2) ≤ ∑ i, (2 * a i ^ 2 + 2 * b i ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [Pi.add_apply]
      nlinarith [sq_nonneg (a i - b i)]
    _ = 2 * ∑ i, a i ^ 2 + 2 * ∑ i, b i ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

theorem vecSq_neg_add_le_two {d : Nat} (a b : EVec d) :
    vecSq (-a + b) ≤ 2 * vecSq a + 2 * vecSq b := by
  have h := vecSq_add_le_two (-a) b
  simpa [Tracking.vecSq_neg] using h

theorem gamma_mul_mu {mu : ℝ} (hmu : 0 < mu) : gamma mu * mu = 8 := by
  unfold gamma
  field_simp

/-- With the constants actually stated in the TeX (`mu = ell`, hence source
constant `2 * mu`), `A_g` is `M0 = 32` Lipschitz. -/
theorem scaledOperator_lipschitz {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r) (hrmu : r ≤ mu / 8)
    (qg : EVec m) (yg : EVec n)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n)
    (hlip : JointGradientLipschitz gradXHat gradYHat (2 * mu)) :
    IsEuclideanLipschitz
      (scaledOperator mu r qg yg gradXHat gradYHat) M0 := by
  intro u v
  let dx := unscaleX mu u - unscaleX mu v
  let dy := unscaleY mu u - unscaleY mu v
  let gx := gradXHat (unscaleX mu u) (unscaleY mu u) -
    gradXHat (unscaleX mu v) (unscaleY mu v)
  let gy := gradYHat (unscaleX mu u) (unscaleY mu u) -
    gradYHat (unscaleX mu v) (unscaleY mu v)
  let b := r + (gamma mu)⁻¹
  have hsource := hlip (unscaleX mu u) (unscaleY mu u)
    (unscaleX mu v) (unscaleY mu v)
  have hsource' :
      vecSq gx + vecSq gy ≤ (2 * mu) ^ 2 * (vecSq dx + vecSq dy) := by
    simpa [gx, gy, dx, dy] using hsource
  have hx := vecSq_add_le_two gx ((mu / 2) • dx)
  have hy := vecSq_neg_add_le_two gy (b • dy)
  rw [vecSq_smul] at hx hy
  have hdx := ProjectionGeometry.vecSq_nonneg dx
  have hdy := ProjectionGeometry.vecSq_nonneg dy
  have hgamma := gamma_pos hmu
  have hb : b ≤ mu / 4 := by
    dsimp [b]
    rw [gamma_inv hmu]
    linarith
  have hb0 : 0 ≤ b := by
    dsimp [b]
    rw [gamma_inv hmu]
    positivity
  have hbSq : b ^ 2 ≤ (mu / 4) ^ 2 := by
    nlinarith
  have hop :
      vecSq
          (scaledOperator mu r qg yg gradXHat gradYHat u -
            scaledOperator mu r qg yg gradXHat gradYHat v) =
        gamma mu *
          (vecSq (gx + (mu / 2) • dx) +
            vecSq (-gy + b • dy)) := by
    rw [scaledOperator_difference hmu, vecSq_pack,
      vecSq_smul, vecSq_smul, scaleRoot_sq hmu]
    dsimp [gx, gy, dx, dy, b]
    ring
  have huv :
      vecSq (u - v) = (gamma mu)⁻¹ * (vecSq dx + vecSq dy) := by
    rw [pair_difference hmu, vecSq_scalePair hmu]
  rw [hop, huv]
  rw [M0]
  have hgm := gamma_mul_mu hmu
  have hginv := gamma_inv hmu
  rw [hginv]
  have hbSqDy : b ^ 2 * vecSq dy ≤ (mu / 4) ^ 2 * vecSq dy :=
    mul_le_mul_of_nonneg_right hbSq hdy
  have hinside :
      vecSq (gx + (mu / 2) • dx) + vecSq (-gy + b • dy) ≤
        9 * mu ^ 2 * (vecSq dx + vecSq dy) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hinside hgamma.le
  have hjoint : 0 ≤ vecSq dx + vecSq dy := add_nonneg hdx hdy
  have hscaled' :
      gamma mu *
          (vecSq (gx + (mu / 2) • dx) + vecSq (-gy + b • dy)) ≤
        72 * mu * (vecSq dx + vecSq dy) := by
    calc
      _ ≤ gamma mu * (9 * mu ^ 2 * (vecSq dx + vecSq dy)) := hscaled
      _ = 9 * (gamma mu * mu) * mu * (vecSq dx + vecSq dy) := by ring
      _ = 72 * mu * (vecSq dx + vecSq dy) := by rw [hgm]; ring
  norm_num
  nlinarith

theorem scaledOperator_lipschitzOn {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r) (hrmu : r ≤ mu / 8)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (qg : EVec m) (yg : EVec n)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n)
    (hlip : JointGradientLipschitzOn X Y gradXHat gradYHat (2 * mu)) :
    IsEuclideanLipschitzOn (scaledSet mu X Y)
      (scaledOperator mu r qg yg gradXHat gradYHat) M0 := by
  intro u hu v hv
  let dx := unscaleX mu u - unscaleX mu v
  let dy := unscaleY mu u - unscaleY mu v
  let gx := gradXHat (unscaleX mu u) (unscaleY mu u) -
    gradXHat (unscaleX mu v) (unscaleY mu v)
  let gy := gradYHat (unscaleX mu u) (unscaleY mu u) -
    gradYHat (unscaleX mu v) (unscaleY mu v)
  let b := r + (gamma mu)⁻¹
  have hsource := hlip (unscaleX mu u) hu.1 (unscaleY mu u) hu.2
    (unscaleX mu v) hv.1 (unscaleY mu v) hv.2
  have hsource' :
      vecSq gx + vecSq gy ≤ (2 * mu) ^ 2 * (vecSq dx + vecSq dy) := by
    simpa [gx, gy, dx, dy] using hsource
  have hx := vecSq_add_le_two gx ((mu / 2) • dx)
  have hy := vecSq_neg_add_le_two gy (b • dy)
  rw [vecSq_smul] at hx hy
  have hdx := ProjectionGeometry.vecSq_nonneg dx
  have hdy := ProjectionGeometry.vecSq_nonneg dy
  have hgamma := gamma_pos hmu
  have hb : b ≤ mu / 4 := by
    dsimp [b]
    rw [gamma_inv hmu]
    linarith
  have hb0 : 0 ≤ b := by
    dsimp [b]
    rw [gamma_inv hmu]
    positivity
  have hbSq : b ^ 2 ≤ (mu / 4) ^ 2 := by
    nlinarith
  have hop :
      vecSq
          (scaledOperator mu r qg yg gradXHat gradYHat u -
            scaledOperator mu r qg yg gradXHat gradYHat v) =
        gamma mu *
          (vecSq (gx + (mu / 2) • dx) +
            vecSq (-gy + b • dy)) := by
    rw [scaledOperator_difference hmu, vecSq_pack,
      vecSq_smul, vecSq_smul, scaleRoot_sq hmu]
    dsimp [gx, gy, dx, dy, b]
    ring
  have huv :
      vecSq (u - v) = (gamma mu)⁻¹ * (vecSq dx + vecSq dy) := by
    rw [pair_difference hmu, vecSq_scalePair hmu]
  rw [hop, huv]
  rw [M0]
  have hgm := gamma_mul_mu hmu
  have hginv := gamma_inv hmu
  rw [hginv]
  have hbSqDy : b ^ 2 * vecSq dy ≤ (mu / 4) ^ 2 * vecSq dy :=
    mul_le_mul_of_nonneg_right hbSq hdy
  have hinside :
      vecSq (gx + (mu / 2) • dx) + vecSq (-gy + b • dy) ≤
        9 * mu ^ 2 * (vecSq dx + vecSq dy) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hinside hgamma.le
  have hjoint : 0 ≤ vecSq dx + vecSq dy := add_nonneg hdx hdy
  have hscaled' :
      gamma mu *
          (vecSq (gx + (mu / 2) • dx) + vecSq (-gy + b • dy)) ≤
        72 * mu * (vecSq dx + vecSq dy) := by
    calc
      _ ≤ gamma mu * (9 * mu ^ 2 * (vecSq dx + vecSq dy)) := hscaled
      _ = 9 * (gamma mu * mu) * mu * (vecSq dx + vecSq dy) := by ring
      _ = 72 * mu * (vecSq dx + vecSq dy) := by rw [hgm]; ring
  norm_num
  nlinarith

def scaledProject {m n : Nat} (mu : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (u : Pair m n) : Pair m n :=
  scalePair mu (projectX (unscaleX mu u)) (projectY (unscaleY mu u))

@[simp] theorem unscaleX_scaledProject {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (u : Pair m n) :
    unscaleX mu (scaledProject mu projectX projectY u) =
      projectX (unscaleX mu u) := by
  simp [scaledProject, hmu]

@[simp] theorem unscaleY_scaledProject {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (u : Pair m n) :
    unscaleY mu (scaledProject mu projectX projectY u) =
      projectY (unscaleY mu u) := by
  simp [scaledProject, hmu]

theorem vecDot_scalePair {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (x x' : EVec m) (y y' : EVec n) :
    vecDot (scalePair mu x y) (scalePair mu x' y') =
      (gamma mu)⁻¹ * (vecDot x x' + vecDot y y') := by
  rw [scalePair, scalePair, vecDot_pack]
  unfold vecDot
  simp only [Pi.smul_apply, smul_eq_mul]
  have hs : scaleRoot mu ≠ 0 := ne_of_gt (scaleRoot_pos hmu)
  have hinvSq : (scaleRoot mu)⁻¹ ^ 2 = (gamma mu)⁻¹ := by
    rw [inv_pow, scaleRoot_sq hmu]
  have hxsum :
      (∑ i : Fin m, (scaleRoot mu)⁻¹ * x i * ((scaleRoot mu)⁻¹ * x' i)) =
        (scaleRoot mu)⁻¹ ^ 2 * ∑ i : Fin m, x i * x' i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hysum :
      (∑ i : Fin n, (scaleRoot mu)⁻¹ * y i * ((scaleRoot mu)⁻¹ * y' i)) =
        (scaleRoot mu)⁻¹ ^ 2 * ∑ i : Fin n, y i * y' i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hxsum, hysum, hinvSq]
  ring

/-- Product projections become the projection onto the scaled product set. -/
theorem scaledProject_isProjection {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hX : IsEuclideanProjection X projectX)
    (hY : IsEuclideanProjection Y projectY) :
    IsEuclideanProjection (scaledSet mu X Y)
      (scaledProject mu projectX projectY) := by
  constructor
  · intro u
    simp [scaledSet, scaledProject, hmu, hX.mem, hY.mem]
  · intro u z hz
    have hx := hX.normal (unscaleX mu u) (unscaleX mu z) hz.1
    have hy := hY.normal (unscaleY mu u) (unscaleY mu z) hz.2
    change vecDot
      (u - scaledProject mu projectX projectY u)
      (z - scaledProject mu projectX projectY u) ≤ 0
    rw [pair_difference hmu, pair_difference hmu,
      unscaleX_scaledProject hmu, unscaleY_scaledProject hmu,
      vecDot_scalePair hmu]
    change vecDot
      (unscaleX mu u - projectX (unscaleX mu u))
      (unscaleX mu z - projectX (unscaleX mu u)) ≤ 0 at hx
    change vecDot
      (unscaleY mu u - projectY (unscaleY mu u))
      (unscaleY mu z - projectY (unscaleY mu u)) ≤ 0 at hy
    exact mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (inv_pos.mpr (gamma_pos hmu))) (add_nonpos hx hy)

def unscaledNormalX {m n : Nat} (mu : ℝ) (b : Pair m n) : EVec m :=
  (scaleRoot mu)⁻¹ • unpackX b

def unscaledNormalY {m n : Nat} (mu : ℝ) (b : Pair m n) : EVec n :=
  (scaleRoot mu)⁻¹ • unpackY b

/-- A normal to the scaled product unscales to normals of both factors. -/
theorem unscale_normal {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    {X : Set (EVec m)} {Y : Set (EVec n)} {u b : Pair m n}
    (hu : u ∈ scaledSet mu X Y)
    (hb : IsEuclideanNormal (scaledSet mu X Y) u b) :
    IsEuclideanNormal X (unscaleX mu u) (unscaledNormalX mu b) ∧
      IsEuclideanNormal Y (unscaleY mu u) (unscaledNormalY mu b) := by
  constructor
  · intro x hx
    have h := hb (scalePair mu x (unscaleY mu u))
      ((scalePair_mem_scaledSet_iff hmu x (unscaleY mu u)).2 ⟨hx, hu.2⟩)
    change vecDot b
      (scalePair mu x (unscaleY mu u) - u) ≤ 0 at h
    rw [show u = scalePair mu (unscaleX mu u) (unscaleY mu u) by
      exact (scalePair_unscale hmu u).symm] at h
    simp only [unscaleY_scalePair hmu] at h
    unfold scalePair at h
    rw [← pack_sub] at h
    simp only [← smul_sub, sub_self, smul_zero] at h
    change vecDot b
      (pack ((scaleRoot mu)⁻¹ • (x - unscaleX mu u)) 0) ≤ 0 at h
    change vecDot (unscaledNormalX mu b) (x - unscaleX mu u) ≤ 0
    unfold vecDot at h
    unfold vecDot unscaledNormalX
    rw [Fin.sum_univ_add] at h
    simpa [pack, unpackX, mul_assoc, mul_left_comm, mul_comm] using h
  · intro y hy
    have h := hb (scalePair mu (unscaleX mu u) y)
      ((scalePair_mem_scaledSet_iff hmu (unscaleX mu u) y).2 ⟨hu.1, hy⟩)
    change vecDot b
      (scalePair mu (unscaleX mu u) y - u) ≤ 0 at h
    rw [show u = scalePair mu (unscaleX mu u) (unscaleY mu u) by
      exact (scalePair_unscale hmu u).symm] at h
    simp only [unscaleX_scalePair hmu] at h
    unfold scalePair at h
    rw [← pack_sub] at h
    simp only [← smul_sub, sub_self, smul_zero] at h
    change vecDot b
      (pack 0 ((scaleRoot mu)⁻¹ • (y - unscaleY mu u))) ≤ 0 at h
    change vecDot (unscaledNormalY mu b) (y - unscaleY mu u) ≤ 0
    unfold vecDot at h
    unfold vecDot unscaledNormalY
    rw [Fin.sum_univ_add] at h
    simpa [pack, unpackY, mul_assoc, mul_left_comm, mul_comm] using h

def decodeOutput {m n : Nat} (mu : ℝ)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n)
    (u b : Pair m n) : MicroOutput m n where
  xFast := unscaleX mu u
  yFastNext := unscaleY mu u
  qFastNext := gradXHat (unscaleX mu u) (unscaleY mu u) +
    unscaledNormalX mu b
  wFastNext := -gradYHat (unscaleX mu u) (unscaleY mu u) +
    unscaledNormalY mu b

theorem decodeOutput_normalRelations {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n)
    {u b : Pair m n} (hu : u ∈ scaledSet mu X Y)
    (hb : IsEuclideanNormal (scaledSet mu X Y) u b) :
    MicroNormalRelations X Y gradXHat gradYHat
      (decodeOutput mu gradXHat gradYHat u b) := by
  obtain ⟨hx, hy⟩ := unscale_normal hmu hu hb
  constructor
  · simpa [decodeOutput] using hx
  · simpa [decodeOutput] using hy

theorem scaled_residual_vector {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (r : ℝ) (qg : EVec m) (yg : EVec n)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n)
    (u b : Pair m n) :
    scaledOperator mu r qg yg gradXHat gradYHat u + b =
      pack
        (scaleRoot mu •
          ((decodeOutput mu gradXHat gradYHat u b).qFastNext +
            (mu / 2) •
              ((decodeOutput mu gradXHat gradYHat u b).xFast - mu⁻¹ • qg)))
        (scaleRoot mu •
          ((decodeOutput mu gradXHat gradYHat u b).wFastNext +
            r • (decodeOutput mu gradXHat gradYHat u b).yFastNext +
            (gamma mu)⁻¹ •
              ((decodeOutput mu gradXHat gradYHat u b).yFastNext - yg))) := by
  have hs : scaleRoot mu ≠ 0 := ne_of_gt (scaleRoot_pos hmu)
  unfold scaledOperator
  conv_lhs => rw [← pack_unpack b]
  rw [← pack_add]
  unfold decodeOutput unscaledNormalX unscaledNormalY
  congr 1 <;> funext i <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  · field_simp
    ring
  · field_simp
    ring

theorem scaled_residual_sq {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (r : ℝ) (S : State m n)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n)
    (u b : Pair m n) :
    let O := decodeOutput mu gradXHat gradYHat u b
    vecSq
        (scaledOperator mu r (qCenter mu r S) (yCenter mu r S)
          gradXHat gradYHat u + b) =
      8 / mu * vecSq (residualX mu r S O) +
        theta mu * vecSq (residualY mu r S O) := by
  dsimp only
  rw [scaled_residual_vector hmu, vecSq_pack, vecSq_smul, vecSq_smul,
    scaleRoot_sq hmu]
  unfold residualX residualY theta gamma
  ring

theorem scaled_center_sq {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (qg : EVec m) (yg : EVec n) (u : Pair m n) :
    vecSq (u - scaledCenter mu qg yg) =
      mu / 8 * vecSq (unscaleX mu u + mu⁻¹ • qg) +
        (theta mu)⁻¹ * vecSq (unscaleY mu u - yg) := by
  rw [pair_difference hmu, vecSq_scalePair hmu, gamma_inv hmu]
  unfold scaledCenter
  rw [unscaleX_scalePair hmu, unscaleY_scalePair hmu]
  unfold theta
  have ht : (8 / mu)⁻¹ = mu / 8 := by field_simp
  rw [ht]
  have hx : unscaleX mu u - -mu⁻¹ • qg =
      unscaleX mu u + mu⁻¹ • qg := by module
  rw [hx]
  ring

/-- The squared stopping test is exactly the paper's relative residual test. -/
theorem stopping_iff_relativeResidual {m n : Nat} {mu : ℝ} (hmu : 0 < mu)
    (r : ℝ) (S : State m n)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n)
    (u b : Pair m n) :
    vecSq
        (scaledOperator mu r (qCenter mu r S) (yCenter mu r S)
          gradXHat gradYHat u + b) ≤
        vecSq (u - scaledCenter mu (qCenter mu r S) (yCenter mu r S)) ↔
      RelativeResidual mu r S
        (decodeOutput mu gradXHat gradYHat u b) := by
  rw [scaled_residual_sq hmu, scaled_center_sq hmu]
  rfl

/-- The actual feasible micro-solver obtained by instantiating
`ProjectedMicro.projectedMicro_certificate` with the scaled operator.  The
only extra premise is a solution of the scaled variational inequality; this is
the existence fact supplied by the paper's compactness/coercivity argument. -/
theorem feasibleMicro_scaledOperator {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r) (hrmu : r ≤ mu / 8)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hX : IsEuclideanProjection X projectX)
    (hY : IsEuclideanProjection Y projectY)
    (S : State m n)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n)
    (hmon : SaddleGradientMonotoneOn X Y gradXHat gradYHat)
    (hlip : JointGradientLipschitzOn X Y gradXHat gradYHat (2 * mu))
    (uStar : Pair m n)
    (huStar : uStar ∈ scaledSet mu X Y)
    (hstar : IsEuclideanNormal (scaledSet mu X Y) uStar
      (-scaledOperator mu r (qCenter mu r S) (yCenter mu r S)
        gradXHat gradYHat uStar)) :
    let A := scaledOperator mu r (qCenter mu r S) (yCenter mu r S)
      gradXHat gradYHat
    let project := scaledProject mu projectX projectY
    let center := scaledCenter mu (qCenter mu r S) (yCenter mu r S)
    let N := feasibleMicroIterations
    let uN := RelativeFOAM.projectedIterate project A (M0 ^ 2)⁻¹ center N
    let bN := RelativeFOAM.projectedB project A (M0 ^ 2)⁻¹ center (N - 1)
    1 ≤ N ∧
      uN ∈ scaledSet mu X Y ∧
      MicroNormalRelations X Y gradXHat gradYHat
        (decodeOutput mu gradXHat gradYHat uN bN) ∧
      RelativeResidual mu r S
        (decodeOutput mu gradXHat gradYHat uN bN) := by
  let A := scaledOperator mu r (qCenter mu r S) (yCenter mu r S)
    gradXHat gradYHat
  let project := scaledProject mu projectX projectY
  let center := scaledCenter mu (qCenter mu r S) (yCenter mu r S)
  let N := feasibleMicroIterations
  let uN := RelativeFOAM.projectedIterate project A (M0 ^ 2)⁻¹ center N
  let bN := RelativeFOAM.projectedB project A (M0 ^ 2)⁻¹ center (N - 1)
  have hp : IsEuclideanProjection (scaledSet mu X Y) project := by
    exact scaledProject_isProjection hmu hX hY
  have hmonoA : IsStronglyMonotoneOn (scaledSet mu X Y) A 1 := by
    exact scaledOperator_stronglyMonotoneOn hmu hr _ _ _ _ hmon
  have hlipA : IsEuclideanLipschitzOn (scaledSet mu X Y) A M0 := by
    exact scaledOperator_lipschitzOn hmu hr hrmu _ _ _ _ hlip
  have cert := projectedMicro_certificate_on hp M0_ge_one hmonoA hlipA
    huStar hstar center
  change 1 ≤ N ∧ uN ∈ scaledSet mu X Y ∧
    IsEuclideanNormal (scaledSet mu X Y) uN bN ∧
    euclideanLength (A uN + bN) ≤ euclideanLength (uN - center) at cert
  have hsq : vecSq (A uN + bN) ≤ vecSq (uN - center) := by
    have hleft := euclideanLength_sq (A uN + bN)
    have hright := euclideanLength_sq (uN - center)
    have hleft0 := euclideanLength_nonneg (A uN + bN)
    have hright0 := euclideanLength_nonneg (uN - center)
    nlinarith [cert.2.2.2]
  refine ⟨cert.1, cert.2.1,
    decodeOutput_normalRelations hmu gradXHat gradYHat cert.2.1 cert.2.2.1, ?_⟩
  apply (stopping_iff_relativeResidual hmu r S gradXHat gradYHat uN bN).1
  exact hsq

/-- The fully closed feasible micro-solver theorem.  Unlike
`feasibleMicro_scaledOperator`, this statement does not assume a solution of
the scaled variational inequality.  Banach existence on the closed scaled
feasible set constructs that solution from the restricted (`On`) operator
properties, after which the existing theorem supplies the finite micro
certificate. -/
theorem feasibleMicro_scaledOperator_of_closedConvex {m n : Nat}
    {mu r : ℝ} (hmu : 0 < mu) (hr : 0 ≤ r) (hrmu : r ≤ mu / 8)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hCne : (scaledSet mu X Y).Nonempty)
    (hCclosed : IsClosed (scaledSet mu X Y))
    (hCconvex : Convex ℝ (scaledSet mu X Y))
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hX : IsEuclideanProjection X projectX)
    (hY : IsEuclideanProjection Y projectY)
    (S : State m n)
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n)
    (hmon : SaddleGradientMonotoneOn X Y gradXHat gradYHat)
    (hlip : JointGradientLipschitzOn X Y gradXHat gradYHat (2 * mu)) :
    let A := scaledOperator mu r (qCenter mu r S) (yCenter mu r S)
      gradXHat gradYHat
    let project := scaledProject mu projectX projectY
    let center := scaledCenter mu (qCenter mu r S) (yCenter mu r S)
    let N := feasibleMicroIterations
    let uN := RelativeFOAM.projectedIterate project A (M0 ^ 2)⁻¹ center N
    let bN := RelativeFOAM.projectedB project A (M0 ^ 2)⁻¹ center (N - 1)
    1 ≤ N ∧
      uN ∈ scaledSet mu X Y ∧
      MicroNormalRelations X Y gradXHat gradYHat
        (decodeOutput mu gradXHat gradYHat uN bN) ∧
      RelativeResidual mu r S
        (decodeOutput mu gradXHat gradYHat uN bN) := by
  let A := scaledOperator mu r (qCenter mu r S) (yCenter mu r S)
    gradXHat gradYHat
  let project := scaledProject mu projectX projectY
  have hp : IsEuclideanProjection (scaledSet mu X Y) project := by
    exact scaledProject_isProjection hmu hX hY
  have hmonoA : IsStronglyMonotoneOn (scaledSet mu X Y) A 1 := by
    exact scaledOperator_stronglyMonotoneOn hmu hr _ _ _ _ hmon
  have hlipA : IsEuclideanLipschitzOn (scaledSet mu X Y) A M0 := by
    exact scaledOperator_lipschitzOn hmu hr hrmu _ _ _ _ hlip
  obtain ⟨uStar, huStar, hstar⟩ :=
    exists_projectedVI_solution hCne hCclosed hCconvex hp M0_ge_one
      hmonoA hlipA
  exact feasibleMicro_scaledOperator hmu hr hrmu hX hY S
    gradXHat gradYHat hmon hlip uStar huStar hstar

end

end ScaledOperator
end Upper
end NCCLowerBoundVerification
