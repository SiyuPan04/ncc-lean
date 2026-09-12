import NCC.Extensions.GameStationarity

/-! A feasible projected step turns proximity to a regularized saddle
point into an explicit normal-cone residual. This is the output conversion
needed by the GS extension, not a replacement of GS by a gradient mapping. -/
namespace NCC.Extensions.ProjectedReadout
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open RelativeFOAM ProjectionGeometry ScaledOperator
open NCC.Model NCC.Upper.WithinSystem

theorem square_sub_le {d : Nat} (a b : EVec d) :
    vecSq (a - b) ≤ 2 * vecSq a + 2 * vecSq b := by
  simpa only [sub_eq_add_neg, Tracking.vecSq_neg] using vecSq_add_le_two a (-b)

/-- A single feasible projected step with step size `1/ell`.
The deliberately loose numerical constants simplify later use. -/
theorem residual_of_proximity {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {ell : ℝ} (hell : 0 < ell) {A : EVec d → EVec d}
    (hlip : ∀ u ∈ C, ∀ v ∈ C,
      vecSq (A u - A v) ≤ 10 * ell ^ 2 * vecSq (u - v))
    {star u : EVec d} (hstar : star ∈ C) (hu : u ∈ C)
    (hnormal : IsEuclideanNormal C star (-A star)) :
    let w := project (u - ell⁻¹ • A u)
    let b := ell • (u - ell⁻¹ • A u - w)
    w ∈ C ∧ IsEuclideanNormal C w b ∧
      vecSq (w - star) ≤ 22 * vecSq (u - star) ∧
      vecSq (A w + b) ≤ 1012 * ell ^ 2 * vecSq (u - star) := by
  let w := project (u - ell⁻¹ • A u)
  have hw : w ∈ C := hp.mem _
  have hfixed : project (star - ell⁻¹ • A star) = star :=
    projectedStep_fixed_of_normal hp (inv_nonneg.mpr hell.le) hstar hnormal
  have hproj := projection_nonexpansive hp
    (u - ell⁻¹ • A u) (star - ell⁻¹ • A star)
  rw [hfixed] at hproj
  have harg : (u - ell⁻¹ • A u) - (star - ell⁻¹ • A star) =
      (u - star) - ell⁻¹ • (A u - A star) := by module
  rw [harg] at hproj
  have htri := square_sub_le (u - star) (ell⁻¹ • (A u - A star))
  rw [vecSq_smul] at htri
  have hg := hlip u hu star hstar
  have hinv := mul_le_mul_of_nonneg_left hg (sq_nonneg ell⁻¹)
  have hcancel : ell⁻¹ ^ 2 * (10 * ell ^ 2 * vecSq (u - star)) =
      10 * vecSq (u - star) := by field_simp
  rw [hcancel] at hinv
  have hclose : vecSq (w - star) ≤ 22 * vecSq (u - star) := by
    dsimp only [w]
    linarith
  have hdiff : vecSq (w - u) ≤ 46 * vecSq (u - star) := by
    have ht := square_sub_le (w - star) (u - star)
    have heq : (w - star) - (u - star) = w - u := by module
    rw [heq] at ht
    linarith
  have hresEq : A w + ell • (u - ell⁻¹ • A u - w) =
      (A w - A u) + ell • (u - w) := by
    ext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  refine ⟨hw, (hp.normal _).nonneg_smul hell.le, hclose, ?_⟩
  change vecSq (A w + ell • (u - ell⁻¹ • A u - w)) ≤ _
  rw [hresEq]
  have ht := vecSq_add_le_two (A w - A u) (ell • (u - w))
  rw [vecSq_smul, vecSq_sub_comm u w] at ht
  have hgu := hlip w hw u hu
  have hm := mul_le_mul_of_nonneg_left hdiff (sq_nonneg ell)
  nlinarith

def pairSet {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n)) : Set (Pair m n) :=
  {u | unpackX u ∈ X ∧ unpackY u ∈ Y}

def pairProject {m n : Nat} (projectX : EVec m → EVec m)
    (projectY : EVec n → EVec n) (u : Pair m n) : Pair m n :=
  pack (projectX (unpackX u)) (projectY (unpackY u))

theorem normal_pair {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {x bx : EVec m} {y byy : EVec n}
    (hx : IsEuclideanNormal X x bx) (hy : IsEuclideanNormal Y y byy) :
    IsEuclideanNormal (pairSet X Y) (pack x y) (pack bx byy) := by
  intro v hv
  have h1 := hx (unpackX v) hv.1
  have h2 := hy (unpackY v) hv.2
  change vecDot (pack bx byy) (v - pack x y) ≤ 0
  rw [← pack_unpack v, ← pack_sub, vecDot_pack]
  exact add_nonpos h1 h2

theorem normal_unpair {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {u b : Pair m n} (hu : u ∈ pairSet X Y)
    (hb : IsEuclideanNormal (pairSet X Y) u b) :
    IsEuclideanNormal X (unpackX u) (unpackX b) ∧
      IsEuclideanNormal Y (unpackY u) (unpackY b) := by
  constructor
  · intro x hx
    have h := hb (pack x (unpackY u)) (by simpa only [pairSet, Set.mem_setOf_eq,
      unpackX_pack, unpackY_pack] using And.intro hx hu.2)
    change vecDot b (pack x (unpackY u) - u) ≤ 0 at h
    rw [← pack_unpack b, ← pack_unpack u, ← pack_sub, vecDot_pack] at h
    simpa only [unpackY_pack, sub_self, vecDot, Pi.sub_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      add_zero] using h
  · intro y hy
    have h := hb (pack (unpackX u) y) (by simpa only [pairSet, Set.mem_setOf_eq,
      unpackX_pack, unpackY_pack] using And.intro hu.1 hy)
    change vecDot b (pack (unpackX u) y - u) ≤ 0 at h
    rw [← pack_unpack b, ← pack_unpack u, ← pack_sub, vecDot_pack] at h
    simpa only [unpackX_pack, sub_self, vecDot, Pi.sub_apply, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
      zero_add] using h

theorem pairProject_spec {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hx : IsEuclideanProjection X projectX) (hy : IsEuclideanProjection Y projectY) :
    IsEuclideanProjection (pairSet X Y) (pairProject projectX projectY) where
  mem u := by simpa only [pairProject, pairSet, Set.mem_setOf_eq,
    unpackX_pack, unpackY_pack] using And.intro (hx.mem (unpackX u)) (hy.mem (unpackY u))
  normal u := by
    have h := normal_pair (hx.normal (unpackX u)) (hy.normal (unpackY u))
    simpa only [pack_sub, pack_unpack, pairProject] using h

def saddlePair {m n : Nat} (P : NCCInstance m n) (ell r : ℝ)
    (z : EVec m) (u : Pair m n) : Pair m n :=
  pack (saddleX P ell z (unpackX u) (unpackY u))
    (saddleY P r (unpackX u) (unpackY u))

theorem saddlePair_lipschitz {m n : Nat} {P : NCCInstance m n}
    {ell D Delta r : ℝ} (hP : WithinClass ell D Delta P)
    (hr : 0 ≤ r) (hrle : r ≤ ell) (z : EVec m) :
    ∀ u ∈ pairSet P.X P.Y, ∀ v ∈ pairSet P.X P.Y,
      vecSq (saddlePair P ell r z u - saddlePair P ell r z v) ≤
        10 * ell ^ 2 * vecSq (u - v) := by
  intro u hu v hv
  let dx := unpackX u - unpackX v
  let dy := unpackY u - unpackY v
  let gx := P.gradX (unpackX u) (unpackY u) - P.gradX (unpackX v) (unpackY v)
  let gy := P.gradY (unpackX u) (unpackY u) - P.gradY (unpackX v) (unpackY v)
  have hs : vecSq gx + vecSq gy ≤ ell ^ 2 * (vecSq dx + vecSq dy) := by
    simpa only [gx, gy, dx, dy, jointSq] using
      hP.jointly_smooth (unpackX u) hu.1 (unpackY u) hu.2
        (unpackX v) hv.1 (unpackY v) hv.2
  have hform : saddlePair P ell r z u - saddlePair P ell r z v =
      pack (gx + (2 * ell) • dx) (-gy + r • dy) := by
    unfold saddlePair
    rw [← pack_sub]
    congr 1 <;> ext i <;>
      simp only [saddleX, saddleY, ClassOperator.gradXHat, ClassOperator.gradYHat,
        gx, gy, dx, dy, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.smul_apply,
        smul_eq_mul] <;> ring
  have huform : vecSq (u - v) = vecSq dx + vecSq dy := by
    rw [← pack_unpack u, ← pack_unpack v, ← pack_sub, vecSq_pack]
  rw [hform, vecSq_pack, huform]
  have htx := vecSq_add_le_two gx ((2 * ell) • dx)
  have hty := vecSq_neg_add_le_two gy (r • dy)
  rw [vecSq_smul] at htx hty
  have he : r ^ 2 ≤ ell ^ 2 := by nlinarith [hP.ell_pos]
  have hdy := ProjectionGeometry.vecSq_nonneg dy
  have hdx := ProjectionGeometry.vecSq_nonneg dx
  have hre := mul_le_mul_of_nonneg_right he hdy
  have hex := mul_nonneg (sq_nonneg ell) hdx
  have hey := mul_nonneg (sq_nonneg ell) hdy
  nlinarith

/-- The final readout is obtained by one regularized saddle-gradient
query and two known-domain projections. No saddle solution is computed. -/
def readoutPair {m n : Nat} (P : NCCInstance m n) (ell r : ℝ)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (z : EVec m) (u : Pair m n) : Pair m n :=
  pairProject projectX projectY (u - ell⁻¹ • saddlePair P ell r z u)

theorem readoutPair_hasGSWitness {m n : Nat} {P : NCCInstance m n}
    {ell D Delta r eps : ℝ} (hP : WithinClass ell D Delta P)
    (hr : 0 ≤ r) (hrle : r ≤ ell) (heps : 0 < eps)
    {projectX : EVec m → EVec m} {projectY : EVec n → EVec n}
    (hpX : IsEuclideanProjection P.X projectX)
    (hpY : IsEuclideanProjection P.Y projectY)
    {z : EVec m} (W : NCC.Upper.WithinSystem.SaddleWitness P ell r z)
    {u : Pair m n} (hu : u ∈ pairSet P.X P.Y)
    (hprecision : 50000 * ell ^ 2 * vecSq (u - pack W.x W.y) ≤ eps ^ 2)
    (hanchor : 64 * ell ^ 2 * vecSq (z - W.x) ≤ eps ^ 2)
    (hdual : 16 * r ^ 2 * D ^ 2 ≤ eps ^ 2) :
    HasGSWitness P eps
      (unpackX (readoutPair P ell r projectX projectY z u))
      (unpackY (readoutPair P ell r projectX projectY z u)) := by
  let A := saddlePair P ell r z
  let w := readoutPair P ell r projectX projectY z u
  let b := ell • (u - ell⁻¹ • A u - w)
  have hstar : pack W.x W.y ∈ pairSet P.X P.Y := by
    simpa only [pairSet, Set.mem_setOf_eq, unpackX_pack, unpackY_pack] using
      And.intro W.x_mem W.y_mem
  have hnstar : IsEuclideanNormal (pairSet P.X P.Y) (pack W.x W.y)
      (-A (pack W.x W.y)) := by
    have hn := normal_pair W.normalX W.normalY
    have heq : pack (-saddleX P ell z W.x W.y) (-saddleY P r W.x W.y) =
        -A (pack W.x W.y) := by
      dsimp only [A, saddlePair]
      simp only [unpackX_pack, unpackY_pack]
      simpa only [neg_one_smul] using
        (pack_smul (-1 : ℝ) (saddleX P ell z W.x W.y) (saddleY P r W.x W.y))
    rwa [heq] at hn
  obtain ⟨hw, hb, hclose, hres⟩ := residual_of_proximity
    (pairProject_spec hpX hpY) hP.ell_pos (saddlePair_lipschitz hP hr hrle z)
    hstar hu hnstar
  change w ∈ pairSet P.X P.Y at hw
  change IsEuclideanNormal (pairSet P.X P.Y) w b at hb
  change vecSq (w - pack W.x W.y) ≤ 22 * vecSq (u - pack W.x W.y) at hclose
  change vecSq (A w + b) ≤ 1012 * ell ^ 2 * vecSq (u - pack W.x W.y) at hres
  obtain ⟨hnx, hny⟩ := normal_unpair hw hb
  have hsquares (v : Pair m n) :
      vecSq (unpackX v) + vecSq (unpackY v) = vecSq v := by
    rw [← vecSq_pack, pack_unpack]
  have hresX : vecSq (unpackX (A w + b)) ≤ vecSq (A w + b) := by
    rw [← hsquares]
    linarith [ProjectionGeometry.vecSq_nonneg (unpackY (A w + b))]
  have hresY : vecSq (unpackY (A w + b)) ≤ vecSq (A w + b) := by
    rw [← hsquares]
    linarith [ProjectionGeometry.vecSq_nonneg (unpackX (A w + b))]
  have hcloseX : vecSq (unpackX w - W.x) ≤ 22 * vecSq (u - pack W.x W.y) := by
    have heq : vecSq (w - pack W.x W.y) =
        vecSq (unpackX w - W.x) + vecSq (unpackY w - W.y) := by
      rw [← pack_unpack w, ← pack_sub, vecSq_pack]
      simp only [unpackX_pack, unpackY_pack]
    rw [heq] at hclose
    linarith [ProjectionGeometry.vecSq_nonneg (unpackY w - W.y)]
  have hza : vecSq (z - unpackX w) ≤
      2 * vecSq (z - W.x) + 44 * vecSq (u - pack W.x W.y) := by
    have hh := square_sub_le (z - W.x) (unpackX w - W.x)
    have heq : (z - W.x) - (unpackX w - W.x) = z - unpackX w := by module
    rw [heq] at hh
    linarith
  have hformX : P.gradX (unpackX w) (unpackY w) + unpackX b =
      unpackX (A w + b) + (2 * ell) • (z - unpackX w) := by
    ext i
    simp only [A, saddlePair, saddleX, ClassOperator.gradXHat, unpackX,
      pack, Fin.append_left, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hformY : -P.gradY (unpackX w) (unpackY w) + unpackY b =
      unpackY (A w + b) - r • unpackY w := by
    ext i
    simp only [A, saddlePair, saddleY, ClassOperator.gradYHat, unpackY,
      pack, Fin.append_right, Pi.add_apply, Pi.neg_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul]
    ring
  refine ⟨heps, hw.1, hw.2, unpackX b, unpackY b, hnx, hny, ?_, ?_⟩
  · change vecSq (P.gradX (unpackX w) (unpackY w) + unpackX b) ≤ _
    rw [hformX]
    have ht := vecSq_add_le_two (unpackX (A w + b)) ((2 * ell) • (z - unpackX w))
    rw [vecSq_smul] at ht
    have hzbound := mul_le_mul_of_nonneg_left hza (sq_nonneg ell)
    nlinarith [sq_nonneg eps]
  · change vecSq (-P.gradY (unpackX w) (unpackY w) + unpackY b) ≤ _
    rw [hformY]
    have ht := square_sub_le (unpackY (A w + b)) (r • unpackY w)
    rw [vecSq_smul] at ht
    have hybound := mul_le_mul_of_nonneg_left (hP.dual_vecSq_le hw.2) (sq_nonneg r)
    nlinarith [sq_nonneg eps]

end
end NCC.Extensions.ProjectedReadout
