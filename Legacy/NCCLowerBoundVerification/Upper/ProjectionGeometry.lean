import NCCLowerBoundVerification.Upper.RelativeFOAM

/-!
# Euclidean projection and projected strongly-monotone steps

The ambient Lean norm on `Fin d → ℝ` is not used here.  All statements are
proved directly for the paper's Euclidean coordinate square `vecSq`.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace ProjectionGeometry

noncomputable section

open RelativeFOAM

def vecDot {d : Nat} (x y : EVec d) : ℝ :=
  ∑ i : Fin d, x i * y i

theorem vecDot_comm {d : Nat} (x y : EVec d) :
    vecDot x y = vecDot y x := by
  unfold vecDot
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem vecSq_eq_vecDot_self {d : Nat} (x : EVec d) :
    vecSq x = vecDot x x := by
  unfold vecSq NCPLVerification.vecSq vecDot
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem vecSq_eq_zero_iff {d : Nat} (x : EVec d) :
    vecSq x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    have hi : x i ^ 2 ≤ vecSq x := by
      unfold vecSq NCPLVerification.vecSq
      exact Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j)) (Finset.mem_univ i)
    have : x i ^ 2 = 0 := by nlinarith [sq_nonneg (x i)]
    exact sq_eq_zero_iff.mp this
  · rintro rfl
    simp [vecSq, NCPLVerification.vecSq]

theorem vecSq_nonneg {d : Nat} (x : EVec d) : 0 ≤ vecSq x := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i)

theorem vecSq_sub_dot_expand {d : Nat} (x y : EVec d) :
    vecSq (x - y) = vecSq x - 2 * vecDot x y + vecSq y := by
  unfold vecSq NCPLVerification.vecSq vecDot
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

theorem vecSq_sub_smul_expand {d : Nat} (x y : EVec d) (a : ℝ) :
    vecSq (x - a • y) =
      vecSq x - 2 * a * vecDot y x + a ^ 2 * vecSq y := by
  unfold vecSq NCPLVerification.vecSq vecDot
  rw [Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- A map satisfying the exact Euclidean projection variational inequality. -/
structure IsEuclideanProjection {d : Nat} (C : Set (EVec d))
    (project : EVec d → EVec d) : Prop where
  mem : ∀ z, project z ∈ C
  normal : ∀ z, IsEuclideanNormal C (project z) (z - project z)

theorem projection_pairing {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    (x y : EVec d) :
    vecSq (project x - project y) ≤
      vecDot (project x - project y) (x - y) := by
  let p := project x
  let q := project y
  have hx := hp.normal x q (hp.mem y)
  have hy := hp.normal y p (hp.mem x)
  change (∑ i : Fin d, (x i - p i) * (q i - p i)) ≤ 0 at hx
  change (∑ i : Fin d, (y i - q i) * (p i - q i)) ≤ 0 at hy
  have hsum :
      (∑ i : Fin d,
        ((x i - p i) * (q i - p i) +
          (y i - q i) * (p i - q i))) ≤ 0 := by
    rw [Finset.sum_add_distrib]
    linarith
  have hid :
      vecSq (p - q) - vecDot (p - q) (x - y) =
        ∑ i : Fin d,
          ((x i - p i) * (q i - p i) +
            (y i - q i) * (p i - q i)) := by
    unfold vecSq NCPLVerification.vecSq vecDot
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  dsimp [p, q] at hsum hid ⊢
  linarith

/-- Firm nonexpansiveness implies ordinary Euclidean nonexpansiveness. -/
theorem projection_nonexpansive {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    (x y : EVec d) :
    vecSq (project x - project y) ≤ vecSq (x - y) := by
  have hpair := projection_pairing hp x y
  have hres := vecSq_nonneg ((x - y) - (project x - project y))
  rw [vecSq_sub_dot_expand] at hres
  rw [vecDot_comm (x - y) (project x - project y)] at hres
  nlinarith

/-- The variational inequality characterizes the projection uniquely. -/
theorem eq_projection_of_normal {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {z c : EVec d} (hc : c ∈ C)
    (hnormal : IsEuclideanNormal C c (z - c)) :
    project z = c := by
  let p := project z
  have hpz := hp.normal z c hc
  have hcz := hnormal p (hp.mem z)
  change (∑ i : Fin d, (z i - p i) * (c i - p i)) ≤ 0 at hpz
  change (∑ i : Fin d, (z i - c i) * (p i - c i)) ≤ 0 at hcz
  have hsum :
      (∑ i : Fin d,
        ((z i - p i) * (c i - p i) +
          (z i - c i) * (p i - c i))) ≤ 0 := by
    rw [Finset.sum_add_distrib]
    linarith
  have hid : vecSq (p - c) =
      ∑ i : Fin d,
        ((z i - p i) * (c i - p i) +
          (z i - c i) * (p i - c i)) := by
    unfold vecSq NCPLVerification.vecSq
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  have hsum_nonneg : 0 ≤ ∑ i : Fin d,
      ((z i - p i) * (c i - p i) +
        (z i - c i) * (p i - c i)) := by
    rw [← hid]
    exact vecSq_nonneg _
  have hsquare : vecSq (p - c) = 0 := by
    calc
      vecSq (p - c) = ∑ i : Fin d,
          ((z i - p i) * (c i - p i) +
            (z i - c i) * (p i - c i)) := hid
      _ = 0 := le_antisymm hsum hsum_nonneg
  have : p - c = 0 := (vecSq_eq_zero_iff _).mp hsquare
  exact sub_eq_zero.mp this

def IsStronglyMonotone {d : Nat} (A : EVec d → EVec d)
    (sigma : ℝ) : Prop :=
  ∀ u v, sigma * vecSq (u - v) ≤ vecDot (A u - A v) (u - v)

def IsEuclideanLipschitz {d : Nat} (A : EVec d → EVec d)
    (M : ℝ) : Prop :=
  ∀ u v, vecSq (A u - A v) ≤ M ^ 2 * vecSq (u - v)

/-- The paper only assumes regularity on the feasible set. -/
def IsStronglyMonotoneOn {d : Nat} (C : Set (EVec d))
    (A : EVec d → EVec d) (sigma : ℝ) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C,
    sigma * vecSq (u - v) ≤ vecDot (A u - A v) (u - v)

def IsEuclideanLipschitzOn {d : Nat} (C : Set (EVec d))
    (A : EVec d → EVec d) (M : ℝ) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C,
    vecSq (A u - A v) ≤ M ^ 2 * vecSq (u - v)

theorem IsStronglyMonotone.on {d : Nat} {A : EVec d → EVec d}
    {sigma : ℝ} (h : IsStronglyMonotone A sigma) (C : Set (EVec d)) :
    IsStronglyMonotoneOn C A sigma := by
  intro u _ v _
  exact h u v

theorem IsEuclideanLipschitz.on {d : Nat} {A : EVec d → EVec d}
    {M : ℝ} (h : IsEuclideanLipschitz A M) (C : Set (EVec d)) :
    IsEuclideanLipschitzOn C A M := by
  intro u _ v _
  exact h u v

def projectedStep {d : Nat} (project : EVec d → EVec d)
    (A : EVec d → EVec d) (eta : ℝ) (u : EVec d) : EVec d :=
  project (u - eta • A u)

theorem projectedStep_fixed_of_normal {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {eta : ℝ} (heta : 0 ≤ eta)
    {uStar : EVec d} (hu : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar)) :
    projectedStep project A eta uStar = uStar := by
  have hn := hnormal.nonneg_smul heta
  have hchar : project (uStar - eta • A uStar) = uStar := by
    apply eq_projection_of_normal hp hu
    have heq : uStar - eta • A uStar - uStar = eta • (-A uStar) := by
      module
    rw [heq]
    exact hn
  exact hchar

theorem projectedStep_contraction {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {sigma M eta : ℝ}
    (hmono : IsStronglyMonotone A sigma)
    (hlip : IsEuclideanLipschitz A M)
    (heta : 0 ≤ eta) (u v : EVec d) :
    vecSq (projectedStep project A eta u - projectedStep project A eta v) ≤
      (1 - 2 * eta * sigma + eta ^ 2 * M ^ 2) * vecSq (u - v) := by
  have hproj := projection_nonexpansive hp
    (u - eta • A u) (v - eta • A v)
  have harg :
      (u - eta • A u) - (v - eta • A v) =
        (u - v) - eta • (A u - A v) := by module
  rw [harg, vecSq_sub_smul_expand] at hproj
  have hm := hmono u v
  have hl := hlip u v
  unfold projectedStep
  have hscaleMono := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * eta)
  have hscaleLip := mul_le_mul_of_nonneg_left hl (sq_nonneg eta)
  nlinarith

theorem projectedStep_contraction_on {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {sigma M eta : ℝ}
    (hmono : IsStronglyMonotoneOn C A sigma)
    (hlip : IsEuclideanLipschitzOn C A M)
    (heta : 0 ≤ eta) {u v : EVec d} (hu : u ∈ C) (hv : v ∈ C) :
    vecSq (projectedStep project A eta u - projectedStep project A eta v) ≤
      (1 - 2 * eta * sigma + eta ^ 2 * M ^ 2) * vecSq (u - v) := by
  have hproj := projection_nonexpansive hp
    (u - eta • A u) (v - eta • A v)
  have harg :
      (u - eta • A u) - (v - eta • A v) =
        (u - v) - eta • (A u - A v) := by module
  rw [harg, vecSq_sub_smul_expand] at hproj
  have hm := hmono u hu v hv
  have hl := hlip u hu v hv
  unfold projectedStep
  have hscaleMono := mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 2 * eta)
  have hscaleLip := mul_le_mul_of_nonneg_left hl (sq_nonneg eta)
  nlinarith

theorem projectedStep_contraction_to_solution {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {sigma M eta : ℝ}
    (hmono : IsStronglyMonotone A sigma)
    (hlip : IsEuclideanLipschitz A M)
    (heta : 0 ≤ eta) {uStar : EVec d} (hu : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar)) (u : EVec d) :
    vecSq (projectedStep project A eta u - uStar) ≤
      (1 - 2 * eta * sigma + eta ^ 2 * M ^ 2) * vecSq (u - uStar) := by
  have hfixed := projectedStep_fixed_of_normal hp heta hu hnormal
  have h := projectedStep_contraction hp hmono hlip heta u uStar
  rwa [hfixed] at h

theorem projectedStep_contraction_to_solution_on {d : Nat}
    {C : Set (EVec d)} {project : EVec d → EVec d}
    (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {sigma M eta : ℝ}
    (hmono : IsStronglyMonotoneOn C A sigma)
    (hlip : IsEuclideanLipschitzOn C A M)
    (heta : 0 ≤ eta) {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    {u : EVec d} (hu : u ∈ C) :
    vecSq (projectedStep project A eta u - uStar) ≤
      (1 - 2 * eta * sigma + eta ^ 2 * M ^ 2) * vecSq (u - uStar) := by
  have hfixed := projectedStep_fixed_of_normal hp heta huStar hnormal
  have h := projectedStep_contraction_on hp hmono hlip heta hu huStar
  rwa [hfixed] at h

/-- The numerical projected step used in `ub:lem:feasible-micro`. -/
theorem projectedStep_contraction_M_inv_sq {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotone A 1)
    (hlip : IsEuclideanLipschitz A M) (u v : EVec d) :
    vecSq (projectedStep project A (M ^ 2)⁻¹ u -
        projectedStep project A (M ^ 2)⁻¹ v) ≤
      (1 - (M ^ 2)⁻¹) * vecSq (u - v) := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have heta : 0 ≤ (M ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg M)
  have h := projectedStep_contraction hp hmono hlip heta u v
  have hcoef :
      1 - 2 * (M ^ 2)⁻¹ * 1 + ((M ^ 2)⁻¹) ^ 2 * M ^ 2 =
        1 - (M ^ 2)⁻¹ := by
    field_simp [ne_of_gt hMpos]
    ring
  rwa [hcoef] at h

theorem projectedStep_contraction_M_inv_sq_on {d : Nat}
    {C : Set (EVec d)} {project : EVec d → EVec d}
    (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotoneOn C A 1)
    (hlip : IsEuclideanLipschitzOn C A M)
    {u v : EVec d} (hu : u ∈ C) (hv : v ∈ C) :
    vecSq (projectedStep project A (M ^ 2)⁻¹ u -
        projectedStep project A (M ^ 2)⁻¹ v) ≤
      (1 - (M ^ 2)⁻¹) * vecSq (u - v) := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  have heta : 0 ≤ (M ^ 2)⁻¹ := inv_nonneg.mpr (sq_nonneg M)
  have h := projectedStep_contraction_on hp hmono hlip heta hu hv
  have hcoef :
      1 - 2 * (M ^ 2)⁻¹ * 1 + ((M ^ 2)⁻¹) ^ 2 * M ^ 2 =
        1 - (M ^ 2)⁻¹ := by
    field_simp [ne_of_gt hMpos]
    ring
  rwa [hcoef] at h

end

end ProjectionGeometry
end Upper
end NCCLowerBoundVerification
