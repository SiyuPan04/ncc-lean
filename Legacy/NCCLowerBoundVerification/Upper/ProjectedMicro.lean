import NCCLowerBoundVerification.Upper.ProjectionGeometry
import NCCLowerBoundVerification.Upper.Tracking

/-!
# The projected residual micro-solver

This file discharges the vector geometry and finite-stopping part of
`ub:lem:feasible-micro`.  In particular, projected-step contraction, the
residual estimate, the reverse-triangle estimate, and existence of a numerical
stopping index are derived here rather than supplied as hypotheses to the
algorithmic theorem.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace ProjectedMicro

noncomputable section

open ProjectionGeometry
open RelativeFOAM

/-- Euclidean length associated with the paper's coordinate square `vecSq`. -/
def euclideanLength {d : Nat} (x : EVec d) : ℝ :=
  Real.sqrt (vecSq x)

theorem euclideanLength_nonneg {d : Nat} (x : EVec d) :
    0 ≤ euclideanLength x :=
  Real.sqrt_nonneg _

theorem euclideanLength_sq {d : Nat} (x : EVec d) :
    euclideanLength x ^ 2 = vecSq x := by
  exact Real.sq_sqrt (ProjectionGeometry.vecSq_nonneg x)

theorem euclideanLength_neg {d : Nat} (x : EVec d) :
    euclideanLength (-x) = euclideanLength x := by
  unfold euclideanLength
  rw [Tracking.vecSq_neg]

theorem euclideanLength_sub_comm {d : Nat} (x y : EVec d) :
    euclideanLength (x - y) = euclideanLength (y - x) := by
  unfold euclideanLength
  rw [vecSq_sub_comm]

theorem euclideanLength_add_le {d : Nat} (x y : EVec d) :
    euclideanLength (x + y) ≤ euclideanLength x + euclideanLength y := by
  exact Tracking.sqrt_vecSq_add_le x y

theorem euclideanLength_sub_triangle {d : Nat} (x y z : EVec d) :
    euclideanLength (x - z) ≤
      euclideanLength (x - y) + euclideanLength (y - z) := by
  have h := euclideanLength_add_le (x - y) (y - z)
  have hid : (x - y) + (y - z) = x - z := by module
  rwa [hid] at h

theorem euclideanLength_smul {d : Nat} (c : ℝ) (x : EVec d) :
    euclideanLength (c • x) = |c| * euclideanLength x := by
  unfold euclideanLength
  rw [vecSq_smul, Real.sqrt_mul (sq_nonneg c),
    Real.sqrt_sq_eq_abs]

theorem lipschitz_length {d : Nat} {A : EVec d → EVec d} {M : ℝ}
    (hM : 0 ≤ M) (hlip : IsEuclideanLipschitz A M) (u v : EVec d) :
    euclideanLength (A u - A v) ≤ M * euclideanLength (u - v) := by
  have h := Real.sqrt_le_sqrt (hlip u v)
  rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM] at h
  exact h

/-! ## Contraction of the concrete projected recurrence -/

def contractionFactor (M : ℝ) : ℝ :=
  Real.sqrt (1 - (M ^ 2)⁻¹)

theorem inv_sq_le_one {M : ℝ} (hM : 1 ≤ M) : (M ^ 2)⁻¹ ≤ 1 := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  apply (inv_le_one₀ (sq_pos_of_pos hMpos)).2
  nlinarith

theorem contractionCoefficient_nonneg {M : ℝ} (hM : 1 ≤ M) :
    0 ≤ 1 - (M ^ 2)⁻¹ := by
  linarith [inv_sq_le_one hM]

theorem contractionFactor_nonneg (M : ℝ) : 0 ≤ contractionFactor M :=
  Real.sqrt_nonneg _

theorem contractionFactor_lt_one {M : ℝ} (hM : 1 ≤ M) :
    contractionFactor M < 1 := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  unfold contractionFactor
  rw [Real.sqrt_lt' one_pos]
  have hinv : 0 < (M ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hMpos)
  nlinarith

theorem projection_fixed_of_mem {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {u : EVec d} (hu : u ∈ C) : project u = u := by
  apply eq_projection_of_normal hp hu
  intro z hz
  simp

theorem projectedIterate_succ {d : Nat} (project : EVec d → EVec d)
    (A : EVec d → EVec d) (eta : ℝ) (uMinusOne : EVec d) (s : Nat) :
    projectedIterate project A eta uMinusOne (s + 1) =
      projectedStep project A eta
        (projectedIterate project A eta uMinusOne s) := by
  rfl

theorem projectedIterate_distance_step {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotone A 1)
    (hlip : IsEuclideanLipschitz A M)
    {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    (uMinusOne : EVec d) (s : Nat) :
    euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1) - uStar) ≤
      contractionFactor M *
        euclideanLength
          (projectedIterate project A (M ^ 2)⁻¹ uMinusOne s - uStar) := by
  let u := projectedIterate project A (M ^ 2)⁻¹ uMinusOne s
  have hfixed := projectedStep_fixed_of_normal hp
    (inv_nonneg.mpr (sq_nonneg M)) huStar hnormal
  have hsq := projectedStep_contraction_M_inv_sq hp hM hmono hlip u uStar
  rw [hfixed] at hsq
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (contractionCoefficient_nonneg hM)] at hsqrt
  simpa [euclideanLength, contractionFactor, projectedIterate_succ, u] using hsqrt

theorem projectedIterate_initial_distance {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    (A : EVec d → EVec d) {M : ℝ} {uStar : EVec d}
    (huStar : uStar ∈ C) (uMinusOne : EVec d) :
    euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne 0 - uStar) ≤
      euclideanLength (uMinusOne - uStar) := by
  have hfix := projection_fixed_of_mem hp huStar
  have hsq := projection_nonexpansive hp uMinusOne uStar
  rw [hfix] at hsq
  exact Real.sqrt_le_sqrt hsq

theorem projectedIterate_geometric_distance {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotone A 1)
    (hlip : IsEuclideanLipschitz A M)
    {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    (uMinusOne : EVec d) (s : Nat) :
    euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne s - uStar) ≤
      contractionFactor M ^ s * euclideanLength (uMinusOne - uStar) := by
  apply geometric_bound (contractionFactor M)
    (euclideanLength (uMinusOne - uStar))
    (fun k => euclideanLength
      (projectedIterate project A (M ^ 2)⁻¹ uMinusOne k - uStar))
    (contractionFactor_nonneg M)
    (projectedIterate_initial_distance hp A huStar uMinusOne)
    (projectedIterate_distance_step hp hM hmono hlip huStar hnormal uMinusOne)

/-! ## Residual and reverse-triangle estimates -/

theorem projectedIterate_step_size {d : Nat} (project : EVec d → EVec d)
    (A : EVec d → EVec d) {M : ℝ} {uStar uMinusOne : EVec d} (s : Nat) :
    euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1) -
          projectedIterate project A (M ^ 2)⁻¹ uMinusOne s) ≤
      euclideanLength
          (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1) - uStar) +
        euclideanLength
          (projectedIterate project A (M ^ 2)⁻¹ uMinusOne s - uStar) := by
  have h := euclideanLength_sub_triangle
    (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1)) uStar
    (projectedIterate project A (M ^ 2)⁻¹ uMinusOne s)
  rwa [euclideanLength_sub_comm uStar
    (projectedIterate project A (M ^ 2)⁻¹ uMinusOne s)] at h

theorem projectedIterate_step_geometric {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotone A 1)
    (hlip : IsEuclideanLipschitz A M)
    {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    (uMinusOne : EVec d) (s : Nat) :
    euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1) -
          projectedIterate project A (M ^ 2)⁻¹ uMinusOne s) ≤
      (1 + contractionFactor M) * contractionFactor M ^ s *
        euclideanLength (uMinusOne - uStar) := by
  let dseq : Nat → ℝ := fun k => euclideanLength
    (projectedIterate project A (M ^ 2)⁻¹ uMinusOne k - uStar)
  let stepSize : Nat → ℝ
    | 0 => 0
    | k + 1 => euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (k + 1) -
          projectedIterate project A (M ^ 2)⁻¹ uMinusOne k)
  have hd : ∀ k, dseq k ≤ contractionFactor M ^ k *
      euclideanLength (uMinusOne - uStar) :=
    projectedIterate_geometric_distance hp hM hmono hlip huStar hnormal uMinusOne
  have hs : ∀ k, stepSize (k + 1) ≤ dseq (k + 1) + dseq k := by
    intro k
    exact projectedIterate_step_size project A k
  have h := step_size_geometric_bound
    (contractionFactor_nonneg M)
    (euclideanLength_nonneg (uMinusOne - uStar)) hd hs s
  exact h

theorem projected_residual_bound {d : Nat}
    (project : EVec d → EVec d) {A : EVec d → EVec d}
    {M : ℝ} (hM : 1 ≤ M) (hlip : IsEuclideanLipschitz A M)
    (uMinusOne : EVec d) (s : Nat) :
    euclideanLength
        (A (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1)) +
          projectedB project A (M ^ 2)⁻¹ uMinusOne s) ≤
      (M + M ^ 2) *
        euclideanLength
          (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1) -
            projectedIterate project A (M ^ 2)⁻¹ uMinusOne s) := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  let us := projectedIterate project A (M ^ 2)⁻¹ uMinusOne s
  let un := projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1)
  have hid := operator_add_projectedB project A
    (inv_ne_zero (pow_ne_zero 2 (ne_of_gt hMpos))) uMinusOne s
  have htri := euclideanLength_add_le (A un - A us) ((M ^ 2) • (us - un))
  have hLipLen := lipschitz_length (le_trans zero_le_one hM) hlip un us
  have hscale : euclideanLength ((M ^ 2) • (us - un)) =
      M ^ 2 * euclideanLength (un - us) := by
    rw [euclideanLength_smul, abs_of_nonneg (sq_nonneg M),
      euclideanLength_sub_comm us un]
  have hsum : euclideanLength ((A un - A us) + (M ^ 2) • (us - un)) ≤
      (M + M ^ 2) * euclideanLength (un - us) := by
    rw [hscale] at htri
    nlinarith
  have hid' :
      A un + projectedB project A (M ^ 2)⁻¹ uMinusOne s =
        (A un - A us) + (M ^ 2) • (us - un) := by
    simpa [us, un] using hid
  rw [hid']
  exact hsum

theorem projected_residual_geometric {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotone A 1)
    (hlip : IsEuclideanLipschitz A M)
    {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    (uMinusOne : EVec d) (s : Nat) :
    euclideanLength
        (A (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1)) +
          projectedB project A (M ^ 2)⁻¹ uMinusOne s) ≤
      (M + M ^ 2) * (1 + contractionFactor M) *
        contractionFactor M ^ s * euclideanLength (uMinusOne - uStar) := by
  calc
    _ ≤ (M + M ^ 2) * euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1) -
          projectedIterate project A (M ^ 2)⁻¹ uMinusOne s) :=
      projected_residual_bound project hM hlip uMinusOne s
    _ ≤ (M + M ^ 2) * ((1 + contractionFactor M) *
          contractionFactor M ^ s * euclideanLength (uMinusOne - uStar)) := by
      exact mul_le_mul_of_nonneg_left
        (projectedIterate_step_geometric hp hM hmono hlip huStar hnormal
          uMinusOne s)
        (add_nonneg (le_trans zero_le_one hM) (sq_nonneg M))
    _ = _ := by ring

theorem projected_center_distance_lower {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotone A 1)
    (hlip : IsEuclideanLipschitz A M)
    {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    (uMinusOne : EVec d) (s : Nat) :
    (1 - contractionFactor M ^ s) * euclideanLength (uMinusOne - uStar) ≤
      euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne s - uMinusOne) := by
  let dseq : Nat → ℝ := fun k => euclideanLength
    (projectedIterate project A (M ^ 2)⁻¹ uMinusOne k - uStar)
  let centerDistance : Nat → ℝ := fun k => euclideanLength
    (projectedIterate project A (M ^ 2)⁻¹ uMinusOne k - uMinusOne)
  have hd : ∀ k, dseq k ≤ contractionFactor M ^ k *
      euclideanLength (uMinusOne - uStar) :=
    projectedIterate_geometric_distance hp hM hmono hlip huStar hnormal uMinusOne
  have hreverse : ∀ k, euclideanLength (uMinusOne - uStar) ≤
      centerDistance k + dseq k := by
    intro k
    have h := euclideanLength_sub_triangle uMinusOne
      (projectedIterate project A (M ^ 2)⁻¹ uMinusOne k) uStar
    rw [euclideanLength_sub_comm uMinusOne
      (projectedIterate project A (M ^ 2)⁻¹ uMinusOne k)] at h
    exact h
  exact center_distance_lower_bound
    (euclideanLength_nonneg (uMinusOne - uStar)) hd hreverse s

/-! ## The same proof chain with operator assumptions only on `C` -/

theorem lipschitz_length_on {d : Nat} {C : Set (EVec d)}
    {A : EVec d → EVec d} {M : ℝ}
    (hM : 0 ≤ M) (hlip : IsEuclideanLipschitzOn C A M)
    {u v : EVec d} (hu : u ∈ C) (hv : v ∈ C) :
    euclideanLength (A u - A v) ≤ M * euclideanLength (u - v) := by
  have h := Real.sqrt_le_sqrt (hlip u hu v hv)
  rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM] at h
  exact h

theorem projectedIterate_distance_step_on {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotoneOn C A 1)
    (hlip : IsEuclideanLipschitzOn C A M)
    {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    (uMinusOne : EVec d) (s : Nat) :
    euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1) - uStar) ≤
      contractionFactor M *
        euclideanLength
          (projectedIterate project A (M ^ 2)⁻¹ uMinusOne s - uStar) := by
  let u := projectedIterate project A (M ^ 2)⁻¹ uMinusOne s
  have hu : u ∈ C := projectedIterate_mem project A (M ^ 2)⁻¹
    uMinusOne hp.mem s
  have hfixed := projectedStep_fixed_of_normal hp
    (inv_nonneg.mpr (sq_nonneg M)) huStar hnormal
  have hsq := projectedStep_contraction_M_inv_sq_on hp hM hmono hlip hu huStar
  rw [hfixed] at hsq
  have hsqrt := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul (contractionCoefficient_nonneg hM)] at hsqrt
  simpa [euclideanLength, contractionFactor, projectedIterate_succ, u] using hsqrt

theorem projectedIterate_geometric_distance_on {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotoneOn C A 1)
    (hlip : IsEuclideanLipschitzOn C A M)
    {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    (uMinusOne : EVec d) (s : Nat) :
    euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne s - uStar) ≤
      contractionFactor M ^ s * euclideanLength (uMinusOne - uStar) := by
  apply geometric_bound (contractionFactor M)
    (euclideanLength (uMinusOne - uStar))
    (fun k => euclideanLength
      (projectedIterate project A (M ^ 2)⁻¹ uMinusOne k - uStar))
    (contractionFactor_nonneg M)
    (projectedIterate_initial_distance hp A huStar uMinusOne)
    (projectedIterate_distance_step_on hp hM hmono hlip huStar hnormal uMinusOne)

theorem projectedIterate_step_geometric_on {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotoneOn C A 1)
    (hlip : IsEuclideanLipschitzOn C A M)
    {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    (uMinusOne : EVec d) (s : Nat) :
    euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1) -
          projectedIterate project A (M ^ 2)⁻¹ uMinusOne s) ≤
      (1 + contractionFactor M) * contractionFactor M ^ s *
        euclideanLength (uMinusOne - uStar) := by
  let dseq : Nat → ℝ := fun k => euclideanLength
    (projectedIterate project A (M ^ 2)⁻¹ uMinusOne k - uStar)
  let stepSize : Nat → ℝ
    | 0 => 0
    | k + 1 => euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (k + 1) -
          projectedIterate project A (M ^ 2)⁻¹ uMinusOne k)
  have hd : ∀ k, dseq k ≤ contractionFactor M ^ k *
      euclideanLength (uMinusOne - uStar) :=
    projectedIterate_geometric_distance_on hp hM hmono hlip huStar hnormal uMinusOne
  have hs : ∀ k, stepSize (k + 1) ≤ dseq (k + 1) + dseq k := by
    intro k
    exact projectedIterate_step_size project A k
  exact step_size_geometric_bound
    (contractionFactor_nonneg M)
    (euclideanLength_nonneg (uMinusOne - uStar)) hd hs s

theorem projected_residual_bound_on {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hlip : IsEuclideanLipschitzOn C A M)
    (uMinusOne : EVec d) (s : Nat) :
    euclideanLength
        (A (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1)) +
          projectedB project A (M ^ 2)⁻¹ uMinusOne s) ≤
      (M + M ^ 2) *
        euclideanLength
          (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1) -
            projectedIterate project A (M ^ 2)⁻¹ uMinusOne s) := by
  have hMpos : 0 < M := zero_lt_one.trans_le hM
  let us := projectedIterate project A (M ^ 2)⁻¹ uMinusOne s
  let un := projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1)
  have hus : us ∈ C := projectedIterate_mem project A (M ^ 2)⁻¹
    uMinusOne hp.mem s
  have hun : un ∈ C := projectedIterate_mem project A (M ^ 2)⁻¹
    uMinusOne hp.mem (s + 1)
  have hid := operator_add_projectedB project A
    (inv_ne_zero (pow_ne_zero 2 (ne_of_gt hMpos))) uMinusOne s
  have htri := euclideanLength_add_le (A un - A us) ((M ^ 2) • (us - un))
  have hLipLen := lipschitz_length_on (le_trans zero_le_one hM) hlip hun hus
  have hscale : euclideanLength ((M ^ 2) • (us - un)) =
      M ^ 2 * euclideanLength (un - us) := by
    rw [euclideanLength_smul, abs_of_nonneg (sq_nonneg M),
      euclideanLength_sub_comm us un]
  have hsum : euclideanLength ((A un - A us) + (M ^ 2) • (us - un)) ≤
      (M + M ^ 2) * euclideanLength (un - us) := by
    rw [hscale] at htri
    nlinarith
  have hid' :
      A un + projectedB project A (M ^ 2)⁻¹ uMinusOne s =
        (A un - A us) + (M ^ 2) • (us - un) := by
    simpa [us, un] using hid
  rw [hid']
  exact hsum

theorem projected_residual_geometric_on {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotoneOn C A 1)
    (hlip : IsEuclideanLipschitzOn C A M)
    {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    (uMinusOne : EVec d) (s : Nat) :
    euclideanLength
        (A (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1)) +
          projectedB project A (M ^ 2)⁻¹ uMinusOne s) ≤
      (M + M ^ 2) * (1 + contractionFactor M) *
        contractionFactor M ^ s * euclideanLength (uMinusOne - uStar) := by
  calc
    _ ≤ (M + M ^ 2) * euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (s + 1) -
          projectedIterate project A (M ^ 2)⁻¹ uMinusOne s) :=
      projected_residual_bound_on hp hM hlip uMinusOne s
    _ ≤ (M + M ^ 2) * ((1 + contractionFactor M) *
          contractionFactor M ^ s * euclideanLength (uMinusOne - uStar)) := by
      exact mul_le_mul_of_nonneg_left
        (projectedIterate_step_geometric_on hp hM hmono hlip huStar hnormal
          uMinusOne s)
        (add_nonneg (le_trans zero_le_one hM) (sq_nonneg M))
    _ = _ := by ring

theorem projected_center_distance_lower_on {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotoneOn C A 1)
    (hlip : IsEuclideanLipschitzOn C A M)
    {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    (uMinusOne : EVec d) (s : Nat) :
    (1 - contractionFactor M ^ s) * euclideanLength (uMinusOne - uStar) ≤
      euclideanLength
        (projectedIterate project A (M ^ 2)⁻¹ uMinusOne s - uMinusOne) := by
  let dseq : Nat → ℝ := fun k => euclideanLength
    (projectedIterate project A (M ^ 2)⁻¹ uMinusOne k - uStar)
  let centerDistance : Nat → ℝ := fun k => euclideanLength
    (projectedIterate project A (M ^ 2)⁻¹ uMinusOne k - uMinusOne)
  have hd : ∀ k, dseq k ≤ contractionFactor M ^ k *
      euclideanLength (uMinusOne - uStar) :=
    projectedIterate_geometric_distance_on hp hM hmono hlip huStar hnormal uMinusOne
  have hreverse : ∀ k, euclideanLength (uMinusOne - uStar) ≤
      centerDistance k + dseq k := by
    intro k
    have h := euclideanLength_sub_triangle uMinusOne
      (projectedIterate project A (M ^ 2)⁻¹ uMinusOne k) uStar
    rw [euclideanLength_sub_comm uMinusOne
      (projectedIterate project A (M ^ 2)⁻¹ uMinusOne k)] at h
    exact h
  exact center_distance_lower_bound
    (euclideanLength_nonneg (uMinusOne - uStar)) hd hreverse s

/-! ## A numerical stopping index -/

def stoppingPredicate (M chi : ℝ) (N : Nat) : Prop :=
  1 ≤ N ∧
    (M + M ^ 2) * (1 + chi) * chi ^ (N - 1) ≤ 1 - chi ^ N

theorem exists_stoppingIndex {M chi : ℝ}
    (hM : 0 ≤ M) (hchi0 : 0 ≤ chi) (hchi1 : chi < 1) :
    ∃ N, stoppingPredicate M chi N := by
  let C := (M + M ^ 2) * (1 + chi)
  have hC0 : 0 ≤ C := by
    exact mul_nonneg (add_nonneg hM (sq_nonneg M)) (by linarith)
  have hden : 0 < C + 1 := by linarith
  let eps : ℝ := (C + 1)⁻¹
  have heps : 0 < eps := inv_pos.mpr hden
  have htend := tendsto_pow_atTop_nhds_zero_of_lt_one hchi0 hchi1
  obtain ⟨k, hk⟩ := (Metric.tendsto_atTop.1 htend) eps heps
  have hkdist := hk k le_rfl
  have hpow0 : 0 ≤ chi ^ k := pow_nonneg hchi0 k
  have hpowlt : chi ^ k < eps := by
    simpa [Real.dist_eq, abs_pow, abs_of_nonneg hchi0] using hkdist
  have hscaled : (C + 1) * chi ^ k < 1 := by
    have := mul_lt_mul_of_pos_left hpowlt hden
    simpa [eps, ne_of_gt hden] using this
  refine ⟨k + 1, ?_⟩
  constructor
  · omega
  · simp only [Nat.add_sub_cancel, pow_succ]
    dsimp [C] at hscaled ⊢
    have hchi_le : chi ≤ 1 := hchi1.le
    have hpowchi : chi ^ k * chi ≤ chi ^ k :=
      mul_le_of_le_one_right hpow0 hchi_le
    nlinarith

/-- A proof-independent numerical choice; `Nat.find` makes it the first
positive index satisfying the paper's scalar stopping inequality. -/
noncomputable def numericalStoppingIndex (M chi : ℝ) : Nat := by
  classical
  exact if h : ∃ N, stoppingPredicate M chi N then Nat.find h else 1

theorem numericalStoppingIndex_spec {M chi : ℝ}
    (hM : 0 ≤ M) (hchi0 : 0 ≤ chi) (hchi1 : chi < 1) :
    stoppingPredicate M chi (numericalStoppingIndex M chi) := by
  classical
  have hex := exists_stoppingIndex hM hchi0 hchi1
  simp [numericalStoppingIndex, hex, Nat.find_spec hex]

theorem numericalStoppingIndex_minimal {M chi : ℝ}
    (hM : 0 ≤ M) (hchi0 : 0 ≤ chi) (hchi1 : chi < 1)
    {N : Nat} (hN : stoppingPredicate M chi N) :
    numericalStoppingIndex M chi ≤ N := by
  classical
  have hex := exists_stoppingIndex hM hchi0 hchi1
  simpa [numericalStoppingIndex, hex] using Nat.find_min' hex hN

/-! ## The assembled projected-micro certificate -/

/--
At the proof-independent numerical index, the concrete projected recurrence
is feasible, its projection displacement is a genuine normal, and the scaled
stopping test holds.  The index depends only on `M`, not on the dimension,
the feasible set, the operator, or the initial centre.
-/
theorem projectedMicro_certificate {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotone A 1)
    (hlip : IsEuclideanLipschitz A M)
    {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    (uMinusOne : EVec d) :
    let N := numericalStoppingIndex M (contractionFactor M)
    let uN := projectedIterate project A (M ^ 2)⁻¹ uMinusOne N
    let bN := projectedB project A (M ^ 2)⁻¹ uMinusOne (N - 1)
    1 ≤ N ∧
      uN ∈ C ∧
      IsEuclideanNormal C uN bN ∧
      euclideanLength (A uN + bN) ≤ euclideanLength (uN - uMinusOne) := by
  dsimp only
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hchi0 : 0 ≤ contractionFactor M := contractionFactor_nonneg M
  have hchi1 : contractionFactor M < 1 := contractionFactor_lt_one hM
  have hspec : stoppingPredicate M (contractionFactor M)
      (numericalStoppingIndex M (contractionFactor M)) :=
    numericalStoppingIndex_spec hM0 hchi0 hchi1
  obtain ⟨k, hk⟩ : ∃ k,
      numericalStoppingIndex M (contractionFactor M) = k + 1 := by
    cases hN : numericalStoppingIndex M (contractionFactor M) with
    | zero =>
        rw [hN] at hspec
        simp [stoppingPredicate] at hspec
    | succ k => exact ⟨k, rfl⟩
  rw [hk] at hspec ⊢
  have heta : 0 < (M ^ 2)⁻¹ := by
    exact inv_pos.mpr (sq_pos_of_pos (zero_lt_one.trans_le hM))
  refine ⟨by omega, projectedIterate_mem project A (M ^ 2)⁻¹ uMinusOne
    hp.mem (k + 1), ?_, ?_⟩
  · simpa using projectedB_normal project A heta uMinusOne hp.normal k
  · have hres := projected_residual_geometric hp hM hmono hlip huStar hnormal
      uMinusOne k
    have hcenter := projected_center_distance_lower hp hM hmono hlip huStar
      hnormal uMinusOne (k + 1)
    have hnumeric :
        (M + M ^ 2) * (1 + contractionFactor M) *
          contractionFactor M ^ k ≤ 1 - contractionFactor M ^ (k + 1) := by
      simpa [stoppingPredicate] using hspec.2
    have hR0 : 0 ≤ euclideanLength (uMinusOne - uStar) :=
      euclideanLength_nonneg _
    calc
      euclideanLength
          (A (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (k + 1)) +
            projectedB project A (M ^ 2)⁻¹ uMinusOne ((k + 1) - 1)) =
          euclideanLength
            (A (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (k + 1)) +
              projectedB project A (M ^ 2)⁻¹ uMinusOne k) := by simp
      _ ≤ (M + M ^ 2) * (1 + contractionFactor M) *
          contractionFactor M ^ k * euclideanLength (uMinusOne - uStar) := hres
      _ ≤ (1 - contractionFactor M ^ (k + 1)) *
          euclideanLength (uMinusOne - uStar) := by
        exact mul_le_mul_of_nonneg_right hnumeric hR0
      _ ≤ euclideanLength
          (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (k + 1) -
            uMinusOne) := by
        exact hcenter

/-- The complete finite-stopping certificate assuming monotonicity and
Lipschitzness only for pairs of feasible points. -/
theorem projectedMicro_certificate_on {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project)
    {A : EVec d → EVec d} {M : ℝ} (hM : 1 ≤ M)
    (hmono : IsStronglyMonotoneOn C A 1)
    (hlip : IsEuclideanLipschitzOn C A M)
    {uStar : EVec d} (huStar : uStar ∈ C)
    (hnormal : IsEuclideanNormal C uStar (-A uStar))
    (uMinusOne : EVec d) :
    let N := numericalStoppingIndex M (contractionFactor M)
    let uN := projectedIterate project A (M ^ 2)⁻¹ uMinusOne N
    let bN := projectedB project A (M ^ 2)⁻¹ uMinusOne (N - 1)
    1 ≤ N ∧
      uN ∈ C ∧
      IsEuclideanNormal C uN bN ∧
      euclideanLength (A uN + bN) ≤ euclideanLength (uN - uMinusOne) := by
  dsimp only
  have hM0 : 0 ≤ M := le_trans zero_le_one hM
  have hchi0 : 0 ≤ contractionFactor M := contractionFactor_nonneg M
  have hchi1 : contractionFactor M < 1 := contractionFactor_lt_one hM
  have hspec : stoppingPredicate M (contractionFactor M)
      (numericalStoppingIndex M (contractionFactor M)) :=
    numericalStoppingIndex_spec hM0 hchi0 hchi1
  obtain ⟨k, hk⟩ : ∃ k,
      numericalStoppingIndex M (contractionFactor M) = k + 1 := by
    cases hN : numericalStoppingIndex M (contractionFactor M) with
    | zero =>
        rw [hN] at hspec
        simp [stoppingPredicate] at hspec
    | succ k => exact ⟨k, rfl⟩
  rw [hk] at hspec ⊢
  have heta : 0 < (M ^ 2)⁻¹ := by
    exact inv_pos.mpr (sq_pos_of_pos (zero_lt_one.trans_le hM))
  refine ⟨by omega, projectedIterate_mem project A (M ^ 2)⁻¹ uMinusOne
    hp.mem (k + 1), ?_, ?_⟩
  · simpa using projectedB_normal project A heta uMinusOne hp.normal k
  · have hres := projected_residual_geometric_on hp hM hmono hlip huStar hnormal
      uMinusOne k
    have hcenter := projected_center_distance_lower_on hp hM hmono hlip huStar
      hnormal uMinusOne (k + 1)
    have hnumeric :
        (M + M ^ 2) * (1 + contractionFactor M) *
          contractionFactor M ^ k ≤ 1 - contractionFactor M ^ (k + 1) := by
      simpa [stoppingPredicate] using hspec.2
    have hR0 : 0 ≤ euclideanLength (uMinusOne - uStar) :=
      euclideanLength_nonneg _
    calc
      euclideanLength
          (A (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (k + 1)) +
            projectedB project A (M ^ 2)⁻¹ uMinusOne ((k + 1) - 1)) =
          euclideanLength
            (A (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (k + 1)) +
              projectedB project A (M ^ 2)⁻¹ uMinusOne k) := by simp
      _ ≤ (M + M ^ 2) * (1 + contractionFactor M) *
          contractionFactor M ^ k * euclideanLength (uMinusOne - uStar) := hres
      _ ≤ (1 - contractionFactor M ^ (k + 1)) *
          euclideanLength (uMinusOne - uStar) := by
        exact mul_le_mul_of_nonneg_right hnumeric hR0
      _ ≤ euclideanLength
          (projectedIterate project A (M ^ 2)⁻¹ uMinusOne (k + 1) -
            uMinusOne) := by
        exact hcenter

def feasibleMicroIterations : Nat :=
  numericalStoppingIndex M0 (contractionFactor M0)

theorem M0_ge_one : (1 : ℝ) ≤ M0 := by
  norm_num [M0]

theorem projectedChi_eq_contractionFactor :
    projectedChi = contractionFactor M0 := by
  norm_num [projectedChi, contractionFactor, M0]

theorem projectedEta_eq : projectedEta = (M0 ^ 2)⁻¹ := by
  norm_num [projectedEta, M0]

theorem feasibleMicroIterations_positive : 1 ≤ feasibleMicroIterations := by
  have h := numericalStoppingIndex_spec
    (M := M0) (chi := contractionFactor M0)
    (le_trans zero_le_one M0_ge_one)
    (contractionFactor_nonneg M0)
    (contractionFactor_lt_one M0_ge_one)
  exact h.1

@[simp] theorem feasibleMicro_cost_oracleCalls :
    (projectedMicroCost feasibleMicroIterations).oracleCalls =
      feasibleMicroIterations + 1 := rfl

@[simp] theorem feasibleMicro_cost_projections :
    (projectedMicroCost feasibleMicroIterations).projections =
      feasibleMicroIterations + 1 := rfl

end

end ProjectedMicro
end Upper
end NCCLowerBoundVerification
