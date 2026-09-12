import NCCLowerBoundVerification.Basic
import NCCLowerBoundVerification.SmoothSectionWeakConvexity

/-!
# Dual-origin normalization

The upper algorithm first translates a feasible dual point to the origin.
This module verifies that the translation preserves every `IsNCCClass`
field and the value function, while making the origin feasible and turning
the diameter bound into the required radius bound.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace DualTranslation

noncomputable section

def translatedDualSet {n : Nat} (Y : Set (EVec n)) (ybar : EVec n) :
    Set (EVec n) :=
  {v | v + ybar ∈ Y}

def translatedInstance {m n : Nat} (P : NCCInstance m n)
    (ybar : EVec n) : NCCInstance m n where
  X := P.X
  Y := translatedDualSet P.Y ybar
  f := fun x v => P.f x (v + ybar)
  gradX := fun x v => P.gradX x (v + ybar)
  gradY := fun x v => P.gradY x (v + ybar)
  x0 := P.x0

@[simp] theorem zero_mem_translatedDualSet {n : Nat} {Y : Set (EVec n)}
    {ybar : EVec n} (hybar : ybar ∈ Y) :
    (0 : EVec n) ∈ translatedDualSet Y ybar := by
  simpa [translatedDualSet]

theorem translatedDualSet_nonempty {n : Nat} {Y : Set (EVec n)}
    {ybar : EVec n} (hybar : ybar ∈ Y) :
    (translatedDualSet Y ybar).Nonempty :=
  ⟨0, zero_mem_translatedDualSet hybar⟩

theorem translatedDualSet_closed {n : Nat} {Y : Set (EVec n)}
    (hY : IsClosed Y) (ybar : EVec n) :
    IsClosed (translatedDualSet Y ybar) := by
  have hc : Continuous (fun v : EVec n => v + ybar) :=
    continuous_id.add continuous_const
  exact hY.preimage hc

theorem translatedDualSet_convex {n : Nat} {Y : Set (EVec n)}
    (hY : Convex ℝ Y) (ybar : EVec n) :
    Convex ℝ (translatedDualSet Y ybar) := by
  intro u hu v hv a b ha hb hab
  change a • u + b • v + ybar ∈ Y
  have h := hY hu hv ha hb hab
  have heq :
      a • u + b • v + ybar =
        a • (u + ybar) + b • (v + ybar) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc
      a * u i + b * v i + ybar i =
          a * u i + b * v i + (a + b) * ybar i := by rw [hab, one_mul]
      _ = a * (u i + ybar i) + b * (v i + ybar i) := by ring
  rwa [heq]

private theorem translated_gradient_representation {m n : Nat}
    (P : NCCInstance m n) (ybar : EVec n)
    (hrep : NCPLVerification.RepresentsJointGradient
      P.f P.gradX P.gradY) :
    NCPLVerification.RepresentsJointGradient
      (translatedInstance P ybar).f
      (translatedInstance P ybar).gradX
      (translatedInstance P ybar).gradY := by
  let shift : (EVec m × EVec n) → (EVec m × EVec n) :=
    fun p => p + (0, ybar)
  have hshift (p : EVec m × EVec n) :
      HasFDerivAt shift (ContinuousLinearMap.id ℝ
        (EVec m × EVec n) :
        (EVec m × EVec n) →L[ℝ] (EVec m × EVec n)) p := by
    simpa [shift] using
      (ContinuousLinearMap.id ℝ (EVec m × EVec n)).hasFDerivAt.add_const
        (0, ybar)
  have hfun : Function.uncurry (translatedInstance P ybar).f =
      (Function.uncurry P.f) ∘ shift := by
    funext p
    rcases p with ⟨x, y⟩
    simp [translatedInstance, shift]
  constructor
  · rw [hfun]
    exact hrep.1.comp (by
      intro p
      exact (hshift p).differentiableAt)
  · intro x y hx hy
    have hout : HasFDerivAt (Function.uncurry P.f)
        (fderiv ℝ (Function.uncurry P.f) (shift (x, y)))
        (shift (x, y)) :=
      hrep.1.differentiableAt.hasFDerivAt
    have hcomp := hout.comp (x, y) (hshift (x, y))
    have hfd :
        fderiv ℝ (Function.uncurry (translatedInstance P ybar).f) (x, y) =
          (fderiv ℝ (Function.uncurry P.f) (x, y + ybar)).comp
            (ContinuousLinearMap.id ℝ (EVec m × EVec n)) := by
      rw [hfun, hcomp.fderiv]
      simp [shift]
    rw [hfd, ContinuousLinearMap.comp_apply]
    change fderiv ℝ (Function.uncurry P.f) (x, y + ybar) (hx, hy) = _
    simpa [translatedInstance] using hrep.2 x (y + ybar) hx hy

theorem translated_maximizer {m n : Nat} {P : NCCInstance m n}
    {ybar : EVec n} {x : EVec m} {y : EVec n}
    (hy : IsMaximizerOn P.Y P.f x y) :
    IsMaximizerOn (translatedDualSet P.Y ybar)
      (translatedInstance P ybar).f x (y - ybar) := by
  constructor
  · change (y - ybar) + ybar ∈ P.Y
    simpa using hy.1
  · intro v hv
    simpa [translatedInstance] using hy.2 (v + ybar) hv

theorem translatedValue_eq {m n : Nat} {P : NCCInstance m n}
    {ybar : EVec n} {x : EVec m}
    (hmax : ∃ y, IsMaximizerOn P.Y P.f x y) :
    ValueOn (translatedDualSet P.Y ybar)
        (translatedInstance P ybar).f x =
      ValueOn P.Y P.f x := by
  obtain ⟨y, hy⟩ := hmax
  rw [value_eq_of_isMaximizerOn (translated_maximizer hy),
    value_eq_of_isMaximizerOn hy]
  simp [translatedInstance]

/-- Translation of a feasible dual point to zero preserves the complete
problem class, with exactly the same constants and primal value. -/
theorem IsNCCClass.translateDual {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    {ybar : EVec n} (hybar : ybar ∈ P.Y) :
    IsNCCClass ell D Delta (translatedInstance P ybar) := by
  refine
    { ell_pos := hP.ell_pos
      D_pos := hP.D_pos
      Delta_pos := hP.Delta_pos
      x0_mem := hP.x0_mem
      X_nonempty := hP.X_nonempty
      X_closed := hP.X_closed
      X_convex := hP.X_convex
      Y_nonempty := translatedDualSet_nonempty hybar
      Y_closed := translatedDualSet_closed hP.Y_closed ybar
      Y_convex := translatedDualSet_convex hP.Y_convex ybar
      gradient_representation := translated_gradient_representation P ybar
        hP.gradient_representation
      jointly_smooth := ?_
      dual_concave := ?_
      maximum_attained := ?_
      value_bddBelow := ?_
      initial_gap := ?_
      dual_diameter := ?_ }
  · intro x hx y hy x' hx' y' hy'
    have h := hP.jointly_smooth x hx (y + ybar) hy
      x' hx' (y' + ybar) hy'
    have heq : (y + ybar) - (y' + ybar) = y - y' := by module
    rw [heq] at h
    exact h
  · intro x hx
    have hc := hP.dual_concave x hx
    refine ⟨translatedDualSet_convex hP.Y_convex ybar, ?_⟩
    intro y hy v hv a b ha hb hab
    have h := hc.2 hy hv ha hb hab
    change a • P.f x (y + ybar) + b • P.f x (v + ybar) ≤
      P.f x (a • y + b • v + ybar)
    have heq : a • y + b • v + ybar =
        a • (y + ybar) + b • (v + ybar) := by
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      calc
        a * y i + b * v i + ybar i =
            a * y i + b * v i + (a + b) * ybar i := by rw [hab, one_mul]
        _ = a * (y i + ybar i) + b * (v i + ybar i) := by ring
    rwa [heq]
  · intro x hx
    obtain ⟨y, hy⟩ := hP.maximum_attained x hx
    exact ⟨y - ybar, translated_maximizer hy⟩
  · -- Only values on `X` enter this field, where attainment is part of the
    -- class data.
    rw [show (translatedInstance P ybar).X = P.X by rfl]
    have hpoint : ∀ x ∈ P.X,
        ValueOn (translatedDualSet P.Y ybar)
            (translatedInstance P ybar).f x = ValueOn P.Y P.f x := by
      intro x hx
      exact translatedValue_eq (hP.maximum_attained x hx)
    rcases hP.value_bddBelow with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    change c ≤ ValueOn (translatedDualSet P.Y ybar)
      (translatedInstance P ybar).f x
    rw [hpoint x hx]
    exact hc ⟨x, hx, rfl⟩
  · have hpoint : ∀ x ∈ P.X,
        ValueOn (translatedDualSet P.Y ybar)
            (translatedInstance P ybar).f x = ValueOn P.Y P.f x := by
      intro x hx
      exact translatedValue_eq (hP.maximum_attained x hx)
    have himage :
        ValueOn (translatedDualSet P.Y ybar)
              (translatedInstance P ybar).f '' P.X =
          ValueOn P.Y P.f '' P.X := by
      ext q
      constructor <;> rintro ⟨x, hx, rfl⟩
      · exact ⟨x, hx, (hpoint x hx).symm⟩
      · exact ⟨x, hx, hpoint x hx⟩
    change ValueOn (translatedDualSet P.Y ybar)
        (translatedInstance P ybar).f P.x0 -
          sInf (ValueOn (translatedDualSet P.Y ybar)
            (translatedInstance P ybar).f '' P.X) ≤ Delta
    rw [hpoint P.x0 hP.x0_mem, himage]
    exact hP.initial_gap
  · intro y hy y' hy'
    have h := hP.dual_diameter (y + ybar) hy (y' + ybar) hy'
    have heq : (y + ybar) - (y' + ybar) = y - y' := by module
    rwa [heq] at h

/-- Every translated feasible dual point lies in the radius-`D` ball about
the new origin. -/
theorem translatedDual_vecSq_le {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P)
    {ybar : EVec n} (hybar : ybar ∈ P.Y) :
    ∀ v ∈ (translatedInstance P ybar).Y, vecSq v ≤ D ^ 2 := by
  intro v hv
  have h := hP.dual_diameter (v + ybar) hv ybar hybar
  simpa only [add_sub_cancel_right] using h

end

end DualTranslation
end Upper
end NCCLowerBoundVerification
