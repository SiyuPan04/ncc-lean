import NCPLVerification.Definitions

/-!
# The bounded-dual-domain NC--C class

This module formalizes the ambient finite-dimensional objects in
`Upper+Lower_unified_lower.tex`, Definitions 2.1 and 2.5.  A paper objective
on a closed domain is represented by one chosen continuously differentiable
extension to the ambient Euclidean coordinate spaces; every class condition
is imposed only on the stated primal and dual domains.
-/

namespace NCCLowerBoundVerification

noncomputable section

abbrev EVec := NCPLVerification.EVec

def vecSq {n : Nat} (x : EVec n) : ℝ :=
  NCPLVerification.vecSq x

def jointSq {m n : Nat} (x : EVec m) (y : EVec n) : ℝ :=
  vecSq x + vecSq y

def IsMaximizerOn {m n : Nat} (Y : Set (EVec n))
    (f : EVec m → EVec n → ℝ) (x : EVec m) (y : EVec n) : Prop :=
  y ∈ Y ∧ ∀ v ∈ Y, f x v ≤ f x y

/-- The value function on the bounded dual domain. -/
def ValueOn {m n : Nat} (Y : Set (EVec n))
    (f : EVec m → EVec n → ℝ) (x : EVec m) : ℝ :=
  sSup (f x '' Y)

/-- The paper's ball has radius `1/2`, so `diameterBall D` has diameter `D`. -/
def diameterBall (n : Nat) (D : ℝ) : Set (EVec n) :=
  {y | vecSq y ≤ (D / 2) ^ 2}

/-- A concrete proximal minimizer over the primal domain. -/
def IsProxPoint {m : Nat} (X : Set (EVec m)) (phi : EVec m → ℝ)
    (ell : ℝ) (x u : EVec m) : Prop :=
  u ∈ X ∧ ∀ v ∈ X,
    phi u + ell * vecSq (u - x) ≤ phi v + ell * vecSq (v - x)

/-- Optimization stationarity from Definition 2.5, written without choosing
an `argmin`: the weak-convexity theorem later proves this minimizer is unique. -/
def IsOptimizationStationary {m : Nat} (X : Set (EVec m))
    (phi : EVec m → ℝ) (ell eps : ℝ) (x : EVec m) : Prop :=
  ∃ u, IsProxPoint X phi ell x u ∧
    vecSq (u - x) ≤ (eps / (2 * ell)) ^ 2

/-- The data carried by one finite-dimensional problem instance. -/
structure NCCInstance (m n : Nat) where
  X : Set (EVec m)
  Y : Set (EVec n)
  f : EVec m → EVec n → ℝ
  gradX : EVec m → EVec n → EVec m
  gradY : EVec m → EVec n → EVec n
  x0 : EVec m

/-- Definition 2.1 in a fully quantified form.  Attainment and a lower bound
are recorded explicitly so every `max` and `inf` used by the paper is literal. -/
structure IsNCCClass {m n : Nat} (ell D Delta : ℝ)
    (P : NCCInstance m n) : Prop where
  ell_pos : 0 < ell
  D_pos : 0 < D
  Delta_pos : 0 < Delta
  x0_mem : P.x0 ∈ P.X
  X_nonempty : P.X.Nonempty
  X_closed : IsClosed P.X
  X_convex : Convex ℝ P.X
  Y_nonempty : P.Y.Nonempty
  Y_closed : IsClosed P.Y
  Y_convex : Convex ℝ P.Y
  gradient_representation :
    NCPLVerification.RepresentsJointGradient P.f P.gradX P.gradY
  jointly_smooth : ∀ x ∈ P.X, ∀ y ∈ P.Y,
    ∀ x' ∈ P.X, ∀ y' ∈ P.Y,
      jointSq (P.gradX x y - P.gradX x' y')
          (P.gradY x y - P.gradY x' y') ≤
        ell ^ 2 * jointSq (x - x') (y - y')
  dual_concave : ∀ x ∈ P.X, ConcaveOn ℝ P.Y (P.f x)
  maximum_attained : ∀ x ∈ P.X, ∃ y, IsMaximizerOn P.Y P.f x y
  value_bddBelow : BddBelow (ValueOn P.Y P.f '' P.X)
  initial_gap :
    ValueOn P.Y P.f P.x0 - sInf (ValueOn P.Y P.f '' P.X) ≤ Delta
  dual_diameter : ∀ y ∈ P.Y, ∀ y' ∈ P.Y, vecSq (y - y') ≤ D ^ 2

theorem value_eq_of_isMaximizerOn {m n : Nat} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {x : EVec m} {y : EVec n}
    (hy : IsMaximizerOn Y f x y) : ValueOn Y f x = f x y := by
  unfold ValueOn
  apply le_antisymm
  · apply csSup_le
    · exact ⟨f x y, ⟨y, hy.1, rfl⟩⟩
    · rintro _ ⟨v, hv, rfl⟩
      exact hy.2 v hv
  · apply le_csSup
    · exact ⟨f x y, by
        rintro _ ⟨v, hv, rfl⟩
        exact hy.2 v hv⟩
    · exact ⟨y, hy.1, rfl⟩

end

end NCCLowerBoundVerification
