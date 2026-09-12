import NCPLVerification.ZeroChain

/-!
# The NC--PL class

This file gives a finite-dimensional, fully quantified version of Definition
1.1.  Gradients are linked to the actual Frechet derivative through its action
on every primal-dual direction.
-/

namespace NCPLVerification

noncomputable section

def vecSq {m : Nat} (v : EVec m) : ℝ :=
  ∑ i : Fin m, v i ^ 2

def jointSq {dx dy : Nat} (x : EVec dx) (y : EVec dy) : ℝ :=
  vecSq x + vecSq y

def IsMaximizer {dx dy : Nat} (F : EVec dx → EVec dy → ℝ)
    (x : EVec dx) (y : EVec dy) : Prop :=
  ∀ v, F x v ≤ F x y

def Envelope {dx dy : Nat} (F : EVec dx → EVec dy → ℝ)
    (x : EVec dx) : ℝ :=
  sSup (Set.range (F x))

/-- The two coordinate fields represent the actual derivative of `F`. -/
def RepresentsJointGradient {dx dy : Nat}
    (F : EVec dx → EVec dy → ℝ)
    (gradX : EVec dx → EVec dy → EVec dx)
    (gradY : EVec dx → EVec dy → EVec dy) : Prop :=
  Differentiable ℝ (Function.uncurry F) ∧
    ∀ x y hx hy,
      fderiv ℝ (Function.uncurry F) (x, y) (hx, hy) =
        (∑ i : Fin dx, gradX x y i * hx i) +
          ∑ j : Fin dy, gradY x y j * hy j

/-- Joint `L`-smoothness, written as the squared Euclidean Lipschitz-gradient
inequality.  The assumption `0 ≤ L` is recorded separately in `NCPLClass`. -/
def IsJointlySmooth {dx dy : Nat} (L : ℝ)
    (gradX : EVec dx → EVec dy → EVec dx)
    (gradY : EVec dx → EVec dy → EVec dy) : Prop :=
  ∀ x y x' y',
    jointSq (gradX x y - gradX x' y') (gradY x y - gradY x' y') ≤
      L ^ 2 * jointSq (x - x') (y - y')

/-- Definition 1.1, including attainment of every inner maximum so that the
paper's `max` is literal rather than only a supremum. -/
structure NCPLClass {dx dy : Nat} (L mu Delta : ℝ)
    (F : EVec dx → EVec dy → ℝ)
    (gradX : EVec dx → EVec dy → EVec dx)
    (gradY : EVec dx → EVec dy → EVec dy) : Prop where
  L_nonneg : 0 ≤ L
  mu_nonneg : 0 ≤ mu
  Delta_nonneg : 0 ≤ Delta
  gradient_representation : RepresentsJointGradient F gradX gradY
  jointly_smooth : IsJointlySmooth L gradX gradY
  maximum_attained : ∀ x, ∃ y, IsMaximizer F x y
  maximization_PL : ∀ x y,
    (1 : ℝ) / 2 * vecSq (gradY x y) ≥ mu * (Envelope F x - F x y)
  envelope_bddBelow : BddBelow (Set.range (Envelope F))
  initial_gap : Envelope F 0 - sInf (Set.range (Envelope F)) ≤ Delta

theorem envelope_eq_of_isMaximizer {dx dy : Nat}
    {F : EVec dx → EVec dy → ℝ} {x : EVec dx} {y : EVec dy}
    (hy : IsMaximizer F x y) : Envelope F x = F x y := by
  unfold Envelope
  apply le_antisymm
  · apply csSup_le
    · exact ⟨F x y, by simp⟩
    · rintro _ ⟨v, rfl⟩
      exact hy v
  · apply le_csSup
    · exact ⟨F x y, by
        rintro _ ⟨v, rfl⟩
        exact hy v⟩
    · exact Set.mem_range_self y

/-- A stronger PL constant implies every weaker requested constant. -/
theorem NCPLClass.weaken_mu {dx dy : Nat} {L mu mu' Delta : ℝ}
    {F : EVec dx → EVec dy → ℝ}
    {gradX : EVec dx → EVec dy → EVec dx}
    {gradY : EVec dx → EVec dy → EVec dy}
    (hclass : NCPLClass L mu' Delta F gradX gradY)
    (hmu : 0 ≤ mu) (hle : mu ≤ mu') :
    NCPLClass L mu Delta F gradX gradY := by
  refine { hclass with mu_nonneg := hmu, maximization_PL := ?_ }
  intro x y
  have hgap : 0 ≤ Envelope F x - F x y := by
    obtain ⟨v, hv⟩ := hclass.maximum_attained x
    rw [envelope_eq_of_isMaximizer hv]
    linarith [hv y]
  exact (mul_le_mul_of_nonneg_right hle hgap).trans
    (hclass.maximization_PL x y)

end

end NCPLVerification
