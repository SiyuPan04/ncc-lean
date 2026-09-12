import NCC.Model.Class

/-!
# Moreau analysis derived from the current class

The value is only used on `X`; minimizing over `X` is the extended-real
indicator convention of the manuscript. The envelope is defined by an
actual minimizer, and is proved equal to the infimum of the proximal
objective. Its derivative and its Euclidean Lipschitz estimate are theorems,
not assumptions about a vector called a gradient.
-/

namespace NCC.Moreau

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper

variable {m n : Nat} {ell D Delta : ℝ} {P : NCCInstance m n}

theorem value_weaklyConvex (h : Model.InClass ell D Delta P) :
    IsWeaklyConvexOn ell P.X (ValueOn P.Y P.f) := by
  obtain ⟨G⟩ := h.globalization
  have hw := G.class_mem.value_weakConvexity
  rw [G.X_eq] at hw
  apply hw.congr
  intro x hx
  change ValueOn G.globalized.Y G.globalized.f x + quadraticCorrection ell x =
    ValueOn P.Y P.f x + quadraticCorrection ell x
  rw [G.value_eq_on hx]

theorem prox_exists (h : Model.InClass ell D Delta P) :
    HasProxEverywhere P.X (ValueOn P.Y P.f) ell := by
  obtain ⟨G⟩ := h.globalization
  intro z
  obtain ⟨u, hu, hmin⟩ :=
    NCCLowerBoundVerification.Upper.IsNCCClass.value_hasProxEverywhere G.class_mem z
  rw [G.X_eq] at hu hmin
  refine ⟨u, hu, ?_⟩
  intro v hv
  have hh := hmin v hv
  rw [G.value_eq_on hu, G.value_eq_on hv] at hh
  exact hh

def prox (h : Model.InClass ell D Delta P) (z : EVec m) : EVec m :=
  selectedProx (prox_exists h) z

def envelope (h : Model.InClass ell D Delta P) (z : EVec m) : ℝ :=
  moreauEnvelope (ValueOn P.Y P.f) ell (prox_exists h) z

def gradient (h : Model.InClass ell D Delta P) (z : EVec m) : EVec m :=
  residualGradient (prox_exists h) z

theorem prox_spec (h : Model.InClass ell D Delta P) (z : EVec m) :
    IsProxPoint P.X (ValueOn P.Y P.f) ell z (prox h z) :=
  selectedProx_spec (prox_exists h) z

theorem prox_unique (h : Model.InClass ell D Delta P) {z u : EVec m}
    (hu : IsProxPoint P.X (ValueOn P.Y P.f) ell z u) : prox h z = u :=
  selectedProx_unique h.ell_pos (value_weaklyConvex h) (prox_exists h) hu

theorem envelope_eq_inf (h : Model.InClass ell D Delta P) (z : EVec m) :
    envelope h z = sInf ((proxObjective (ValueOn P.Y P.f) ell z) '' P.X) := by
  have hp := prox_spec h z
  have hmember : envelope h z ∈
      (proxObjective (ValueOn P.Y P.f) ell z) '' P.X :=
    ⟨prox h z, hp.1, rfl⟩
  have hlower : ∀ a ∈ (proxObjective (ValueOn P.Y P.f) ell z) '' P.X,
      envelope h z ≤ a := by
    rintro _ ⟨v, hv, rfl⟩
    exact hp.2 v hv
  apply le_antisymm
  · exact le_csInf ⟨envelope h z, hmember⟩ hlower
  · exact csInf_le ⟨envelope h z, hlower⟩ hmember

theorem gradient_formula (h : Model.InClass ell D Delta P) (z : EVec m) :
    gradient h z = (2 * ell) • (z - prox h z) := rfl

theorem hasFDerivAt_envelope (h : Model.InClass ell D Delta P) (z : EVec m) :
    HasFDerivAt (envelope h) (residualCLM (gradient h z)) z :=
  hasFDerivAt_moreauEnvelope h.ell_pos (value_weaklyConvex h) (prox_exists h) z

theorem differentiable_envelope (h : Model.InClass ell D Delta P) :
    Differentiable ℝ (envelope h) := by
  intro z
  exact (hasFDerivAt_envelope h z).differentiableAt

/-- Squared Euclidean form of `2*ell`-smoothness, for the actual derivative. -/
theorem gradient_lipschitz_sq (h : Model.InClass ell D Delta P) (z w : EVec m) :
    vecSq (gradient h z - gradient h w) ≤ (2 * ell) ^ 2 * vecSq (z - w) :=
  residualGradient_lipschitz_sq h.ell_pos (value_weaklyConvex h) (prox_exists h) z w

theorem gradient_squared (h : Model.InClass ell D Delta P) (z : EVec m) :
    vecSq (gradient h z) = (2 * ell) ^ 2 * vecSq (prox h z - z) := by
  rw [gradient_formula, vecSq_smul, vecSq_sub_comm]

/-- Current OS includes feasibility of the output, unlike a residual-only predicate. -/
def IsOS (h : Model.InClass ell D Delta P) (eps : ℝ) (z : EVec m) : Prop :=
  0 < eps ∧ z ∈ P.X ∧ vecSq (gradient h z) ≤ eps ^ 2

theorem residual_iff_prox_stationarity (h : Model.InClass ell D Delta P)
    (eps : ℝ) (z : EVec m) :
    vecSq (gradient h z) ≤ eps ^ 2 ↔
      IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps z := by
  have hc : 0 < (2 * ell) ^ 2 := sq_pos_of_pos (by linarith [h.ell_pos])
  rw [gradient_squared]
  constructor
  · intro hg
    refine ⟨prox h z, prox_spec h z, ?_⟩
    have hd : vecSq (prox h z - z) ≤ eps ^ 2 / (2 * ell) ^ 2 := by
      apply (le_div_iff₀ hc).2
      nlinarith only [hg]
    simpa only [div_pow] using hd
  · rintro ⟨u, hu, hd⟩
    rw [← prox_unique h hu] at hd
    have hm := mul_le_mul_of_nonneg_left hd hc.le
    have heq : (2 * ell) ^ 2 * (eps / (2 * ell)) ^ 2 = eps ^ 2 := by
      field_simp [ne_of_gt h.ell_pos]
    rwa [heq] at hm

theorem isOS_iff_feasible_prox (h : Model.InClass ell D Delta P)
    (eps : ℝ) (z : EVec m) :
    IsOS h eps z ↔ 0 < eps ∧ z ∈ P.X ∧
      IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps z := by
  unfold IsOS
  rw [residual_iff_prox_stationarity]

/-- The initial gradient bound now follows from the class alone. -/
theorem initial_gradient_squared_bound (h : Model.InClass ell D Delta P) :
    vecSq (gradient h 0) ≤ (8 / 3 : ℝ) * ell * Delta := by
  have hp := prox_spec h 0
  have hstrong := proxPoint_strongMinimizer h.ell_pos
    (value_weaklyConvex h) hp 0 h.primal_origin
  have hgap := h.initial_gap_pointwise (prox h 0) hp.1
  have hs0 : vecSq (0 : EVec m) = 0 := by
    simp [vecSq, NCPLVerification.vecSq]
  have hsym := vecSq_sub_comm (prox h 0) 0
  unfold proxObjective at hstrong
  rw [sub_self, hs0, mul_zero, add_zero, hsym] at hstrong
  rw [gradient_formula, vecSq_smul]
  have hell := h.ell_pos
  have hbase : (3 / 2 : ℝ) * ell * vecSq (0 - prox h 0) ≤ Delta := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hbase hell.le
  nlinarith only [hscaled]

end

end NCC.Moreau
