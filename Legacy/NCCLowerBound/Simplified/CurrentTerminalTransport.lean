import NCCLowerBound.Simplified.CurrentHardData

/-!
# Exact transport to terminal product coordinates

The framework stores each primal block as `(aᵢ,bᵢ,sᵢ)`, while the terminal
certificate uses the product of the full state vector and the serialised
`(aᵢ,bᵢ)` pulse vector.  This module proves that the actual Fréchet-gradient
energy is exactly preserved by that fixed coordinate permutation.
-/

namespace NCCLowerBound
namespace Simplified
namespace CurrentTerminalTransport

noncomputable section

open scoped BigOperators
open NCCLowerBoundVerification
open CurrentHardData
open TerminalCertificate

private theorem state_basis_state_generic {T : Nat} (i : Fin (T - 1)) :
    primalState
        (NCPLVerification.evecBasis (primalStateIndex i) : UnscaledPrimal T) =
      NCPLVerification.evecBasis i := by
  funext j
  unfold primalState NCPLVerification.evecBasis
  by_cases hji : j = i
  · subst j
    simp
  · have hidx : primalStateIndex j ≠ primalStateIndex i := by
      intro h
      apply hji
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 3 * j.val + 2 = 3 * i.val + 2 at hv
      omega
    simp [hji, hidx]

private theorem A_basis_A_generic {T : Nat} (i : Fin (T - 1)) :
    primalA
        (NCPLVerification.evecBasis (primalAIndex i) : UnscaledPrimal T) =
      NCPLVerification.evecBasis i := by
  funext j
  unfold primalA NCPLVerification.evecBasis
  by_cases hji : j = i
  · subst j
    simp
  · have hidx : primalAIndex j ≠ primalAIndex i := by
      intro h
      apply hji
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 3 * j.val = 3 * i.val at hv
      omega
    simp [hji, hidx]

private theorem B_basis_B_generic {T : Nat} (i : Fin (T - 1)) :
    primalB
        (NCPLVerification.evecBasis (primalBIndex i) : UnscaledPrimal T) =
      NCPLVerification.evecBasis i := by
  funext j
  unfold primalB NCPLVerification.evecBasis
  by_cases hji : j = i
  · subst j
    simp
  · have hidx : primalBIndex j ≠ primalBIndex i := by
      intro h
      apply hji
      apply Fin.ext
      have hv := congrArg Fin.val h
      change 3 * j.val + 1 = 3 * i.val + 1 at hv
      omega
    simp [hji, hidx]

private theorem A_basis_state_generic {T : Nat} (i : Fin (T - 1)) :
    primalA
        (NCPLVerification.evecBasis (primalStateIndex i) : UnscaledPrimal T) =
      0 := by
  funext j
  unfold primalA NCPLVerification.evecBasis
  have hidx : primalAIndex j ≠ primalStateIndex i := by
    intro h
    have hv := congrArg Fin.val h
    change 3 * j.val = 3 * i.val + 2 at hv
    omega
  simp [hidx]

private theorem B_basis_state_generic {T : Nat} (i : Fin (T - 1)) :
    primalB
        (NCPLVerification.evecBasis (primalStateIndex i) : UnscaledPrimal T) =
      0 := by
  funext j
  unfold primalB NCPLVerification.evecBasis
  have hidx : primalBIndex j ≠ primalStateIndex i := by
    intro h
    have hv := congrArg Fin.val h
    change 3 * j.val + 1 = 3 * i.val + 2 at hv
    omega
  simp [hidx]

private theorem state_basis_A_generic {T : Nat} (i : Fin (T - 1)) :
    primalState
        (NCPLVerification.evecBasis (primalAIndex i) : UnscaledPrimal T) =
      0 := by
  funext j
  unfold primalState NCPLVerification.evecBasis
  have hidx : primalStateIndex j ≠ primalAIndex i := by
    intro h
    have hv := congrArg Fin.val h
    change 3 * j.val + 2 = 3 * i.val at hv
    omega
  simp [hidx]

private theorem state_basis_B_generic {T : Nat} (i : Fin (T - 1)) :
    primalState
        (NCPLVerification.evecBasis (primalBIndex i) : UnscaledPrimal T) =
      0 := by
  funext j
  unfold primalState NCPLVerification.evecBasis
  have hidx : primalStateIndex j ≠ primalBIndex i := by
    intro h
    have hv := congrArg Fin.val h
    change 3 * j.val + 2 = 3 * i.val + 1 at hv
    omega
  simp [hidx]

private theorem B_basis_A_generic {T : Nat} (i : Fin (T - 1)) :
    primalB
        (NCPLVerification.evecBasis (primalAIndex i) : UnscaledPrimal T) =
      0 := by
  funext j
  unfold primalB NCPLVerification.evecBasis
  have hidx : primalBIndex j ≠ primalAIndex i := by
    intro h
    have hv := congrArg Fin.val h
    change 3 * j.val + 1 = 3 * i.val at hv
    omega
  simp [hidx]

private theorem A_basis_B_generic {T : Nat} (i : Fin (T - 1)) :
    primalA
        (NCPLVerification.evecBasis (primalBIndex i) : UnscaledPrimal T) =
      0 := by
  funext j
  unfold primalA NCPLVerification.evecBasis
  have hidx : primalAIndex j ≠ primalBIndex i := by
    intro h
    have hv := congrArg Fin.val h
    change 3 * j.val = 3 * i.val + 1 at hv
    omega
  simp [hidx]

private theorem terminalPulse_ext {M : Nat}
    (p q : TerminalCertificate.Pulse M)
    (hA : TerminalCertificate.pulseA p = TerminalCertificate.pulseA q)
    (hB : TerminalCertificate.pulseB p = TerminalCertificate.pulseB q) :
    p = q := by
  funext j
  rcases hij : finProdFinEquiv.symm j with ⟨i, k⟩
  have hj := Equiv.apply_symm_apply finProdFinEquiv j
  rw [hij] at hj
  rw [← hj]
  refine Fin.cases ?_ (fun l => ?_) k
  · simpa [TerminalCertificate.pulseA] using congrFun hA i
  · have hl : l = 0 := Subsingleton.elim _ _
    subst l
    simpa [TerminalCertificate.pulseB] using congrFun hB i

private theorem terminalPulseA_basis_A {M : Nat} (i : Fin M) :
    TerminalCertificate.pulseA
        (NCPLVerification.evecBasis (TerminalCertificate.pulseAIndex i)) =
      NCPLVerification.evecBasis i := by
  funext j
  simp [TerminalCertificate.pulseA, TerminalCertificate.pulseAIndex,
    NCPLVerification.evecBasis]

private theorem terminalPulseB_basis_A {M : Nat} (i : Fin M) :
    TerminalCertificate.pulseB
        (NCPLVerification.evecBasis (TerminalCertificate.pulseAIndex i)) = 0 := by
  funext j
  simp [TerminalCertificate.pulseB, TerminalCertificate.pulseAIndex,
    NCPLVerification.evecBasis]

private theorem terminalPulseA_basis_B {M : Nat} (i : Fin M) :
    TerminalCertificate.pulseA
        (NCPLVerification.evecBasis (TerminalCertificate.pulseBIndex i)) = 0 := by
  funext j
  simp [TerminalCertificate.pulseA, TerminalCertificate.pulseBIndex,
    NCPLVerification.evecBasis]

private theorem terminalPulseB_basis_B {M : Nat} (i : Fin M) :
    TerminalCertificate.pulseB
        (NCPLVerification.evecBasis (TerminalCertificate.pulseBIndex i)) =
      NCPLVerification.evecBasis i := by
  funext j
  simp [TerminalCertificate.pulseB, TerminalCertificate.pulseBIndex,
    NCPLVerification.evecBasis]

theorem toTerminalCLM_basis_state {M : Nat} (i : Fin M) :
    toTerminalCLM
        (NCPLVerification.evecBasis (primalStateIndex i) :
          CurrentHardData.Primal M) =
      (NCPLVerification.evecBasis i, 0) := by
  let ii : Fin ((M + 1) - 1) := ⟨i.val, by omega⟩
  have hs : primalState
      (NCPLVerification.evecBasis (primalStateIndex i) :
        CurrentHardData.Primal M) = NCPLVerification.evecBasis i := by
    simpa [ii] using state_basis_state_generic (T := M + 1) ii
  have hA : primalA
      (NCPLVerification.evecBasis (primalStateIndex i) :
        CurrentHardData.Primal M) = 0 := by
    simpa [ii] using A_basis_state_generic (T := M + 1) ii
  have hB : primalB
      (NCPLVerification.evecBasis (primalStateIndex i) :
        CurrentHardData.Primal M) = 0 := by
    simpa [ii] using B_basis_state_generic (T := M + 1) ii
  rw [toTerminalCLM_apply]
  apply Prod.ext
  · exact hs
  · apply terminalPulse_ext
    · rw [show (toTerminalPrimal
          (NCPLVerification.evecBasis (primalStateIndex i) :
            CurrentHardData.Primal M)).2 = toPulse
            (NCPLVerification.evecBasis (primalStateIndex i) :
              CurrentHardData.Primal M) by rfl]
      rw [terminalPulseA_toPulse, hA]
      rfl
    · rw [show (toTerminalPrimal
          (NCPLVerification.evecBasis (primalStateIndex i) :
            CurrentHardData.Primal M)).2 = toPulse
            (NCPLVerification.evecBasis (primalStateIndex i) :
              CurrentHardData.Primal M) by rfl]
      rw [terminalPulseB_toPulse, hB]
      rfl

theorem toTerminalCLM_basis_A {M : Nat} (i : Fin M) :
    toTerminalCLM
        (NCPLVerification.evecBasis (primalAIndex i) :
          CurrentHardData.Primal M) =
      (0, NCPLVerification.evecBasis (TerminalCertificate.pulseAIndex i)) := by
  let ii : Fin ((M + 1) - 1) := ⟨i.val, by omega⟩
  have hs : primalState
      (NCPLVerification.evecBasis (primalAIndex i) :
        CurrentHardData.Primal M) = 0 := by
    simpa [ii] using state_basis_A_generic (T := M + 1) ii
  have hA : primalA
      (NCPLVerification.evecBasis (primalAIndex i) :
        CurrentHardData.Primal M) = NCPLVerification.evecBasis i := by
    simpa [ii] using A_basis_A_generic (T := M + 1) ii
  have hB : primalB
      (NCPLVerification.evecBasis (primalAIndex i) :
        CurrentHardData.Primal M) = 0 := by
    simpa [ii] using B_basis_A_generic (T := M + 1) ii
  rw [toTerminalCLM_apply]
  apply Prod.ext
  · exact hs
  · apply terminalPulse_ext
    · rw [show (toTerminalPrimal
          (NCPLVerification.evecBasis (primalAIndex i) :
            CurrentHardData.Primal M)).2 = toPulse
            (NCPLVerification.evecBasis (primalAIndex i) :
              CurrentHardData.Primal M) by rfl]
      rw [terminalPulseA_toPulse, hA, terminalPulseA_basis_A]
    · rw [show (toTerminalPrimal
          (NCPLVerification.evecBasis (primalAIndex i) :
            CurrentHardData.Primal M)).2 = toPulse
            (NCPLVerification.evecBasis (primalAIndex i) :
              CurrentHardData.Primal M) by rfl]
      rw [terminalPulseB_toPulse, hB, terminalPulseB_basis_A]
      rfl

theorem toTerminalCLM_basis_B {M : Nat} (i : Fin M) :
    toTerminalCLM
        (NCPLVerification.evecBasis (primalBIndex i) :
          CurrentHardData.Primal M) =
      (0, NCPLVerification.evecBasis (TerminalCertificate.pulseBIndex i)) := by
  let ii : Fin ((M + 1) - 1) := ⟨i.val, by omega⟩
  have hs : primalState
      (NCPLVerification.evecBasis (primalBIndex i) :
        CurrentHardData.Primal M) = 0 := by
    simpa [ii] using state_basis_B_generic (T := M + 1) ii
  have hA : primalA
      (NCPLVerification.evecBasis (primalBIndex i) :
        CurrentHardData.Primal M) = 0 := by
    simpa [ii] using A_basis_B_generic (T := M + 1) ii
  have hB : primalB
      (NCPLVerification.evecBasis (primalBIndex i) :
        CurrentHardData.Primal M) = NCPLVerification.evecBasis i := by
    simpa [ii] using B_basis_B_generic (T := M + 1) ii
  rw [toTerminalCLM_apply]
  apply Prod.ext
  · exact hs
  · apply terminalPulse_ext
    · rw [show (toTerminalPrimal
          (NCPLVerification.evecBasis (primalBIndex i) :
            CurrentHardData.Primal M)).2 = toPulse
            (NCPLVerification.evecBasis (primalBIndex i) :
              CurrentHardData.Primal M) by rfl]
      rw [terminalPulseA_toPulse, hA, terminalPulseA_basis_B]
      rfl
    · rw [show (toTerminalPrimal
          (NCPLVerification.evecBasis (primalBIndex i) :
            CurrentHardData.Primal M)).2 = toPulse
            (NCPLVerification.evecBasis (primalBIndex i) :
              CurrentHardData.Primal M) by rfl]
      rw [terminalPulseB_toPulse, hB, terminalPulseB_basis_B]

/-- Pull a scalar function on terminal product coordinates back to the
framework primal coordinates. -/
def pulledTerminalValue {M : Nat}
    (f : TerminalPrimal M → ℝ) : CurrentHardData.Primal M → ℝ :=
  fun x ↦ f (toTerminalPrimal x)

theorem fderiv_pulledTerminalValue {M : Nat}
    (f : TerminalPrimal M → ℝ) (hf : Differentiable ℝ f)
    (x : CurrentHardData.Primal M) :
    fderiv ℝ (pulledTerminalValue f) x =
      (fderiv ℝ f (toTerminalPrimal x)).comp toTerminalCLM := by
  change fderiv ℝ (f ∘ toTerminalPrimal) x = _
  exact ((hf (toTerminalPrimal x)).hasFDerivAt.comp x
    (toTerminalCLM (M := M)).hasFDerivAt).fderiv

/-- The coordinate gradient after pulling a terminal-product scalar through
the fixed coordinate permutation. -/
def pulledTerminalGradient {M : Nat}
    (f : TerminalPrimal M → ℝ) (x : CurrentHardData.Primal M) :
    CurrentHardData.Primal M :=
  NCPLVerification.continuousLinearMapCoordinates
    ((fderiv ℝ f (toTerminalPrimal x)).comp toTerminalCLM)

theorem pulledTerminalGradient_state {M : Nat}
    (f : TerminalPrimal M → ℝ) (x : CurrentHardData.Primal M)
    (i : Fin M) :
    primalState (pulledTerminalGradient f x) i =
      actualStateGradient f (toTerminalPrimal x) i := by
  unfold pulledTerminalGradient primalState
  simp only [NCPLVerification.continuousLinearMapCoordinates,
    ContinuousLinearMap.comp_apply, toTerminalCLM_basis_state,
    actualStateGradient, ambientGradX]

theorem pulledTerminalGradient_A {M : Nat}
    (f : TerminalPrimal M → ℝ) (x : CurrentHardData.Primal M)
    (i : Fin M) :
    primalA (pulledTerminalGradient f x) i =
      actualPulseGradient f (toTerminalPrimal x)
        (TerminalCertificate.pulseAIndex (M := M) i) := by
  unfold pulledTerminalGradient primalA
  simp only [NCPLVerification.continuousLinearMapCoordinates,
    ContinuousLinearMap.comp_apply, toTerminalCLM_basis_A,
    actualPulseGradient, ambientGradY]

theorem pulledTerminalGradient_B {M : Nat}
    (f : TerminalPrimal M → ℝ) (x : CurrentHardData.Primal M)
    (i : Fin M) :
    primalB (pulledTerminalGradient f x) i =
      actualPulseGradient f (toTerminalPrimal x)
        (TerminalCertificate.pulseBIndex (M := M) i) := by
  unfold pulledTerminalGradient primalB
  simp only [NCPLVerification.continuousLinearMapCoordinates,
    ContinuousLinearMap.comp_apply, toTerminalCLM_basis_B,
    actualPulseGradient, ambientGradY]

theorem vecSq_terminalPulse {M : Nat} (p : TerminalCertificate.Pulse M) :
    vecSq p = ∑ i : Fin M,
      ((p (TerminalCertificate.pulseAIndex (M := M) i)) ^ 2 +
        (p (TerminalCertificate.pulseBIndex (M := M) i)) ^ 2) := by
  simpa [InnerFiniteBall.pulseA, InnerFiniteBall.pulseB,
    TerminalCertificate.pulseAIndex, TerminalCertificate.pulseBIndex] using
    (InnerFiniteBall.vecSq_pulse p)

theorem vecSq_pulledTerminalGradient {M : Nat}
    (f : TerminalPrimal M → ℝ) (x : CurrentHardData.Primal M) :
    vecSq (pulledTerminalGradient f x) =
      actualGradientSq f (toTerminalPrimal x) := by
  rw [NCCLowerBoundVerification.vecSq_unscaledPrimal_blocks]
  unfold actualGradientSq
  rw [vecSq_terminalPulse (actualPulseGradient f (toTerminalPrimal x))]
  unfold vecSq NCPLVerification.vecSq
  simp_rw [pulledTerminalGradient_A, pulledTerminalGradient_B,
    pulledTerminalGradient_state]
  rw [Finset.sum_add_distrib]
  exact add_comm _ _

theorem vecSq_coordinateGradient_pulledTerminalValue {M : Nat}
    (f : TerminalPrimal M → ℝ) (hf : Differentiable ℝ f)
    (x : CurrentHardData.Primal M) :
    vecSq
        (NCPLVerification.continuousLinearMapCoordinates
          (fderiv ℝ (pulledTerminalValue f) x)) =
      actualGradientSq f (toTerminalPrimal x) := by
  rw [fderiv_pulledTerminalValue f hf x]
  exact vecSq_pulledTerminalGradient f x

/-! ## The concrete finite/unbounded scoped values -/

/-- The finite or unrestricted inner value, augmented by the same terminal
outer potential as `CurrentHardData.scopedValue`. -/
def terminalScopedValue {M N : Nat} (hN : 0 < N) (K : ℝ) :
    Framework.DualScope → TerminalPrimal M → ℝ
  | .finite D _ =>
      terminalValue K (InnerFiniteBall.finiteValue hN D)
  | .unbounded =>
      terminalValue K (InnerFiniteBall.unboundedValue hN)

theorem scopedValue_eq_pulledTerminalScopedValue {M N : Nat}
    (hN10 : 10 ≤ N) (K : ℝ) (q : Framework.DualScope) :
    scopedValue (M := M) (by omega : 0 < N) K q =
      pulledTerminalValue
        (terminalScopedValue (M := M) (by omega : 0 < N) K q) := by
  funext x
  cases q with
  | finite D hD =>
      rw [show scopedValue (M := M) (by omega : 0 < N) K
          (.finite D hD) x =
          finiteSourceValue (by omega : 0 < N) K D x by rfl]
      rw [finiteSourceValue_eq (by omega : 0 < N) K D hD.le x]
      simp [pulledTerminalValue, terminalScopedValue, terminalValue,
        terminalOuterValue, outerValue]
  | unbounded =>
      rw [show scopedValue (M := M) (by omega : 0 < N) K .unbounded x =
          unboundedSourceValue (by omega : 0 < N) K x by rfl]
      rw [unboundedSourceValue_eq (by omega : 0 < N) K x]
      simp [pulledTerminalValue, terminalScopedValue, terminalValue,
        terminalOuterValue, outerValue]

theorem terminalScopedValue_differentiable {M N : Nat}
    (hN10 : 10 ≤ N) (K : ℝ) (q : Framework.DualScope) :
    Differentiable ℝ
      (terminalScopedValue (M := M) (by omega : 0 < N) K q) := by
  cases q with
  | finite D hD =>
      exact terminalValue_differentiable K
        (InnerFiniteBall.finiteValue_differentiable
          (by omega : 0 < N) hD.le)
  | unbounded =>
      exact terminalValue_differentiable K
        (InnerFiniteBall.unboundedValue_differentiable (M := M) hN10)

/-- Exact equality between the framework `valueGrad` energy and the actual
terminal-product gradient energy, uniformly over finite and unbounded dual
scopes. -/
theorem vecSq_valueGrad_eq_actualGradientSq {M N : Nat}
    (hN10 : 10 ≤ N) (K : ℝ) (q : Framework.DualScope)
    (x : CurrentHardData.Primal M) :
    vecSq
        (valueGrad (M := M) (N := N) (by omega : 0 < N) K q x) =
      actualGradientSq
        (terminalScopedValue (M := M) (by omega : 0 < N) K q)
        (toTerminalPrimal x) := by
  unfold valueGrad
  rw [scopedValue_eq_pulledTerminalScopedValue hN10 K q]
  exact vecSq_coordinateGradient_pulledTerminalValue
    (terminalScopedValue (M := M) (by omega : 0 < N) K q)
    (terminalScopedValue_differentiable hN10 K q) x

theorem vecSq_valueGrad_finite_eq_actualGradientSq {M N : Nat}
    (hN10 : 10 ≤ N) (K D : ℝ) (hD : 0 < D)
    (x : CurrentHardData.Primal M) :
    vecSq
        (valueGrad (M := M) (N := N) (by omega : 0 < N) K
          (.finite D hD) x) =
      actualGradientSq
        (terminalValue K
          (InnerFiniteBall.finiteValue (M := M) (by omega : 0 < N) D))
        (toTerminalPrimal x) := by
  simpa [terminalScopedValue] using
    (vecSq_valueGrad_eq_actualGradientSq (M := M) hN10 K
      (.finite D hD) x)

theorem vecSq_valueGrad_unbounded_eq_actualGradientSq {M N : Nat}
    (hN10 : 10 ≤ N) (K : ℝ) (x : CurrentHardData.Primal M) :
    vecSq
        (valueGrad (M := M) (N := N) (by omega : 0 < N) K
          .unbounded x) =
      actualGradientSq
        (terminalValue K
          (InnerFiniteBall.unboundedValue (M := M) (by omega : 0 < N)))
        (toTerminalPrimal x) := by
  simpa [terminalScopedValue] using
    (vecSq_valueGrad_eq_actualGradientSq (M := M) hN10 K
      .unbounded x)

end

end CurrentTerminalTransport
end Simplified
end NCCLowerBound
