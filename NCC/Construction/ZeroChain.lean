import NCC.Construction.Regularity

/-!
# The current objective's genuine serialized saddle zero-chain

The serialized order is `(a_i,y_i,1,...,y_i,n,b_i,s_i)`. It is decoded
explicitly to `Composite`'s different flat primal order `(s_i,a_i,b_i)`.
The coordinate gradient below is the derivative of that literal decoded
objective. The old zero-chain theorem is used only after proving equality of
the old and current coordinate derivatives at every zero input coordinate;
the new separable phase correction has derivative zero there.
-/

namespace NCC.Construction.ZeroChain

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators
open NCCLowerBoundVerification

namespace Old
export NCCLowerBound.Simplified.CompositeZeroChain
  (chainObjective chainDecoded chainObjective_eq_saddleObjective coordinateGradient
    signedCoordinateField signedCoordinateField_isFirstOrderZeroChain)
end Old

/-- Serialization parameter `m` means `m-1` actual blocks. For a construction
with `M` blocks, specialize this parameter to `M+1`. -/
abbrev Chain (m n : ℕ) := SerializedSpace m n

def toPrimal {m n : ℕ} (q : Chain m n) : Composite.Primal (m - 1) :=
  Composite.primal (serializedState q) (serializedA q) (serializedB q)

def toDual {m n : ℕ} (q : Chain m n) : Composite.Dual (m - 1) n :=
  NCCLowerBound.Simplified.RestrictedBall.flattenBlocks (serializedDualBlock q)

@[simp] theorem state_toPrimal {m n : ℕ} (q : Chain m n) :
    Composite.state (toPrimal q) = serializedState q := Composite.state_primal ..

@[simp] theorem entrance_toPrimal {m n : ℕ} (q : Chain m n) :
    Composite.entrance (toPrimal q) = serializedA q := Composite.entrance_primal ..

@[simp] theorem exit_toPrimal {m n : ℕ} (q : Chain m n) :
    Composite.exit (toPrimal q) = serializedB q := Composite.exit_primal ..

@[simp] theorem toDual_block {m n : ℕ} (q : Chain m n) (i : Fin (m - 1)) (j : Fin n) :
    toDual q (finProdFinEquiv (i, j)) = q (serializedDualIndex i j) := by
  simp [toDual, NCCLowerBound.Simplified.RestrictedBall.flattenBlocks,
    serializedDualBlock, serializedY]

theorem toPrimal_contDiff {m n : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (toPrimal : Chain m n → _) := by
  apply contDiff_pi.2
  intro j
  unfold toPrimal Composite.primal
  dsimp
  split
  · unfold serializedState
    fun_prop
  · split
    · unfold serializedA
      fun_prop
    · unfold serializedB
      fun_prop

theorem toDual_contDiff {m n : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (toDual : Chain m n → _) := by
  unfold toDual NCCLowerBound.Simplified.RestrictedBall.flattenBlocks
    serializedDualBlock serializedY
  fun_prop

def toPrimalCLM {m n : ℕ} : Chain m n →L[ℝ] Composite.Primal (m - 1) :=
  LinearMap.toContinuousLinearMap
    ({ toFun := toPrimal
       map_add' := by
         intro q r
         funext j
         unfold toPrimal Composite.primal
         dsimp
         split
         · rfl
         · split <;> rfl
       map_smul' := by
         intro c q
         funext j
         unfold toPrimal Composite.primal
         dsimp
         split
         · rfl
         · split <;> rfl } : Chain m n →ₗ[ℝ] Composite.Primal (m - 1))

def toDualCLM {m n : ℕ} : Chain m n →L[ℝ] Composite.Dual (m - 1) n :=
  LinearMap.toContinuousLinearMap
    ({ toFun := toDual
       map_add' := by intro q r; rfl
       map_smul' := by intro c q; rfl } : Chain m n →ₗ[ℝ] Composite.Dual (m - 1) n)

def decoderCLM {m n : ℕ} :
    Chain m n →L[ℝ] Composite.Primal (m - 1) × Composite.Dual (m - 1) n :=
  toPrimalCLM.prod toDualCLM

@[simp] theorem decoderCLM_apply {m n : ℕ} (q : Chain m n) :
    decoderCLM q = (toPrimal q, toDual q) := rfl

def objective {m n : ℕ} (hn : 0 < n) (q : Chain m n) : ℝ :=
  Composite.objective hn (toPrimal q) (toDual q)

def correction {m n : ℕ} (q : Chain m n) : ℝ :=
  ∑ i : Fin (m - 1), Regularity.phaseCorrection (serializedState q i)

theorem objective_eq_old_add_correction {m n : ℕ} (hn : 0 < n) (q : Chain m n) :
    objective hn q = Old.chainObjective hn Outer.c_R q + correction q := by
  rw [objective, Regularity.objective_eq_old_add_correction]
  change NCCLowerBound.Simplified.Composite.hardObjective hn Outer.c_R
      (Composite.state (toPrimal q)) (Composite.entrance (toPrimal q))
      (Composite.exit (toPrimal q))
      (NCCLowerBound.Simplified.RestrictedBall.unflattenBlocks (toDual q)) +
      Regularity.correction (toPrimal q) = _
  simp only [state_toPrimal, entrance_toPrimal, exit_toPrimal, toDual,
    NCCLowerBound.Simplified.RestrictedBall.unflattenBlocks_flattenBlocks,
    Regularity.correction, state_toPrimal]
  rfl

theorem objective_contDiff {m n : ℕ} (hn : 0 < n) :
    ContDiff ℝ (⊤ : ℕ∞) (objective (m := m) hn) := by
  have hf := Regularity.objective_contDiff (m := m - 1) hn
  have hd := (toPrimal_contDiff (m := m) (n := n)).prodMk
    (toDual_contDiff (m := m) (n := n))
  convert! hf.comp hd using 1

theorem old_objective_differentiable {m n : ℕ} (hn : 0 < n) :
    Differentiable ℝ (Old.chainObjective (M := m) hn Outer.c_R) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (Old.chainDecoded (M := m) (N := n)) := by
    unfold Old.chainDecoded serializedState serializedA serializedB serializedDualBlock serializedY
    fun_prop
  have hc := NCCLowerBound.Simplified.CompositeProperties.saddleObjective_contDiff
    (M := m - 1) hn Outer.c_R
  exact (hc.comp hd).differentiable (by simp)

theorem correction_contDiff {m n : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (correction : Chain m n → ℝ) := by
  apply ContDiff.sum
  intro i _
  exact Regularity.phaseCorrection_contDiff.comp (by unfold serializedState; fun_prop)

theorem phaseCorrection_deriv_zero : deriv Regularity.phaseCorrection 0 = 0 := by
  change deriv (R Outer.c_R - NCCLowerBound.Simplified.phasePotential Outer.c_R) 0 = 0
  rw [deriv_sub ((R_contDiff Outer.c_R).differentiable (by simp) 0)
    ((NCCLowerBound.Simplified.phasePotential_contDiff Outer.c_R).differentiable (by simp) 0),
    deriv_R_near_zero (by norm_num) (by norm_num),
    NCCLowerBound.Simplified.phasePotential_deriv_zero]
  ring

theorem coordinateLine_hasDerivAt {m n : ℕ} (q : Chain m n) (j : Fin ((m - 1) * (n + 3))) :
    HasDerivAt (serializedCoordinateLine q j) (NCPLVerification.evecBasis j) (q j) := by
  convert! (hasDerivAt_const (q j) q).add
    (((hasDerivAt_id (q j)).sub_const (q j)).smul_const (NCPLVerification.evecBasis j)) using 1
  simp

@[simp] theorem coordinateLine_self {m n : ℕ} (q : Chain m n) (j : Fin ((m - 1) * (n + 3))) :
    serializedCoordinateLine q j (q j) = q := by
  funext k
  simp [serializedCoordinateLine]

/-- The genuine derivative of the literal serialized objective. -/
def coordinateGradient {m n : ℕ} (hn : 0 < n) (q : Chain m n) : Chain m n := fun j =>
  deriv (fun t => objective hn (serializedCoordinateLine q j t)) (q j)

theorem coordinateGradient_eq_fderiv {m n : ℕ} (hn : 0 < n)
    (q : Chain m n) (j : Fin ((m - 1) * (n + 3))) :
    coordinateGradient hn q j = fderiv ℝ (objective hn) q (NCPLVerification.evecBasis j) := by
  have hf := ((objective_contDiff hn).differentiable (by simp) q).hasFDerivAt
  have hc := hf.comp_hasDerivAt_of_eq (q j) (coordinateLine_hasDerivAt q j) (coordinateLine_self q j).symm
  exact hc.deriv

/-- The full ambient derivative is represented, in every direction. -/
theorem objective_hasFDerivAt {m n : ℕ} (hn : 0 < n) (q : Chain m n) :
    HasFDerivAt (objective hn) (NCPLVerification.evecDot (coordinateGradient hn q)) q := by
  have heq : NCPLVerification.evecDot (coordinateGradient hn q) = fderiv ℝ (objective hn) q := by
    ext d
    simp only [NCPLVerification.evecDot_apply, coordinateGradient_eq_fderiv]
    exact (NCPLVerification.continuousLinearMap_apply_eq_coordinates
      (fderiv ℝ (objective hn) q) d).symm
  rw [heq]
  exact ((objective_contDiff hn).differentiable (by simp) q).hasFDerivAt

theorem objective_hasFDerivAt_via_decoder {m n : ℕ} (hn : 0 < n) (q : Chain m n) :
    HasFDerivAt (objective hn)
      (ContinuousLinearMap.comp
        (fderiv ℝ (Function.uncurry (Composite.objective hn)) (toPrimal q, toDual q)) decoderCLM) q := by
  have hf := ((Regularity.gradient_represents_fderiv (m := m - 1) hn).1
    (toPrimal q, toDual q)).hasFDerivAt
  convert! hf.comp q (decoderCLM (m := m) (n := n)).hasFDerivAt using 1

/-- Exact pullback of the actual primal/dual gradient through the stated
coordinate decoding. This checks the oracle-to-serialization correspondence. -/
theorem coordinateGradient_pairing {m n : ℕ} (hn : 0 < n) (q d : Chain m n) :
    (∑ j, coordinateGradient hn q j * d j) =
      (∑ i, Regularity.gradientX hn (toPrimal q) (toDual q) i * toPrimal d i) +
      ∑ k, Regularity.gradientY hn (toPrimal q) (toDual q) k * toDual d k := by
  have h := congrArg (fun L : Chain m n →L[ℝ] ℝ => L d)
    (objective_hasFDerivAt_via_decoder hn q).fderiv
  rw [(objective_hasFDerivAt hn q).fderiv] at h
  change (∑ j, coordinateGradient hn q j * d j) =
    fderiv ℝ (Function.uncurry (Composite.objective hn))
      (toPrimal q, toDual q) (toPrimal d, toDual d) at h
  rw [(Regularity.gradient_represents_fderiv (m := m - 1) hn).2] at h
  exact h

theorem correction_coordinate_deriv_zero {m n : ℕ} (q : Chain m n)
    (j : Fin ((m - 1) * (n + 3))) (hq : q j = 0) :
    deriv (fun t => correction (serializedCoordinateLine q j t)) (q j) = 0 := by
  have ht (i : Fin (m - 1)) : HasDerivAt
      (fun t => Regularity.phaseCorrection (serializedState (serializedCoordinateLine q j t) i))
      (deriv Regularity.phaseCorrection (serializedState q i) *
        NCPLVerification.evecBasis j (serializedStateIndex i)) (q j) := by
    have hcoord := (hasDerivAt_pi.mp (coordinateLine_hasDerivAt q j))
      (serializedStateIndex (n := n) i)
    have hscalar := (Regularity.phaseCorrection_contDiff.differentiable (by simp)
      (serializedState q i)).hasDerivAt
    convert! hscalar.comp_of_eq (q j) hcoord (by simp [serializedState, serializedCoordinateLine]) using 1
  have hs := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => ht i)
  unfold correction
  rw [hs.deriv]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hij : serializedStateIndex (n := n) i = j
  · simp [serializedState, hij, hq, phaseCorrection_deriv_zero]
  · simp [NCPLVerification.evecBasis, hij]

/-- The phase change cannot expose a previously zero serialized coordinate. -/
theorem coordinateGradient_eq_old_at_zero {m n : ℕ} (hn : 0 < n) (q : Chain m n)
    (j : Fin ((m - 1) * (n + 3))) (hq : q j = 0) :
    coordinateGradient hn q j = Old.coordinateGradient hn Outer.c_R q j := by
  have holdf := (old_objective_differentiable (m := m) hn q).hasFDerivAt
  have hold := holdf.comp_hasDerivAt_of_eq (q j) (coordinateLine_hasDerivAt q j) (coordinateLine_self q j).symm
  have hcf := ((correction_contDiff (m := m) (n := n)).differentiable (by simp) q).hasFDerivAt
  have hc := hcf.comp_hasDerivAt_of_eq (q j) (coordinateLine_hasDerivAt q j) (coordinateLine_self q j).symm
  have heq : (fun t => objective hn (serializedCoordinateLine q j t)) =
      (fun t => Old.chainObjective hn Outer.c_R (serializedCoordinateLine q j t)) +
        (fun t => correction (serializedCoordinateLine q j t)) := by
    funext t
    exact objective_eq_old_add_correction hn _
  unfold coordinateGradient
  rw [heq]
  change deriv (Old.chainObjective hn Outer.c_R ∘ serializedCoordinateLine q j +
    correction ∘ serializedCoordinateLine q j) (q j) = _
  rw [deriv_add hold.differentiableAt hc.differentiableAt]
  have hz : deriv (correction ∘ serializedCoordinateLine q j) (q j) = 0 :=
    correction_coordinate_deriv_zero q j hq
  rw [hz, add_zero]
  rfl

/-- Only the actual dual coordinate derivatives receive the saddle sign. -/
def signedField {m n : ℕ} (hn : 0 < n) (q : Chain m n) : Chain m n :=
  (∑ i : Fin (m - 1), Pi.single (serializedAIndex (n := n) i)
    (coordinateGradient hn q (serializedAIndex (n := n) i))) +
  (∑ i : Fin (m - 1), ∑ k : Fin n, Pi.single (serializedDualIndex i k)
    (-coordinateGradient hn q (serializedDualIndex i k))) +
  (∑ i : Fin (m - 1), Pi.single (serializedBIndex (n := n) i)
    (coordinateGradient hn q (serializedBIndex (n := n) i))) +
  (∑ i : Fin (m - 1), Pi.single (serializedStateIndex (n := n) i)
    (coordinateGradient hn q (serializedStateIndex (n := n) i)))

theorem signedField_eq_old_at_zero {m n : ℕ} (hn : 0 < n) (q : Chain m n)
    (j : Fin ((m - 1) * (n + 3))) (hq : q j = 0) :
    signedField hn q j = Old.signedCoordinateField hn Outer.c_R q j := by
  have hs (k : Fin ((m - 1) * (n + 3))) :
      (Pi.single k (coordinateGradient hn q k) : Chain m n) j =
        (Pi.single k (Old.coordinateGradient hn Outer.c_R q k) : Chain m n) j := by
    by_cases hkj : k = j
    · subst k
      simp [coordinateGradient_eq_old_at_zero hn q j hq]
    · simp [hkj]
  have hsn (k : Fin ((m - 1) * (n + 3))) :
      (Pi.single k (-coordinateGradient hn q k) : Chain m n) j =
        (Pi.single k (-Old.coordinateGradient hn Outer.c_R q k) : Chain m n) j := by
    by_cases hkj : k = j
    · subst k
      simp [coordinateGradient_eq_old_at_zero hn q j hq]
    · simp [hkj]
  simp only [signedField, Old.signedCoordinateField, Pi.add_apply, Finset.sum_apply, hs, hsn]

theorem signedField_isFirstOrderZeroChain {m n : ℕ} (hn : 0 < n) :
    NCPLVerification.IsFirstOrderZeroChain (signedField (m := m) hn) := by
  intro r q hz j hj
  have hq : q j = 0 := hz j (by omega)
  rw [signedField_eq_old_at_zero hn q j hq]
  exact Old.signedCoordinateField_isFirstOrderZeroChain hn Outer.c_R r q hz j hj

theorem signedField_origin_supportedBelow_one {m n : ℕ} (hn : 0 < n) :
    NCPLVerification.SupportedBelow 1 (signedField (m := m) hn 0) :=
  signedField_isFirstOrderZeroChain hn 0 0 (NCPLVerification.supportedBelow_zero _ _)

end

end NCC.Construction.ZeroChain
