import NCCLowerBoundVerification.Upper.DualTranslation
import NCCLowerBoundVerification.Upper.SystemInstantiation
import NCCLowerBoundVerification.Upper.UniformCost

/-!
# Class-level uniform upper theorem

This module closes the last abstract interface in the uniform upper bound.
At every curvature in the homotopy schedule, the proximal witness and the
entire concrete outer system are constructed from `IsNCCClass`.  Translation
of an arbitrary feasible dual point to the origin removes the normalization
used by the startup proof without changing the primal value function.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace MainTheorem

noncomputable section

open OuterTrajectoryConcrete
open HomotopyRun HomotopySchedule UniformSchedule

set_option maxHeartbeats 3000000

set_option linter.defProp false in
/-- The genuine proximal family at every curvature of the paper's homotopy
schedule. -/
def classProxFamily {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P) :
    ProxFamily P.X P.Y P.f ell (ell / 8) :=
  fun j => SystemInstantiation.regularizedValue_hasProxEverywhere_of_class hP
    (HomotopyCost.curvature_pos (div_pos hP.ell_pos (by norm_num)) j).le

/-- Every curvature layer is backed by the concrete projection, saddle, and
finite micro-oracle constructed in `SystemInstantiation`. -/
def classSystemFamily {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P) :
    SystemFamily P.X P.Y P.f ell (ell / 8) (classProxFamily hP) :=
  fun j => SystemInstantiation.outerSystemOfClassWithProx hP
    (HomotopyCost.curvature_pos (div_pos hP.ell_pos (by norm_num)) j)
    (by
      unfold Tracking.curvature
      exact Tracking.div_pow_le_self (div_nonneg hP.ell_pos.le (by norm_num))
        (by norm_num) j)
    (classProxFamily hP j)

/-- The fully instantiated uniform theorem under the temporary startup
normalization `0 ∈ Y`.  No proximal family or bottom-level system is an
assumption of this theorem. -/
theorem exists_OS_of_class_zero {m n : Nat}
    {ell D Delta eps : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (hzero : (0 : EVec n) ∈ P.Y)
    (heps : 0 < eps) :
    let prox := classProxFamily hP
    let systems := classSystemFamily hP
    let target := targetCurvature ell D eps
    let J := homotopyStage (ell / 8) target
      (div_pos hP.ell_pos (by norm_num))
      (targetCurvature_pos hP.ell_pos hP.D_pos heps)
    let r := Tracking.curvature (ell / 8) J
    let S0 := HomotopyRun.startupState (systems 0) hzero
    let B0 := 8 * (Delta + (ell / 8) * D ^ 2)
    let R0 := HomotopyRun.homotopySnapshot (D := D) (B0 := B0)
      systems P.x0 S0 J
    let T := paperOuterIterations ell Delta r D eps
    ∃ t < T, IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (trajectory (systems J) R0 t).z := by
  exact UniformTheorem.exists_OS_with_system_family hP hzero heps
    (classSystemFamily hP)

/-- The literal oracle and projection counts of the same schedule obey the
uniform complexity rate, with the explicit numerical constant proved in
`UniformCost`. -/
theorem class_uniform_cost_bound {m n : Nat}
    {ell D Delta eps : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (heps : 0 < eps) :
    let target := targetCurvature ell D eps
    let J := homotopyStage (ell / 8) target
      (div_pos hP.ell_pos (by norm_num))
      (targetCurvature_pos hP.ell_pos hP.D_pos heps)
    let r := Tracking.curvature (ell / 8) J
    let T := paperOuterIterations ell Delta r D eps
    let rate := (ell * Delta / eps ^ 2 + 1) *
      max 1 (ell * D / eps)
    ((UniformCost.assembledCost ell (ell / 8) r J T).oracleCalls : ℝ) ≤
        UniformCost.uniformCostConstant * rate ∧
      ((UniformCost.assembledCost ell (ell / 8) r J T).projections : ℝ) ≤
        UniformCost.uniformCostConstant * rate := by
  exact UniformCost.assembledCost_uniform_bound
    hP.ell_pos hP.D_pos hP.Delta_pos heps rfl rfl rfl rfl

/-- Optimization stationarity depends only on the values of the objective on
the feasible primal set. -/
theorem optimizationStationary_congr_on {m : Nat}
    {X : Set (EVec m)} {phi psi : EVec m → ℝ} {ell eps : ℝ}
    {x : EVec m} (hEq : ∀ u ∈ X, phi u = psi u)
    (h : IsOptimizationStationary X phi ell eps x) :
    IsOptimizationStationary X psi ell eps x := by
  obtain ⟨u, hu, hdist⟩ := h
  refine ⟨u, ⟨hu.1, ?_⟩, hdist⟩
  intro v hv
  rw [← hEq u hu.1, ← hEq v hv]
  exact hu.2 v hv

/-- Run the completely instantiated algorithm after translating any chosen
feasible dual point to zero, then transfer its stationarity certificate back
to the original (identical on `X`) value function. -/
theorem exists_OS_of_class_at_dual_basepoint {m n : Nat}
    {ell D Delta eps : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) {ybar : EVec n} (hybar : ybar ∈ P.Y)
    (heps : 0 < eps) :
    let Pbar := DualTranslation.translatedInstance P ybar
    let hPbar := DualTranslation.IsNCCClass.translateDual hP hybar
    let prox := classProxFamily hPbar
    let systems := classSystemFamily hPbar
    let target := targetCurvature ell D eps
    let J := homotopyStage (ell / 8) target
      (div_pos hP.ell_pos (by norm_num))
      (targetCurvature_pos hP.ell_pos hP.D_pos heps)
    let r := Tracking.curvature (ell / 8) J
    let S0 := HomotopyRun.startupState (systems 0)
      (DualTranslation.zero_mem_translatedDualSet hybar)
    let B0 := 8 * (Delta + (ell / 8) * D ^ 2)
    let R0 := HomotopyRun.homotopySnapshot (D := D) (B0 := B0)
      systems Pbar.x0 S0 J
    let T := paperOuterIterations ell Delta r D eps
    ∃ t < T, IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (trajectory (systems J) R0 t).z := by
  dsimp only
  obtain ⟨t, ht, hstationary⟩ := exists_OS_of_class_zero
    (DualTranslation.IsNCCClass.translateDual hP hybar)
    (DualTranslation.zero_mem_translatedDualSet hybar) heps
  refine ⟨t, ht, ?_⟩
  apply optimizationStationary_congr_on (X := P.X) ?_ hstationary
  intro u hu
  exact DualTranslation.translatedValue_eq (hP.maximum_attained u hu)

/-- A canonical feasible point used only to state the normalization-free
corollary without requiring a dual basepoint from the caller. -/
def classDualBasepoint {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P) : EVec n :=
  Classical.choose hP.Y_nonempty

theorem classDualBasepoint_mem {m n : Nat} {ell D Delta : ℝ}
    {P : NCCInstance m n} (hP : IsNCCClass ell D Delta P) :
    classDualBasepoint hP ∈ P.Y :=
  Classical.choose_spec hP.Y_nonempty

/-- Normalization-free class-level existence of an optimization-stationary
point.  The witness is produced by the finite translated trajectory above;
`Y.Nonempty` is already a field of `IsNCCClass`. -/
theorem exists_OS_of_class {m n : Nat}
    {ell D Delta eps : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (heps : 0 < eps) :
    ∃ x, IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps x := by
  let ybar := classDualBasepoint hP
  have hybar : ybar ∈ P.Y := classDualBasepoint_mem hP
  have hrun := exists_OS_of_class_at_dual_basepoint hP hybar heps
  dsimp only at hrun
  obtain ⟨t, _ht, hstationary⟩ := hrun
  exact ⟨_, hstationary⟩

/-- Final uniform upper bound: a genuine stationary output exists for every
class instance (without an origin normalization), and the literal finite
schedule uses no more than the stated oracle and projection budget. -/
theorem uniform_upper_bound_of_class {m n : Nat}
    {ell D Delta eps : ℝ} {P : NCCInstance m n}
    (hP : IsNCCClass ell D Delta P) (heps : 0 < eps) :
    (∃ x, IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps x) ∧
    (let target := targetCurvature ell D eps
     let J := homotopyStage (ell / 8) target
       (div_pos hP.ell_pos (by norm_num))
       (targetCurvature_pos hP.ell_pos hP.D_pos heps)
     let r := Tracking.curvature (ell / 8) J
     let T := paperOuterIterations ell Delta r D eps
     let rate := (ell * Delta / eps ^ 2 + 1) *
       max 1 (ell * D / eps)
     ((UniformCost.assembledCost ell (ell / 8) r J T).oracleCalls : ℝ) ≤
         UniformCost.uniformCostConstant * rate ∧
       ((UniformCost.assembledCost ell (ell / 8) r J T).projections : ℝ) ≤
         UniformCost.uniformCostConstant * rate) := by
  exact ⟨exists_OS_of_class hP heps, class_uniform_cost_bound hP heps⟩

end

end MainTheorem
end Upper
end NCCLowerBoundVerification
