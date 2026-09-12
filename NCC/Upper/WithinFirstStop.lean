import NCC.Upper.WithinSystem
import NCC.Upper.CurrentProgram

/-!
# First-success oracle and micro-program correctness on the feasible class

The projections, support inequalities, and universal stopping certificate
come directly from `WithinClass`. No ambient derivative or stronger-class
coercion is introduced. The objective-independent micro program is reused
unchanged; only its source-class correspondence proof is supplied here.
-/

namespace NCC.Upper.WithinFirstStop
noncomputable section
open NCC.Model NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open RelativeFOAM RelativeFOAMContraction ScaledOperator ProjectionGeometry
open OuterTrajectoryConcrete HomotopyRun
open WithinSystem AnalyticBridge SharedOracle AdaptiveMicroProgram
set_option maxHeartbeats 2000000
variable {m n : Nat} {ell r : ℝ}

theorem exists_microStops {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) :
    ∃ s, microStops P ell r (chosenProjectX hP) (chosenProjectY hP) z S s := by
  refine ⟨ProjectedMicro.feasibleMicroIterations,
    ProjectedMicro.feasibleMicroIterations_positive, ?_⟩
  exact classOracle_residual hP hr hrle
    (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S

/-- The first successful residual test on the actual projected recurrence. -/
def firstStopIndex {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) : Nat := by
  classical
  exact Nat.find (exists_microStops hP hr hrle z S)

theorem firstStopIndex_spec {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) :
    microStops P ell r (chosenProjectX hP) (chosenProjectY hP) z S
      (firstStopIndex hP hr hrle z S) := by
  classical
  exact Nat.find_spec (exists_microStops hP hr hrle z S)

theorem firstStopIndex_minimal {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) (s : Nat)
    (hs : s < firstStopIndex hP hr hrle z S) :
    ¬ microStops P ell r (chosenProjectX hP) (chosenProjectY hP) z S s := by
  classical
  exact Nat.find_min (exists_microStops hP hr hrle z S) hs

/-- The exact first-stop loop never exceeds the universal cutoff. -/
theorem firstStopIndex_le_universal {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) :
    firstStopIndex hP hr hrle z S ≤ ProjectedMicro.feasibleMicroIterations := by
  classical
  unfold firstStopIndex
  apply Nat.find_min'
  exact ⟨ProjectedMicro.feasibleMicroIterations_positive,
    classOracle_residual hP hr hrle
      (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S⟩

def firstStopOracle {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) : MicroOutput m n :=
  microOutputAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S
    (firstStopIndex hP hr hrle z S)

theorem firstStopOracle_certificate {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) :
    (firstStopOracle hP hr hrle z S).xFast ∈ P.X ∧
      (firstStopOracle hP hr hrle z S).yFastNext ∈ P.Y ∧
      MicroNormalRelations P.X P.Y
        (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z)
        (firstStopOracle hP hr hrle z S) ∧
      RelativeResidual ell r S (firstStopOracle hP hr hrle z S) := by
  let project := scaledProject ell (chosenProjectX hP) (chosenProjectY hP)
  let A := scaledOperator ell r (qCenter ell r S) (yCenter ell r S)
    (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z)
  let center := scaledCenter ell (qCenter ell r S) (yCenter ell r S)
  let s := firstStopIndex hP hr hrle z S
  have hp : ProjectionGeometry.IsEuclideanProjection
      (scaledSet ell P.X P.Y) project :=
    scaledProject_isProjection hP.ell_pos (chosenProjectX_spec hP)
      (chosenProjectY_spec hP)
  have hs := (firstStopIndex_spec hP hr hrle z S).1
  have hu := projectedIterate_mem project A (M0 ^ 2)⁻¹ center hp.mem s
  have hb := projectedB_normal project A
    (show 0 < (M0 ^ 2)⁻¹ by norm_num [M0]) center hp.normal (s - 1)
  have hsEq : s - 1 + 1 = s := Nat.sub_add_cancel hs
  rw [hsEq] at hb
  have hn := decodeOutput_normalRelations hP.ell_pos
    (ClassOperator.gradXHat P ell z) (ClassOperator.gradYHat P ell z) hu hb
  exact ⟨hu.1, hu.2, hn, (firstStopIndex_spec hP hr hrle z S).2⟩

/-- The class-derived analytic system with precisely the appendix's micro loop. -/
def firstStopSystemWithProx {ell D Delta r : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 < r) (hrle : r ≤ ell / 8)
    (hprox : HasProxEverywhere P.X (DualRegularizedValueOn P.Y P.f r) ell) :
    OuterSystem P.X P.Y P.f ell r hprox := by
  let oracle := fun (z : EVec m) (S : ValidState (m := m) P.Y) =>
    firstStopOracle hP hr.le hrle z S.1
  have hfeasible : ∀ z S, (oracle z S).yFastNext ∈ P.Y :=
    fun z S => (firstStopOracle_certificate hP hr.le hrle z S.1).2.1
  refine { outerSystemOfClassWithProx hP hr hrle hprox with
    oracle := oracle
    oracle_feasible := hfeasible
    oracle_subgradient := ?_
    oracle_residual := ?_ }
  · intro z S
    have hc := firstStopOracle_certificate hP hr.le hrle z S.1
    exact PointwiseConjugate.gamma_subgradient (gammaBddAbove_of_class hP z)
      hc.1 (WithinOperator.convexSupportX (r := r) hP z hc.1 hc.2.1)
      (WithinOperator.concaveSupportY (r := r) hP z hc.1 hc.2.1)
      hc.2.2.1.1 hc.2.2.1.2
  · intro z S
    exact (firstStopOracle_certificate hP hr.le hrle z S.1).2.2.2


theorem advance_at_iterate {D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (z : EVec m) (S : State m n)
    (s : Nat) (u : ScaledFeasible ell P.X P.Y)
    (hu : u.1 = microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S s) :
    (microAdvance (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
      (chosenProjectX_spec hP) (chosenProjectY_spec hP)
      z (qCenter ell r S) (yCenter ell r S) u
      (Oracle.firstOrderOracle P (scaledQuery u))).1 =
      microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S (s + 1) := by
  rw [microAdvance_firstOrderOracle, hu]
  rfl

theorem decoded_at_iterate {D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (z : EVec m) (S : State m n)
    (s : Nat) (u v : ScaledFeasible ell P.X P.Y)
    (hu : u.1 = microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S s)
    (hv : v.1 = microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S (s + 1)) :
    (decoded (r := r) z S u v
      (Oracle.firstOrderOracle P (scaledQuery u))
      (Oracle.firstOrderOracle P (scaledQuery v))).1 =
      microOutputAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S (s + 1) := by
  have hop := replyOperator_firstOrderOracle P ell r z
    (qCenter ell r S) (yCenter ell r S) u.1
  unfold decoded outputFromReplies microOutputAt decodeOutput
  dsimp only
  simp only [scaledQuery]
  rw [hop, hu, hv]
  congr 1 <;>
    simp [ClassOperator.gradXHat, ClassOperator.gradYHat, microUAt, microBAt,
      projectedB, M0]

/-- Starting after the reply at iterate `s`, with enough remaining fuel,
the genuine-reply loop reaches exactly the first successful index. -/
theorem eval_loop_before_stop {D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) (fuel s : Nat)
    (u : ScaledFeasible ell P.X P.Y)
    (hu : u.1 = microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S s)
    (hbefore : s < firstStopIndex hP hr hrle z S)
    (hcap : firstStopIndex hP hr hrle z S ≤ s + fuel + 1) :
    (Oracle.Program.eval P
      (loop (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S fuel u
        (Oracle.firstOrderOracle P (scaledQuery u)))).1 =
        firstStopOracle hP hr hrle z S ∧
      (queryTrace P
        (loop (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
          (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S fuel u
          (Oracle.firstOrderOracle P (scaledQuery u)))).length =
        firstStopIndex hP hr hrle z S - s := by
  classical
  induction fuel generalizing s u with
  | zero =>
      let a := Oracle.firstOrderOracle P (scaledQuery u)
      let v := microAdvance (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP)
        z (qCenter ell r S) (yCenter ell r S) u a
      have hv : v.1 = microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S
          (s + 1) := advance_at_iterate hP z S s u hu
      have hO := decoded_at_iterate hP z S s u v hu hv
      have hindex : firstStopIndex hP hr hrle z S = s + 1 := by omega
      constructor
      · change (decoded (r := r) z S u v a
          (Oracle.firstOrderOracle P (scaledQuery v))).1 = _
        rw [hO, ← hindex]
        rfl
      · change 1 = firstStopIndex hP hr hrle z S - s
        omega
  | succ fuel ih =>
      let a := Oracle.firstOrderOracle P (scaledQuery u)
      let v := microAdvance (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP)
        z (qCenter ell r S) (yCenter ell r S) u a
      let b := Oracle.firstOrderOracle P (scaledQuery v)
      let O := decoded (r := r) z S u v a b
      have hv : v.1 = microUAt P ell r (chosenProjectX hP) (chosenProjectY hP) z S
          (s + 1) := advance_at_iterate hP z S s u hu
      have hO : O.1 = microOutputAt P ell r (chosenProjectX hP) (chosenProjectY hP)
          z S (s + 1) := decoded_at_iterate hP z S s u v hu hv
      change (Oracle.Program.eval P
          (if RelativeResidual ell r S O.1 then Oracle.Program.pure O
            else loop (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
              (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S fuel v b)).1 = _ ∧
        (queryTrace P
          (if RelativeResidual ell r S O.1 then Oracle.Program.pure O
            else loop (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
              (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S fuel v b)).length + 1 = _
      by_cases hindex : firstStopIndex hP hr hrle z S = s + 1
      · have htest : RelativeResidual ell r S O.1 := by
          rw [hO, ← hindex]
          exact (firstStopIndex_spec hP hr hrle z S).2
        rw [if_pos htest]
        constructor
        · rw [Oracle.Program.eval_pure, hO, ← hindex]
          rfl
        · change 0 + 1 = firstStopIndex hP hr hrle z S - s
          omega
      · have hbefore' : s + 1 < firstStopIndex hP hr hrle z S := by omega
        have htest : ¬ RelativeResidual ell r S O.1 := by
          intro h
          apply firstStopIndex_minimal hP hr hrle z S (s + 1) hbefore'
          refine ⟨by omega, ?_⟩
          rwa [← hO]
        rw [if_neg htest]
        have hrec := ih (s + 1) v hv hbefore' (by omega)
        constructor
        · exact hrec.1
        · rw [hrec.2]
          omega

/-- Value and exact genuine query count for the adaptive micro client.
No instance is supplied to `program`; `P` occurs only in the evaluator. -/
theorem program_correct {D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (hr : 0 ≤ r) (hrle : r ≤ ell / 8)
    (z : EVec m) (S : State m n) :
    (Oracle.Program.eval P
      (program (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S)).1 =
        firstStopOracle hP hr hrle z S ∧
      (queryTrace P
        (program (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
          (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S)).length =
        firstStopIndex hP hr hrle z S + 1 := by
  let u := microInitial (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
    (chosenProjectX_spec hP) (chosenProjectY_spec hP) S
  have hpos := (firstStopIndex_spec hP hr hrle z S).1
  have hbound := firstStopIndex_le_universal hP hr hrle z S
  have hN := ProjectedMicro.feasibleMicroIterations_positive
  have hloop := eval_loop_before_stop hP hr hrle z S
    (ProjectedMicro.feasibleMicroIterations - 1) 0 u rfl (by omega) (by omega)
  constructor
  · exact hloop.1
  · change (queryTrace P
      (loop (r := r) hP.ell_pos (chosenProjectX hP) (chosenProjectY hP)
        (chosenProjectX_spec hP) (chosenProjectY_spec hP) z S
        (ProjectedMicro.feasibleMicroIterations - 1) u
        (Oracle.firstOrderOracle P (scaledQuery u)))).length + 1 = _
    rw [hloop.2]
    simp


theorem level_pos {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (j : Nat) :
    0 < Tracking.curvature (ell / 8) j :=
  HomotopyCost.curvature_pos (div_pos hP.ell_pos (by norm_num)) j

theorem level_le {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) (j : Nat) :
    Tracking.curvature (ell / 8) j ≤ ell / 8 := by
  unfold Tracking.curvature
  exact Tracking.div_pow_le_self (div_nonneg hP.ell_pos.le (by norm_num)) (by norm_num) j

theorem proxFamily {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) : ProxFamily P.X P.Y P.f ell (ell / 8) :=
  fun j => WithinRegularization.prox_exists hP (level_pos hP j).le

def firstStopSystemFamily {ell D Delta : ℝ} {P : NCCInstance m n}
    (hP : WithinClass ell D Delta P) :
    SystemFamily P.X P.Y P.f ell (ell / 8) (proxFamily hP) :=
  fun j => firstStopSystemWithProx hP (level_pos hP j) (level_le hP j) (proxFamily hP j)

end
end NCC.Upper.WithinFirstStop
