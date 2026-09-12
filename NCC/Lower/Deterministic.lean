import NCC.Lower.Rotation
import NCCLowerBoundVerification.Lower.MainTheorem
import NCCLowerBoundVerification.Oracle.Complexity

/-!
# The fixed-instance deterministic resisting lift

These theorems use the supplied instance's literal function and both actual
gradient fields. Their hypotheses include its analytic class membership,
exact domains, initialization, tagged zero-chain, and terminal obstruction.
No old hard objective or old numerical complexity theorem is instantiated.

The typed causal component may use every preceding value/gradient reply and
must issue feasible queries for every history. It need not be zero-respecting.
As in the current manuscript, no separate measurability condition is imposed.
The hitting index starts at zero, exactly as in the current manuscript.

This is the sufficient fixed-zero-chain lift, not the manuscript's stronger
`∀ A, ∃ Z, ∀ f` resisting lemma. The explicit capacities below use ambient
dimension at least base dimension plus `K+2`; see `RESISTING_MODEL_GAP.md`.
-/

namespace NCC.Lower.Deterministic

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Oracle
open NCPLVerification (IsFirstOrderZeroChain IsOrthonormalFrame frameProject)

/-- Actual feasible queried transcript under one pair of completed frames. -/
theorem feasible_rotated_terminal_transcript
    {T n DX DY K : ℕ} (D : ℝ)
    (A : DeterministicFOComponent (Set.univ : Set (EVec DX)) (diameterBall DY D))
    (P : NCCInstance (3 * (T - 1)) (n * (T - 1)))
    (hchain : IsFirstOrderZeroChain (taggedSerializedSaddleFieldOf P.gradX P.gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY) :
    ∃ U V, IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      ∀ t < K,
        let q := A.queriedAt (rotatedNCCInstance D U V P) t
        (q.1 ∈ Set.univ ∧ q.2 ∈ diameterBall DY D) ∧
        serializeUnscaled (frameProject U q.1) (frameProject V q.2)
          (⟨(T - 1) * (n + 3) - 1, by omega⟩ : Fin ((T - 1) * (n + 3))) = 0 := by
  obtain ⟨U, V, hU, hV, ht⟩ := finite_horizon_tagged_queried_terminal_orthonormal
    A P.f P.gradX P.gradY hchain hKM hcapX hcapY
  refine ⟨U, V, hU, hV, ?_⟩
  intro t hit
  refine ⟨A.queriedAt_mem (rotatedNCCInstance D U V P) t, ?_⟩
  exact ht t hit

theorem hittingTime_ge_of_failsWithin {m n K : ℕ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (A : DeterministicFOComponent X Y) (P : NCCInstance m n) (ell eps : ℝ)
    (hfail : A.FailsWithin P ell eps K) :
    (K : WithTop ℕ) ≤ queriedHittingTime A P ell eps := by
  apply le_of_not_gt
  intro hlt
  have hhit := (queriedHittingTime_lt_iff A P ell eps K).1 hlt
  exact (DeterministicFOComponent.failsWithin_iff_not_hitsWithin A P ell eps K).1 hfail hhit

/-- A hard actual class member for every deterministic feasible component.
The terminal and zero-chain premises refer to the supplied current instance. -/
theorem exists_hard_instance_of_terminal
    {T n DX DY K : ℕ} (hT : 2 ≤ T) {ell D Delta eps : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec DX)) (diameterBall DY D))
    (P : NCCInstance (3 * (T - 1)) (n * (T - 1)))
    (hclass : IsNCCClass ell D Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall (n * (T - 1)) D)
    (hinit : P.x0 = 0)
    (hchain : IsFirstOrderZeroChain (taggedSerializedSaddleFieldOf P.gradX P.gradY))
    (hKM : K < (T - 1) * (n + 3))
    (hcapX : 3 * (T - 1) + (K + 1) < DX)
    (hcapY : n * (T - 1) + (K + 1) < DY)
    (hfailure : ∀ x : UnscaledPrimal T,
      x (terminalPrimalIndex hT) = 0 →
        ¬ IsOptimizationStationary Set.univ
          (ValueOn (diameterBall (n * (T - 1)) D) P.f) ell eps x) :
    ∃ Q : NCCInstance DX DY, ∃ hQ : Model.WithinClass ell D Delta Q,
      IsNCCClass ell D Delta Q ∧ Q.X = Set.univ ∧ Q.Y = diameterBall DY D ∧ Q.x0 = 0 ∧
      A.FailsWithin Q ell eps K ∧ (K : WithTop ℕ) ≤ queriedHittingTime A Q ell eps ∧
      ∀ t < K, ¬ Moreau.Within.IsOS hQ eps (A.queriedAt Q t).1 := by
  obtain ⟨Q, hQA, hfail, hQX, hQY, hQinit⟩ :=
    exists_rotated_hard_instance_of_terminal hT A P hclass hX hY hinit hchain
      hKM hcapX hcapY hfailure
  have hQ : Model.WithinClass ell D Delta Q :=
    Rotation.withinClass_of_analytic hQA hQinit
      (by rw [hQY]; exact zero_mem_diameterBall DY D hQA.D_pos.le)
  refine ⟨Q, hQ, hQA, hQX, hQY, hQinit, hfail,
    hittingTime_ge_of_failsWithin A Q ell eps hfail, ?_⟩
  intro t ht hos
  exact hfail t ht ((Moreau.Within.isOS_iff_feasible_prox hQ eps _).1 hos).2.2

/-- At a positive horizon, query a deterministic feasible final output paired
with the dual origin. Earlier queries are unchanged. -/
def appendOutput {m n K : ℕ} {X : Set (EVec m)} {Y : Set (EVec n)}
    (A : DeterministicFOComponent X Y) (hK : 0 < K)
    (out : ReplyHistory m n K → EVec m) (hout : ∀ hist, out hist ∈ X)
    (hy0 : (0 : EVec n) ∈ Y) : DeterministicFOComponent X Y where
  nextQuery t hist := if ht : t = K then
    (out (fun i => hist (Fin.cast ht.symm i)), 0) else A.nextQuery t hist
  next_mem := by
    intro t hist
    split
    · exact ⟨hout _, hy0⟩
    · exact A.next_mem t hist
  initial_query := by
    rw [dif_neg (ne_of_lt hK)]
    exact A.initial_query

theorem appendOutput_queriedAt_lt {m n K : ℕ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (A : DeterministicFOComponent X Y) (hK : 0 < K)
    (out : ReplyHistory m n K → EVec m) (hout : ∀ hist, out hist ∈ X)
    (hy0 : (0 : EVec n) ∈ Y) (P : NCCInstance m n) {t : ℕ} (ht : t < K) :
    (appendOutput A hK out hout hy0).queriedAt P t = A.queriedAt P t := by
  revert ht
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro ht
    rw [DeterministicFOComponent.queriedAt_eq_nextQuery,
      DeterministicFOComponent.queriedAt_eq_nextQuery A]
    dsimp only [appendOutput]
    rw [dif_neg (ne_of_lt ht)]
    congr 1
    funext i
    change firstOrderOracle P ((appendOutput A hK out hout hy0).queriedAt P i) =
      firstOrderOracle P (A.queriedAt P i)
    rw [ih i.val i.isLt (i.isLt.trans ht)]

theorem appendOutput_queriedAt_horizon {m n K : ℕ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (A : DeterministicFOComponent X Y) (hK : 0 < K)
    (out : ReplyHistory m n K → EVec m) (hout : ∀ hist, out hist ∈ X)
    (hy0 : (0 : EVec n) ∈ Y) (P : NCCInstance m n) :
    (appendOutput A hK out hout hy0).queriedAt P K =
      (out (A.queriedTranscript P K), 0) := by
  have hh : (appendOutput A hK out hout hy0).queriedTranscript P K =
      A.queriedTranscript P K := by
    funext i
    change firstOrderOracle P ((appendOutput A hK out hout hy0).queriedAt P i) =
      firstOrderOracle P (A.queriedAt P i)
    rw [appendOutput_queriedAt_lt A hK out hout hy0 P i.isLt]
  rw [DeterministicFOComponent.queriedAt_eq_nextQuery, hh]
  simp [appendOutput]

/-- Formal positive-horizon version of `rem:arbitrary-output`: one extra
query reduces any feasible deterministic transcript output to queried OS. -/
theorem arbitrary_output_failure {m n K : ℕ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (A : DeterministicFOComponent X Y) (hK : 0 < K)
    (out : ReplyHistory m n K → EVec m) (hout : ∀ hist, out hist ∈ X)
    (hy0 : (0 : EVec n) ∈ Y) (P : NCCInstance m n) (ell eps : ℝ)
    (hfail : (appendOutput A hK out hout hy0).FailsWithin P ell eps (K + 1)) :
    ¬ IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
      (out (A.queriedTranscript P K)) := by
  have h := hfail K (Nat.lt_succ_self K)
  change ¬ IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps
    ((appendOutput A hK out hout hy0).queriedAt P K).1 at h
  rw [appendOutput_queriedAt_horizon A hK out hout hy0 P] at h
  exact h

end

end NCC.Lower.Deterministic
