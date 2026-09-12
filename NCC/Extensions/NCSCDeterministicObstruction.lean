import NCC.Extensions.NCSCResisting
import NCC.Extensions.NCSCRotation

/-!
# No finite GS query cap from primal gap and condition number alone

For every finite horizon, an arbitrary causal first-order component has a
single fixed, corrected-rotated quadratic NC-SC instance on full spaces on
which none of the first queries is GS. The class parameters are always
`(ell, mu, Delta) = (98, 1, 1)`; the actual primal gap is zero. This statement
concerns queried points, not unqueried outputs, and makes no OS claim.
-/

namespace NCC.Extensions.NCSCDeterministicObstruction

noncomputable section

open NCCLowerBoundVerification
open NCPLVerification (IsOrthonormalFrame frameProject frameEmbed frameEmbed_zero)
open NCSCZeroChainObstruction NCSCResisting

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

/-- One fixed frame pair makes the terminal base-dual coordinate vanish at
every actual query before the prescribed horizon. -/
theorem exists_lifted_terminal_zero (K : ℕ) (c : ℝ)
    (A : Oracle.DeterministicFOComponent (Set.univ : Set (EVec (K + 3)))
      (Set.univ : Set (EVec (2 * K + 3)))) :
    ∃ U : Fin 1 → EVec (K + 3), ∃ V : Fin (K + 1) → EVec (2 * K + 3),
      IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      ∀ t < K, frameProject V
        (A.queriedAt (NCSCRotation.lifted 1 U V (family K c)) t).2 (Fin.last K) = 0 := by
  have general := @one_block_corrected_records (K + 1) (K + 3) (2 * K + 3) K
  rw [Nat.one_mul] at general
  obtain ⟨U, V, hU, hV, hr⟩ := general 1 (componentBlackBox A)
    (NCSC.auxiliary (family K c) 1).f (fun y => gradient K c y + y)
    (auxiliary_gradient_chain K c) (by omega) (by omega) (by omega)
  refine ⟨U, V, hU, hV, ?_⟩
  intro t ht
  let P := NCSCRotation.lifted 1 U V (family K c)
  have hmem := actualRecord_mem_run A P ht
  have hmem' : actualRecord A P t ∈ NCPLVerification.runHistory (componentBlackBox A)
      (fun x y => (NCSC.auxiliary (family K c) 1).f (frameProject U x) (frameProject V y) -
        quadraticCorrection 1 y)
      (fun _ _ => 0) (fun _ y => frameEmbed V
        (gradient K c (frameProject V y) + frameProject V y) - (1 : ℝ) • y) K := by
    simpa only [P, NCSCRotation.lifted, NCSC.auxiliary, family, one_smul, frameEmbed_zero] using hmem
  exact hr _ hmem' (Fin.last K) (by simp)

/-- The arbitrary deterministic queried-history obstruction. Ambient
dimensions are explicitly `K+3` and `2*K+3`, with full unbounded domains. -/
theorem fixed_conditioned_arbitrary_deterministic (K : ℕ) {eps : ℝ} (heps : 0 < eps)
    (A : Oracle.DeterministicFOComponent (Set.univ : Set (EVec (K + 3)))
      (Set.univ : Set (EVec (2 * K + 3)))) :
    ∃ P : NCCInstance (K + 3) (2 * K + 3),
      NCSC.NCSCClass 98 1 1 P ∧ P.X = Set.univ ∧ P.Y = Set.univ ∧
      ValueOn P.Y P.f 0 - sInf (Set.range (ValueOn P.Y P.f)) = 0 ∧
      ∀ t < K, ¬ IsGS P eps (A.queriedAt P t).1 (A.queriedAt P t).2 := by
  let c := (5 ^ (K + 1) + 1) * eps
  have hc : 5 ^ (K + 1) * eps < c := by dsimp [c]; nlinarith
  obtain ⟨U, V, hU, hV, ht⟩ := exists_lifted_terminal_zero K c A
  let P := NCSCRotation.lifted 1 U V (family K c)
  have hclass : NCSC.NCSCClass 98 1 1 P := by
    simpa only [NCSCRotation.smoothness, NCSC.internalSmoothness, show (2 : ℝ) * (8 * (5 + 1) + 1) = 98 by norm_num]
      using NCSCRotation.class_rotate (withinClass K c) rfl rfl hU hV
  refine ⟨P, hclass, rfl, rfl, ?_, ?_⟩
  · have hconst : ∀ x, ValueOn P.Y P.f x = ValueOn P.Y P.f 0 := by
      intro x
      have hf : P.f x = P.f 0 := by funext y; rfl
      exact congrArg sSup (congrArg (fun g : EVec (2 * K + 3) → ℝ => g '' P.Y) hf)
    have hsingle : Set.range (ValueOn P.Y P.f) = {ValueOn P.Y P.f 0} := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        exact hconst x
      · intro hv
        rw [Set.mem_singleton_iff] at hv
        exact ⟨0, hv.symm⟩
    rw [hsingle, csInf_singleton, sub_self]
  · intro t htk hgs
    have hbase := NCSCRotation.isGS_projects (P := family K c) rfl rfl hU hV hgs
    exact not_GS_of_terminal_zero heps.le hc _ _ (ht t htk) hbase

/-- A method chosen on all full-space dimensions before the horizon still
has no finite uniform GS query cap at the fixed parameters `(98,1,1)`. -/
theorem domainwise_no_finite_GS_cap
    (A : ∀ m n : ℕ, Oracle.DeterministicFOComponent
      (Set.univ : Set (EVec m)) (Set.univ : Set (EVec n)))
    {eps : ℝ} (heps : 0 < eps) :
    ∀ K : ℕ, ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ ∃ P : NCCInstance m n,
      NCSC.NCSCClass 98 1 1 P ∧ P.X = Set.univ ∧ P.Y = Set.univ ∧
      ValueOn P.Y P.f 0 - sInf (Set.range (ValueOn P.Y P.f)) = 0 ∧
      ∀ t < K, ¬ IsGS P eps ((A m n).queriedAt P t).1 ((A m n).queriedAt P t).2 := by
  intro K
  exact ⟨K + 3, 2 * K + 3, by omega, by omega,
    fixed_conditioned_arbitrary_deterministic K heps (A _ _)⟩

/-- The same statement with only the manuscript's positive dimensions in
the algorithm's domain-wise index; no degenerate component is required. -/
theorem positive_domainwise_no_finite_GS_cap
    (A : ∀ m n : ℕ, 0 < m → 0 < n → Oracle.DeterministicFOComponent
      (Set.univ : Set (EVec m)) (Set.univ : Set (EVec n)))
    {eps : ℝ} (heps : 0 < eps) :
    ∀ K : ℕ, ∃ m n : ℕ, ∃ hm : 0 < m, ∃ hn : 0 < n, ∃ P : NCCInstance m n,
      NCSC.NCSCClass 98 1 1 P ∧ P.X = Set.univ ∧ P.Y = Set.univ ∧
      ValueOn P.Y P.f 0 - sInf (Set.range (ValueOn P.Y P.f)) = 0 ∧
      ∀ t < K, ¬ IsGS P eps ((A m n hm hn).queriedAt P t).1
        ((A m n hm hn).queriedAt P t).2 := by
  intro K
  exact ⟨K + 3, 2 * K + 3, by omega, by omega,
    fixed_conditioned_arbitrary_deterministic K heps (A _ _ (by omega) (by omega))⟩

end

end NCC.Extensions.NCSCDeterministicObstruction
