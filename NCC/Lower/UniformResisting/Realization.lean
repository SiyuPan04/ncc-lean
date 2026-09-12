import NCC.Lower.UniformResisting.Simulator

/-!
# One completed pair of frames realizes the entire uniform simulation

The simulator is fixed before the oracle instance is supplied. Completion
depends on the resulting finite transcript, and uses exactly `m+K,n+K`.
The proof identifies the actual causal oracle runs, including their values
and both gradient fields; it does not postulate transcript consistency.
-/

namespace NCC.Lower.UniformResisting

noncomputable section

set_option backward.isDefEq.respectTransparency false

open NCCLowerBoundVerification Oracle
open NCPLVerification (IsOrthonormalFrame frameProject frameEmbed)

theorem exists_completed_replay {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (hist : ReplyHistory m n K) :
    ∃ (U : Fin m → EVec (m + K)) (V : Fin n → EVec (n + K)),
      IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      (∀ i, (frameProject U ((replay A K le_rfl hist).virtual i).1,
        frameProject V ((replay A K le_rfl hist).virtual i).2) = (replay A K le_rfl hist).base i) ∧
      ∀ i, (replay A K le_rfl hist).replies i =
        ⟨(hist i).value, frameEmbed U (hist i).gradX, frameEmbed V (hist i).gradY⟩ := by
  let s := replay A K le_rfl hist
  obtain ⟨U, hU, hkeepU, hprojU⟩ := exists_completion_sharp s.U
    (List.ofFn (fun i => (s.virtual i).1)) s.partialU (by simp)
  obtain ⟨V, hV, hkeepV, hprojV⟩ := exists_completion_sharp s.V
    (List.ofFn (fun i => (s.virtual i).2)) s.partialV (by simp)
  refine ⟨U, V, hU, hV, ?_, ?_⟩
  · intro i
    calc
      _ = projectedQuery s (s.virtual i) := Prod.ext
        (hprojU _ (List.mem_ofFn.mpr ⟨i, rfl⟩)) (hprojV _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
      _ = _ := replay_projects A K le_rfl hist i
  · intro i
    have hseen := replay_seen_nonzero A K le_rfl hist i
    have heU := frameEmbed_eq_of_support s.U U (hist i).gradX (fun j hj => hkeepU j (hseen.1 j hj))
    have heV := frameEmbed_eq_of_support s.V V (hist i).gradY (fun j hj => hkeepV j (hseen.2 j hj))
    rw [heU, heV]
    exact replay_represents_replies A K le_rfl hist i

@[simp] theorem historyPrefix_actual {m n r t : ℕ} {X : Set (EVec m)} {Y : Set (EVec n)}
    (A : DeterministicFOComponent X Y) (P : NCCInstance m n) (hrt : r ≤ t) :
    historyPrefix hrt (A.queriedTranscript P t) = A.queriedTranscript P r := rfl

theorem replay_base_actual {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (P : NCCInstance m n) (t : ℕ) (ht : t ≤ K) (i : Fin t) :
    (replay A t ht ((simulator A).queriedTranscript P t)).base i =
      (simulator A).queriedAt P i := by
  rw [replay_base_causal, historyPrefix_actual]
  exact (DeterministicFOComponent.queriedAt_eq_nextQuery (simulator A) P i).symm

/-- The literal uniform-in-objective projected transcript, at fixed known
domains. No zero-chain, smoothness, or hard-instance premise is required for
this algebraic local-oracle realization theorem. -/
theorem uniform_component_realization {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (P : NCCInstance m n) :
    ∃ (U : Fin m → EVec (m + K)) (V : Fin n → EVec (n + K)),
      IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      ∀ t < K, (simulator A).queriedAt P t =
        (frameProject U (A.queriedAt (rotatedNCCInstance D U V P) t).1,
         frameProject V (A.queriedAt (rotatedNCCInstance D U V P) t).2) := by
  let hist := (simulator A).queriedTranscript P K
  let s := replay A K le_rfl hist
  obtain ⟨U, V, hU, hV, hproj, hreply⟩ := exists_completed_replay A hist
  have hbase (i : Fin K) : s.base i = (simulator A).queriedAt P i :=
    replay_base_actual A P K le_rfl i
  have horacle (i : Fin K) : firstOrderOracle (rotatedNCCInstance D U V P) (s.virtual i) =
      s.replies i := by
    rw [hreply]
    have hh : hist i = firstOrderOracle P (s.base i) := by rw [hbase]; rfl
    rw [hh]
    have hpX := congrArg Prod.fst (hproj i)
    have hpY := congrArg Prod.snd (hproj i)
    change frameProject U (s.virtual i).1 = (s.base i).1 at hpX
    change frameProject V (s.virtual i).2 = (s.base i).2 at hpY
    simp only [firstOrderOracle, rotatedNCCInstance, NCPLVerification.rotatedF,
      NCPLVerification.rotatedGradX, NCPLVerification.rotatedGradY]
    rw [hpX, hpY]
  have hvirtual : ∀ (t : ℕ) (ht : t < K),
      A.queriedAt (rotatedNCCInstance D U V P) t = s.virtual ⟨t, ht⟩ := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
        intro ht
        rw [DeterministicFOComponent.queriedAt_eq_nextQuery]
        have hc := replay_virtual_causal A K le_rfl hist (⟨t, ht⟩ : Fin K)
        change s.virtual ⟨t, ht⟩ = A.nextQuery t (historyPrefix ht.le s.replies) at hc
        rw [hc]
        congr 1
        funext i
        change firstOrderOracle (rotatedNCCInstance D U V P)
          (A.queriedAt (rotatedNCCInstance D U V P) i) = s.replies ⟨i, by omega⟩
        rw [ih i i.isLt (i.isLt.trans ht)]
        exact horacle ⟨i, by omega⟩
  refine ⟨U, V, hU, hV, ?_⟩
  intro t ht
  rw [hvirtual t ht]
  exact ((hproj ⟨t, ht⟩).trans (hbase ⟨t, ht⟩)).symm

/-- Quantifier order is explicit: choose the simulator once, then supply an
arbitrary oracle instance. The same component is zero-respecting on all of
them and returns to the origin after the horizon. -/
theorem exists_uniform_component {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D)) :
    ∃ Z : DeterministicFOComponent (Set.univ : Set (EVec m)) (diameterBall n D),
      (∀ P : NCCInstance m n, Z.IsZeroRespectingOn P) ∧
      ∀ P : NCCInstance m n,
        ∃ (U : Fin m → EVec (m + K)) (V : Fin n → EVec (n + K)),
          IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
          ∀ t < K, Z.queriedAt P t =
            (frameProject U (A.queriedAt (rotatedNCCInstance D U V P) t).1,
             frameProject V (A.queriedAt (rotatedNCCInstance D U V P) t).2) :=
  ⟨simulator A, simulator_zeroRespecting A, uniform_component_realization A⟩

end

end NCC.Lower.UniformResisting
