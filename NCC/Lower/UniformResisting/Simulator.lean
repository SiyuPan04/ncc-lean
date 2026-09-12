import NCC.Lower.UniformResisting.Frames
import NCCLowerBoundVerification.Oracle.ZeroRespectingAlgorithm
import NCCLowerBoundVerification.Lower.RotationClosure

/-!
# Objective-independent finite-history simulator

Every choice in `replay` depends only on the ambient algorithm, dimensions,
the horizon, and a finite list of oracle replies. In particular the base
objective is not an argument. The known domain diameter selects a component
of the ambient algorithm; it is not inferred from an objective.
-/

namespace NCC.Lower.UniformResisting

noncomputable section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open NCCLowerBoundVerification Oracle
open NCPLVerification (IsPartialOrthonormalFrame IsOrthonormalFrame frameProject frameEmbed
  evecDotValue isPartialOrthonormalFrame_zero)

def reveal {m D : ℕ} (U : Fin m → EVec D) (q : List (EVec D)) (g : EVec m)
    (hU : IsPartialOrthonormalFrame U) (hcap : m + q.length ≤ D) : Fin m → EVec D :=
  (exists_extend_on (Finset.univ.filter (fun i => g i ≠ 0)) U q hU hcap).choose

theorem reveal_spec {m D : ℕ} (U : Fin m → EVec D) (q : List (EVec D)) (g : EVec m)
    (hU : IsPartialOrthonormalFrame U) (hcap : m + q.length ≤ D) :
    IsPartialOrthonormalFrame (reveal U q g hU hcap) ∧
      (∀ i, g i ≠ 0 → evecDotValue (reveal U q g hU hcap i) (reveal U q g hU hcap i) = 1) ∧
      (∀ i, g i = 0 → reveal U q g hU hcap i = U i) ∧
      (∀ i, U i ≠ 0 → reveal U q g hU hcap i = U i) ∧
      ∀ X ∈ q, frameProject (reveal U q g hU hcap) X = frameProject U X := by
  have h := (exists_extend_on (Finset.univ.filter (fun i => g i ≠ 0)) U q hU hcap).choose_spec
  exact ⟨h.1, fun i hi => h.2.1 i (by simp [hi]),
    fun i hi => h.2.2.1 i (by simp [hi]), h.2.2.2⟩

structure Snapshot (m n K t : ℕ) where
  U : Fin m → EVec (m + K)
  V : Fin n → EVec (n + K)
  partialU : IsPartialOrthonormalFrame U
  partialV : IsPartialOrthonormalFrame V
  virtual : Fin t → Query (m + K) (n + K)
  base : Fin t → Query m n
  replies : ReplyHistory (m + K) (n + K) t

def emptySnapshot (m n K : ℕ) : Snapshot m n K 0 where
  U := 0
  V := 0
  partialU := isPartialOrthonormalFrame_zero
  partialV := isPartialOrthonormalFrame_zero
  virtual := Fin.elim0
  base := Fin.elim0
  replies := Fin.elim0

def projectedQuery {m n K t : ℕ} (s : Snapshot m n K t)
    (q : Query (m + K) (n + K)) : Query m n :=
  (frameProject s.U q.1, frameProject s.V q.2)

def advance {m n K t : ℕ} (s : Snapshot m n K t) (ht : t < K)
    (q : Query (m + K) (n + K)) (r : OracleReply m n) : Snapshot m n K (t + 1) :=
  let xs := List.ofFn (fun i => (s.virtual i).1) ++ [q.1]
  let ys := List.ofFn (fun i => (s.virtual i).2) ++ [q.2]
  let U := reveal s.U xs r.gradX s.partialU (by
    simp only [xs, List.length_append, List.length_ofFn, List.length_singleton]
    omega)
  let V := reveal s.V ys r.gradY s.partialV (by
    simp only [ys, List.length_append, List.length_ofFn, List.length_singleton]
    omega)
  { U := U
    V := V
    partialU := (reveal_spec ..).1
    partialV := (reveal_spec ..).1
    virtual := Fin.snoc s.virtual q
    base := Fin.snoc s.base (projectedQuery s q)
    replies := Fin.snoc s.replies ⟨r.value, frameEmbed U r.gradX, frameEmbed V r.gradY⟩ }

theorem advance_U_spec {m n K t : ℕ} (s : Snapshot m n K t) (ht : t < K)
    (q : Query (m + K) (n + K)) (r : OracleReply m n) :
    (∀ i, r.gradX i ≠ 0 → evecDotValue ((advance s ht q r).U i) ((advance s ht q r).U i) = 1) ∧
    (∀ i, r.gradX i = 0 → (advance s ht q r).U i = s.U i) ∧
    (∀ i, s.U i ≠ 0 → (advance s ht q r).U i = s.U i) ∧
    ∀ X ∈ List.ofFn (fun i => (s.virtual i).1) ++ [q.1],
      frameProject (advance s ht q r).U X = frameProject s.U X := by
  exact (reveal_spec s.U (List.ofFn (fun i => (s.virtual i).1) ++ [q.1]) r.gradX
    s.partialU (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)).2

theorem advance_V_spec {m n K t : ℕ} (s : Snapshot m n K t) (ht : t < K)
    (q : Query (m + K) (n + K)) (r : OracleReply m n) :
    (∀ i, r.gradY i ≠ 0 → evecDotValue ((advance s ht q r).V i) ((advance s ht q r).V i) = 1) ∧
    (∀ i, r.gradY i = 0 → (advance s ht q r).V i = s.V i) ∧
    (∀ i, s.V i ≠ 0 → (advance s ht q r).V i = s.V i) ∧
    ∀ X ∈ List.ofFn (fun i => (s.virtual i).2) ++ [q.2],
      frameProject (advance s ht q r).V X = frameProject s.V X := by
  exact (reveal_spec s.V (List.ofFn (fun i => (s.virtual i).2) ++ [q.2]) r.gradY
    s.partialV (by simp only [List.length_append, List.length_ofFn, List.length_singleton]; omega)).2

theorem advance_U_zero {m n K t : ℕ} (s : Snapshot m n K t) (ht : t < K)
    (q : Query (m + K) (n + K)) (r : OracleReply m n) (i : Fin m) (hi : r.gradX i = 0) :
    (advance s ht q r).U i = s.U i := by
  exact (advance_U_spec s ht q r).2.1 i hi

theorem advance_V_zero {m n K t : ℕ} (s : Snapshot m n K t) (ht : t < K)
    (q : Query (m + K) (n + K)) (r : OracleReply m n) (i : Fin n) (hi : r.gradY i = 0) :
    (advance s ht q r).V i = s.V i := by
  exact (advance_V_spec s ht q r).2.1 i hi

def replay {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D)) :
    (t : ℕ) → t ≤ K → ReplyHistory m n t → Snapshot m n K t
  | 0, _, _ => emptySnapshot m n K
  | t + 1, ht, hist =>
      let s := replay A t (by omega) (fun i => hist i.castSucc)
      advance s (by omega) (A.nextQuery t s.replies) (hist (Fin.last t))

def simulatorQuery {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (t : ℕ) (hist : ReplyHistory m n t) : Query m n :=
  if ht : t < K then
    let s := replay A t ht.le hist
    projectedQuery s (A.nextQuery t s.replies)
  else (0, 0)

theorem simulatorQuery_mem {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (t : ℕ) (hist : ReplyHistory m n t) :
    (simulatorQuery A t hist).1 ∈ (Set.univ : Set (EVec m)) ∧
      (simulatorQuery A t hist).2 ∈ diameterBall n D := by
  constructor
  · exact Set.mem_univ _
  · unfold simulatorQuery
    split_ifs with ht
    · let s := replay A t ht.le hist
      have hmem := (A.next_mem t s.replies).2
      exact (partial_project_sq_le s.V s.partialV (by omega) (A.nextQuery t s.replies).2).trans hmem
    · change vecSq (0 : EVec n) ≤ (D / 2) ^ 2
      change (∑ _i : Fin n, (0 : ℝ) ^ 2) ≤ (D / 2) ^ 2
      simpa using sq_nonneg (D / 2)

def simulator {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D)) :
    DeterministicFOComponent (Set.univ : Set (EVec m)) (diameterBall n D) where
  nextQuery := simulatorQuery A
  next_mem := simulatorQuery_mem A
  initial_query := by
    unfold simulatorQuery
    split_ifs
    · apply Prod.ext <;> funext i <;>
        simp [replay, emptySnapshot, projectedQuery, frameProject, evecDotValue]
    · rfl

theorem replay_zero_unseen {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (t : ℕ) (ht : t ≤ K) (hist : ReplyHistory m n t) :
    (∀ i, (∀ r, (hist r).gradX i = 0) → (replay A t ht hist).U i = 0) ∧
    (∀ i, (∀ r, (hist r).gradY i = 0) → (replay A t ht hist).V i = 0) := by
  induction t with
  | zero => exact ⟨by simp [replay, emptySnapshot], by simp [replay, emptySnapshot]⟩
  | succ t ih =>
      have hp := ih (by omega) (fun i => hist i.castSucc)
      constructor
      · intro i hi
        unfold replay
        rw [advance_U_zero _ _ _ _ i (hi (Fin.last t))]
        exact hp.1 i (fun r => hi r.castSucc)
      · intro i hi
        unfold replay
        rw [advance_V_zero _ _ _ _ i (hi (Fin.last t))]
        exact hp.2 i (fun r => hi r.castSucc)

theorem simulatorQuery_support {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (t : ℕ) (hist : ReplyHistory m n t) :
    (∀ i, (simulatorQuery A t hist).1 i ≠ 0 → ∃ r, (hist r).gradX i ≠ 0) ∧
    (∀ i, (simulatorQuery A t hist).2 i ≠ 0 → ∃ r, (hist r).gradY i ≠ 0) := by
  classical
  unfold simulatorQuery
  split_ifs with ht
  · have hz := replay_zero_unseen A t ht.le hist
    constructor
    · intro i hi
      by_contra! hzero
      exact hi (by simp [projectedQuery, NCPLVerification.frameProject, hz.1 i hzero, evecDotValue])
    · intro i hi
      by_contra! hzero
      exact hi (by simp [projectedQuery, NCPLVerification.frameProject, hz.2 i hzero, evecDotValue])
  · simp

theorem simulator_zeroRespecting {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (P : NCCInstance m n) : (simulator A).IsZeroRespectingOn P := by
  intro t j hj
  dsimp only at hj ⊢
  have hs := simulatorQuery_support A t ((simulator A).queriedTranscript P t)
  rw [DeterministicFOComponent.queriedAt_eq_nextQuery] at hj
  refine Fin.addCases ?_ ?_ j hj
  · intro i hi
    have hxi : (simulatorQuery A t ((simulator A).queriedTranscript P t)).1 i ≠ 0 := by
      simpa [standardJointQuery, standardJointVector, simulator] using hi
    obtain ⟨r, hr⟩ := hs.1 i hxi
    refine ⟨r, r.isLt, ?_⟩
    simpa [standardSaddleField_standardJointQuery, standardJointVector,
      DeterministicFOComponent.queriedTranscript, DeterministicFOComponent.replyAt] using hr
  · intro i hi
    have hyi : (simulatorQuery A t ((simulator A).queriedTranscript P t)).2 i ≠ 0 := by
      simpa [standardJointQuery, standardJointVector, simulator] using hi
    obtain ⟨r, hr⟩ := hs.2 i hyi
    refine ⟨r, r.isLt, ?_⟩
    simpa [standardSaddleField_standardJointQuery, standardJointVector,
      DeterministicFOComponent.queriedTranscript, DeterministicFOComponent.replyAt] using hr

def historyPrefix {α : Type*} {r t : ℕ} (hrt : r ≤ t) (hist : Fin t → α) : Fin r → α :=
  fun i => hist (Fin.castLE hrt i)

@[simp] theorem replay_virtual_castSucc {m n K t : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (ht : t + 1 ≤ K) (hist : ReplyHistory m n (t + 1)) (i : Fin t) :
    (replay A (t + 1) ht hist).virtual i.castSucc =
      (replay A t (by omega) (fun j => hist j.castSucc)).virtual i := by
  simp only [replay, advance, Fin.snoc_castSucc]

@[simp] theorem replay_base_castSucc {m n K t : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (ht : t + 1 ≤ K) (hist : ReplyHistory m n (t + 1)) (i : Fin t) :
    (replay A (t + 1) ht hist).base i.castSucc =
      (replay A t (by omega) (fun j => hist j.castSucc)).base i := by
  simp only [replay, advance, Fin.snoc_castSucc]

@[simp] theorem replay_replies_castSucc {m n K t : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (ht : t + 1 ≤ K) (hist : ReplyHistory m n (t + 1)) (i : Fin t) :
    (replay A (t + 1) ht hist).replies i.castSucc =
      (replay A t (by omega) (fun j => hist j.castSucc)).replies i := by
  simp only [replay, advance, Fin.snoc_castSucc]

theorem replay_prefix {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (t : ℕ) (ht : t ≤ K) (hist : ReplyHistory m n t) {r : ℕ} (hrt : r ≤ t) (i : Fin r) :
    (replay A t ht hist).virtual (Fin.castLE hrt i) =
        (replay A r (hrt.trans ht) (historyPrefix hrt hist)).virtual i ∧
    (replay A t ht hist).base (Fin.castLE hrt i) =
        (replay A r (hrt.trans ht) (historyPrefix hrt hist)).base i ∧
    (replay A t ht hist).replies (Fin.castLE hrt i) =
        (replay A r (hrt.trans ht) (historyPrefix hrt hist)).replies i := by
  induction t generalizing r with
  | zero => exact Fin.elim0 (Fin.castLE hrt i)
  | succ t ih =>
      by_cases he : r = t + 1
      · subst r
        exact ⟨rfl, rfl, rfl⟩
      · have hr : r ≤ t := by omega
        have hi : Fin.castLE hrt i = (Fin.castLE hr i).castSucc := rfl
        rw [hi, replay_virtual_castSucc, replay_base_castSucc, replay_replies_castSucc]
        exact ih (by omega) (fun j => hist j.castSucc) hr i

theorem replay_virtual_causal {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (t : ℕ) (ht : t ≤ K) (hist : ReplyHistory m n t) (i : Fin t) :
    (replay A t ht hist).virtual i =
      A.nextQuery i (historyPrefix i.isLt.le (replay A t ht hist).replies) := by
  have h := (replay_prefix A t ht hist (Nat.succ_le_of_lt i.isLt) (Fin.last i.val)).1
  have hr : historyPrefix i.isLt.le (replay A t ht hist).replies =
      (replay A i.val (i.isLt.le.trans ht) (historyPrefix i.isLt.le hist)).replies := by
    funext j
    exact (replay_prefix A t ht hist i.isLt.le j).2.2
  rw [hr]
  convert h using 1 <;> simp [replay, advance, historyPrefix] <;> rfl

theorem replay_base_causal {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (t : ℕ) (ht : t ≤ K) (hist : ReplyHistory m n t) (i : Fin t) :
    (replay A t ht hist).base i = simulatorQuery A i (historyPrefix i.isLt.le hist) := by
  have h := (replay_prefix A t ht hist (Nat.succ_le_of_lt i.isLt) (Fin.last i.val)).2.1
  have hi : i.val < K := i.isLt.trans_le ht
  convert h using 1 <;> simp [simulatorQuery, hi, replay, advance, historyPrefix] <;> rfl

theorem frameEmbed_eq_of_support {m D : ℕ} (U V : Fin m → EVec D) (g : EVec m)
    (h : ∀ i, g i ≠ 0 → V i = U i) : frameEmbed V g = frameEmbed U g := by
  funext j
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : g i = 0
  · simp [hi]
  · rw [h i hi]

theorem advance_U_nonzero {m n K t : ℕ} (s : Snapshot m n K t) (ht : t < K)
    (q : Query (m + K) (n + K)) (r : OracleReply m n) (i : Fin m)
    (hi : s.U i ≠ 0 ∨ r.gradX i ≠ 0) : (advance s ht q r).U i ≠ 0 := by
  rcases hi with hi | hi
  · rw [(advance_U_spec s ht q r).2.2.1 i hi]
    exact hi
  · have hu := (advance_U_spec s ht q r).1 i hi
    intro hz
    simp [hz, evecDotValue] at hu

theorem advance_V_nonzero {m n K t : ℕ} (s : Snapshot m n K t) (ht : t < K)
    (q : Query (m + K) (n + K)) (r : OracleReply m n) (i : Fin n)
    (hi : s.V i ≠ 0 ∨ r.gradY i ≠ 0) : (advance s ht q r).V i ≠ 0 := by
  rcases hi with hi | hi
  · rw [(advance_V_spec s ht q r).2.2.1 i hi]
    exact hi
  · have hu := (advance_V_spec s ht q r).1 i hi
    intro hz
    simp [hz, evecDotValue] at hu

theorem replay_seen_nonzero {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (t : ℕ) (ht : t ≤ K) (hist : ReplyHistory m n t) (r : Fin t) :
    (∀ i, (hist r).gradX i ≠ 0 → (replay A t ht hist).U i ≠ 0) ∧
    (∀ i, (hist r).gradY i ≠ 0 → (replay A t ht hist).V i ≠ 0) := by
  induction t with
  | zero => exact Fin.elim0 r
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) r
      · constructor
        · intro i hi
          exact advance_U_nonzero _ (by omega) _ _ i (Or.inr hi)
        · intro i hi
          exact advance_V_nonzero _ (by omega) _ _ i (Or.inr hi)
      · have hp := ih (by omega) (fun i => hist i.castSucc) j
        constructor
        · intro i hi
          exact advance_U_nonzero _ (by omega) _ _ i (Or.inl (hp.1 i hi))
        · intro i hi
          exact advance_V_nonzero _ (by omega) _ _ i (Or.inl (hp.2 i hi))

theorem advance_project_last {m n K t : ℕ} (s : Snapshot m n K t) (ht : t < K)
    (q : Query (m + K) (n + K)) (r : OracleReply m n) :
    projectedQuery (advance s ht q r) q = projectedQuery s q := by
  apply Prod.ext
  · exact (advance_U_spec s ht q r).2.2.2 _ (by simp)
  · exact (advance_V_spec s ht q r).2.2.2 _ (by simp)

theorem advance_project_previous {m n K t : ℕ} (s : Snapshot m n K t) (ht : t < K)
    (q : Query (m + K) (n + K)) (r : OracleReply m n) (i : Fin t) :
    projectedQuery (advance s ht q r) (s.virtual i) = projectedQuery s (s.virtual i) := by
  apply Prod.ext
  · exact (advance_U_spec s ht q r).2.2.2 _
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  · exact (advance_V_spec s ht q r).2.2.2 _
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))

theorem replay_projects {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (t : ℕ) (ht : t ≤ K) (hist : ReplyHistory m n t) (i : Fin t) :
    projectedQuery (replay A t ht hist) ((replay A t ht hist).virtual i) =
      (replay A t ht hist).base i := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [replay, advance, Fin.snoc_last] using
          advance_project_last (replay A t (by omega) (fun j => hist j.castSucc))
            (by omega) (A.nextQuery t (replay A t (by omega) (fun j => hist j.castSucc)).replies)
            (hist (Fin.last t))
      · rw [replay_virtual_castSucc, replay_base_castSucc]
        change projectedQuery (advance _ (by omega) _ _) _ = _
        rw [advance_project_previous]
        exact ih (by omega) (fun j => hist j.castSucc) j

theorem replay_represents_replies {m n K : ℕ} {D : ℝ}
    (A : DeterministicFOComponent (Set.univ : Set (EVec (m + K))) (diameterBall (n + K) D))
    (t : ℕ) (ht : t ≤ K) (hist : ReplyHistory m n t) (i : Fin t) :
    (replay A t ht hist).replies i =
      ⟨(hist i).value, frameEmbed (replay A t ht hist).U (hist i).gradX,
        frameEmbed (replay A t ht hist).V (hist i).gradY⟩ := by
  induction t with
  | zero => exact Fin.elim0 i
  | succ t ih =>
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [replay, advance, Fin.snoc_last]
      · rw [replay_replies_castSucc, ih]
        have hn := replay_seen_nonzero A t (by omega) (fun j => hist j.castSucc) j
        congr 1
        · symm
          apply frameEmbed_eq_of_support
          intro k hk
          exact (advance_U_spec _ (by omega) _ _).2.2.1 k (hn.1 k hk)
        · symm
          apply frameEmbed_eq_of_support
          intro k hk
          exact (advance_V_spec _ (by omega) _ _).2.2.1 k (hn.2 k hk)

end

end NCC.Lower.UniformResisting
