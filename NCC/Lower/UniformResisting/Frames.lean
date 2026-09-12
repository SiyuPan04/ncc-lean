import NCPLVerification.ResistingOracle

/-!
# Sharp partial-frame extensions for a uniform resisting simulator

Unlike the older tagged construction, the capacity here is non-strict:
`base dimension + number of queries ≤ ambient dimension`. When assigning a
previously zero column, that zero column is removed from the constraint
list. This is the equality case needed for the manuscript's exact ambient
dimensions `m+T₀` and `n+T₀`, including final frame completion.
-/

namespace NCC.Lower.UniformResisting

noncomputable section

open scoped BigOperators
open NCPLVerification

theorem exists_unit_orthogonal_sharp {m D : ℕ}
    (U : Fin m → EVec D) (q : List (EVec D)) (i : Fin m) (hi : U i = 0)
    (hcap : m + q.length ≤ D) :
    ∃ u : EVec D, evecDotValue u u = 1 ∧
      (∀ j, evecDotValue (U j) u = 0) ∧
      ∀ X ∈ q, evecDotValue u X = 0 := by
  classical
  let s := Finset.univ.erase i
  let l := s.toList.map U ++ q
  have hcard : s.card + 1 = m := by
    simpa [s] using Finset.card_erase_add_one (s := (Finset.univ : Finset (Fin m)))
      (Finset.mem_univ i)
  have hlen : l.length < D := by
    simp only [l, List.length_append, List.length_map, Finset.length_toList]
    omega
  obtain ⟨u, hu, horth⟩ := exists_unit_orthogonal_to_list l hlen
  refine ⟨u, hu, ?_, ?_⟩
  · intro j
    by_cases hj : j = i
    · subst j
      simp [hi, evecDotValue]
    · apply horth (U j)
      exact List.mem_append_left _ (List.mem_map.mpr ⟨j,
        Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩), rfl⟩)
  · intro X hX
    rw [evecDotValue_comm]
    exact horth X (List.mem_append_right _ hX)

/-- Fill any requested finite set of columns, preserving every existing
nonzero column and every previous query projection. No objective occurs in
this statement or in the choice of the extension. -/
theorem exists_extend_on {m D : ℕ} (s : Finset (Fin m))
    (U : Fin m → EVec D) (q : List (EVec D))
    (hU : IsPartialOrthonormalFrame U) (hcap : m + q.length ≤ D) :
    ∃ V : Fin m → EVec D,
      IsPartialOrthonormalFrame V ∧
      (∀ i ∈ s, evecDotValue (V i) (V i) = 1) ∧
      (∀ i ∉ s, V i = U i) ∧
      (∀ i, U i ≠ 0 → V i = U i) ∧
      ∀ X ∈ q, frameProject V X = frameProject U X := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨U, hU, by simp, by simp, by simp, by simp⟩
  | @insert i s hi ih =>
      obtain ⟨V, hV, hunit, hout, hold, hproj⟩ := ih
      by_cases hz : V i = 0
      · obtain ⟨u, hu, horth, hq⟩ := exists_unit_orthogonal_sharp V q i hz hcap
        refine ⟨Function.update V i u, hV.update_zero i hz u hu horth, ?_, ?_, ?_, ?_⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · simp [hu]
          · have hji : j ≠ i := by intro he; subst j; exact hi hj
            simpa [Function.update, hji] using hunit j hj
        · intro j hj
          have hji : j ≠ i := by intro he; subst j; exact hj (Finset.mem_insert_self _ _)
          rw [Function.update_of_ne hji]
          exact hout j (fun hs => hj (Finset.mem_insert_of_mem hs))
        · intro j hj
          have hji : j ≠ i := by
            intro he
            subst j
            exact hj ((hold i hj).symm.trans hz)
          rw [Function.update_of_ne hji]
          exact hold j hj
        · intro X hX
          rw [frameProject_update_eq_of_dots V i u X (by simp [hz, evecDotValue]) (hq X hX)]
          exact hproj X hX
      · refine ⟨V, hV, ?_, ?_, hold, hproj⟩
        · intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · exact (hV.1 _).resolve_left hz
          · exact hunit j hj
        · intro j hj
          exact hout j (fun hs => hj (Finset.mem_insert_of_mem hs))

theorem exists_completion_sharp {m D : ℕ}
    (U : Fin m → EVec D) (q : List (EVec D))
    (hU : IsPartialOrthonormalFrame U) (hcap : m + q.length ≤ D) :
    ∃ V : Fin m → EVec D, IsOrthonormalFrame V ∧
      (∀ i, U i ≠ 0 → V i = U i) ∧
      ∀ X ∈ q, frameProject V X = frameProject U X := by
  obtain ⟨V, hV, hunit, _, hold, hproj⟩ := exists_extend_on Finset.univ U q hU hcap
  exact ⟨V, isOrthonormalFrame_of_partial_complete hV (fun i => hunit i (Finset.mem_univ i)),
    hold, hproj⟩

/-- Partial projections contract whenever at least one spare ambient
dimension is available. This is exactly the positive-horizon regime. -/
theorem partial_project_sq_le {m D : ℕ} (U : Fin m → EVec D)
    (hU : IsPartialOrthonormalFrame U) (hcap : m + 1 ≤ D) (X : EVec D) :
    vecSq (frameProject U X) ≤ vecSq X := by
  obtain ⟨V, hV, _, hproj⟩ := exists_completion_sharp U [X] hU (by simpa using hcap)
  rw [← hproj X (by simp)]
  exact vecSq_frameProject_le hV X

end

end NCC.Lower.UniformResisting
