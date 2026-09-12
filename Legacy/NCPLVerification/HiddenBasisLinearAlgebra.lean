import NCPLVerification.RotatedClass

/-!
# Finite-dimensional hidden directions

The resisting oracle repeatedly needs a unit vector orthogonal to a finite
list of already constrained vectors.  The proof below is an exact kernel-
dimension argument for the explicit Euclidean dot product used by this
project.  It also supplies list-level orthonormality and completion lemmas.
-/

namespace NCPLVerification

noncomputable section

theorem vecSq_pos_of_ne_zero {D : Nat} {v : EVec D} (hv : v ≠ 0) :
    0 < vecSq v := by
  have hex : ∃ i : Fin D, v i ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hex
  have hi2 : 0 < v i ^ 2 := sq_pos_of_ne_zero hi
  unfold vecSq
  exact lt_of_lt_of_le hi2
    (Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i))

theorem evecDotValue_scaleEVec_right {D : Nat}
    (c : ℝ) (x y : EVec D) :
    evecDotValue x (scaleEVec c y) = c * evecDotValue x y := by
  unfold evecDotValue scaleEVec
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A list is orthonormal when every entry has squared norm one and entries
appearing in increasing list order are mutually orthogonal. -/
def IsOrthonormalList {D : Nat} (l : List (EVec D)) : Prop :=
  (∀ u ∈ l, evecDotValue u u = 1) ∧
    l.Pairwise (fun u v ↦ evecDotValue u v = 0)

theorem isOrthonormalList_nil {D : Nat} :
    IsOrthonormalList ([] : List (EVec D)) := by
  simp [IsOrthonormalList]

theorem IsOrthonormalList.cons {D : Nat} {l : List (EVec D)}
    {u : EVec D} (hl : IsOrthonormalList l)
    (hu : evecDotValue u u = 1)
    (horth : ∀ v ∈ l, evecDotValue v u = 0) :
    IsOrthonormalList (u :: l) := by
  constructor
  · intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with hv | hv
    · subst v
      exact hu
    · exact hl.1 v hv
  · rw [List.pairwise_cons]
    constructor
    · intro v hv
      rw [evecDotValue_comm]
      exact horth v hv
    · exact hl.2

theorem IsOrthonormalList.snoc {D : Nat} {l : List (EVec D)}
    {u : EVec D} (hl : IsOrthonormalList l)
    (hu : evecDotValue u u = 1)
    (horth : ∀ v ∈ l, evecDotValue v u = 0) :
    IsOrthonormalList (l ++ [u]) := by
  constructor
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact hl.1 v hv
    · simp only [List.mem_singleton] at hv
      subst v
      exact hu
  · rw [List.pairwise_append]
    refine ⟨hl.2, by simp, ?_⟩
    intro v hv w hw
    simp only [List.mem_singleton] at hw
    subst w
    exact horth v hv

theorem IsOrthonormalList.reverse {D : Nat} {l : List (EVec D)}
    (hl : IsOrthonormalList l) : IsOrthonormalList l.reverse := by
  constructor
  · intro u hu
    exact hl.1 u (by simpa using hu)
  · rw [List.pairwise_reverse]
    have hp := hl.2
    apply hp.imp
    intro u v huv
    rw [evecDotValue_comm]
    exact huv

theorem IsOrthonormalList.get_frame {D : Nat} {l : List (EVec D)}
    (hl : IsOrthonormalList l) : IsOrthonormalFrame (fun i ↦ l.get i) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact hl.1 (l.get i) (List.get_mem l i)
  · rw [if_neg hij]
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact (List.pairwise_iff_get.mp hl.2) i j hijlt
    · rw [evecDotValue_comm]
      exact (List.pairwise_iff_get.mp hl.2) j i hjilt

/-- A finite list of fewer than `D` vectors has a unit Euclidean vector
orthogonal to every entry.  No independence assumption on the list is used. -/
theorem exists_unit_orthogonal_to_list {D : Nat} (l : List (EVec D))
    (hlen : l.length < D) :
    ∃ u : EVec D,
      evecDotValue u u = 1 ∧
        ∀ v ∈ l, evecDotValue v u = 0 := by
  let w : Fin l.length → EVec D := fun i ↦ l.get i
  let A : EVec D →ₗ[ℝ] EVec l.length :=
    (frameProjectCLM w).toLinearMap
  have hdim : Module.finrank ℝ (EVec l.length) <
      Module.finrank ℝ (EVec D) := by
    simpa only [Module.finrank_fin_fun] using hlen
  have hker : A.ker ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (f := A) hdim
  obtain ⟨v, hvker, hvne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hAv : A v = 0 := LinearMap.mem_ker.mp hvker
  have hsv : 0 < vecSq v := vecSq_pos_of_ne_zero hvne
  let u : EVec D := scaleEVec (1 / Real.sqrt (vecSq v)) v
  refine ⟨u, ?_, ?_⟩
  · rw [evecDotValue_self]
    unfold u
    rw [vecSq_scaleEVec]
    have hsqrt : 0 < Real.sqrt (vecSq v) := Real.sqrt_pos.2 hsv
    rw [div_pow, one_pow, Real.sq_sqrt hsv.le]
    field_simp [hsv.ne']
  · intro q hq
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hq
    subst q
    have hcoord : evecDotValue (l.get i) v = 0 := by
      have := congrFun hAv i
      change frameProject w v i = 0 at this
      exact this
    unfold u
    rw [evecDotValue_scaleEVec_right, hcoord, mul_zero]

/-- One can prepend a new orthonormal direction while making it orthogonal to
an arbitrary additional constraint list. -/
theorem IsOrthonormalList.exists_cons_orthogonal {D : Nat}
    {l q : List (EVec D)} (hl : IsOrthonormalList l)
    (hlen : (l ++ q).length < D) :
    ∃ u : EVec D,
      IsOrthonormalList (u :: l) ∧
      (∀ v ∈ q, evecDotValue v u = 0) := by
  obtain ⟨u, hu, horth⟩ := exists_unit_orthogonal_to_list (l ++ q) hlen
  refine ⟨u, hl.cons hu ?_, ?_⟩
  · intro v hv
    exact horth v (List.mem_append_left q hv)
  · intro v hv
    exact horth v (List.mem_append_right l hv)

/-- Complete an orthonormal list by `n` further directions.  All newly added
directions avoid the fixed constraint list `q`; the previously present
directions need not avoid it. -/
theorem IsOrthonormalList.complete_avoiding {D n : Nat}
    {l q : List (EVec D)} (hl : IsOrthonormalList l)
    (hcapacity : l.length + q.length + n ≤ D) :
    ∃ a : List (EVec D),
      a.length = n ∧
      IsOrthonormalList (a ++ l) ∧
      ∀ u ∈ a, ∀ v ∈ q, evecDotValue v u = 0 := by
  induction n generalizing l with
  | zero =>
      refine ⟨[], rfl, ?_, ?_⟩
      · simpa using hl
      · simp
  | succ n ih =>
      have hshort : (l ++ q).length < D := by
        simp only [List.length_append]
        omega
      obtain ⟨u, hlu, huq⟩ := hl.exists_cons_orthogonal hshort
      have hcapacity' : (u :: l).length + q.length + n ≤ D := by
        simp only [List.length_cons]
        omega
      obtain ⟨a, halen, haorth, haq⟩ := ih hlu hcapacity'
      refine ⟨a ++ [u], ?_, ?_, ?_⟩
      · simp [halen]
      · simpa [List.append_assoc] using haorth
      · intro w hw v hv
        rcases List.mem_append.mp hw with hw | hw
        · exact haq w hw v hv
        · simp only [List.mem_singleton] at hw
          subst w
          exact huq v hv

/-- Right-handed version of `complete_avoiding`, convenient when list order
is the order of revealed coordinates. -/
theorem IsOrthonormalList.complete_avoiding_right {D n : Nat}
    {l q : List (EVec D)} (hl : IsOrthonormalList l)
    (hcapacity : l.length + q.length + n ≤ D) :
    ∃ a : List (EVec D),
      a.length = n ∧
      IsOrthonormalList (l ++ a) ∧
      ∀ u ∈ a, ∀ v ∈ q, evecDotValue v u = 0 := by
  induction n generalizing l with
  | zero =>
      refine ⟨[], rfl, ?_, ?_⟩
      · simpa using hl
      · simp
  | succ n ih =>
      have hshort : (l ++ q).length < D := by
        simp only [List.length_append]
        omega
      obtain ⟨u, hu, horth⟩ := exists_unit_orthogonal_to_list (l ++ q) hshort
      have hlu : IsOrthonormalList (l ++ [u]) := by
        apply hl.snoc hu
        intro v hv
        exact horth v (List.mem_append_left q hv)
      have huq : ∀ v ∈ q, evecDotValue v u = 0 := by
        intro v hv
        exact horth v (List.mem_append_right l hv)
      have hcapacity' : (l ++ [u]).length + q.length + n ≤ D := by
        simp only [List.length_append, List.length_singleton]
        omega
      obtain ⟨a, halen, haorth, haq⟩ := ih hlu hcapacity'
      refine ⟨u :: a, ?_, ?_, ?_⟩
      · simp [halen]
      · simpa [List.append_assoc] using haorth
      · intro w hw v hv
        simp only [List.mem_cons] at hw
        rcases hw with rfl | hw
        · exact huq v hv
        · exact haq w hw v hv

end

end NCPLVerification
