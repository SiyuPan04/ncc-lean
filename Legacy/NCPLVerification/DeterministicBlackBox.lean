import NCPLVerification.HiddenBasisLinearAlgebra

/-!
# Deterministic first-order black-box methods

The method is an arbitrary deterministic function of the complete finite
oracle history.  An oracle record contains the query, value, and both partial
gradients.  No span or zero-respecting restriction is imposed.
-/

namespace NCPLVerification

noncomputable section

structure FirstOrderRecord (DX DY : Nat) where
  queryX : EVec DX
  queryY : EVec DY
  value : ℝ
  gradX : EVec DX
  gradY : EVec DY

structure DeterministicFOBlackBox (DX DY : Nat) where
  nextQuery : List (FirstOrderRecord DX DY) → EVec DX × EVec DY
  output : List (FirstOrderRecord DX DY) → EVec DX

def firstOrderRecord {DX DY : Nat}
    (F : EVec DX → EVec DY → ℝ)
    (gradX : EVec DX → EVec DY → EVec DX)
    (gradY : EVec DX → EVec DY → EVec DY)
    (q : EVec DX × EVec DY) : FirstOrderRecord DX DY where
  queryX := q.1
  queryY := q.2
  value := F q.1 q.2
  gradX := gradX q.1 q.2
  gradY := gradY q.1 q.2

def runHistory {DX DY : Nat} (A : DeterministicFOBlackBox DX DY)
    (F : EVec DX → EVec DY → ℝ)
    (gradX : EVec DX → EVec DY → EVec DX)
    (gradY : EVec DX → EVec DY → EVec DY) :
    Nat → List (FirstOrderRecord DX DY)
  | 0 => []
  | t + 1 =>
      let h := runHistory A F gradX gradY t
      h ++ [firstOrderRecord F gradX gradY (A.nextQuery h)]

theorem runHistory_length {DX DY : Nat}
    (A : DeterministicFOBlackBox DX DY)
    (F : EVec DX → EVec DY → ℝ)
    (gradX : EVec DX → EVec DY → EVec DX)
    (gradY : EVec DX → EVec DY → EVec DY) (t : Nat) :
    (runHistory A F gradX gradY t).length = t := by
  induction t with
  | zero => rfl
  | succ t ih => simp [runHistory, ih]

/-- Turn the first `l.length` columns of a chronological column list into a
partial frame, filling all not-yet-chosen columns with zero. -/
def partialFrame {m D : Nat} (l : List (EVec D)) : Fin m → EVec D :=
  fun i ↦ if h : i.1 < l.length then l.get ⟨i.1, h⟩ else 0

theorem partialFrame_apply_of_lt {m D : Nat} (l : List (EVec D))
    (i : Fin m) (hi : i.1 < l.length) :
    partialFrame l i = l.get ⟨i.1, hi⟩ := by
  simp [partialFrame, hi]

theorem partialFrame_apply_of_le {m D : Nat} (l : List (EVec D))
    (i : Fin m) (hi : l.length ≤ i.1) :
    partialFrame l i = 0 := by
  simp [partialFrame, Nat.not_lt_of_ge hi]

theorem partialFrame_snoc_old {m D : Nat} (l : List (EVec D))
    (u : EVec D) (i : Fin m) (hi : i.1 < l.length) :
    partialFrame (l ++ [u]) i = partialFrame l i := by
  rw [partialFrame_apply_of_lt l i hi]
  have hi' : i.1 < (l ++ [u]).length := by simp; omega
  rw [partialFrame_apply_of_lt (l ++ [u]) i hi']
  simp only [List.get_eq_getElem]
  exact List.getElem_append_left hi

theorem partialFrame_snoc_new {m D : Nat} (l : List (EVec D))
    (u : EVec D) (i : Fin m) (hi : i.1 = l.length) :
    partialFrame (l ++ [u]) i = u := by
  have hnew : l.length < (l ++ [u]).length := by simp
  have hinew : i.1 < (l ++ [u]).length := by simp [hi]
  rw [partialFrame_apply_of_lt (l ++ [u]) i hinew]
  simp only [List.get_eq_getElem]
  simp [hi]

theorem partialFrame_snoc_future {m D : Nat} (l : List (EVec D))
    (u : EVec D) (i : Fin m) (hi : l.length + 1 ≤ i.1) :
    partialFrame (l ++ [u]) i = partialFrame l i := by
  rw [partialFrame_apply_of_le l i (by omega)]
  rw [partialFrame_apply_of_le (l ++ [u]) i (by simp; omega)]

theorem frameProject_partialFrame_snoc_of_orthogonal {m D : Nat}
    (l : List (EVec D)) (u X : EVec D)
    (horth : evecDotValue u X = 0) :
    frameProject (partialFrame (m := m) (l ++ [u])) X =
      frameProject (partialFrame (m := m) l) X := by
  funext i
  unfold frameProject
  by_cases hi : i.1 < l.length
  · rw [partialFrame_snoc_old l u i hi]
  · by_cases hieq : i.1 = l.length
    · rw [partialFrame_snoc_new l u i hieq,
        partialFrame_apply_of_le l i (by omega), horth]
      unfold evecDotValue
      simp
    · rw [partialFrame_snoc_future l u i (by omega)]

theorem frameEmbed_partialFrame_snoc_of_next_zero {m D : Nat}
    (l : List (EVec D)) (u : EVec D) (g : EVec m)
    (hnext : ∀ i : Fin m, i.1 = l.length → g i = 0) :
    frameEmbed (partialFrame (m := m) (l ++ [u])) g =
      frameEmbed (partialFrame (m := m) l) g := by
  funext k
  unfold frameEmbed
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i.1 < l.length
  · rw [partialFrame_snoc_old l u i hi]
  · by_cases hieq : i.1 = l.length
    · rw [partialFrame_snoc_new l u i hieq,
        partialFrame_apply_of_le l i (by omega), hnext i hieq]
      simp
    · rw [partialFrame_snoc_future l u i (by omega)]

end

end NCPLVerification
