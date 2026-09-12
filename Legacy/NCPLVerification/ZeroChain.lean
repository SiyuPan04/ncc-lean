import Mathlib

/-!
# Zero-chain discovery

This file formalizes Definition 1.2, Definition 1.3, and Lemma 1.4
(`Sequential discovery`) of `NC_PL_merged.tex` after reindexing the ordered
coordinates by `Fin m`.
-/

namespace NCPLVerification

abbrev EVec (m : ℕ) := Fin m → ℝ

/-- `SupportedBelow k v` means that every coordinate with index at least `k`
is zero. Indices are zero-based, so this is the formal counterpart of
`supp(v) ⊆ [k]` in the paper's one-based notation. -/
def SupportedBelow {m : ℕ} (k : ℕ) (v : EVec m) : Prop :=
  ∀ i, k ≤ i.1 → v i = 0

theorem supportedBelow_zero (m k : ℕ) : SupportedBelow k (0 : EVec m) := by
  intro i hi
  rfl

theorem SupportedBelow.mono {m a b : ℕ} {v : EVec m}
    (h : SupportedBelow a v) (hab : a ≤ b) : SupportedBelow b v := by
  intro i hbi
  exact h i (hab.trans hbi)

/-- A vector field is a first-order zero-chain if input support below `r`
forces output support below `r+1`. This is the paper's saddle zero-chain
condition after flattening and reordering the joint primal-dual coordinates. -/
def IsFirstOrderZeroChain {m : ℕ} (G : EVec m → EVec m) : Prop :=
  ∀ r z, SupportedBelow r z → SupportedBelow (r + 1) (G z)

/-- Every nonzero coordinate of query `t` must have appeared in an earlier
oracle response. In particular, query zero is forced to be the zero vector. -/
def QueriesAreZeroRespecting {m : ℕ} (G : EVec m → EVec m)
    (query : ℕ → EVec m) : Prop :=
  ∀ t i, query t i ≠ 0 → ∃ s < t, G (query s) i ≠ 0

/-- Every nonzero coordinate returned after `t` calls must have appeared in
one of the first `t` oracle responses. -/
def OutputsAreZeroRespecting {m : ℕ} (G : EVec m → EVec m)
    (query output : ℕ → EVec m) : Prop :=
  ∀ t i, output t i ≠ 0 → ∃ s < t, G (query s) i ≠ 0

/-- Query part of the sequential-discovery lemma. -/
theorem sequential_query_discovery {m : ℕ} {G : EVec m → EVec m}
    {query : ℕ → EVec m} (hG : IsFirstOrderZeroChain G)
    (hq : QueriesAreZeroRespecting G query) (t : ℕ) :
    SupportedBelow t (query t) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro i hti
      by_contra hne
      obtain ⟨s, hst, hresponse⟩ := hq t i hne
      have hquery : SupportedBelow s (query s) := ih s hst
      have hnext : SupportedBelow (s + 1) (G (query s)) := hG s (query s) hquery
      have hsit : s + 1 ≤ i.1 := (Nat.succ_le_of_lt hst).trans hti
      exact hresponse (hnext i hsit)

/-- Full sequential-discovery lemma, including the returned point as required
by the tightened output model in the article. -/
theorem sequential_output_discovery {m : ℕ} {G : EVec m → EVec m}
    {query output : ℕ → EVec m} (hG : IsFirstOrderZeroChain G)
    (hq : QueriesAreZeroRespecting G query)
    (ho : OutputsAreZeroRespecting G query output) (t : ℕ) :
    SupportedBelow t (output t) := by
  intro i hti
  by_contra hne
  obtain ⟨s, hst, hresponse⟩ := ho t i hne
  have hquery : SupportedBelow s (query s) := sequential_query_discovery hG hq s
  have hnext : SupportedBelow (s + 1) (G (query s)) := hG s (query s) hquery
  have hsit : s + 1 ≤ i.1 := (Nat.succ_le_of_lt hst).trans hti
  exact hresponse (hnext i hsit)

end NCPLVerification
