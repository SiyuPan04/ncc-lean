import NCCLowerBoundVerification.Basic
import NCPLVerification.ZeroChain

/-!
# Saddle zero-chains and queried-iterate lower bounds

This module formalizes Definition `def:saddle-chain`, Lemma
`lem:sequential-discovery`, and Lemma `lem:chain-criterion` from
`Upper+Lower_unified_lower.tex`.

The paper first fixes an order `q` on the joint primal--dual coordinates.  We
work after applying that permutation, so `Fin d` is precisely the ordered
coordinate list.  In these coordinates the saddle field is
`(gradX f, -gradY f)`; all discovery arguments depend only on this field.
-/

namespace NCCLowerBoundVerification

noncomputable section

/-- Support is contained in the first `k` coordinates of the fixed joint
coordinate order.  This is the zero-based form of `supp_q(z) ⊆ [k]`. -/
abbrev SupportedInPrefix {d : Nat} (k : Nat) (z : EVec d) : Prop :=
  NCPLVerification.SupportedBelow k z

theorem supportedInPrefix_zero (d k : Nat) :
    SupportedInPrefix k (0 : EVec d) :=
  NCPLVerification.supportedBelow_zero d k

theorem SupportedInPrefix.mono {d a b : Nat} {z : EVec d}
    (h : SupportedInPrefix a z) (hab : a ≤ b) : SupportedInPrefix b z :=
  NCPLVerification.SupportedBelow.mono h hab

/-- Definition `def:saddle-chain`, after reindexing the ordered joint
coordinates by `Fin d`.  Only prefixes strictly shorter than the finite
coordinate list occur in the paper's definition. -/
def IsFirstOrderSaddleZeroChain {d : Nat} (G : EVec d → EVec d) : Prop :=
  ∀ k, k < d → ∀ z,
    SupportedInPrefix k z → SupportedInPrefix (k + 1) (G z)

/-- The unrestricted zero-chain definition from the NC--PL development
implies the finite saddle-chain condition used here. -/
theorem isFirstOrderSaddleZeroChain_of_global {d : Nat} {G : EVec d → EVec d}
    (hG : NCPLVerification.IsFirstOrderZeroChain G) :
    IsFirstOrderSaddleZeroChain G := by
  intro k _ z hz
  exact hG k z hz

/-- A finite prefix of a query trajectory is zero-respecting when every
nonzero queried coordinate has already appeared in a strictly earlier saddle
oracle response.  At `t = 0` this forces the full joint query to be zero. -/
def FiniteQueriesAreZeroRespecting {d : Nat} (G : EVec d → EVec d)
    (query : Nat → EVec d) (horizon : Nat) : Prop :=
  ∀ t, t < horizon → ∀ i, query t i ≠ 0 →
    ∃ s, s < t ∧ G (query s) i ≠ 0

/-- A global zero-respecting trajectory is zero-respecting on each finite
query prefix. -/
theorem finiteQueriesAreZeroRespecting_of_global {d horizon : Nat}
    {G : EVec d → EVec d} {query : Nat → EVec d}
    (hq : NCPLVerification.QueriesAreZeroRespecting G query) :
    FiniteQueriesAreZeroRespecting G query horizon := by
  intro t _ i hti
  exact hq t i hti

/-- Lemma `lem:sequential-discovery`: before query `t`, a zero-respecting
trajectory can use only the first `t` coordinates in the chosen saddle-chain
order.  The bounds `t < horizon` and `t ≤ d` make the finite-query and
finite-coordinate scopes explicit. -/
theorem sequential_discovery {d horizon : Nat} {G : EVec d → EVec d}
    {query : Nat → EVec d} (hG : IsFirstOrderSaddleZeroChain G)
    (hq : FiniteQueriesAreZeroRespecting G query horizon) :
    ∀ t, t < horizon → t ≤ d → SupportedInPrefix t (query t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro htH htd i hit
      by_contra hne
      obtain ⟨s, hst, hresponse⟩ := hq t htH i hne
      have hsH : s < horizon := hst.trans htH
      have hsd : s < d := hst.trans_le htd
      have hquery : SupportedInPrefix s (query s) :=
        ih s hst hsH hsd.le
      have hnext : SupportedInPrefix (s + 1) (G (query s)) :=
        hG s hsd (query s) hquery
      have hsit : s + 1 ≤ i.1 := (Nat.succ_le_of_lt hst).trans hit
      exact hresponse (hnext i hsit)

/-- In a coordinate list of length `d + 1`, its last coordinate is still zero
at every query made before all `d + 1` coordinates have been discovered. -/
theorem final_coordinate_zero_before_full_discovery {d horizon : Nat}
    {G : EVec (d + 1) → EVec (d + 1)} {query : Nat → EVec (d + 1)}
    (hG : IsFirstOrderSaddleZeroChain G)
    (hq : FiniteQueriesAreZeroRespecting G query horizon)
    {t : Nat} (htH : t < horizon) (htd : t < d + 1) :
    query t (Fin.last d) = 0 := by
  have hsupp : SupportedInPrefix t (query t) :=
    sequential_discovery hG hq t htH htd.le
  exact hsupp (Fin.last d) (by simpa using htd)

/-- `QueriedIterateHittingTimeAtLeast query primal IsStationary K` is the
finite, exact version of the paper's statement that the first stationary
*queried* primal iterate has hitting time at least `K`.  It deliberately does
not count an unqueried output produced after seeing the transcript. -/
def QueriedIterateHittingTimeAtLeast {d : Nat} {Primal : Type*}
    (query : Nat → EVec d) (primal : EVec d → Primal)
    (IsStationary : Primal → Prop) (K : Nat) : Prop :=
  ∀ t, t < K → ¬ IsStationary (primal (query t))

/-- Lemma `lem:chain-criterion`, stated for an arbitrary feasibility predicate
and an arbitrary primal stationarity predicate (in the application, the
latter is `epsilon`-optimization stationarity).  If every feasible point whose
final ordered coordinate is at most `r` fails stationarity, then no one of the
first `d + 1` queried primal iterates can be stationary. -/
theorem queried_iterate_lower_bound_of_zero_chain
    {d : Nat} {Primal : Type*}
    {G : EVec (d + 1) → EVec (d + 1)}
    {query : Nat → EVec (d + 1)}
    {primal : EVec (d + 1) → Primal}
    {Feasible : EVec (d + 1) → Prop}
    {IsStationary : Primal → Prop} {r : ℝ}
    (hG : IsFirstOrderSaddleZeroChain G)
    (hq : FiniteQueriesAreZeroRespecting G query (d + 1))
    (hfeasible : ∀ t, t < d + 1 → Feasible (query t))
    (hr : 0 ≤ r)
    (hfailure : ∀ z, Feasible z → z (Fin.last d) ≤ r →
      ¬ IsStationary (primal z)) :
    QueriedIterateHittingTimeAtLeast query primal IsStationary (d + 1) := by
  intro t htd
  apply hfailure (query t) (hfeasible t htd)
  rw [final_coordinate_zero_before_full_discovery hG hq htd htd]
  exact hr

end

end NCCLowerBoundVerification
