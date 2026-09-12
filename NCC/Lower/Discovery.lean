import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic.Omega

/-!
# The finite coordinate-discovery induction

This file proves the combinatorial implication used in `prop:saddle-zero-chain`
and `thm:zr-lower`. Coordinates are numbered from zero in Lean.

The oracle field is an abstract function. Proving that the gradient of the
manuscript's explicit objective satisfies `IsZeroChain` is a separate task.
Likewise, the terminal obstruction below is an explicit hypothesis, not a
proof of the analytic certificate or of the resisting-oracle construction.
-/

namespace NCC.Lower

abbrev CoordinatePoint (d : ℕ) := Fin d → ℝ

/-- Coordinates at positions `k, k+1, ...` vanish. -/
def SupportedThrough {d : ℕ} (x : CoordinatePoint d) (k : ℕ) : Prop :=
  ∀ i, k ≤ i.val → x i = 0

/-- One application of the oracle exposes at most one new coordinate. -/
def IsZeroChain {d : ℕ} (oracle : CoordinatePoint d → CoordinatePoint d) : Prop :=
  ∀ k x, SupportedThrough x k → SupportedThrough (oracle x) (k + 1)

/-- A coordinate can be queried only after appearing in an earlier reply.
For `t = 0` this definition forces the initial query to be zero. -/
def IsZeroRespecting {d : ℕ}
    (oracle : CoordinatePoint d → CoordinatePoint d)
    (query : ℕ → CoordinatePoint d) : Prop :=
  ∀ t i, (∀ s, s < t → oracle (query s) i = 0) → query t i = 0

theorem supportedThrough_of_zeroRespecting {d : ℕ}
    {oracle : CoordinatePoint d → CoordinatePoint d}
    {query : ℕ → CoordinatePoint d}
    (hchain : IsZeroChain oracle) (hrespect : IsZeroRespecting oracle query) :
    ∀ t, SupportedThrough (query t) t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      intro i hi
      apply hrespect t i
      intro s hs
      exact hchain s (query s) (ih s hs) i (by omega)

/-- The final coordinate stays zero before the full chain length. -/
theorem terminal_coordinate_zero {d : ℕ}
    {oracle : CoordinatePoint d → CoordinatePoint d}
    {query : ℕ → CoordinatePoint d}
    (hchain : IsZeroChain oracle) (hrespect : IsZeroRespecting oracle query)
    (terminal : Fin d) (hlast : terminal.val + 1 = d)
    {t : ℕ} (ht : t < d) : query t terminal = 0 := by
  exact supportedThrough_of_zeroRespecting hchain hrespect t terminal (by omega)

/-- Conditional finite-query obstruction. This is not the paper's complete
complexity theorem: the analytic and oracle hypotheses remain explicit. -/
theorem no_stationarity_before_terminal {d : ℕ}
    {oracle : CoordinatePoint d → CoordinatePoint d}
    {query : ℕ → CoordinatePoint d}
    (hchain : IsZeroChain oracle) (hrespect : IsZeroRespecting oracle query)
    (terminal : Fin d) (hlast : terminal.val + 1 = d)
    (stationary : CoordinatePoint d → Prop)
    (hobstruction : ∀ x, x terminal = 0 → ¬stationary x)
    {t : ℕ} (ht : t < d) : ¬stationary (query t) := by
  exact hobstruction (query t)
    (terminal_coordinate_zero hchain hrespect terminal hlast ht)

end NCC.Lower
