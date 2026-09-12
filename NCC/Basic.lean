import Mathlib.Data.Real.Basic
import Lean.Elab.Tactic.Omega

/-!
# Initial definitions for the current NC-C manuscript

This project is a partial formalization. The main complexity theorems of the
manuscript are not claimed here. See `STATUS.md` for the precise boundary.
-/

namespace NCC

/-- Integer admissibility from `cond:unscaled`; the real diameter is separate. -/
def Admissible (M N : ℕ) : Prop := 1 ≤ M ∧ 10 ≤ N

/-- Number of coordinates in the saddle zero-chain. -/
def chainLength (M N : ℕ) : ℕ := M * (N + 3)

theorem chainLength_pos {M N : ℕ} (h : Admissible M N) :
    0 < chainLength M N := by
  rcases h with ⟨hM, hN⟩
  unfold chainLength
  exact Nat.mul_pos (by omega) (by omega)

/-- A query contains feasibility proofs, rather than just ambient coordinates.
No claim about a particular oracle or its derivatives is built into this type. -/
structure FeasibleQuery {X Y : Type*} (primal : Set X) (dual : Set Y) where
  x : X
  y : Y
  x_mem : x ∈ primal
  y_mem : y ∈ dual

end NCC
