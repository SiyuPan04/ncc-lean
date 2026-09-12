import NCC.Lower.Membership
import NCC.Lower.Parameters
import NCC.Construction.Terminal
import NCC.Construction.ZeroChain
import NCC.Lower.MoreauObstruction

/-! Numerical constants and terminal certificate of the current instance. -/

namespace NCC.Lower.Certificates

noncomputable section

open NCCLowerBoundVerification NCC.Construction

def constants : Parameters.Constants where
  ell0 := Regularity.ell₀
  g0 := min Terminal.g₀ Regularity.ell₀
  cD := Terminal.c_D
  cDelta := Composite.c_Δ
  ell0_pos := Regularity.ell₀_pos
  g0_pos := lt_min Terminal.g₀_pos Regularity.ell₀_pos
  cD_pos := Terminal.c_D_pos
  cDelta_pos := Composite.c_Δ_pos
  g0_le := min_le_right _ _

def terminalIndex {m : ℕ} (hm : 0 < m) : Fin (m * 3) :=
  finProdFinEquiv (⟨m - 1, by omega⟩, ⟨0, by omega⟩)

theorem terminalIndex_state {m : ℕ} (hm : 0 < m) (x : Composite.Primal m) :
    x (terminalIndex hm) = Composite.state x ⟨m - 1, by omega⟩ := rfl

theorem value_representsGradient {m n : ℕ} (hn : 0 < n)
    {D : ℝ} (hD : 0 ≤ D) :
    RepresentsGradient (Composite.value (m := m) hn D)
      (Frontier.gradient (Composite.value hn D)) :=
  ⟨Composite.value_differentiable hn hD,
    Frontier.gradient_represents (Composite.value hn D)⟩

theorem terminal_gradient_squared {m n : ℕ} (hm : 0 < m) (hn : 10 ≤ n)
    {D : ℝ} (hD : 0 < D) (hsize : (n : ℝ) ≤ constants.cD * D)
    (x : Composite.Primal m) (hlast : x (terminalIndex hm) ≤ (1 : ℝ) / 5) :
    constants.g0 ^ 2 ≤
      vecSq (Frontier.gradient (Composite.value (by omega : 0 < n) D) x) := by
  have ht := Terminal.terminal_gradient_lower (by omega : 1 ≤ m) hn hD hsize x hlast
  have hg : constants.g0 ≤ Terminal.g₀ := min_le_left _ _
  have hsq := Frontier.norm₂_sq
    (Frontier.gradient (Composite.value (by omega : 0 < n) D) x)
  have hg0 := constants.g0_pos
  nlinarith

end

end NCC.Lower.Certificates
