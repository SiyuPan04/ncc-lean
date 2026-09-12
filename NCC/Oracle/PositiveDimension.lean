import NCC.Lower.DeterministicLower
import NCC.Upper.Theorem

/-!
# The manuscript's positive-dimensional minimax quantity

The source distinguishes positive `N` from `N₀`; both primal and dual
dimensions in its class are positive. Algorithms here have components
only for those domain labels. Extending a family to zero dimensions does
not change any source-domain component. The older unrestricted quantity
is retained only as a helper for transferring the upper bound.
-/
namespace NCC.Complexity.PositiveDimension
noncomputable section
open NCCLowerBoundVerification
open scoped ENNReal

abbrev Domain := {Q : Oracle.AdmissibleDomainPair // 0 < Q.m ∧ 0 < Q.n}

/-- Only known positive-dimensional domains index the causal query rules. -/
structure Algorithm where
  component : (Q : Domain) → Oracle.DeterministicFOComponent Q.val.X Q.val.Y

def restrictAlgorithm (A : Oracle.DomainWiseDeterministicAlgorithm) : Algorithm where
  component Q := A.component Q.val

/-- No objective is consulted when extending a source-domain algorithm
to the unused zero-dimensional labels. -/
def extendAlgorithm (A : Algorithm) : Oracle.DomainWiseDeterministicAlgorithm where
  component Q := by
    classical
    exact if h : 0 < Q.m ∧ 0 < Q.n then A.component ⟨Q, h⟩ else {
      nextQuery := fun _ _ => (0, 0)
      next_mem := fun _ _ => ⟨Q.zero_mem_X, Q.zero_mem_Y⟩
      initial_query := rfl }

theorem extendAlgorithm_component (A : Algorithm) (Q : Domain) :
    (extendAlgorithm A).component Q.val = A.component Q := by
  dsimp only [extendAlgorithm]
  rw [dif_pos Q.property]

theorem restrict_extend (A : Algorithm) : restrictAlgorithm (extendAlgorithm A) = A := by
  cases A with
  | mk component =>
      unfold restrictAlgorithm
      congr 1
      funext Q
      exact extendAlgorithm_component ⟨component⟩ Q

def worstCaseHittingTime (A : Algorithm) (ell D Delta eps : ℝ) : WithTop ℕ :=
  ⨆ Q : Domain,
    ⨆ P : {P : NCCInstance Q.val.m Q.val.n // WithinDomainMember ell D Delta Q.val P},
      Oracle.queriedHittingTime (A.component Q) P.val ell eps

def minimaxHittingTime (ell D Delta eps : ℝ) : WithTop ℕ :=
  ⨅ A : Algorithm, worstCaseHittingTime A ell D Delta eps

def minimaxOracleComplexity (ell D Delta eps : ℝ) : ℝ≥0∞ :=
  ENat.toENNReal (minimaxHittingTime ell D Delta eps)

set_option backward.isDefEq.respectTransparency false in
theorem minimaxOracleComplexity_eq (ell D Delta eps : ℝ) :
    minimaxOracleComplexity ell D Delta eps =
      ⨅ A : Algorithm, ⨆ Q : Domain,
        ⨆ P : {P : NCCInstance Q.val.m Q.val.n // WithinDomainMember ell D Delta Q.val P},
          ENat.toENNReal (Oracle.queriedHittingTime (A.component Q) P.val ell eps) := by
  change ENat.toENNReal
    (⨅ A : Algorithm, ⨆ Q : Domain,
      ⨆ P : {P : NCCInstance Q.val.m Q.val.n // WithinDomainMember ell D Delta Q.val P},
        (Oracle.queriedHittingTime (A.component Q) P.val ell eps : ℕ∞)) = _
  simp only [ENat.toENNReal_iInf, ENat.toENNReal_iSup]

theorem queriedHittingTime_lt_iff_actualOS {ell D Delta eps : ℝ} (heps : 0 < eps)
    (A : Algorithm) (Q : Domain) (P : NCCInstance Q.val.m Q.val.n)
    (hP : WithinDomainMember ell D Delta Q.val P) (K : ℕ) :
    Oracle.queriedHittingTime (A.component Q) P ell eps < (K : WithTop ℕ) ↔
      ∃ t < K, Moreau.Within.IsOS hP.2.2 eps ((A.component Q).queriedAt P t).1 := by
  have h := NCC.Complexity.queriedHittingTime_lt_iff_actualOS heps
    (extendAlgorithm A) Q.val P hP K
  rwa [extendAlgorithm_component] at h

/-- Restricting the larger class transfers its upper bound in the correct
direction; no equality of the two minimax quantities is assumed. -/
theorem minimaxHittingTime_le_enlarged (ell D Delta eps : ℝ) :
    minimaxHittingTime ell D Delta eps ≤ NCC.Complexity.minimaxHittingTime ell D Delta eps := by
  apply le_iInf
  intro A
  apply (iInf_le _ (restrictAlgorithm A)).trans
  apply iSup_le
  intro Q
  apply iSup_le
  intro P
  exact le_iSup_of_le Q.val (le_iSup_of_le P le_rfl)

theorem minimaxOracleComplexity_le_enlarged (ell D Delta eps : ℝ) :
    minimaxOracleComplexity ell D Delta eps ≤
      NCC.Complexity.minimaxOracleComplexity ell D Delta eps :=
  ENat.toENNReal_mono (minimaxHittingTime_le_enlarged ell D Delta eps)

/-- Every source-domain algorithm has a genuine hard member in positive
dimensions. The instance may depend on the algorithm, as in the source. -/
theorem minimaxHittingTime_lower {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ Lower.Parameters.c0 Lower.Certificates.constants *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    (Lower.DeterministicLower.horizon ell D Delta eps : WithTop ℕ) ≤
      minimaxHittingTime ell D Delta eps := by
  apply le_iInf
  intro A
  let Q : Domain := ⟨Lower.DeterministicLower.domain ell D Delta eps hD.le,
    Lower.DeterministicLower.dimensions_positive ell D Delta eps⟩
  obtain ⟨P, hP, _hPA, hPX, hPY, _hinit, _hfail, htime, _hOS⟩ :=
    Lower.DeterministicLower.exists_current_hard_instance hell hD hDelta heps hacc
      (A.component Q)
  have hm : WithinDomainMember ell D Delta Q.val P := ⟨hPX, hPY, hP⟩
  exact le_iSup_of_le Q (le_iSup_of_le ⟨P, hm⟩ htime)

theorem oracleComplexity_lower {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ Lower.Parameters.c0 Lower.Certificates.constants *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    ENNReal.ofReal (Lower.Parameters.c1 Lower.Certificates.constants *
      (ell ^ 2 * D * Delta / eps ^ 3)) ≤ minimaxOracleComplexity ell D Delta eps := by
  have hreal := Lower.DeterministicLower.horizon_lower hell hD hDelta heps hacc
  have hnat := ENat.toENNReal_mono (minimaxHittingTime_lower hell hD hDelta heps hacc)
  calc
    _ ≤ ENNReal.ofReal (Lower.DeterministicLower.horizon ell D Delta eps : ℝ) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = (Lower.DeterministicLower.horizon ell D Delta eps : ℝ≥0∞) := by simp
    _ ≤ _ := hnat

theorem oracleComplexity_upper {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps) :
    minimaxOracleComplexity ell D Delta eps ≤
      ENNReal.ofReal ((Upper.CurrentCost.traceRateConstant + 3) *
        Upper.Theorem.uniformRate ell D Delta eps) :=
  (minimaxOracleComplexity_le_enlarged ell D Delta eps).trans
    (Upper.Theorem.minimaxOracleComplexity_upper hell hD hDelta heps)

/-- Both bounds concern precisely the positive-dimensional source union. -/
theorem oracleComplexity_bounds {ell D Delta eps : ℝ}
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hacc : eps ≤ Lower.Parameters.c0 Lower.Certificates.constants *
      min (ell * D) (Real.sqrt (ell * Delta))) :
    ENNReal.ofReal (Lower.Parameters.c1 Lower.Certificates.constants *
      (ell ^ 2 * D * Delta / eps ^ 3)) ≤ minimaxOracleComplexity ell D Delta eps ∧
    minimaxOracleComplexity ell D Delta eps ≤
      ENNReal.ofReal ((Upper.CurrentCost.traceRateConstant + 3) *
        Upper.Theorem.uniformRate ell D Delta eps) :=
  ⟨oracleComplexity_lower hell hD hDelta heps hacc,
    oracleComplexity_upper hell hD hDelta heps⟩

end
end NCC.Complexity.PositiveDimension
