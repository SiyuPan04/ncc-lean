import NCCLowerBoundVerification.Lower.MainTheorem
import NCCLowerBoundVerification.Oracle.Complexity
import NCCLowerBoundVerification.Oracle.PaperHittingComplexity

/-!
# Domain-free threshold form of the concrete lower bound

`MainTheorem` defeats a component on the canonical Euclidean domains.  Here
those domains are packaged as a label in the disjoint union over dimensions,
so the result quantifies one arbitrary domain-wise causal algorithm exactly
as the deterministic complexity definition does.
-/

namespace NCCLowerBoundVerification
namespace Lower

noncomputable section

open Oracle

/-- Explicit numerical coefficient in front of the cubic lower rate. -/
def concreteLowerRateConstant (ell0 : ℝ) : ℝ :=
  concreteTerminalC0 ell0 ^ 3 /
    (2048 * concreteCy * concreteUnscaledParameters.P1 *
      concreteCDelta * ell0 ^ 2)

theorem concreteLowerRateConstant_pos {ell0 : ℝ} (hell0 : 0 < ell0) :
    0 < concreteLowerRateConstant ell0 := by
  unfold concreteLowerRateConstant
  have hc0 := concreteTerminalC0_pos hell0
  have hcy := concreteCy_pos
  have hP1 := concreteUnscaledP1_pos
  have hdelta := concreteCDelta_pos
  positivity

/-- The domain label selected by the concrete hard dimensions. -/
def concreteHardDomainPair (ell0 ell D Delta eps : ℝ) (hD : 0 < D) :
    AdmissibleDomainPair where
  m := concreteHardDX ell0 ell D Delta eps
  n := concreteHardDY ell0 ell D Delta eps
  X := Set.univ
  Y := diameterBall (concreteHardDY ell0 ell D Delta eps) D
  zero_mem_X := Set.mem_univ 0
  zero_mem_Y := zero_mem_diameterBall _ _ hD.le
  X_closed := isClosed_univ
  X_convex := convex_univ
  Y_closed := diameterBall_closed _ _
  Y_convex := diameterBall_convex _ _

/-- The component-wise headline theorem is a genuine lower threshold for one
algorithm over the domain-labelled analytic class. -/
theorem concrete_complexityAtLeast_of_uniform_source
    {ell0 ell D Delta eps : ℝ}
    (hell0 : 0 < ell0) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ lowerAccuracyConstant ell0
      (concreteTerminalC0 ell0) concreteCy
      concreteUnscaledParameters.P1 concreteCDelta *
        min (ell * D) (Real.sqrt (ell * Delta)))
    (hsource : ∀ {T n : Nat} (hT : 1 ≤ T) (hn : 10 ≤ n)
      {D0 Delta0 : ℝ},
      0 < D0 → concreteDelta0 T ≤ Delta0 →
        ScalingSource ell0 D0 Delta0
          (unscaledNCCInstance (T := T) (n := n) (by omega)
            concreteUnscaledParameters D0)) :
    ComplexityAtLeast ell D Delta eps
      (concreteHardK ell0 ell D Delta eps) := by
  intro A
  let Q := concreteHardDomainPair ell0 ell D Delta eps hD
  obtain ⟨P, hclass, _hpaper, hfail, hX, hY, hx0, _hrate⟩ :=
    concrete_deterministic_lower_bound_of_uniform_source
      hell0 hell hD hDelta heps haccuracy hsource (A.component Q)
  refine ⟨Q, P, ?_, hfail⟩
  exact ⟨hX, hY, hx0, hclass⟩

/-- The same hard instances lie in Definition 2.1's literal
neighborhood-`C^1` class, hence establish the paper lower threshold itself. -/
theorem concrete_paperComplexityAtLeast_of_uniform_source
    {ell0 ell D Delta eps : ℝ}
    (hell0 : 0 < ell0) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ lowerAccuracyConstant ell0
      (concreteTerminalC0 ell0) concreteCy
      concreteUnscaledParameters.P1 concreteCDelta *
        min (ell * D) (Real.sqrt (ell * Delta)))
    (hsource : ∀ {T n : Nat} (hT : 1 ≤ T) (hn : 10 ≤ n)
      {D0 Delta0 : ℝ},
      0 < D0 → concreteDelta0 T ≤ Delta0 →
        ScalingSource ell0 D0 Delta0
          (unscaledNCCInstance (T := T) (n := n) (by omega)
            concreteUnscaledParameters D0)) :
    PaperComplexityAtLeast ell D Delta eps
      (concreteHardK ell0 ell D Delta eps) := by
  intro A
  let Q := concreteHardDomainPair ell0 ell D Delta eps hD
  obtain ⟨P, _hclass, hpaper, hfail, hX, hY, hx0, _hrate⟩ :=
    concrete_deterministic_lower_bound_of_uniform_source
      hell0 hell hD hDelta heps haccuracy hsource (A.component Q)
  refine ⟨Q, P, ?_, hfail⟩
  exact ⟨hX, hY, hx0, hpaper⟩

/-- In particular, the lower threshold holds for the literal measurable
algorithm class of Definition `def:det-alg`. -/
theorem concrete_measurablePaperComplexityAtLeast_of_uniform_source
    {ell0 ell D Delta eps : ℝ}
    (hell0 : 0 < ell0) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ lowerAccuracyConstant ell0
      (concreteTerminalC0 ell0) concreteCy
      concreteUnscaledParameters.P1 concreteCDelta *
        min (ell * D) (Real.sqrt (ell * Delta)))
    (hsource : ∀ {T n : Nat} (hT : 1 ≤ T) (hn : 10 ≤ n)
      {D0 Delta0 : ℝ},
      0 < D0 → concreteDelta0 T ≤ Delta0 →
        ScalingSource ell0 D0 Delta0
          (unscaledNCCInstance (T := T) (n := n) (by omega)
            concreteUnscaledParameters D0)) :
    MeasurablePaperComplexityAtLeast ell D Delta eps
      (concreteHardK ell0 ell D Delta eps) :=
  measurablePaperComplexityAtLeast_of_paperComplexityAtLeast
    (concrete_paperComplexityAtLeast_of_uniform_source
      hell0 hell hD hDelta heps haccuracy hsource)

/-- Explicit lower half of the final `Θ` statement: the measurable paper
threshold and its real-valued cubic-rate comparison hold simultaneously. -/
theorem concrete_measurablePaper_lower_rate_of_uniform_source
    {ell0 ell D Delta eps : ℝ}
    (hell0 : 0 < ell0) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ lowerAccuracyConstant ell0
      (concreteTerminalC0 ell0) concreteCy
      concreteUnscaledParameters.P1 concreteCDelta *
        min (ell * D) (Real.sqrt (ell * Delta)))
    (hsource : ∀ {T n : Nat} (hT : 1 ≤ T) (hn : 10 ≤ n)
      {D0 Delta0 : ℝ},
      0 < D0 → concreteDelta0 T ≤ Delta0 →
        ScalingSource ell0 D0 Delta0
          (unscaledNCCInstance (T := T) (n := n) (by omega)
            concreteUnscaledParameters D0)) :
    MeasurablePaperComplexityAtLeast ell D Delta eps
        (concreteHardK ell0 ell D Delta eps) ∧
      concreteLowerRateConstant ell0 *
          (ell ^ 2 * D * Delta / eps ^ 3) ≤
        (concreteHardK ell0 ell D Delta eps : ℝ) := by
  constructor
  · exact concrete_measurablePaperComplexityAtLeast_of_uniform_source
      hell0 hell hD hDelta heps haccuracy hsource
  · let A0 : DeterministicFOComponent
        (Set.univ : Set (EVec (concreteHardDX ell0 ell D Delta eps)))
        (diameterBall (concreteHardDY ell0 ell D Delta eps) D) :=
      { nextQuery := fun _ _ => (0, 0)
        next_mem := fun _ _ =>
          ⟨Set.mem_univ 0, zero_mem_diameterBall _ _ hD.le⟩
        initial_query := rfl }
    obtain ⟨_P, _hclass, _hpaper, _hfail, _hX, _hY, _hx0, hrate⟩ :=
      concrete_deterministic_lower_bound_of_uniform_source
        hell0 hell hD hDelta heps haccuracy hsource A0
    simpa [concreteLowerRateConstant] using hrate

/-- Literal infimum--supremum form of the lower bound in `thm:main`. -/
theorem concrete_lower_bound_for_paper_hitting_complexity
    {ell0 ell D Delta eps : ℝ}
    (hell0 : 0 < ell0) (hell : 0 < ell) (hD : 0 < D)
    (hDelta : 0 < Delta) (heps : 0 < eps)
    (haccuracy : eps ≤ lowerAccuracyConstant ell0
      (concreteTerminalC0 ell0) concreteCy
      concreteUnscaledParameters.P1 concreteCDelta *
        min (ell * D) (Real.sqrt (ell * Delta)))
    (hsource : ∀ {T n : Nat} (hT : 1 ≤ T) (hn : 10 ≤ n)
      {D0 Delta0 : ℝ},
      0 < D0 → concreteDelta0 T ≤ Delta0 →
        ScalingSource ell0 D0 Delta0
          (unscaledNCCInstance (T := T) (n := n) (by omega)
            concreteUnscaledParameters D0)) :
    ((concreteHardK ell0 ell D Delta eps : Nat) : WithTop Nat) ≤
      measurablePaperHittingComplexity ell D Delta eps :=
  le_measurablePaperHittingComplexity_of_atLeast
    (concrete_measurablePaperComplexityAtLeast_of_uniform_source
      hell0 hell hD hDelta heps haccuracy hsource)

end

end Lower
end NCCLowerBoundVerification
