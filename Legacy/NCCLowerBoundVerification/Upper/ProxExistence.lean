import NCCLowerBoundVerification.Upper.MoreauEnvelope
import NCCLowerBoundVerification.DiameterBall

/-!
# Existence of the paper's proximal points

The Moreau-envelope development uses `HasProxEverywhere` as a clean local
interface.  Here we discharge that interface on a nonempty closed Euclidean
domain whenever the value is continuous on the domain and bounded below.
The proof minimizes on a sufficiently large compact ball and then proves that
the compact minimizer is global.
-/

namespace NCCLowerBoundVerification
namespace Upper

noncomputable section

/-- The ambient sup norm of the finite function type is bounded by the
coordinate Euclidean norm used throughout the paper. -/
theorem norm_le_sqrt_vecSq {m : Nat} (x : EVec m) :
    ‖x‖ ≤ Real.sqrt (vecSq x) := by
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
  intro i
  have hi : (x i) ^ 2 ≤ vecSq x := by
    unfold vecSq NCPLVerification.vecSq
    exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
  have hs0 := Real.sqrt_nonneg (vecSq x)
  have hs2 := Real.sq_sqrt (vecSq_nonneg x)
  have habs : |x i| ≤ Real.sqrt (vecSq x) := by
    nlinarith [sq_abs (x i), abs_nonneg (x i)]
  simpa only [Real.norm_eq_abs] using habs

/-- A continuous lower-bounded function on a nonempty closed finite-
dimensional domain has a minimizer after adding any positive proximal
quadratic. -/
theorem exists_proxPoint_of_continuousOn_bddBelow {m : Nat}
    {X : Set (EVec m)} {phi : EVec m → ℝ} {ell lower : ℝ}
    (hXne : X.Nonempty) (hXclosed : IsClosed X) (hell : 0 < ell)
    (hphi : ContinuousOn phi X)
    (hlower : ∀ x ∈ X, lower ≤ phi x) (z : EVec m) :
    ∃ u, IsProxPoint X phi ell z u := by
  obtain ⟨x0, hx0⟩ := hXne
  let R2 : ℝ := vecSq (x0 - z) + (phi x0 - lower + 1) / ell
  have hgap0 : 0 ≤ phi x0 - lower := sub_nonneg.mpr (hlower x0 hx0)
  have hR2 : 0 ≤ R2 := by
    dsimp [R2]
    exact add_nonneg (vecSq_nonneg _) (div_nonneg (by linarith) hell.le)
  let K : Set (EVec m) := Metric.closedBall z (Real.sqrt R2) ∩ X
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact (isCompact_closedBall z (Real.sqrt R2)).inter_right hXclosed
  have hx0ball : x0 ∈ Metric.closedBall z (Real.sqrt R2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hvec : vecSq (x0 - z) ≤ R2 := by
      dsimp [R2]
      exact le_add_of_nonneg_right (div_nonneg (by linarith) hell.le)
    exact (norm_le_sqrt_vecSq (x0 - z)).trans
      (Real.sqrt_le_sqrt hvec)
  have hKne : K.Nonempty := ⟨x0, hx0ball, hx0⟩
  have hquad : Continuous (fun u : EVec m => ell * vecSq (u - z)) := by
    exact continuous_const.mul
      (continuous_vecSq.comp (continuous_id.sub continuous_const))
  have hobj : ContinuousOn (proxObjective phi ell z) X := by
    intro u hu
    unfold proxObjective
    exact (hphi u hu).add hquad.continuousWithinAt
  obtain ⟨u, huK, hminK⟩ := hKcompact.exists_isMinOn hKne
    (hobj.mono fun _ h => h.2)
  refine ⟨u, huK.2, ?_⟩
  intro v hv
  by_cases hvball : v ∈ Metric.closedBall z (Real.sqrt R2)
  · exact hminK ⟨hvball, hv⟩
  · have hdist : Real.sqrt R2 < dist v z := by
      simpa [Metric.mem_closedBall] using hvball
    have hnorm : ‖v - z‖ ≤ Real.sqrt (vecSq (v - z)) :=
      norm_le_sqrt_vecSq (v - z)
    have hsqrtlt : Real.sqrt R2 < Real.sqrt (vecSq (v - z)) := by
      rw [dist_eq_norm] at hdist
      exact hdist.trans_le hnorm
    have hvsq : R2 < vecSq (v - z) := by
      have hsR := Real.sq_sqrt hR2
      have hsv := Real.sq_sqrt (vecSq_nonneg (v - z))
      nlinarith [Real.sqrt_nonneg R2, Real.sqrt_nonneg (vecSq (v - z))]
    have hx0min : proxObjective phi ell z u ≤ proxObjective phi ell z x0 :=
      hminK ⟨hx0ball, hx0⟩
    have hvlarge : proxObjective phi ell z x0 < proxObjective phi ell z v := by
      have hvlow := hlower v hv
      unfold proxObjective
      dsimp [R2] at hvsq
      have hmul := mul_lt_mul_of_pos_left hvsq hell
      field_simp [ne_of_gt hell] at hmul
      nlinarith
    exact hx0min.trans hvlarge.le

/-- The preceding compactness argument supplies the global interface used by
the Moreau modules. -/
theorem hasProxEverywhere_of_continuousOn_bddBelow {m : Nat}
    {X : Set (EVec m)} {phi : EVec m → ℝ} {ell lower : ℝ}
    (hXne : X.Nonempty) (hXclosed : IsClosed X) (hell : 0 < ell)
    (hphi : ContinuousOn phi X)
    (hlower : ∀ x ∈ X, lower ≤ phi x) :
    HasProxEverywhere X phi ell := by
  intro z
  exact exists_proxPoint_of_continuousOn_bddBelow
    hXne hXclosed hell hphi hlower z

end

end Upper
end NCCLowerBoundVerification
