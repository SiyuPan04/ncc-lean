import NCC.Extensions.NCSC

/-!
# Actual NC-SC Moreau envelope on unbounded dual domains

The maximum is attained by strong dual coercivity. Lower semicontinuity of
the resulting value is enough for primal proximal existence; no compact dual
set or unproved continuity/VI certificate is needed. All derivatives below
are full derivatives of the actual infimum envelope.
-/

namespace NCC.Extensions.NCSC

noncomputable section

open NCCLowerBoundVerification NCCLowerBoundVerification.Upper
open scoped Topology

/-- Lower semicontinuity suffices in the compact-ball proximal existence
argument. This generalization has no assumption on an inner maximizer. -/
theorem exists_prox_of_lowerSemicontinuousOn {d : ℕ}
    {X : Set (EVec d)} {phi : EVec d → ℝ} {ell lower : ℝ}
    (hXne : X.Nonempty) (hXclosed : IsClosed X) (hell : 0 < ell)
    (hphi : LowerSemicontinuousOn phi X) (hlower : ∀ x ∈ X, lower ≤ phi x)
    (z : EVec d) : ∃ u, IsProxPoint X phi ell z u := by
  obtain ⟨x0, hx0⟩ := hXne
  let R2 : ℝ := vecSq (x0 - z) + (phi x0 - lower + 1) / ell
  have hgap0 : 0 ≤ phi x0 - lower := sub_nonneg.mpr (hlower x0 hx0)
  have hR2 : 0 ≤ R2 := by
    dsimp [R2]
    exact add_nonneg (vecSq_nonneg _) (div_nonneg (by linarith) hell.le)
  let K : Set (EVec d) := Metric.closedBall z (Real.sqrt R2) ∩ X
  have hKcompact : IsCompact K :=
    (isCompact_closedBall z (Real.sqrt R2)).inter_right hXclosed
  have hx0ball : x0 ∈ Metric.closedBall z (Real.sqrt R2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hvec : vecSq (x0 - z) ≤ R2 := by
      dsimp [R2]
      exact le_add_of_nonneg_right (div_nonneg (by linarith) hell.le)
    exact (norm_le_sqrt_vecSq (x0 - z)).trans (Real.sqrt_le_sqrt hvec)
  have hKne : K.Nonempty := ⟨x0, hx0ball, hx0⟩
  have hquad : Continuous (fun u : EVec d => ell * vecSq (u - z)) :=
    continuous_const.mul (continuous_vecSq.comp (continuous_id.sub continuous_const))
  have hobj : LowerSemicontinuousOn (proxObjective phi ell z) X :=
    hphi.add hquad.continuousOn.lowerSemicontinuousOn
  obtain ⟨u, huK, hminK⟩ := LowerSemicontinuousOn.exists_isMinOn hKne hKcompact
    (hobj.mono fun _ h => h.2)
  refine ⟨u, huK.2, ?_⟩
  intro v hv
  by_cases hvball : v ∈ Metric.closedBall z (Real.sqrt R2)
  · exact hminK ⟨hvball, hv⟩
  · have hdist : Real.sqrt R2 < dist v z := by simpa [Metric.mem_closedBall] using hvball
    have hsqrtlt : Real.sqrt R2 < Real.sqrt (vecSq (v - z)) := by
      rw [dist_eq_norm] at hdist
      exact hdist.trans_le (norm_le_sqrt_vecSq (v - z))
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
      field_simp [hell.ne'] at hmul
      nlinarith
    exact hx0min.trans hvlarge.le

variable {m n : ℕ} {ell mu Delta : ℝ} {P : NCCInstance m n}

theorem value_lowerSemicontinuousOn (h : NCSCClass ell mu Delta P) :
    LowerSemicontinuousOn (ValueOn P.Y P.f) P.X := by
  intro x hx a ha
  obtain ⟨y, hy⟩ := maximum_attained h hx
  have ha' : a < P.f x y := by rwa [value_eq_of_isMaximizerOn hy] at ha
  have hf := (Model.hasFDerivWithinAt_section h.gradient_representation hx hy.1).continuousWithinAt
  have he : ∀ᶠ u in 𝓝[P.X] x, a < P.f u y := hf.eventually (lt_mem_nhds ha')
  filter_upwards [he, self_mem_nhdsWithin] with u hau hu
  obtain ⟨v, hv⟩ := maximum_attained h hu
  rw [value_eq_of_isMaximizerOn hv]
  exact hau.trans_le (hv.2 y hy.1)

theorem value_weaklyConvex (h : NCSCClass ell mu Delta P) :
    IsWeaklyConvexOn ell P.X (ValueOn P.Y P.f) :=
  value_weaklyConvexOn_of_sections h.X_convex
    (fun _ hx => maximum_attained h hx)
    (fun _ hy => Model.section_weaklyConvex_of_within h.ell_pos h.X_convex
      h.gradient_representation h.jointly_smooth hy)

theorem prox_exists_with_parameter (h : NCSCClass ell mu Delta P)
    {rho : ℝ} (hrho : 0 < rho) :
    HasProxEverywhere P.X (ValueOn P.Y P.f) rho := by
  apply exists_prox_of_lowerSemicontinuousOn ⟨0, h.primal_origin⟩ h.X_closed hrho
    (value_lowerSemicontinuousOn h)
    (lower := ValueOn P.Y P.f 0 - Delta)
  intro x hx
  linarith [h.initial_gap_pointwise x hx]

theorem prox_exists (h : NCSCClass ell mu Delta P) :
    HasProxEverywhere P.X (ValueOn P.Y P.f) ell := prox_exists_with_parameter h h.ell_pos

def prox (h : NCSCClass ell mu Delta P) (z : EVec m) : EVec m :=
  selectedProx (prox_exists h) z

def envelope (h : NCSCClass ell mu Delta P) (z : EVec m) : ℝ :=
  moreauEnvelope (ValueOn P.Y P.f) ell (prox_exists h) z

def gradient (h : NCSCClass ell mu Delta P) (z : EVec m) : EVec m :=
  residualGradient (prox_exists h) z

theorem prox_spec (h : NCSCClass ell mu Delta P) (z : EVec m) :
    IsProxPoint P.X (ValueOn P.Y P.f) ell z (prox h z) := selectedProx_spec (prox_exists h) z

theorem prox_unique (h : NCSCClass ell mu Delta P) {z u : EVec m}
    (hu : IsProxPoint P.X (ValueOn P.Y P.f) ell z u) : prox h z = u :=
  selectedProx_unique h.ell_pos (value_weaklyConvex h) (prox_exists h) hu

theorem envelope_eq_inf (h : NCSCClass ell mu Delta P) (z : EVec m) :
    envelope h z = sInf ((proxObjective (ValueOn P.Y P.f) ell z) '' P.X) := by
  have hp := prox_spec h z
  have hmember : envelope h z ∈ (proxObjective (ValueOn P.Y P.f) ell z) '' P.X :=
    ⟨prox h z, hp.1, rfl⟩
  have hlower : ∀ a ∈ (proxObjective (ValueOn P.Y P.f) ell z) '' P.X, envelope h z ≤ a := by
    rintro _ ⟨v, hv, rfl⟩
    exact hp.2 v hv
  exact le_antisymm (le_csInf ⟨envelope h z, hmember⟩ hlower)
    (csInf_le ⟨envelope h z, hlower⟩ hmember)

theorem gradient_formula (h : NCSCClass ell mu Delta P) (z : EVec m) :
    gradient h z = (2 * ell) • (z - prox h z) := rfl

theorem hasFDerivAt_envelope (h : NCSCClass ell mu Delta P) (z : EVec m) :
    HasFDerivAt (envelope h) (residualCLM (gradient h z)) z :=
  hasFDerivAt_moreauEnvelope h.ell_pos (value_weaklyConvex h) (prox_exists h) z

theorem gradient_lipschitz_sq (h : NCSCClass ell mu Delta P) (z w : EVec m) :
    vecSq (gradient h z - gradient h w) ≤ (2 * ell) ^ 2 * vecSq (z - w) :=
  residualGradient_lipschitz_sq h.ell_pos (value_weaklyConvex h) (prox_exists h) z w

def IsOS (h : NCSCClass ell mu Delta P) (eps : ℝ) (z : EVec m) : Prop :=
  0 < eps ∧ z ∈ P.X ∧ vecSq (gradient h z) ≤ eps ^ 2

theorem isOS_iff_feasible_prox (h : NCSCClass ell mu Delta P) (eps : ℝ) (z : EVec m) :
    IsOS h eps z ↔ 0 < eps ∧ z ∈ P.X ∧
      IsOptimizationStationary P.X (ValueOn P.Y P.f) ell eps z := by
  have hc : 0 < (2 * ell) ^ 2 := sq_pos_of_pos (by linarith [h.ell_pos])
  have heq : vecSq (gradient h z) = (2 * ell) ^ 2 * vecSq (prox h z - z) := by
    rw [gradient_formula, vecSq_smul, vecSq_sub_comm]
  unfold IsOS
  rw [heq]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro hg
    refine ⟨prox h z, prox_spec h z, ?_⟩
    have hd : vecSq (prox h z - z) ≤ eps ^ 2 / (2 * ell) ^ 2 :=
      (le_div_iff₀ hc).2 (by nlinarith [hg])
    simpa only [div_pow] using hd
  · rintro ⟨u, hu, hd⟩
    rw [← prox_unique h hu] at hd
    have hm := mul_le_mul_of_nonneg_left hd hc.le
    have hcancel : (2 * ell) ^ 2 * (eps / (2 * ell)) ^ 2 = eps ^ 2 := by
      field_simp [h.ell_pos.ne']
    rwa [hcancel] at hm

end

end NCC.Extensions.NCSC
