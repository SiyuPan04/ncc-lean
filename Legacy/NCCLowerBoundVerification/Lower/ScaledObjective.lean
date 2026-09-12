import NCCLowerBoundVerification.Lower.ScalingArithmetic
import NCCLowerBoundVerification.Oracle.Model
import NCPLVerification.ZeroChain

/-!
# Functional scaling of the lower-bound instance

This file formalizes the actual change of variables in (3288)--(3410),
including derivatives, domains, values, gaps, and proximal stationarity.
-/

namespace NCCLowerBoundVerification

noncomputable section

/-- Coordinate dilation `z ↦ λz`. -/
def scaleCoords {d : Nat} (lambda : ℝ) (z : EVec d) : EVec d :=
  fun i => lambda * z i

/-- Coordinate contraction `z ↦ z/λ`. -/
def unscaleCoords {d : Nat} (lambda : ℝ) (z : EVec d) : EVec d :=
  fun i => z i / lambda

@[simp] theorem unscaleCoords_scaleCoords {d : Nat} {lambda : ℝ}
    (hlambda : lambda ≠ 0) (z : EVec d) :
    unscaleCoords lambda (scaleCoords lambda z) = z := by
  funext i
  unfold unscaleCoords scaleCoords
  field_simp [hlambda]

@[simp] theorem scaleCoords_unscaleCoords {d : Nat} {lambda : ℝ}
    (hlambda : lambda ≠ 0) (z : EVec d) :
    scaleCoords lambda (unscaleCoords lambda z) = z := by
  funext i
  unfold unscaleCoords scaleCoords
  field_simp [hlambda]

theorem scaleCoords_sub {d : Nat} (lambda : ℝ) (u v : EVec d) :
    scaleCoords lambda (u - v) =
      scaleCoords lambda u - scaleCoords lambda v := by
  funext i
  simp [scaleCoords]
  ring

theorem unscaleCoords_sub {d : Nat} (lambda : ℝ) (u v : EVec d) :
    unscaleCoords lambda (u - v) =
      unscaleCoords lambda u - unscaleCoords lambda v := by
  funext i
  simp [unscaleCoords]
  ring

theorem vecSq_scaleCoords {d : Nat} (lambda : ℝ) (z : EVec d) :
    vecSq (scaleCoords lambda z) = lambda ^ 2 * vecSq z := by
  unfold vecSq NCPLVerification.vecSq scaleCoords
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem vecSq_unscaleCoords {d : Nat} (lambda : ℝ) (z : EVec d) :
    vecSq (unscaleCoords lambda z) = (1 / lambda) ^ 2 * vecSq z := by
  unfold vecSq NCPLVerification.vecSq unscaleCoords
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Scaled preimage of a feasible set. -/
def scaledDomain {d : Nat} (lambda : ℝ) (S : Set (EVec d)) : Set (EVec d) :=
  {z | unscaleCoords lambda z ∈ S}

/-- The paper's function scaling `amp · f(x/λ,y/λ)`. -/
def scaledObjective {m n : Nat} (lambda amp : ℝ)
    (f : EVec m → EVec n → ℝ) (x : EVec m) (y : EVec n) : ℝ :=
  amp * f (unscaleCoords lambda x) (unscaleCoords lambda y)

/-- The true chain-rule scaled primal gradient. -/
def scaledGradX {m n : Nat} (lambda amp : ℝ)
    (g : EVec m → EVec n → EVec m) (x : EVec m) (y : EVec n) : EVec m :=
  scaleCoords (amp / lambda)
    (g (unscaleCoords lambda x) (unscaleCoords lambda y))

/-- The true chain-rule scaled dual gradient. -/
def scaledGradY {m n : Nat} (lambda amp : ℝ)
    (g : EVec m → EVec n → EVec n) (x : EVec m) (y : EVec n) : EVec n :=
  scaleCoords (amp / lambda)
    (g (unscaleCoords lambda x) (unscaleCoords lambda y))

/-- Scaling of a complete bounded-domain instance. -/
def scaleNCCInstance {m n : Nat} (lambda amp : ℝ)
    (P : NCCInstance m n) : NCCInstance m n where
  X := scaledDomain lambda P.X
  Y := scaledDomain lambda P.Y
  f := scaledObjective lambda amp P.f
  gradX := scaledGradX lambda amp P.gradX
  gradY := scaledGradY lambda amp P.gradY
  x0 := scaleCoords lambda P.x0

def unscaleCLM (d : Nat) (lambda : ℝ) : EVec d →L[ℝ] EVec d :=
  (1 / lambda) • ContinuousLinearMap.id ℝ (EVec d)

@[simp] theorem unscaleCLM_apply (d : Nat) (lambda : ℝ) (z : EVec d) :
    unscaleCLM d lambda z = unscaleCoords lambda z := by
  funext i
  simp [unscaleCLM, unscaleCoords, div_eq_mul_inv, mul_comm]

theorem hasFDerivAt_unscaleProd {m n : Nat} (lambda : ℝ)
    (x : EVec m) (y : EVec n) :
    HasFDerivAt
      (fun p : EVec m × EVec n =>
        (unscaleCoords lambda p.1, unscaleCoords lambda p.2))
      (((1 / lambda) • ContinuousLinearMap.fst ℝ (EVec m) (EVec n)).prod
        ((1 / lambda) • ContinuousLinearMap.snd ℝ (EVec m) (EVec n))) (x, y) := by
  have hx := (hasFDerivAt_fst (𝕜 := ℝ) (p := (x, y))).const_smul
    (1 / lambda)
  have hy := (hasFDerivAt_snd (𝕜 := ℝ) (p := (x, y))).const_smul
    (1 / lambda)
  have hfun : (fun p : EVec m × EVec n =>
      (unscaleCoords lambda p.1, unscaleCoords lambda p.2)) =
      (fun p => ((1 / lambda) • p.1, (1 / lambda) • p.2)) := by
    funext p
    apply Prod.ext <;> funext i <;>
      simp [unscaleCoords, div_eq_mul_inv, mul_comm]
  rw [hfun]
  exact hx.prodMk hy

theorem scaledObjective_representsJointGradient {m n : Nat}
    {f : EVec m → EVec n → ℝ}
    {gx : EVec m → EVec n → EVec m}
    {gy : EVec m → EVec n → EVec n}
    (hrep : NCPLVerification.RepresentsJointGradient f gx gy)
    (lambda amp : ℝ) :
    NCPLVerification.RepresentsJointGradient
      (scaledObjective lambda amp f)
      (scaledGradX lambda amp gx) (scaledGradY lambda amp gy) := by
  constructor
  · intro p
    rcases p with ⟨x, y⟩
    have hR := hasFDerivAt_unscaleProd lambda x y
    have hb := (hrep.1 _).hasFDerivAt.comp (x, y) hR
    exact (hb.const_mul amp).differentiableAt
  · intro x y hx hy
    let B := Function.uncurry f
    let R : EVec m × EVec n → EVec m × EVec n := fun p =>
      (unscaleCoords lambda p.1, unscaleCoords lambda p.2)
    let R' : (EVec m × EVec n) →L[ℝ] (EVec m × EVec n) :=
      ((1 / lambda) • ContinuousLinearMap.fst ℝ (EVec m) (EVec n)).prod
        ((1 / lambda) • ContinuousLinearMap.snd ℝ (EVec m) (EVec n))
    have hR : HasFDerivAt R R' (x, y) := hasFDerivAt_unscaleProd lambda x y
    have hb : HasFDerivAt B (fderiv ℝ B (R (x, y))) (R (x, y)) :=
      (hrep.1 (R (x, y))).hasFDerivAt
    have hs : HasFDerivAt
        (Function.uncurry (scaledObjective lambda amp f))
        (amp • (fderiv ℝ B (R (x, y))).comp R') (x, y) := by
      convert (hb.comp (x, y) hR).const_mul amp using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      all_goals try { rfl }
    rw [hs.fderiv]
    simp only [smul_apply, ContinuousLinearMap.comp_apply]
    have hbase := hrep.2 (unscaleCoords lambda x) (unscaleCoords lambda y)
      ((1 / lambda) • hx) ((1 / lambda) • hy)
    change amp * (fderiv ℝ B
      (unscaleCoords lambda x, unscaleCoords lambda y))
      ((1 / lambda) • hx, (1 / lambda) • hy) = _
    rw [hbase]
    unfold scaledGradX scaledGradY scaleCoords
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      ring

private theorem scaledGradX_sub {m n : Nat} (lambda amp : ℝ)
    (g : EVec m → EVec n → EVec m) (x x' : EVec m) (y y' : EVec n) :
    scaledGradX lambda amp g x y - scaledGradX lambda amp g x' y' =
      scaleCoords (amp / lambda)
        (g (unscaleCoords lambda x) (unscaleCoords lambda y) -
          g (unscaleCoords lambda x') (unscaleCoords lambda y')) := by
  funext i
  simp [scaledGradX, scaleCoords]
  ring

private theorem scaledGradY_sub {m n : Nat} (lambda amp : ℝ)
    (g : EVec m → EVec n → EVec n) (x x' : EVec m) (y y' : EVec n) :
    scaledGradY lambda amp g x y - scaledGradY lambda amp g x' y' =
      scaleCoords (amp / lambda)
        (g (unscaleCoords lambda x) (unscaleCoords lambda y) -
          g (unscaleCoords lambda x') (unscaleCoords lambda y')) := by
  funext i
  simp [scaledGradY, scaleCoords]
  ring

private theorem jointSq_scaleCoords {m n : Nat} (c : ℝ)
    (u : EVec m) (v : EVec n) :
    jointSq (scaleCoords c u) (scaleCoords c v) = c ^ 2 * jointSq u v := by
  unfold jointSq
  rw [vecSq_scaleCoords, vecSq_scaleCoords]
  ring

private theorem jointSq_unscale_sub {m n : Nat} (lambda : ℝ)
    (x x' : EVec m) (y y' : EVec n) :
    jointSq (unscaleCoords lambda x - unscaleCoords lambda x')
        (unscaleCoords lambda y - unscaleCoords lambda y') =
      (1 / lambda) ^ 2 * jointSq (x - x') (y - y') := by
  rw [← unscaleCoords_sub, ← unscaleCoords_sub]
  unfold jointSq
  rw [vecSq_unscaleCoords, vecSq_unscaleCoords]
  ring

/-- Joint smoothness transports with constant `amp·L₀/λ²`. -/
theorem scaledObjective_jointly_smooth {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {gx : EVec m → EVec n → EVec m}
    {gy : EVec m → EVec n → EVec n}
    {L0 lambda amp : ℝ} (hlambda : 0 < lambda) (_hamp : 0 ≤ amp)
    (_hL0 : 0 ≤ L0)
    (hbase : ∀ x ∈ X, ∀ y ∈ Y, ∀ x' ∈ X, ∀ y' ∈ Y,
      jointSq (gx x y - gx x' y') (gy x y - gy x' y') ≤
        L0 ^ 2 * jointSq (x - x') (y - y')) :
    ∀ x ∈ scaledDomain lambda X, ∀ y ∈ scaledDomain lambda Y,
      ∀ x' ∈ scaledDomain lambda X, ∀ y' ∈ scaledDomain lambda Y,
      jointSq
          (scaledGradX lambda amp gx x y - scaledGradX lambda amp gx x' y')
          (scaledGradY lambda amp gy x y - scaledGradY lambda amp gy x' y') ≤
        (amp * L0 / lambda ^ 2) ^ 2 * jointSq (x - x') (y - y') := by
  intro x hx y hy x' hx' y' hy'
  have hb := hbase _ hx _ hy _ hx' _ hy'
  have hbin := jointSq_unscale_sub lambda x x' y y'
  rw [scaledGradX_sub, scaledGradY_sub, jointSq_scaleCoords]
  have hmul := mul_le_mul_of_nonneg_left hb (sq_nonneg (amp / lambda))
  rw [hbin] at hmul
  field_simp [hlambda.ne'] at hmul ⊢
  nlinarith

theorem scaledObjective_concaveOn {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {lambda amp : ℝ}
    (hamp : 0 ≤ amp)
    (hbase : ∀ x ∈ X, ConcaveOn ℝ Y (f x)) :
    ∀ x ∈ scaledDomain lambda X,
      ConcaveOn ℝ (scaledDomain lambda Y) (scaledObjective lambda amp f x) := by
  intro x hx
  have hc := hbase (unscaleCoords lambda x) hx
  have hconv : Convex ℝ (scaledDomain lambda Y) := by
    have hset : scaledDomain lambda Y = (unscaleCLM n lambda) ⁻¹' Y := by
      ext z
      simp [scaledDomain]
    rw [hset]
    exact hc.1.linear_preimage _
  refine ⟨hconv, ?_⟩
  intro y hy z hz a b ha hb hab
  have hineq := hc.2 hy hz ha hb hab
  have hlinear : unscaleCoords lambda (a • y + b • z) =
      a • unscaleCoords lambda y + b • unscaleCoords lambda z := by
    funext i
    simp [unscaleCoords]
    ring
  unfold scaledObjective
  rw [hlinear]
  have hmul := mul_le_mul_of_nonneg_left hineq hamp
  change a * (amp * f (unscaleCoords lambda x) (unscaleCoords lambda y)) +
      b * (amp * f (unscaleCoords lambda x) (unscaleCoords lambda z)) ≤
    amp * f (unscaleCoords lambda x)
      (a • unscaleCoords lambda y + b • unscaleCoords lambda z)
  calc
    _ = amp * (a * f (unscaleCoords lambda x) (unscaleCoords lambda y) +
        b * f (unscaleCoords lambda x) (unscaleCoords lambda z)) := by ring
    _ ≤ _ := by simpa only [smul_eq_mul] using hmul

theorem scaledDomain_nonempty {d : Nat} {lambda : ℝ} (hlambda : lambda ≠ 0)
    {S : Set (EVec d)} (hS : S.Nonempty) : (scaledDomain lambda S).Nonempty := by
  obtain ⟨z, hz⟩ := hS
  exact ⟨scaleCoords lambda z, by simp [scaledDomain, hlambda, hz]⟩

theorem scaledDomain_closed {d : Nat} (lambda : ℝ) {S : Set (EVec d)}
    (hS : IsClosed S) : IsClosed (scaledDomain lambda S) := by
  have hset : scaledDomain lambda S = (unscaleCLM d lambda) ⁻¹' S := by
    ext z
    simp [scaledDomain]
  rw [hset]
  exact hS.preimage (unscaleCLM d lambda).continuous

theorem scaledDomain_convex {d : Nat} (lambda : ℝ) {S : Set (EVec d)}
    (hS : Convex ℝ S) : Convex ℝ (scaledDomain lambda S) := by
  have hset : scaledDomain lambda S = (unscaleCLM d lambda) ⁻¹' S := by
    ext z
    simp [scaledDomain]
  rw [hset]
  exact hS.linear_preimage _

theorem scaledDomain_diameter {d : Nat} {lambda D0 : ℝ}
    (hlambda : 0 < lambda)
    {S : Set (EVec d)}
    (hdiam : ∀ u ∈ S, ∀ v ∈ S, vecSq (u - v) ≤ D0 ^ 2) :
    ∀ u ∈ scaledDomain lambda S, ∀ v ∈ scaledDomain lambda S,
      vecSq (u - v) ≤ (lambda * D0) ^ 2 := by
  intro u hu v hv
  have hb := hdiam _ hu _ hv
  rw [← unscaleCoords_sub] at hb
  rw [vecSq_unscaleCoords] at hb
  field_simp [hlambda.ne'] at hb ⊢
  nlinarith

theorem scaledObjective_maximizer {m n : Nat}
    {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ}
    {lambda amp : ℝ} (hlambda : lambda ≠ 0) (hamp : 0 ≤ amp)
    {x : EVec m} {u : EVec n}
    (hu : IsMaximizerOn Y f (unscaleCoords lambda x) u) :
    IsMaximizerOn (scaledDomain lambda Y) (scaledObjective lambda amp f) x
      (scaleCoords lambda u) := by
  constructor
  · simpa [scaledDomain, hlambda] using hu.1
  · intro v hv
    unfold scaledObjective
    rw [unscaleCoords_scaleCoords hlambda]
    exact mul_le_mul_of_nonneg_left (hu.2 _ hv) hamp

theorem scaledValue_eq {m n : Nat}
    {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ}
    {lambda amp : ℝ} (hlambda : lambda ≠ 0) (hamp : 0 ≤ amp)
    (x : EVec m)
    (hmax : ∃ y, IsMaximizerOn Y f (unscaleCoords lambda x) y) :
    ValueOn (scaledDomain lambda Y) (scaledObjective lambda amp f) x =
      amp * ValueOn Y f (unscaleCoords lambda x) := by
  obtain ⟨u, hu⟩ := hmax
  rw [value_eq_of_isMaximizerOn
      (scaledObjective_maximizer hlambda hamp hu),
    value_eq_of_isMaximizerOn hu]
  simp [scaledObjective, hlambda]

theorem scaledValue_bddBelow {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {lambda amp : ℝ}
    (hlambda : lambda ≠ 0) (hamp : 0 ≤ amp)
    (hmax : ∀ x ∈ X, ∃ y, IsMaximizerOn Y f x y)
    (hbdd : BddBelow (ValueOn Y f '' X)) :
    BddBelow (ValueOn (scaledDomain lambda Y)
      (scaledObjective lambda amp f) '' scaledDomain lambda X) := by
  obtain ⟨r, hr⟩ := hbdd
  refine ⟨amp * r, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [scaledValue_eq hlambda hamp x (hmax _ hx)]
  exact mul_le_mul_of_nonneg_left (hr ⟨unscaleCoords lambda x, hx, rfl⟩) hamp

theorem scaled_initial_gap {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {f : EVec m → EVec n → ℝ} {x0 : EVec m}
    {lambda amp Delta0 : ℝ}
    (hlambda : lambda ≠ 0) (hamp : 0 ≤ amp)
    (hX : X.Nonempty) (hx0 : x0 ∈ X)
    (hmax : ∀ x ∈ X, ∃ y, IsMaximizerOn Y f x y)
    (hbdd : BddBelow (ValueOn Y f '' X))
    (hgap : ValueOn Y f x0 - sInf (ValueOn Y f '' X) ≤ Delta0) :
    ValueOn (scaledDomain lambda Y) (scaledObjective lambda amp f)
          (scaleCoords lambda x0) -
        sInf (ValueOn (scaledDomain lambda Y) (scaledObjective lambda amp f) ''
          scaledDomain lambda X) ≤ amp * Delta0 := by
  let S0 : Set ℝ := ValueOn Y f '' X
  let Ss : Set ℝ := ValueOn (scaledDomain lambda Y)
    (scaledObjective lambda amp f) '' scaledDomain lambda X
  have hbdds : BddBelow Ss :=
    scaledValue_bddBelow hlambda hamp hmax hbdd
  have hSs : Ss.Nonempty := by
    obtain ⟨x, hx⟩ := hX
    refine ⟨ValueOn (scaledDomain lambda Y) (scaledObjective lambda amp f)
      (scaleCoords lambda x), ?_⟩
    exact ⟨scaleCoords lambda x, by simp [scaledDomain, hlambda, hx], rfl⟩
  have hinf : amp * sInf S0 ≤ sInf Ss := by
    rw [le_csInf_iff hbdds hSs]
    intro q hq
    rcases hq with ⟨x, hx, rfl⟩
    rw [scaledValue_eq hlambda hamp x (hmax _ hx)]
    have hsource : sInf S0 ≤ ValueOn Y f (unscaleCoords lambda x) :=
      csInf_le hbdd ⟨unscaleCoords lambda x, hx, rfl⟩
    exact mul_le_mul_of_nonneg_left hsource hamp
  have hscaled0 := scaledValue_eq hlambda hamp
    (scaleCoords lambda x0) (by
      simpa [hlambda] using hmax x0 hx0)
  rw [unscaleCoords_scaleCoords hlambda] at hscaled0
  have hgapmul := mul_le_mul_of_nonneg_left hgap hamp
  dsimp [S0, Ss] at hinf ⊢
  rw [hscaled0]
  nlinarith

/-- Source-side hypotheses consumed compositionally by the scaling theorem.
No scaled class-membership or lower-bound conclusion is stored here. -/
structure ScalingSource {m n : Nat} (L0 D0 Delta0 : ℝ)
    (P : NCCInstance m n) : Prop where
  x0_mem : P.x0 ∈ P.X
  X_nonempty : P.X.Nonempty
  X_closed : IsClosed P.X
  X_convex : Convex ℝ P.X
  Y_nonempty : P.Y.Nonempty
  Y_closed : IsClosed P.Y
  Y_convex : Convex ℝ P.Y
  gradient_representation :
    NCPLVerification.RepresentsJointGradient P.f P.gradX P.gradY
  jointly_smooth : ∀ x ∈ P.X, ∀ y ∈ P.Y,
    ∀ x' ∈ P.X, ∀ y' ∈ P.Y,
      jointSq (P.gradX x y - P.gradX x' y')
          (P.gradY x y - P.gradY x' y') ≤
        L0 ^ 2 * jointSq (x - x') (y - y')
  dual_concave : ∀ x ∈ P.X, ConcaveOn ℝ P.Y (P.f x)
  maximum_attained : ∀ x ∈ P.X, ∃ y, IsMaximizerOn P.Y P.f x y
  value_bddBelow : BddBelow (ValueOn P.Y P.f '' P.X)
  initial_gap : ValueOn P.Y P.f P.x0 -
    sInf (ValueOn P.Y P.f '' P.X) ≤ Delta0
  dual_diameter : ∀ y ∈ P.Y, ∀ y' ∈ P.Y,
    vecSq (y - y') ≤ D0 ^ 2

/-- The scaled instance belongs to the requested class with the constants
dictated by the genuine chain rule. -/
theorem scaleNCCInstance_isNCCClass {m n : Nat}
    {L0 D0 Delta0 lambda amp : ℝ} {P : NCCInstance m n}
    (hL0 : 0 < L0) (hD0 : 0 < D0) (hDelta0 : 0 < Delta0)
    (hlambda : 0 < lambda) (hamp : 0 < amp)
    (hsrc : ScalingSource L0 D0 Delta0 P) :
    IsNCCClass (amp * L0 / lambda ^ 2) (lambda * D0) (amp * Delta0)
      (scaleNCCInstance lambda amp P) := by
  refine
    { ell_pos := by positivity
      D_pos := by positivity
      Delta_pos := by positivity
      x0_mem := ?_
      X_nonempty := scaledDomain_nonempty hlambda.ne' hsrc.X_nonempty
      X_closed := scaledDomain_closed lambda hsrc.X_closed
      X_convex := scaledDomain_convex lambda hsrc.X_convex
      Y_nonempty := scaledDomain_nonempty hlambda.ne' hsrc.Y_nonempty
      Y_closed := scaledDomain_closed lambda hsrc.Y_closed
      Y_convex := scaledDomain_convex lambda hsrc.Y_convex
      gradient_representation := ?_
      jointly_smooth := ?_
      dual_concave := ?_
      maximum_attained := ?_
      value_bddBelow := ?_
      initial_gap := ?_
      dual_diameter := ?_ }
  · change unscaleCoords lambda (scaleCoords lambda P.x0) ∈ P.X
    simpa [hlambda.ne'] using hsrc.x0_mem
  · exact scaledObjective_representsJointGradient
      hsrc.gradient_representation lambda amp
  · exact scaledObjective_jointly_smooth hlambda hamp.le hL0.le
      hsrc.jointly_smooth
  · exact scaledObjective_concaveOn hamp.le hsrc.dual_concave
  · intro x hx
    obtain ⟨y, hy⟩ := hsrc.maximum_attained _ hx
    exact ⟨scaleCoords lambda y,
      scaledObjective_maximizer hlambda.ne' hamp.le hy⟩
  · exact scaledValue_bddBelow hlambda.ne' hamp.le
      hsrc.maximum_attained hsrc.value_bddBelow
  · exact scaled_initial_gap hlambda.ne' hamp.le hsrc.X_nonempty
      hsrc.x0_mem hsrc.maximum_attained hsrc.value_bddBelow hsrc.initial_gap
  · exact scaledDomain_diameter hlambda hsrc.dual_diameter

/-- Amplitude in (3320)--(3323). -/
def lowerAmplitude (ell ell0 lambda : ℝ) : ℝ :=
  ell * lambda ^ 2 / ell0

theorem lowerAmplitude_smooth_constant {ell ell0 lambda : ℝ}
    (hell0 : ell0 ≠ 0) (hlambda : lambda ≠ 0) :
    lowerAmplitude ell ell0 lambda * ell0 / lambda ^ 2 = ell := by
  unfold lowerAmplitude
  field_simp [hell0, hlambda]

theorem lowerAmplitude_gradient_factor {ell ell0 lambda : ℝ}
    (hell0 : ell0 ≠ 0) (hlambda : lambda ≠ 0) :
    lowerAmplitude ell ell0 lambda / lambda = ell * lambda / ell0 := by
  unfold lowerAmplitude
  field_simp [hell0, hlambda]

theorem paper_lambda_gradient_factor {ell ell0 eps c0 : ℝ}
    (hell : ell ≠ 0) (hell0 : ell0 ≠ 0) (hc0 : c0 ≠ 0) :
    lowerAmplitude ell ell0 (lowerScale ell ell0 eps c0) /
        lowerScale ell ell0 eps c0 = 4 * eps / c0 := by
  unfold lowerAmplitude lowerScale
  field_simp [hell, hell0, hc0]

/-- One-variable function scaling, used for the value function and prox map. -/
def scaledScalar {m : Nat} (lambda amp : ℝ) (phi : EVec m → ℝ)
    (x : EVec m) : ℝ := amp * phi (unscaleCoords lambda x)

theorem scaledValue_eq_scaledScalar {m n : Nat}
    {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ}
    {lambda amp : ℝ} (hlambda : lambda ≠ 0) (hamp : 0 ≤ amp)
    (hmax : ∀ x, ∃ y, IsMaximizerOn Y f x y) :
    ValueOn (scaledDomain lambda Y) (scaledObjective lambda amp f) =
      scaledScalar lambda amp (ValueOn Y f) := by
  funext x
  exact scaledValue_eq hlambda hamp x (hmax _)

theorem unscale_proxPoint {m : Nat}
    {X : Set (EVec m)} {phi : EVec m → ℝ}
    {lambda amp ell0 : ℝ} (hlambda : 0 < lambda) (hamp : 0 < amp)
    {x u : EVec m}
    (hu : IsProxPoint (scaledDomain lambda X) (scaledScalar lambda amp phi)
      (amp * ell0 / lambda ^ 2) x u) :
    IsProxPoint X phi ell0 (unscaleCoords lambda x)
      (unscaleCoords lambda u) := by
  constructor
  · exact hu.1
  · intro v hv
    have hvscaled : scaleCoords lambda v ∈ scaledDomain lambda X := by
      simpa [scaledDomain, hlambda.ne'] using hv
    have hi := hu.2 (scaleCoords lambda v) hvscaled
    have hux : vecSq (u - x) = lambda ^ 2 *
        vecSq (unscaleCoords lambda u - unscaleCoords lambda x) := by
      have heq : u - x = scaleCoords lambda
          (unscaleCoords lambda u - unscaleCoords lambda x) := by
        funext i
        unfold scaleCoords unscaleCoords
        simp only [Pi.sub_apply]
        field_simp [hlambda.ne']
      rw [heq, vecSq_scaleCoords]
    have hvx : vecSq (scaleCoords lambda v - x) = lambda ^ 2 *
        vecSq (v - unscaleCoords lambda x) := by
      have heq : scaleCoords lambda v - x = scaleCoords lambda
          (v - unscaleCoords lambda x) := by
        funext i
        unfold scaleCoords unscaleCoords
        simp only [Pi.sub_apply]
        field_simp [hlambda.ne']
      rw [heq, vecSq_scaleCoords]
    unfold scaledScalar at hi
    rw [unscaleCoords_scaleCoords hlambda.ne', hux, hvx] at hi
    field_simp [hlambda.ne'] at hi
    nlinarith

/-- Scaled OS implies source OS with the chain-rule threshold
`eps = (amp/λ) eps₀`.  This is the direction used by the lower bound. -/
theorem unscale_optimizationStationary {m : Nat}
    {X : Set (EVec m)} {phi : EVec m → ℝ}
    {lambda amp ell0 eps0 : ℝ}
    (hlambda : 0 < lambda) (hamp : 0 < amp) (hell0 : 0 < ell0)
    {x : EVec m}
    (hos : IsOptimizationStationary (scaledDomain lambda X)
      (scaledScalar lambda amp phi) (amp * ell0 / lambda ^ 2)
      (amp / lambda * eps0) x) :
    IsOptimizationStationary X phi ell0 eps0 (unscaleCoords lambda x) := by
  rcases hos with ⟨u, hu, hdist⟩
  refine ⟨unscaleCoords lambda u,
    unscale_proxPoint hlambda hamp hu, ?_⟩
  have hscale := vecSq_unscaleCoords lambda (u - x)
  rw [unscaleCoords_sub] at hscale
  rw [hscale]
  have hpos : 0 < amp * ell0 / lambda ^ 2 := by positivity
  rw [div_pow] at hdist ⊢
  field_simp [hlambda.ne', hamp.ne', hell0.ne'] at hdist ⊢
  nlinarith [sq_nonneg eps0]

theorem not_scaledOS_of_not_sourceOS {m : Nat}
    {X : Set (EVec m)} {phi : EVec m → ℝ}
    {lambda amp ell0 eps0 : ℝ}
    (hlambda : 0 < lambda) (hamp : 0 < amp) (hell0 : 0 < ell0)
    {x : EVec m}
    (hfail : ¬IsOptimizationStationary X phi ell0 eps0
      (unscaleCoords lambda x)) :
    ¬IsOptimizationStationary (scaledDomain lambda X)
      (scaledScalar lambda amp phi) (amp * ell0 / lambda ^ 2)
      (amp / lambda * eps0) x := by
  intro hos
  exact hfail (unscale_optimizationStationary hlambda hamp hell0 hos)

/-- A coordinate field is the actual Fréchet gradient of a scalar function. -/
def RepresentsGradient {m : Nat} (phi : EVec m → ℝ) (g : EVec m → EVec m) : Prop :=
  Differentiable ℝ phi ∧ ∀ x h,
    fderiv ℝ phi x h = ∑ i : Fin m, g x i * h i

/-- Chain-rule scaling of a scalar gradient. -/
def scaledScalarGrad {m : Nat} (lambda amp : ℝ) (g : EVec m → EVec m)
    (x : EVec m) : EVec m :=
  scaleCoords (amp / lambda) (g (unscaleCoords lambda x))

theorem hasFDerivAt_unscale {m : Nat} (lambda : ℝ) (x : EVec m) :
    HasFDerivAt (unscaleCoords lambda) (unscaleCLM m lambda) x := by
  have hfun : unscaleCoords lambda = fun z : EVec m => (1 / lambda) • z := by
    funext z i
    simp [unscaleCoords, div_eq_mul_inv, mul_comm]
  rw [hfun]
  exact (unscaleCLM m lambda).hasFDerivAt

theorem scaledScalar_representsGradient {m : Nat}
    {phi : EVec m → ℝ} {g : EVec m → EVec m}
    (hrep : RepresentsGradient phi g) (lambda amp : ℝ) :
    RepresentsGradient (scaledScalar lambda amp phi)
      (scaledScalarGrad lambda amp g) := by
  constructor
  · intro x
    have hb := (hrep.1 (unscaleCoords lambda x)).hasFDerivAt
    exact ((hb.comp x (hasFDerivAt_unscale lambda x)).const_mul amp).differentiableAt
  · intro x h
    have hb := (hrep.1 (unscaleCoords lambda x)).hasFDerivAt
    have hs : HasFDerivAt (scaledScalar lambda amp phi)
        (amp • (fderiv ℝ phi (unscaleCoords lambda x)).comp
          (unscaleCLM m lambda)) x := by
      convert ((hb.comp x (hasFDerivAt_unscale lambda x)).const_mul amp) using 1
      all_goals try { apply AddCommGroup.ext <;> rfl }
      all_goals try { apply Module.ext <;> rfl }
      all_goals try { rfl }
    rw [hs.fderiv]
    simp only [smul_apply, ContinuousLinearMap.comp_apply]
    have hbase := hrep.2 (unscaleCoords lambda x) ((1 / lambda) • h)
    change amp * fderiv ℝ phi (unscaleCoords lambda x) ((1 / lambda) • h) = _
    rw [hbase]
    unfold scaledScalarGrad scaleCoords
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem vecSq_scaledScalarGrad {m : Nat} (lambda amp : ℝ)
    (g : EVec m → EVec m) (x : EVec m) :
    vecSq (scaledScalarGrad lambda amp g x) =
      (amp / lambda) ^ 2 * vecSq (g (unscaleCoords lambda x)) := by
  unfold scaledScalarGrad
  exact vecSq_scaleCoords _ _

theorem scaled_gradient_threshold {m : Nat}
    {lambda amp c0 : ℝ} (_hfactor : 0 ≤ amp / lambda)
    {g : EVec m → EVec m} {x : EVec m}
    (hsource : c0 ^ 2 ≤ vecSq (g (unscaleCoords lambda x))) :
    ((amp / lambda) * c0) ^ 2 ≤
      vecSq (scaledScalarGrad lambda amp g x) := by
  rw [vecSq_scaledScalarGrad]
  have hmul := mul_le_mul_of_nonneg_left hsource (sq_nonneg (amp / lambda))
  nlinarith

theorem paper_scaled_gradient_threshold {m : Nat}
    {ell ell0 eps c0 : ℝ}
    (hell : 0 < ell) (hell0 : 0 < ell0) (heps : 0 < eps) (hc0 : 0 < c0)
    {g : EVec m → EVec m} {x : EVec m}
    (hsource : c0 ^ 2 ≤ vecSq
      (g (unscaleCoords (lowerScale ell ell0 eps c0) x))) :
    (4 * eps) ^ 2 ≤ vecSq
      (scaledScalarGrad (lowerScale ell ell0 eps c0)
        (lowerAmplitude ell ell0 (lowerScale ell ell0 eps c0)) g x) := by
  have hlambda : 0 < lowerScale ell ell0 eps c0 := by
    unfold lowerScale
    positivity
  have hfactor := paper_lambda_gradient_factor
    (eps := eps) hell.ne' hell0.ne' hc0.ne'
  have h := scaled_gradient_threshold
    (lambda := lowerScale ell ell0 eps c0)
    (amp := lowerAmplitude ell ell0 (lowerScale ell ell0 eps c0))
    (c0 := c0) (by
      rw [hfactor]
      positivity) hsource
  rw [hfactor] at h
  have hc : 4 * eps / c0 * c0 = 4 * eps := by
    field_simp [hc0.ne']
  rw [hc] at h
  exact h

/-- Direct specialization of the generic class theorem to (3302)--(3323).
The source diameter and gap are expressed in the unscaled coordinates. -/
theorem paper_scaleNCCInstance_isNCCClass {m n : Nat}
    {ell ell0 D Delta lambda : ℝ} {P : NCCInstance m n}
    (hell : 0 < ell) (hell0 : 0 < ell0) (hD : 0 < D)
    (hDelta : 0 < Delta) (hlambda : 0 < lambda)
    (hsrc : ScalingSource ell0 (D / lambda)
      (Delta / lowerAmplitude ell ell0 lambda) P) :
    IsNCCClass ell D Delta
      (scaleNCCInstance lambda (lowerAmplitude ell ell0 lambda) P) := by
  have hamp : 0 < lowerAmplitude ell ell0 lambda := by
    unfold lowerAmplitude
    positivity
  have hbase := scaleNCCInstance_isNCCClass hell0
    (by positivity : 0 < D / lambda)
    (by positivity : 0 < Delta / lowerAmplitude ell ell0 lambda)
    hlambda hamp hsrc
  have hsmooth := lowerAmplitude_smooth_constant
    (ell := ell) hell0.ne' hlambda.ne'
  have hdiam : lambda * (D / lambda) = D := by
    field_simp [hlambda.ne']
  have hgap : lowerAmplitude ell ell0 lambda *
      (Delta / lowerAmplitude ell ell0 lambda) = Delta := by
    field_simp [hamp.ne']
  simpa [hsmooth, hdiam, hgap] using hbase

private theorem coordinate_sq_le_vecSq {m : Nat} (z : EVec m) (i : Fin m) :
    z i ^ 2 ≤ vecSq z := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i)

theorem coordinate_displacement_le {m : Nat} {x u : EVec m} {r : ℝ}
    (hr : 0 ≤ r) (hdist : vecSq (u - x) ≤ r ^ 2) (i : Fin m)
    (hxi : x i = 0) : |u i| ≤ r := by
  have hi := coordinate_sq_le_vecSq (u - x) i
  have husq : u i ^ 2 ≤ r ^ 2 := by
    simpa [hxi] using hi.trans hdist
  rwa [sq_le_sq, abs_of_nonneg hr] at husq

theorem paper_terminal_ratio {ell ell0 eps c0 : ℝ}
    (hell : ell ≠ 0) (hell0 : ell0 ≠ 0) (heps : eps ≠ 0) (hc0 : c0 ≠ 0) :
    eps / (2 * ell * lowerScale ell ell0 eps c0) = c0 / (8 * ell0) := by
  unfold lowerScale
  field_simp [hell, hell0, heps, hc0]
  ring

theorem unscaled_coordinate_le_one {m : Nat}
    {lambda : ℝ} (hlambda : 0 < lambda) {u : EVec m} (i : Fin m)
    (hu : |u i| ≤ lambda) :
    |unscaleCoords lambda u i| ≤ 1 := by
  unfold unscaleCoords
  rw [abs_div, abs_of_pos hlambda, div_le_one hlambda]
  exact hu

/-- Source interface for the ordinary first-order optimality equation of the
proximal subproblem.  It mentions neither class membership nor OS failure. -/
def ProxFirstOrderLaw {m : Nat} (X : Set (EVec m))
    (phi : EVec m → ℝ) (g : EVec m → EVec m) (ell : ℝ) : Prop :=
  ∀ x u, IsProxPoint X phi ell x u →
    g u + scaleCoords (2 * ell) (u - x) = 0

/-- Abstract form of the argument in `lem:terminal-os`: a prox displacement
bound, terminal-coordinate control, the `4ε` gradient lower bound, and the
proximal optimality equation are inconsistent. -/
theorem terminal_not_optimizationStationary {m : Nat}
    {X : Set (EVec m)} {phi : EVec m → ℝ} {g : EVec m → EVec m}
    {ell eps lambda : ℝ} (hell : 0 < ell) (heps : 0 < eps)
    (hlambda : 0 < lambda) (hratio : eps / (2 * ell) ≤ lambda)
    (hprox : ProxFirstOrderLaw X phi g ell)
    (i : Fin m)
    (hterminalGrad : ∀ u, |unscaleCoords lambda u i| ≤ 1 →
      (4 * eps) ^ 2 ≤ vecSq (g u))
    {x : EVec m} (hxi : x i = 0) :
    ¬IsOptimizationStationary X phi ell eps x := by
  intro hos
  rcases hos with ⟨u, hu, hdist⟩
  have hr : 0 ≤ eps / (2 * ell) := by positivity
  have hui : |u i| ≤ eps / (2 * ell) :=
    coordinate_displacement_le hr hdist i hxi
  have huiLambda : |u i| ≤ lambda := hui.trans hratio
  have huUnscaled : |unscaleCoords lambda u i| ≤ 1 :=
    unscaled_coordinate_le_one hlambda i huiLambda
  have hlower := hterminalGrad u huUnscaled
  have hfirst := hprox x u hu
  have hgradEq : g u = scaleCoords (-2 * ell) (u - x) := by
    funext j
    have hj := congrFun hfirst j
    simp only [Pi.add_apply, Pi.zero_apply] at hj
    unfold scaleCoords at hj ⊢
    linarith
  rw [hgradEq, vecSq_scaleCoords] at hlower
  have hupper := mul_le_mul_of_nonneg_left hdist (sq_nonneg (-2 * ell))
  have hfactor : (-2 * ell) ^ 2 * (eps / (2 * ell)) ^ 2 = eps ^ 2 := by
    field_simp [hell.ne']
  rw [hfactor] at hupper
  nlinarith [sq_pos_of_pos heps]

/-! ## Preservation of the ordered zero-chain under scaling -/

/-- The scaled joint oracle field.  This is the same change of variables as
`scaledGradX` and `scaledGradY`, expressed on a single ordered coordinate
vector. -/
def scaledVectorField {d : Nat} (lambda amp : ℝ) (G : EVec d → EVec d) :
    EVec d → EVec d :=
  fun z => scaleCoords (amp / lambda) (G (unscaleCoords lambda z))

theorem supportedBelow_unscaleCoords {d k : Nat} {lambda : ℝ} {z : EVec d}
    (hz : NCPLVerification.SupportedBelow k z) :
    NCPLVerification.SupportedBelow k (unscaleCoords lambda z) := by
  intro i hi
  simp only [unscaleCoords, hz i hi, zero_div]

theorem supportedBelow_scaleCoords {d k : Nat} {a : ℝ} {z : EVec d}
    (hz : NCPLVerification.SupportedBelow k z) :
    NCPLVerification.SupportedBelow k (scaleCoords a z) := by
  intro i hi
  simp only [scaleCoords, hz i hi, mul_zero]

/-- Coordinate scaling neither reveals a new input coordinate nor a new
oracle-response coordinate.  Hence it preserves the exact coordinate order
used by the paper's zero-chain argument. -/
theorem scaledVectorField_isFirstOrderZeroChain {d : Nat}
    {lambda amp : ℝ} {G : EVec d → EVec d}
    (hG : NCPLVerification.IsFirstOrderZeroChain G) :
    NCPLVerification.IsFirstOrderZeroChain
      (scaledVectorField lambda amp G) := by
  intro k z hz
  apply supportedBelow_scaleCoords
  exact hG k (unscaleCoords lambda z) (supportedBelow_unscaleCoords hz)

end

end NCCLowerBoundVerification
