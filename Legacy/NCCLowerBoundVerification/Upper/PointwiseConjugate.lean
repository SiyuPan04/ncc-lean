import NCCLowerBoundVerification.Upper.RelativeFOAM

/-!
# Pointwise conjugate bridge

This module formalizes the mathematical core of TeX
`ub:eq:decurved`, `ub:eq:pointwise-conjugate`, `ub:eq:Pzr`,
`ub:lem:gamma-subgradient`, and `ub:eq:qstar-primal`.

The conjugate is finite-valued on the subtype `Y`.  Its only finiteness input
is an explicit `BddAbove` hypothesis for the primal supremum.  At the point
used by the subgradient lemma, attainment is proved from the stated primal
support inequality and normal relation rather than assumed.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace PointwiseConjugate

noncomputable section

def dot {d : Nat} (a b : EVec d) : ℝ :=
  ∑ i : Fin d, a i * b i

theorem dot_sub_left {d : Nat} (a b c : EVec d) :
    dot (a - b) c = dot a c - dot b c := by
  unfold dot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

theorem dot_add_left {d : Nat} (a b c : EVec d) :
    dot (a + b) c = dot a c + dot b c := by
  unfold dot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

theorem dot_sub_right {d : Nat} (a b c : EVec d) :
    dot a (b - c) = dot a b - dot a c := by
  unfold dot
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

theorem dot_smul_left {d : Nat} (c : ℝ) (a b : EVec d) :
    dot (c • a) b = c * dot a b := by
  unfold dot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem dot_comm {d : Nat} (a b : EVec d) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem vecSq_nonneg {d : Nat} (x : EVec d) : 0 ≤ vecSq x := by
  unfold vecSq NCPLVerification.vecSq
  exact Finset.sum_nonneg fun i _ ↦ sq_nonneg (x i)

private theorem vecSq_eq_zero_iff {d : Nat} (x : EVec d) :
    vecSq x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    unfold vecSq NCPLVerification.vecSq at hx
    have hi : x i ^ 2 = 0 := by
      apply le_antisymm
      · have := Finset.single_le_sum (fun j _ ↦ sq_nonneg (x j))
          (Finset.mem_univ i)
        linarith
      · exact sq_nonneg _
    exact sq_eq_zero_iff.mp hi
  · rintro rfl
    simp [vecSq, NCPLVerification.vecSq]

/-! ## Decurving identity -/

/-- The strongly convex--concave proximal saddle objective. -/
def smoothedSaddle {m n : Nat} (f : EVec m → EVec n → ℝ)
    (ell r : ℝ) (z x : EVec m) (y : EVec n) : ℝ :=
  f x y + ell * vecSq (x - z) - r / 2 * vecSq y

/-- Removing the explicit primal and dual curvatures. -/
def decurved {m n : Nat} (f : EVec m → EVec n → ℝ)
    (ell r : ℝ) (z x : EVec m) (y : EVec n) : ℝ :=
  smoothedSaddle f ell r z x y - ell / 2 * vecSq x + r / 2 * vecSq y

theorem vecSq_sub_expand {d : Nat} (x z : EVec d) :
    vecSq (x - z) = vecSq x - 2 * dot z x + vecSq z := by
  unfold vecSq NCPLVerification.vecSq dot
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

/-- TeX `ub:eq:decurved`; in particular the result is independent of `r`. -/
theorem vecSq_add_expand {d : Nat} (x z : EVec d) :
    vecSq (x + z) = vecSq x + 2 * dot x z + vecSq z := by
  unfold vecSq NCPLVerification.vecSq dot
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply]
  ring

theorem decurved_eq {m n : Nat} (f : EVec m → EVec n → ℝ)
    (ell r : ℝ) (z x : EVec m) (y : EVec n) :
    decurved f ell r z x y =
      f x y + ell / 2 * vecSq x - 2 * ell * dot z x + ell * vecSq z := by
  unfold decurved smoothedSaddle
  rw [vecSq_sub_expand]
  ring

/-- The exact affine anchor change in TeX `ub:eq:P-anchor-identity`. -/
theorem decurved_anchor_shift {m n : Nat}
    (f : EVec m → EVec n → ℝ) (ell r : ℝ)
    (z d x : EVec m) (y : EVec n) :
    decurved f ell r (z + d) x y =
      decurved f ell r z x y - dot ((2 * ell) • d) x +
        (2 * ell * dot z d + ell * vecSq d) := by
  rw [decurved_eq, decurved_eq, dot_add_left, vecSq_add_expand,
    dot_smul_left]
  ring

/-! ## Finite pointwise conjugate and its global subgradient -/

/-- TeX `ub:eq:pointwise-conjugate`, restricted to the finite domain `y : Y`. -/
def gamma {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (H : EVec m → EVec n → ℝ) (q : EVec m) (y : Y) : ℝ :=
  ValueOn X (fun p x ↦ dot p x - H x y.1) q

/-- A bounded supremum commutes with subtraction of a scalar constant. -/
theorem valueOn_sub_const {d : Nat} {X : Set (EVec d)}
    (hX : X.Nonempty) {F F' : EVec d → ℝ} (c : ℝ)
    (hshift : ∀ x ∈ X, F' x = F x - c)
    (hbounded : BddAbove (F '' X)) :
    sSup (F' '' X) = sSup (F '' X) - c := by
  have hbounded' : BddAbove (F' '' X) := by
    rcases hbounded with ⟨B, hB⟩
    refine ⟨B - c, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [hshift x hx]
    exact sub_le_sub_right (hB ⟨x, hx, rfl⟩) c
  have hne : (F '' X).Nonempty := hX.image F
  have hne' : (F' '' X).Nonempty := hX.image F'
  apply le_antisymm
  · apply csSup_le hne'
    rintro _ ⟨x, hx, rfl⟩
    have hle := le_csSup hbounded ⟨x, hx, rfl⟩
    rw [hshift x hx]
    linarith
  · have hle : sSup (F '' X) ≤ sSup (F' '' X) + c := by
      apply csSup_le hne
      rintro _ ⟨x, hx, rfl⟩
      have hx' := le_csSup hbounded' ⟨x, hx, rfl⟩
      rw [hshift x hx] at hx'
      linarith
    linarith

/-- Minimal finiteness condition for every conjugate value used below. -/
def GammaBddAbove {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (H : EVec m → EVec n → ℝ) : Prop :=
  ∀ q (y : Y), BddAbove ((fun x ↦ dot q x - H x y.1) '' X)

/-- TeX `ub:eq:Pzr`. -/
def Pzr {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (H : EVec m → EVec n → ℝ) (mu r : ℝ)
    (q : EVec m) (y : Y) : ℝ :=
  1 / (2 * mu) * vecSq q + r / 2 * vecSq y.1 + gamma X Y H q y

/--
The pointwise conjugate identity behind moving-anchor co-translation.  This
is proved directly from the defining `sSup`; no conjugate-shift rule is
assumed.
-/
theorem gamma_of_linear_shift {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} (hX : X.Nonempty)
    {H H' : EVec m → EVec n → ℝ} {delta : EVec m} {c : ℝ}
    (hbounded : GammaBddAbove X Y H)
    (hshift : ∀ x ∈ X, ∀ y ∈ Y,
      H' x y = H x y - dot delta x + c)
    (q : EVec m) (y : Y) :
    gamma X Y H' (q - delta) y = gamma X Y H q y - c := by
  unfold gamma ValueOn
  apply valueOn_sub_const hX c
  · intro x hx
    change dot (q - delta) x - H' x y.1 =
      (dot q x - H x y.1) - c
    rw [hshift x hx y.1 y.2, dot_sub_left]
    ring
  · exact hbounded q y

/-- The corresponding exact shifted identity for the regularized conjugate. -/
theorem Pzr_of_linear_shift {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} (hX : X.Nonempty)
    {H H' : EVec m → EVec n → ℝ} {delta : EVec m} {c mu r : ℝ}
    (hmu : mu ≠ 0) (hbounded : GammaBddAbove X Y H)
    (hshift : ∀ x ∈ X, ∀ y ∈ Y,
      H' x y = H x y - dot delta x + c)
    (q : EVec m) (y : Y) :
    Pzr X Y H' mu r (q - delta) y =
      Pzr X Y H mu r q y - 1 / mu * dot delta q +
        1 / (2 * mu) * vecSq delta - c := by
  unfold Pzr
  rw [gamma_of_linear_shift hX hbounded hshift q y,
    vecSq_sub_expand]
  field_simp [hmu]
  ring

/-- The concrete co-translated `P_{z,r}` identity for an anchor step `z ↦ z+d`. -/
theorem Pzr_anchor_cotranslate {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} (hX : X.Nonempty)
    (f : EVec m → EVec n → ℝ) {ell mu r : ℝ}
    (hmu : mu ≠ 0) (z d q : EVec m) (y : Y)
    (hbounded : GammaBddAbove X Y (decurved f ell r z)) :
    Pzr X Y (decurved f ell r (z + d)) mu r
        (q - (2 * ell) • d) y =
      Pzr X Y (decurved f ell r z) mu r q y -
        1 / mu * dot ((2 * ell) • d) q +
        1 / (2 * mu) * vecSq ((2 * ell) • d) -
        (2 * ell * dot z d + ell * vecSq d) := by
  apply Pzr_of_linear_shift hX hmu hbounded
  intro x _ y' _
  exact decurved_anchor_shift f ell r z d x y'

/-- After removing the state-independent constant, co-translation is exactly
the linear tilt consumed by `TrackingAnalytic.anchor_energy_tilt_bound`. -/
theorem Pzr_anchor_normalized_tilt {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} (hX : X.Nonempty)
    (f : EVec m → EVec n → ℝ) {ell mu r : ℝ}
    (hmu : mu ≠ 0) (z d q : EVec m) (y : Y)
    (hbounded : GammaBddAbove X Y (decurved f ell r z)) :
    Pzr X Y (decurved f ell r (z + d)) mu r
          (q - (2 * ell) • d) y -
        (1 / (2 * mu) * vecSq ((2 * ell) • d) -
          (2 * ell * dot z d + ell * vecSq d)) =
      Pzr X Y (decurved f ell r z) mu r q y -
        1 / mu * dot ((2 * ell) • d) q := by
  rw [Pzr_anchor_cotranslate hX f hmu z d q y hbounded]
  ring

/-- Concrete first-order support inequality expressing convexity in `x`. -/
def ConvexSupportX {m n : Nat} (X : Set (EVec m))
    (H : EVec m → EVec n → ℝ) (gradX : EVec m)
    (x : EVec m) (y : EVec n) : Prop :=
  ∀ u ∈ X, H x y + dot gradX (u - x) ≤ H u y

/-- Concrete first-order support inequality expressing concavity in `y`. -/
def ConcaveSupportY {m n : Nat} (Y : Set (EVec n))
    (H : EVec m → EVec n → ℝ) (gradY : EVec n)
    (x : EVec m) (y : EVec n) : Prop :=
  ∀ v ∈ Y, H x v ≤ H x y + dot gradY (v - y)

/-- The genuine global subgradient inequality on `EVec m × Y`. -/
def IsGammaSubgradient {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (H : EVec m → EVec n → ℝ) (q : EVec m) (y : Y)
    (x : EVec m) (w : EVec n) : Prop :=
  ∀ q' (y' : Y), gamma X Y H q y + dot x (q' - q) + dot w (y'.1 - y.1) ≤
    gamma X Y H q' y'

/-- The primal normal relation makes `x` attain the defining supremum. -/
theorem gamma_attained_of_primal_normal {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {q gradX : EVec m}
    {x : EVec m} {y : Y} (hx : x ∈ X)
    (hsupport : ConvexSupportX X H gradX x y.1)
    (hnormal : RelativeFOAM.IsEuclideanNormal X x (q - gradX)) :
    IsMaximizerOn X (fun p u ↦ dot p u - H u y.1) q x := by
  refine ⟨hx, ?_⟩
  intro u hu
  have hs := hsupport u hu
  have hn := hnormal u hu
  rw [dot_sub_right] at hs
  change dot (q - gradX) (u - x) ≤ 0 at hn
  rw [dot_sub_left, dot_sub_right, dot_sub_right] at hn
  nlinarith

/-- TeX `ub:lem:gamma-subgradient`. -/
theorem gamma_subgradient {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} (hbounded : GammaBddAbove X Y H)
    {q : EVec m} {y : Y} {x : EVec m} {w : EVec n}
    {gradX : EVec m} {gradY : EVec n} (hx : x ∈ X)
    (hsupportX : ConvexSupportX X H gradX x y.1)
    (hsupportY : ConcaveSupportY Y H gradY x y.1)
    (hnormalX : RelativeFOAM.IsEuclideanNormal X x (q - gradX))
    (hnormalY : RelativeFOAM.IsEuclideanNormal Y y.1 (w + gradY)) :
    IsGammaSubgradient X Y H q y x w := by
  have hattain := gamma_attained_of_primal_normal hx hsupportX hnormalX
  have hgamma : gamma X Y H q y = dot q x - H x y.1 := by
    exact value_eq_of_isMaximizerOn hattain
  intro q' y'
  have hlower : dot q' x - H x y'.1 ≤ gamma X Y H q' y' := by
    unfold gamma ValueOn
    apply le_csSup (hbounded q' y')
    exact ⟨x, hx, rfl⟩
  have hy := hsupportY y'.1 y'.2
  have hn := hnormalY y'.1 y'.2
  change dot (w + gradY) (y'.1 - y.1) ≤ 0 at hn
  have hadd : dot (w + gradY) (y'.1 - y.1) =
      dot w (y'.1 - y.1) + dot gradY (y'.1 - y.1) := by
    unfold dot
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply]
    ring
  rw [hadd] at hn
  rw [hgamma]
  rw [dot_sub_right]
  rw [dot_comm x q', dot_comm x q]
  nlinarith

/-! ## Positive quadratic terms and the `q★ = -mu x★` relation -/

theorem vecSq_translate {d : Nat} (a b : EVec d) :
    vecSq a = vecSq b + 2 * dot b (a - b) + vecSq (a - b) := by
  unfold vecSq NCPLVerification.vecSq dot
  rw [Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.sub_apply]
  ring

/-- Saddle stationarity in `q` forces the paper's conjugate-primal identity. -/
theorem q_eq_neg_mu_smul_of_stationary {m : Nat} {mu : ℝ} (hmu : 0 < mu)
    {q x : EVec m} (hstation : x + mu⁻¹ • q = 0) :
    q = (-mu) • x := by
  funext i
  have hi := congrFun hstation i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
  field_simp [ne_of_gt hmu] at hi
  nlinarith

/--
A subgradient of `gamma`, after adding the two quadratic gradients, gives the
global one-strong-convexity support inequality used in the FOAM Lyapunov
argument.  Unlike `Pzr_strongMinimizer`, this statement does not assume that
the displayed subgradient is stationary.
-/
theorem Pzr_strongSupport {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r : ℝ}
    (hmu : 0 < mu) {q : EVec m} {y : Y}
    {x : EVec m} {w : EVec n}
    (hsubgrad : IsGammaSubgradient X Y H q y x w) :
    ∀ q' (y' : Y),
      Pzr X Y H mu r q y +
          dot (x + mu⁻¹ • q) (q' - q) +
          dot (w + r • y.1) (y'.1 - y.1) +
          1 / (2 * mu) * vecSq (q' - q) +
          r / 2 * vecSq (y'.1 - y.1) ≤
        Pzr X Y H mu r q' y' := by
  intro q' y'
  have hg := hsubgrad q' y'
  have hq := vecSq_translate q' q
  have hy := vecSq_translate y'.1 y.1
  have hmucoeff : 1 / (2 * mu) = mu⁻¹ / 2 := by
    field_simp [ne_of_gt hmu]
  have hdotQ : dot (x + mu⁻¹ • q) (q' - q) =
      dot x (q' - q) + mu⁻¹ * dot q (q' - q) := by
    unfold dot
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdotY : dot (w + r • y.1) (y'.1 - y.1) =
      dot w (y'.1 - y.1) + r * dot y.1 (y'.1 - y.1) := by
    unfold dot
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold Pzr
  rw [hq, hy, hmucoeff, hdotQ, hdotY]
  ring_nf
  linarith [hg]

/--
A gamma subgradient together with the two concrete stationarity equations
gives the strong global minimizer inequality for `Pzr`.
-/
theorem Pzr_strongMinimizer {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r : ℝ}
    (hmu : 0 < mu) (_hr : 0 < r) {q : EVec m} {y : Y}
    {x : EVec m} {w : EVec n}
    (hsubgrad : IsGammaSubgradient X Y H q y x w)
    (hstationQ : x + mu⁻¹ • q = 0)
    (hstationY : w + r • y.1 = 0) :
    ∀ q' (y' : Y),
      Pzr X Y H mu r q y + 1 / (2 * mu) * vecSq (q' - q) +
          r / 2 * vecSq (y'.1 - y.1) ≤ Pzr X Y H mu r q' y' := by
  intro q' y'
  have hg := hsubgrad q' y'
  have hq := vecSq_translate q' q
  have hy := vecSq_translate y'.1 y.1
  have hxrel : x = (-mu⁻¹) • q := by
    funext i
    have hi := congrFun hstationQ i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
    linarith
  have hwrel : w = (-r) • y.1 := by
    funext i
    have hi := congrFun hstationY i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hi ⊢
    linarith
  rw [hxrel, hwrel, dot_smul_left, dot_smul_left] at hg
  unfold Pzr
  rw [hq, hy]
  have hmucoeff : 1 / (2 * mu) = mu⁻¹ / 2 := by
    field_simp [ne_of_gt hmu]
  rw [hmucoeff]
  ring_nf
  linarith [hg]

/-- The stationary point is the unique global minimizer of `Pzr`. -/
theorem Pzr_unique_minimizer {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {H : EVec m → EVec n → ℝ} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 < r) {q : EVec m} {y : Y}
    {x : EVec m} {w : EVec n}
    (hsubgrad : IsGammaSubgradient X Y H q y x w)
    (hstationQ : x + mu⁻¹ • q = 0)
    (hstationY : w + r • y.1 = 0) :
    (∀ q' (y' : Y), Pzr X Y H mu r q y ≤ Pzr X Y H mu r q' y') ∧
      ∀ q' (y' : Y), Pzr X Y H mu r q' y' ≤ Pzr X Y H mu r q y →
        q' = q ∧ y' = y := by
  have hstrong := Pzr_strongMinimizer hmu hr hsubgrad hstationQ hstationY
  constructor
  · intro q' y'
    have h := hstrong q' y'
    have hq0 := vecSq_nonneg (q' - q)
    have hy0 := vecSq_nonneg (y'.1 - y.1)
    have hcq : 0 ≤ 1 / (2 * mu) := by positivity
    have hcy : 0 ≤ r / 2 := by positivity
    nlinarith
  · intro q' y' hle
    have h := hstrong q' y'
    have hq0 := vecSq_nonneg (q' - q)
    have hy0 := vecSq_nonneg (y'.1 - y.1)
    have hcq : 0 < 1 / (2 * mu) := by positivity
    have hcy : 0 < r / 2 := by positivity
    have hqz : vecSq (q' - q) = 0 := by nlinarith
    have hyz : vecSq (y'.1 - y.1) = 0 := by nlinarith
    have hqe : q' = q := sub_eq_zero.mp ((vecSq_eq_zero_iff _).mp hqz)
    have hye : y'.1 = y.1 := sub_eq_zero.mp ((vecSq_eq_zero_iff _).mp hyz)
    exact ⟨hqe, Subtype.ext hye⟩

/-- TeX `ub:eq:qstar-primal`, now as a consequence of stationarity. -/
theorem qstar_primal {m : Nat} {mu : ℝ} (hmu : 0 < mu)
    {qStar xStar : EVec m} (hstation : xStar + mu⁻¹ • qStar = 0) :
    qStar = (-mu) • xStar :=
  q_eq_neg_mu_smul_of_stationary hmu hstation

end

end PointwiseConjugate
end Upper
end NCCLowerBoundVerification
