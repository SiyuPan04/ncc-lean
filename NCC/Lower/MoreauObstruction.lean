import NCC.Lower.Parameters
import NCCLowerBoundVerification.Lower.ScaledObjective
import NCCLowerBoundVerification.Lower.TerminalOS

/-!
# The current terminal certificate implies failure of OS after scaling

Source: the proximal argument in `thm:zr-lower`. The input is an actual
Fréchet gradient and the separate terminal certificate for that gradient.
Proximal optimality is derived from the derivative, not assumed as a law.
The main lower theorem still needs the concrete certificate and the oracle
support induction for its actual saddle objective.
-/

namespace NCC.Lower.MoreauObstruction

noncomputable section

open NCCLowerBoundVerification
open Parameters

def amplitude (C : Constants) (ell eps : ℝ) : ℝ :=
  ell * scale C ell eps ^ 2 / C.ell0

theorem amplitude_pos (C : Constants) {ell eps : ℝ}
    (hell : 0 < ell) (heps : 0 < eps) : 0 < amplitude C ell eps :=
  div_pos (mul_pos hell (sq_pos_of_pos (scale_pos C hell heps))) C.ell0_pos

theorem gradient_factor (C : Constants) {ell eps : ℝ}
    (hell : 0 < ell) (heps : 0 < eps) :
    amplitude C ell eps / scale C ell eps = ell * scale C ell eps / C.ell0 := by
  unfold amplitude
  exact lowerAmplitude_gradient_factor (ne_of_gt C.ell0_pos)
    (ne_of_gt (scale_pos C hell heps))

theorem represented_hasFDerivAt {m : Nat} {phi : EVec m → ℝ}
    {g : EVec m → EVec m} (hrep : RepresentsGradient phi g) (x : EVec m) :
    NCPLVerification.HasEVecFDerivAt phi (NCPLVerification.evecDot (g x)) x := by
  have hclm : fderiv ℝ phi x = NCPLVerification.evecDot (g x) := by
    ext d
    rw [hrep.2 x d]
    rfl
  rw [← hclm]
  exact (hrep.1 x).hasFDerivAt

/-- The source C3 region is exactly `terminal ≤ 1/5`; no stronger
obstruction on the larger region `terminal ≤ 1` is assumed. -/
theorem not_OS_of_terminal_certificate {m : Nat} (C : Constants)
    {ell eps : ℝ} (hell : 0 < ell) (heps : 0 < eps)
    {phi : EVec m → ℝ} {g : EVec m → EVec m}
    (hrep : RepresentsGradient phi g) (terminal : Fin m)
    (hterminal : ∀ u, u terminal ≤ (1 : ℝ) / 5 → C.g0 ^ 2 ≤ vecSq (g u))
    {x : EVec m} (hx : x terminal = 0) :
    ¬ IsOptimizationStationary Set.univ
      (scaledScalar (scale C ell eps) (amplitude C ell eps) phi) ell eps x := by
  have hlam := scale_pos C hell heps
  have hratio := moreau_terminal_threshold C hell heps
  have hmove : eps / (2 * ell) ≤ scale C ell eps / 5 := by
    have heq : eps / (2 * ell) / scale C ell eps =
        eps / (2 * ell * scale C ell eps) := by rw [div_div]
    have hd : eps / (2 * ell) / scale C ell eps ≤ (1 : ℝ) / 5 := by
      rw [heq]
      exact hratio.le
    have := (div_le_iff₀ hlam).1 hd
    linarith
  have hscaled := scaledScalar_representsGradient hrep
    (scale C ell eps) (amplitude C ell eps)
  apply not_optimizationStationary_of_terminal_gradient hell heps
    (div_pos hlam (by norm_num : (0 : ℝ) < 5)) hmove
    (fun u => represented_hasFDerivAt hscaled u) terminal hx
  intro u hu
  have hut : unscaleCoords (scale C ell eps) u terminal ≤ (1 : ℝ) / 5 := by
    have hum := (div_le_iff₀ (div_pos hlam (by norm_num : (0 : ℝ) < 5))).1 hu
    change u terminal / scale C ell eps ≤ (1 : ℝ) / 5
    apply (div_le_iff₀ hlam).2
    linarith
  have hlow := hterminal (unscaleCoords (scale C ell eps) u) hut
  rw [vecSq_scaledScalarGrad]
  have hmul := mul_le_mul_of_nonneg_left hlow
    (sq_nonneg (amplitude C ell eps / scale C ell eps))
  have heq : (amplitude C ell eps / scale C ell eps) * C.g0 = 4 * eps := by
    rw [gradient_factor C hell heps]
    have := scaled_gradient_margin C hell heps
    simpa only [div_mul_eq_mul_div] using this
  calc
    16 * eps ^ 2 = ((amplitude C ell eps / scale C ell eps) * C.g0) ^ 2 := by
      rw [heq]
      ring
    _ = (amplitude C ell eps / scale C ell eps) ^ 2 * C.g0 ^ 2 := mul_pow _ _ _
    _ ≤ _ := hmul

/-- The value scaling identity uses an actual attained dual maximum. -/
theorem value_scaling {m n : Nat} (C : Constants) {ell eps : ℝ}
    (hell : 0 < ell) (heps : 0 < eps)
    {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ}
    (hmax : ∀ x, ∃ y, IsMaximizerOn Y f x y) :
    ValueOn (scaledDomain (scale C ell eps) Y)
      (scaledObjective (scale C ell eps) (amplitude C ell eps) f) =
      scaledScalar (scale C ell eps) (amplitude C ell eps) (ValueOn Y f) :=
  scaledValue_eq_scaledScalar (ne_of_gt (scale_pos C hell heps))
    (amplitude_pos C hell heps).le hmax

/-- Applying the preceding obstruction to the genuinely maximized scaled
saddle objective, rather than an unrelated scalar function. -/
theorem scaled_saddle_not_OS {m n : Nat} (C : Constants) {ell eps : ℝ}
    (hell : 0 < ell) (heps : 0 < eps)
    {Y : Set (EVec n)} {f : EVec m → EVec n → ℝ}
    (hmax : ∀ x, ∃ y, IsMaximizerOn Y f x y)
    {g : EVec m → EVec m} (hrep : RepresentsGradient (ValueOn Y f) g)
    (terminal : Fin m)
    (hterminal : ∀ u, u terminal ≤ (1 : ℝ) / 5 → C.g0 ^ 2 ≤ vecSq (g u))
    {x : EVec m} (hx : x terminal = 0) :
    ¬ IsOptimizationStationary Set.univ
      (ValueOn (scaledDomain (scale C ell eps) Y)
        (scaledObjective (scale C ell eps) (amplitude C ell eps) f)) ell eps x := by
  rw [value_scaling C hell heps hmax]
  exact not_OS_of_terminal_certificate C hell heps hrep terminal hterminal hx

end

end NCC.Lower.MoreauObstruction
