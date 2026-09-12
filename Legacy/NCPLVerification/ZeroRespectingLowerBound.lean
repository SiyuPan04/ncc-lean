import NCPLVerification.SaddleZeroChain

/-!
# The scaled zero-respecting lower bound

This file makes the floor choices and the numerical regime in Section 8
fully explicit.  Stationarity is stated in squared Euclidean norm, so the
threshold `ε` is represented by `vecSq ≤ ε²`.
-/

namespace NCPLVerification

noncomputable section

def articleLambdaWall : ℝ := 12
def articleEta : ℝ := 1
def articleEll0 : ℝ := hardJointSmoothL articleLambdaWall articleEta
def articleC0 : ℝ :=
  perspectivePLConstant articleLambdaWall articleEta carmonAmax

theorem carmonPhiCap_pos : 0 < carmonPhiCap := by
  have hmono : carmonPhi (-1) < carmonPhi 0 :=
    carmonPhi_monotone (by norm_num)
  have hzero : 0 ≤ carmonPhi (-1) := carmonPhi_nonneg _
  exact lt_of_lt_of_le (lt_of_le_of_lt hzero hmono) (carmonPhi_le_cap 0)

theorem carmonTermCap_pos : 0 < carmonTermCap := by
  unfold carmonTermCap
  exact mul_pos (Real.exp_pos _) carmonPhiCap_pos

theorem articleEll0_pos : 0 < articleEll0 := by
  exact hardJointSmoothL_pos articleLambdaWall articleEta

theorem articleC0_pos : 0 < articleC0 := by
  unfold articleC0 articleLambdaWall articleEta perspectivePLConstant
  rw [lt_min_iff]
  constructor
  · have hA := carmonAmax_nonneg
    positivity
  · norm_num

def articleN (kappa : ℝ) : Nat :=
  ⌊articleC0 * kappa / (2 * articleEll0)⌋₊

def articleScale (L eps : ℝ) : ℝ :=
  2 * articleEll0 * eps / L

def articleAmp (L eps : ℝ) : ℝ :=
  L * articleScale L eps ^ 2 / articleEll0

def articleT (L Delta eps : ℝ) : Nat :=
  ⌊articleEll0 * Delta /
    (2 * L * carmonTermCap * articleScale L eps ^ 2)⌋₊

theorem articleN_two_le {kappa : ℝ}
    (hkappa : 4 * articleEll0 / articleC0 ≤ kappa) :
    2 ≤ articleN kappa := by
  unfold articleN
  apply Nat.le_floor
  have he := articleEll0_pos
  have hc := articleC0_pos
  calc
    (2 : ℝ) ≤ articleC0 * (4 * articleEll0 / articleC0) /
        (2 * articleEll0) := by
      field_simp [ne_of_gt he, ne_of_gt hc]
      norm_num
    _ ≤ articleC0 * kappa / (2 * articleEll0) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkappa hc.le) (by positivity)

theorem articleN_cast_le {kappa : ℝ} (hkappa : 0 ≤ kappa) :
    (articleN kappa : ℝ) ≤ articleC0 * kappa / (2 * articleEll0) := by
  unfold articleN
  apply Nat.floor_le
  have hc := articleC0_pos
  have he := articleEll0_pos
  exact div_nonneg (mul_nonneg articleC0_pos.le hkappa)
    (mul_nonneg (by norm_num) articleEll0_pos.le)

theorem articleScale_pos {L eps : ℝ} (hL : 0 < L) (heps : 0 < eps) :
    0 < articleScale L eps := by
  unfold articleScale
  exact div_pos (mul_pos (mul_pos (by norm_num) articleEll0_pos) heps) hL

theorem articleAmp_nonneg {L eps : ℝ} (hL : 0 ≤ L) :
    0 ≤ articleAmp L eps := by
  unfold articleAmp
  exact div_nonneg (mul_nonneg hL (sq_nonneg _)) articleEll0_pos.le

theorem articleAmp_div_scale_sq {L eps : ℝ}
    (hL : L ≠ 0) (heps : eps ≠ 0) :
    articleAmp L eps / articleScale L eps ^ 2 = L / articleEll0 := by
  have hs : articleScale L eps ≠ 0 := by
    unfold articleScale
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt articleEll0_pos)) heps) hL
  unfold articleAmp
  field_simp [hs, ne_of_gt articleEll0_pos]

theorem articleAmp_div_scale {L eps : ℝ}
    (hL : L ≠ 0) (heps : eps ≠ 0) :
    articleAmp L eps / articleScale L eps = 2 * eps := by
  have hs : articleScale L eps ≠ 0 := by
    unfold articleScale
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt articleEll0_pos)) heps) hL
  unfold articleAmp articleScale
  field_simp [hL, heps, hs, ne_of_gt articleEll0_pos]

theorem articleT_one_le {L Delta eps : ℝ}
    (hL : 0 < L) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hregime : 16 * carmonTermCap * articleEll0 * eps ^ 2 ≤ L * Delta) :
    1 ≤ articleT L Delta eps := by
  unfold articleT
  apply Nat.le_floor
  have hs := articleScale_pos hL heps
  have hc := carmonTermCap_pos
  have he := articleEll0_pos
  unfold articleScale
  field_simp [ne_of_gt hL, ne_of_gt he]
  ring_nf at hregime ⊢
  nlinarith [mul_pos hc he, sq_pos_of_pos heps]

theorem articleT_cast_le {L Delta eps : ℝ}
    (hL : 0 ≤ L) (hDelta : 0 ≤ Delta) :
    (articleT L Delta eps : ℝ) ≤
      articleEll0 * Delta /
        (2 * L * carmonTermCap * articleScale L eps ^ 2) := by
  unfold articleT
  apply Nat.floor_le
  exact div_nonneg (mul_nonneg articleEll0_pos.le hDelta)
    (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) hL) carmonTermCap_pos.le)
      (sq_nonneg _))

theorem NCPLClass.weaken_L_Delta {dx dy : Nat}
    {L L' mu Delta Delta' : ℝ}
    {F : EVec dx → EVec dy → ℝ}
    {gradX : EVec dx → EVec dy → EVec dx}
    {gradY : EVec dx → EVec dy → EVec dy}
    (hclass : NCPLClass L' mu Delta' F gradX gradY)
    (hL : 0 ≤ L) (hLle : L' ≤ L)
    (hDelta : 0 ≤ Delta) (hDle : Delta' ≤ Delta) :
    NCPLClass L mu Delta F gradX gradY := by
  refine
    { hclass with
      L_nonneg := hL
      Delta_nonneg := hDelta
      jointly_smooth := ?_
      initial_gap := hclass.initial_gap.trans hDle }
  intro x y x' y'
  have hbase := hclass.jointly_smooth x y x' y'
  have hin : 0 ≤ jointSq (x - x') (y - y') := by
    unfold jointSq vecSq
    positivity
  have hsquare : L' ^ 2 ≤ L ^ 2 := by
    nlinarith [hclass.L_nonneg]
  exact hbase.trans (mul_le_mul_of_nonneg_right hsquare hin)

theorem articleScaledSmoothL_eq {L eps : ℝ}
    (hL : L ≠ 0) (heps : eps ≠ 0) :
    scaledHardSmoothL articleLambdaWall articleEta
      (articleScale L eps) (articleAmp L eps) = L := by
  unfold scaledHardSmoothL
  rw [articleAmp_div_scale_sq hL heps]
  change L / articleEll0 * articleEll0 = L
  field_simp [ne_of_gt articleEll0_pos]

/-- The floor-selected scaled instance belongs to the requested NC--PL
class.  The stronger block PL constant is weakened to exactly `L / κ`. -/
theorem articleScaledHardF_NCPLClass
    {L Delta kappa eps : ℝ}
    (hL : 0 < L) (hDelta : 0 < Delta) (hkappa : 0 < kappa)
    (heps : 0 < eps)
    (hkappaLarge : 4 * articleEll0 / articleC0 ≤ kappa)
    (hregime : 16 * carmonTermCap * articleEll0 * eps ^ 2 ≤ L * Delta) :
    NCPLClass L (L / kappa) Delta
      (scaledHardF (articleT L Delta eps) (articleN kappa)
        articleLambdaWall articleEta (articleScale L eps) (articleAmp L eps))
      (scaledHardGradX (articleT L Delta eps) (articleN kappa)
        articleLambdaWall articleEta (articleScale L eps) (articleAmp L eps))
      (scaledHardGradY (articleT L Delta eps) (articleN kappa)
        articleLambdaWall articleEta (articleScale L eps) (articleAmp L eps)) := by
  let T := articleT L Delta eps
  let N := articleN kappa
  have hN2 : 2 ≤ N := articleN_two_le hkappaLarge
  have hNpos : 0 < N := by omega
  have hspos := articleScale_pos hL heps
  have hamp0 := articleAmp_nonneg (L := L) (eps := eps) hL.le
  have hbase := scaledHardF_NCPLClass (T := T) (N := N) hN2
    (lambdaWall := articleLambdaWall) (eta := articleEta)
    (scale := articleScale L eps) (amp := articleAmp L eps)
    (by norm_num [articleLambdaWall]) (by norm_num [articleEta])
    (by norm_num [articleEta]) hspos hamp0
  have hLeq := articleScaledSmoothL_eq hL.ne' heps.ne'
  change scaledHardSmoothL articleLambdaWall articleEta
      (articleScale L eps) (articleAmp L eps) = L at hLeq
  rw [hLeq] at hbase
  have hNupper : (N : ℝ) ≤
      articleC0 * kappa / (2 * articleEll0) := by
    exact articleN_cast_le hkappa.le
  have hcross : articleEll0 * (N : ℝ) ≤ articleC0 * kappa := by
    have hm := mul_le_mul_of_nonneg_left hNupper articleEll0_pos.le
    calc
      articleEll0 * (N : ℝ) ≤
          articleEll0 * (articleC0 * kappa / (2 * articleEll0)) := hm
      _ = articleC0 * kappa / 2 := by
        field_simp [ne_of_gt articleEll0_pos]
      _ ≤ articleC0 * kappa := by
        nlinarith [mul_pos articleC0_pos hkappa]
  have hratio : 1 / kappa ≤ articleC0 / (articleEll0 * (N : ℝ)) := by
    rw [div_le_div_iff₀ hkappa (mul_pos articleEll0_pos (by exact_mod_cast hNpos))]
    simpa using hcross
  have hmuMul := mul_le_mul_of_nonneg_left hratio hL.le
  have hmu : L / kappa ≤
      (articleAmp L eps / articleScale L eps ^ 2) *
        (articleC0 / (N : ℝ)) := by
    rw [articleAmp_div_scale_sq hL.ne' heps.ne']
    calc
      L / kappa = L * (1 / kappa) := by ring
      _ ≤ L * (articleC0 / (articleEll0 * (N : ℝ))) := hmuMul
      _ = (L / articleEll0) * (articleC0 / (N : ℝ)) := by
        field_simp [ne_of_gt articleEll0_pos,
          Nat.cast_ne_zero.mpr (Nat.ne_of_gt hNpos)]
  have hmu0 : 0 ≤ L / kappa := div_nonneg hL.le hkappa.le
  have hmuClass := hbase.weaken_mu hmu0 hmu
  have hTupper : (T : ℝ) ≤ articleEll0 * Delta /
      (2 * L * carmonTermCap * articleScale L eps ^ 2) := by
    exact articleT_cast_le hL.le hDelta.le
  have hgap : articleAmp L eps * (T : ℝ) * carmonTermCap ≤ Delta := by
    have hm := mul_le_mul_of_nonneg_left hTupper hamp0
    have hm' := mul_le_mul_of_nonneg_right hm carmonTermCap_pos.le
    calc
      articleAmp L eps * (T : ℝ) * carmonTermCap ≤
          articleAmp L eps *
            (articleEll0 * Delta /
              (2 * L * carmonTermCap * articleScale L eps ^ 2)) *
                carmonTermCap := by simpa [mul_assoc] using hm'
      _ ≤ Delta := by
        unfold articleAmp
        field_simp [hL.ne', ne_of_gt carmonTermCap_pos,
          ne_of_gt articleEll0_pos, ne_of_gt hspos]
        nlinarith
  exact hmuClass.weaken_L_Delta hL.le le_rfl hDelta.le hgap

/-- Before the full interleaved chain is discovered, the returned primal
coordinate still has zero terminal coordinate. -/
theorem zeroRespecting_terminal_zero_before_chain {T N : Nat}
    (hT : 0 < T) (hN : 0 < N)
    (lambdaWall eta scale amp : ℝ)
    {query output : Nat → EVec (T * (N + 1))}
    (hq : QueriesAreZeroRespecting
      (scaledHardOrderedSaddleField T N lambdaWall eta scale amp) query)
    (ho : OutputsAreZeroRespecting
      (scaledHardOrderedSaddleField T N lambdaWall eta scale amp) query output)
    {t : Nat} (ht : t < T * (N + 1)) :
    orderedPrimal (output t) (carmonLastIndex T hT) = 0 := by
  have hsupp := sequential_output_discovery
    (scaledHardOrderedSaddleField_is_zeroChain hN lambdaWall eta scale amp)
    hq ho t
  apply hsupp
  rw [finProdFinEquiv_val]
  unfold carmonLastIndex
  simp only [Fin.val_last]
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
  rw [hm] at ht ⊢
  simp only [Nat.succ_sub_one, Nat.succ_mul] at ht ⊢
  omega

/-- Exact finite-horizon obstruction: every zero-respecting returned point
before `T(N+1)` calls has envelope-gradient squared norm strictly above
`ε²`, whenever the scaled terminal certificate exceeds that threshold. -/
theorem zeroRespecting_not_stationary_before_chain {T N : Nat}
    (hT : 0 < T) (hN : 0 < N)
    {lambdaWall eta scale amp eps : ℝ}
    (hscale : 0 < scale) (hamp : 0 ≤ amp)
    (hthreshold : eps ^ 2 < (amp / scale) ^ 2)
    {query output : Nat → EVec (T * (N + 1))}
    (hq : QueriesAreZeroRespecting
      (scaledHardOrderedSaddleField T N lambdaWall eta scale amp) query)
    (ho : OutputsAreZeroRespecting
      (scaledHardOrderedSaddleField T N lambdaWall eta scale amp) query output)
    {t : Nat} (ht : t < T * (N + 1)) :
    ¬vecSq (scaledEnvelopeGradient T scale amp
      (orderedPrimal (output t))) ≤ eps ^ 2 := by
  intro hstationary
  have hlast := zeroRespecting_terminal_zero_before_chain hT hN
    lambdaWall eta scale amp hq ho ht
  have hterminal := scaledEnvelope_terminal_gradient hT hscale hamp
    (orderedPrimal (output t)) hlast
  linarith

theorem articleZeroRespecting_not_stationary
    {L Delta kappa eps : ℝ}
    (hL : 0 < L) (hDelta : 0 < Delta) (hkappa : 0 < kappa)
    (heps : 0 < eps)
    (hkappaLarge : 4 * articleEll0 / articleC0 ≤ kappa)
    (hregime : 16 * carmonTermCap * articleEll0 * eps ^ 2 ≤ L * Delta)
    {query output : Nat →
      EVec (articleT L Delta eps * (articleN kappa + 1))}
    (hq : QueriesAreZeroRespecting
      (scaledHardOrderedSaddleField (articleT L Delta eps) (articleN kappa)
        articleLambdaWall articleEta (articleScale L eps) (articleAmp L eps))
      query)
    (ho : OutputsAreZeroRespecting
      (scaledHardOrderedSaddleField (articleT L Delta eps) (articleN kappa)
        articleLambdaWall articleEta (articleScale L eps) (articleAmp L eps))
      query output)
    {t : Nat}
    (ht : t < articleT L Delta eps * (articleN kappa + 1)) :
    ¬vecSq (scaledEnvelopeGradient (articleT L Delta eps)
      (articleScale L eps) (articleAmp L eps)
      (orderedPrimal (output t))) ≤ eps ^ 2 := by
  have hT : 0 < articleT L Delta eps :=
    lt_of_lt_of_le Nat.zero_lt_one
      (articleT_one_le hL hDelta heps hregime)
  have hN : 0 < articleN kappa := by
    have := articleN_two_le hkappaLarge
    omega
  have hs := articleScale_pos hL heps
  have ha := articleAmp_nonneg (L := L) (eps := eps) hL.le
  apply zeroRespecting_not_stationary_before_chain hT hN hs ha
  · rw [articleAmp_div_scale hL.ne' heps.ne']
    nlinarith [sq_pos_of_pos heps]
  · exact hq
  · exact ho
  · exact ht

theorem articleN_cast_lower {kappa : ℝ}
    (hkappa : 4 * articleEll0 / articleC0 ≤ kappa) :
    articleC0 * kappa / (4 * articleEll0) ≤ (articleN kappa : ℝ) := by
  let a := articleC0 * kappa / (2 * articleEll0)
  have ha2 : (2 : ℝ) ≤ a := by
    unfold a
    have he := articleEll0_pos
    have hc := articleC0_pos
    calc
      (2 : ℝ) ≤ articleC0 * (4 * articleEll0 / articleC0) /
          (2 * articleEll0) := by
        field_simp [ne_of_gt he, ne_of_gt hc]
        norm_num
      _ ≤ articleC0 * kappa / (2 * articleEll0) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hkappa hc.le) (by positivity)
  have hfloor : a < (articleN kappa : ℝ) + 1 := by
    simpa [a, articleN] using (Nat.lt_floor_add_one a)
  have hhalf : a / 2 ≤ (articleN kappa : ℝ) := by linarith
  calc
    articleC0 * kappa / (4 * articleEll0) = a / 2 := by
      unfold a
      field_simp [ne_of_gt articleEll0_pos]
      ring
    _ ≤ _ := hhalf

theorem articleT_cast_lower {L Delta eps : ℝ}
    (hL : 0 < L) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hregime : 16 * carmonTermCap * articleEll0 * eps ^ 2 ≤ L * Delta) :
    L * Delta / (16 * carmonTermCap * articleEll0 * eps ^ 2) ≤
      (articleT L Delta eps : ℝ) := by
  let a := articleEll0 * Delta /
    (2 * L * carmonTermCap * articleScale L eps ^ 2)
  have hs := articleScale_pos hL heps
  have hc := carmonTermCap_pos
  have he := articleEll0_pos
  have ha2 : (2 : ℝ) ≤ a := by
    unfold a articleScale
    field_simp [ne_of_gt hL, ne_of_gt he, ne_of_gt hc,
      ne_of_gt heps]
    ring_nf at hregime ⊢
    nlinarith [mul_pos hc he, sq_pos_of_pos heps]
  have hfloor : a < (articleT L Delta eps : ℝ) + 1 := by
    simpa [a, articleT] using (Nat.lt_floor_add_one a)
  have hhalf : a / 2 ≤ (articleT L Delta eps : ℝ) := by linarith
  calc
    L * Delta / (16 * carmonTermCap * articleEll0 * eps ^ 2) = a / 2 := by
      unfold a articleScale
      field_simp [ne_of_gt hL, ne_of_gt he, ne_of_gt hc,
        ne_of_gt heps]
      ring
    _ ≤ _ := hhalf

def articleOmegaC : ℝ :=
  articleC0 / (64 * carmonTermCap * articleEll0 ^ 2)

theorem articleOmegaC_pos : 0 < articleOmegaC := by
  unfold articleOmegaC
  exact div_pos articleC0_pos
    (mul_pos (mul_pos (by norm_num) carmonTermCap_pos)
      (sq_pos_of_pos articleEll0_pos))

/-- A constant-bearing version of the article's `Ω` statement. -/
theorem article_chain_length_lower_bound
    {L Delta kappa eps : ℝ}
    (hL : 0 < L) (hDelta : 0 < Delta) (hkappa : 0 < kappa)
    (heps : 0 < eps)
    (hkappaLarge : 4 * articleEll0 / articleC0 ≤ kappa)
    (hregime : 16 * carmonTermCap * articleEll0 * eps ^ 2 ≤ L * Delta) :
    articleOmegaC * (L * Delta * kappa / eps ^ 2) ≤
      (articleT L Delta eps * (articleN kappa + 1) : Nat) := by
  have hTl := articleT_cast_lower hL hDelta heps hregime
  have hNl := articleN_cast_lower hkappaLarge
  have hprod :
      (L * Delta / (16 * carmonTermCap * articleEll0 * eps ^ 2)) *
          (articleC0 * kappa / (4 * articleEll0)) ≤
        (articleT L Delta eps : ℝ) * (articleN kappa : ℝ) := by
    exact mul_le_mul hTl hNl
      (div_nonneg (mul_nonneg articleC0_pos.le hkappa.le)
        (mul_nonneg (by norm_num) articleEll0_pos.le))
      (Nat.cast_nonneg _)
  calc
    articleOmegaC * (L * Delta * kappa / eps ^ 2) =
        (L * Delta / (16 * carmonTermCap * articleEll0 * eps ^ 2)) *
          (articleC0 * kappa / (4 * articleEll0)) := by
      unfold articleOmegaC
      field_simp [ne_of_gt articleEll0_pos, ne_of_gt carmonTermCap_pos,
        ne_of_gt heps]
      ring
    _ ≤ (articleT L Delta eps : ℝ) * (articleN kappa : ℝ) := hprod
    _ ≤ (articleT L Delta eps * (articleN kappa + 1) : Nat) := by
      norm_cast
      exact Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- The complete zero-respecting theorem: class membership and the
finite-horizon stationarity obstruction hold for the same explicit instance. -/
theorem article_zero_respecting_lower_bound
    {L Delta kappa eps : ℝ}
    (hL : 0 < L) (hDelta : 0 < Delta) (hkappa : 0 < kappa)
    (heps : 0 < eps)
    (hkappaLarge : 4 * articleEll0 / articleC0 ≤ kappa)
    (hregime : 16 * carmonTermCap * articleEll0 * eps ^ 2 ≤ L * Delta) :
    NCPLClass L (L / kappa) Delta
      (scaledHardF (articleT L Delta eps) (articleN kappa)
        articleLambdaWall articleEta (articleScale L eps) (articleAmp L eps))
      (scaledHardGradX (articleT L Delta eps) (articleN kappa)
        articleLambdaWall articleEta (articleScale L eps) (articleAmp L eps))
      (scaledHardGradY (articleT L Delta eps) (articleN kappa)
        articleLambdaWall articleEta (articleScale L eps) (articleAmp L eps)) ∧
    ∀ (query output : Nat →
        EVec (articleT L Delta eps * (articleN kappa + 1))),
      QueriesAreZeroRespecting
        (scaledHardOrderedSaddleField (articleT L Delta eps) (articleN kappa)
          articleLambdaWall articleEta (articleScale L eps) (articleAmp L eps))
        query →
      OutputsAreZeroRespecting
        (scaledHardOrderedSaddleField (articleT L Delta eps) (articleN kappa)
          articleLambdaWall articleEta (articleScale L eps) (articleAmp L eps))
        query output →
      ∀ t < articleT L Delta eps * (articleN kappa + 1),
        ¬vecSq (scaledEnvelopeGradient (articleT L Delta eps)
          (articleScale L eps) (articleAmp L eps)
          (orderedPrimal (output t))) ≤ eps ^ 2 := by
  constructor
  · exact articleScaledHardF_NCPLClass hL hDelta hkappa heps
      hkappaLarge hregime
  · intro query output hq ho t ht
    exact articleZeroRespecting_not_stationary hL hDelta hkappa heps
      hkappaLarge hregime hq ho ht

end

end NCPLVerification
