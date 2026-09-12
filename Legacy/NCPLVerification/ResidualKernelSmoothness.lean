import NCPLVerification.BetaRadialSmoothness

/-!
# Uniform homogeneous estimates for one residual kernel
-/

namespace NCPLVerification

noncomputable section

def residualSqKernel (s t : ℝ) : ℝ := gateResidual s t ^ 2

def residualGradS (s t : ℝ) : ℝ :=
  -2 * sigmaDeriv s * beta t * gateResidual s t

def residualGradT (s t : ℝ) : ℝ :=
  -2 * sigma s * betaDeriv t * gateResidual s t

def residualWeightedGradS (s t : ℝ) : ℝ :=
  -2 * sigmaWeightedDeriv s * beta t * gateResidual s t

def residualWeightedGradT (s t : ℝ) : ℝ :=
  -2 * sigma s * betaWeightedDeriv t * gateResidual s t

def residualRadialField (s t : ℝ) : ℝ :=
  2 * residualSqKernel s t - residualWeightedGradS s t -
    residualWeightedGradT s t

theorem hasDerivAt_residualSqKernel_left (s t : ℝ) :
    HasDerivAt (fun q ↦ residualSqKernel q t) (residualGradS s t) s := by
  have hs := hasDerivAt_sigma s
  have ht : HasDerivAt (fun _ : ℝ ↦ beta t) 0 s := hasDerivAt_const s _
  have hi := (hasDerivAt_const s (1 : ℝ)).sub (hs.mul ht)
  have ho := (hasDerivAt_posPart_sq
    (1 - sigma s * beta t)).comp s hi
  convert ho using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext q
    simp [residualSqKernel, gateResidual]
  · simp [residualGradS, gateResidual]
    ring

theorem hasDerivAt_residualSqKernel_right (s t : ℝ) :
    HasDerivAt (fun q ↦ residualSqKernel s q) (residualGradT s t) t := by
  have hs : HasDerivAt (fun _ : ℝ ↦ sigma s) 0 t := hasDerivAt_const t _
  have ht := hasDerivAt_beta t
  have hi := (hasDerivAt_const t (1 : ℝ)).sub (hs.mul ht)
  have ho := (hasDerivAt_posPart_sq
    (1 - sigma s * beta t)).comp t hi
  convert ho using 1
  all_goals try { apply AddCommGroup.ext <;> rfl }
  all_goals try { apply Module.ext <;> rfl }
  · funext q
    simp [residualSqKernel, gateResidual]
  · simp [residualGradT, gateResidual]
    ring

private theorem abs_triple_sub_le (a b c a' b' c' : ℝ) :
    |a * b * c - a' * b' * c'| ≤
      |a - a'| * |b| * |c| + |a'| * |b - b'| * |c| +
        |a'| * |b'| * |c - c'| := by
  have heq : a * b * c - a' * b' * c' =
      (a - a') * b * c + a' * (b - b') * c +
        a' * b' * (c - c') := by ring
  rw [heq]
  calc
    |(a - a') * b * c + a' * (b - b') * c +
        a' * b' * (c - c')| ≤
        |(a - a') * b * c + a' * (b - b') * c| +
          |a' * b' * (c - c')| := abs_add_le _ _
    _ ≤ (|(a - a') * b * c| + |a' * (b - b') * c|) +
          |a' * b' * (c - c')| := by
      gcongr
      exact abs_add_le _ _
    _ = _ := by repeat' rw [abs_mul]

theorem residualSqKernel_abs_le_four (s t : ℝ) :
    |residualSqKernel s t| ≤ 4 := by
  unfold residualSqKernel
  rw [abs_of_nonneg (sq_nonneg _)]
  nlinarith [gateResidual_nonneg s t, gateResidual_le_two s t]

theorem residualGradS_abs_le_sixteen (s t : ℝ) :
    |residualGradS s t| ≤ 16 := by
  unfold residualGradS
  repeat' rw [abs_mul]
  rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hs := sigmaDeriv_abs_le_two s
  have hb := beta_abs_le_two t
  have hr0 := gateResidual_nonneg s t
  have hr2 := gateResidual_le_two s t
  rw [abs_of_nonneg hr0]
  calc
    2 * |sigmaDeriv s| * |beta t| * gateResidual s t ≤
        2 * 2 * 2 * 2 := by gcongr
    _ = 16 := by norm_num

theorem residualGradT_abs_le_eight (s t : ℝ) :
    |residualGradT s t| ≤ 8 := by
  unfold residualGradT
  repeat' rw [abs_mul]
  rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hs := sigma_abs_le_one s
  have hb := betaDeriv_abs_le_two t
  have hr0 := gateResidual_nonneg s t
  have hr2 := gateResidual_le_two s t
  rw [abs_of_nonneg hr0]
  calc
    2 * |sigma s| * |betaDeriv t| * gateResidual s t ≤
        2 * 1 * 2 * 2 := by gcongr
    _ = 8 := by norm_num

theorem residualWeightedGradS_abs_le_sixteen (s t : ℝ) :
    |residualWeightedGradS s t| ≤ 16 := by
  unfold residualWeightedGradS
  repeat' rw [abs_mul]
  rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hs := sigmaWeightedDeriv_abs_le_two s
  have hb := beta_abs_le_two t
  have hr0 := gateResidual_nonneg s t
  have hr2 := gateResidual_le_two s t
  rw [abs_of_nonneg hr0]
  calc
    2 * |sigmaWeightedDeriv s| * |beta t| * gateResidual s t ≤
        2 * 2 * 2 * 2 := by gcongr
    _ = 16 := by norm_num

theorem residualWeightedGradT_abs_le_sixteen (s t : ℝ) :
    |residualWeightedGradT s t| ≤ 16 := by
  unfold residualWeightedGradT
  repeat' rw [abs_mul]
  rw [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hs := sigma_abs_le_one s
  have hb := betaWeightedDeriv_abs_le_four t
  have hr0 := gateResidual_nonneg s t
  have hr2 := gateResidual_le_two s t
  rw [abs_of_nonneg hr0]
  calc
    2 * |sigma s| * |betaWeightedDeriv t| * gateResidual s t ≤
        2 * 1 * 4 * 2 := by gcongr
    _ = 16 := by norm_num

theorem residualRadialField_abs_le_forty (s t : ℝ) :
    |residualRadialField s t| ≤ 40 := by
  unfold residualRadialField
  have h1 := abs_sub (2 * residualSqKernel s t)
    (residualWeightedGradS s t)
  have h2 := abs_sub
    (2 * residualSqKernel s t - residualWeightedGradS s t)
    (residualWeightedGradT s t)
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h1
  nlinarith [residualSqKernel_abs_le_four s t,
    residualWeightedGradS_abs_le_sixteen s t,
    residualWeightedGradT_abs_le_sixteen s t]

theorem residualSqKernel_abs_sub_le (s t s' t' : ℝ) :
    |residualSqKernel s t - residualSqKernel s' t'| ≤
      16 * |s - s'| + 8 * |t - t'| := by
  let r := gateResidual s t
  let r' := gateResidual s' t'
  have hr0 : 0 ≤ r := gateResidual_nonneg s t
  have hr0' : 0 ≤ r' := gateResidual_nonneg s' t'
  have hr2 : r ≤ 2 := gateResidual_le_two s t
  have hr2' : r' ≤ 2 := gateResidual_le_two s' t'
  have hdiff := gateResidual_abs_sub_le s t s' t'
  have heq : residualSqKernel s t - residualSqKernel s' t' =
      (r - r') * (r + r') := by unfold residualSqKernel r r'; ring
  rw [heq, abs_mul]
  have hsum : |r + r'| ≤ 4 := by
    rw [abs_of_nonneg (add_nonneg hr0 hr0')]
    linarith
  nlinarith [abs_nonneg (r - r')]

theorem residualGradS_abs_sub_le (s t s' t' : ℝ) :
    |residualGradS s t - residualGradS s' t'| ≤
      200 * (|s - s'| + |t - t'|) := by
  unfold residualGradS
  rw [show -2 * sigmaDeriv s * beta t * gateResidual s t -
      (-2 * sigmaDeriv s' * beta t' * gateResidual s' t') =
      -2 * (sigmaDeriv s * beta t * gateResidual s t -
        sigmaDeriv s' * beta t' * gateResidual s' t') by ring,
    abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have htri := abs_triple_sub_le (sigmaDeriv s) (beta t) (gateResidual s t)
    (sigmaDeriv s') (beta t') (gateResidual s' t')
  have hs := sigmaDeriv_abs_sub_le s s'
  have hs' := sigmaDeriv_abs_le_two s'
  have hb := beta_abs_sub_le t t'
  have hb0 := beta_abs_le_two t
  have hb' := beta_abs_le_two t'
  have hr := gateResidual_abs_sub_le s t s' t'
  have hr0 := gateResidual_nonneg s t
  have hr2 := gateResidual_le_two s t
  rw [abs_of_nonneg (gateResidual_nonneg s t)] at htri
  have h1 : |sigmaDeriv s - sigmaDeriv s'| * |beta t| *
      gateResidual s t ≤ (6 * |s - s'|) * 2 * 2 := by gcongr
  have h2 : |sigmaDeriv s'| * |beta t - beta t'| *
      gateResidual s t ≤ 2 * (2 * |t - t'|) * 2 := by gcongr
  have h3 : |sigmaDeriv s'| * |beta t'| *
      |gateResidual s t - gateResidual s' t'| ≤
        2 * 2 * (4 * |s - s'| + 2 * |t - t'|) := by gcongr
  calc
    2 * |sigmaDeriv s * beta t * gateResidual s t -
        sigmaDeriv s' * beta t' * gateResidual s' t'| ≤
        2 * (|sigmaDeriv s - sigmaDeriv s'| * |beta t| *
            gateResidual s t +
          |sigmaDeriv s'| * |beta t - beta t'| * gateResidual s t +
          |sigmaDeriv s'| * |beta t'| *
            |gateResidual s t - gateResidual s' t'|) :=
      mul_le_mul_of_nonneg_left htri (by norm_num)
    _ ≤ 2 * ((6 * |s - s'|) * 2 * 2 +
        2 * (2 * |t - t'|) * 2 +
        2 * 2 * (4 * |s - s'| + 2 * |t - t'|)) := by gcongr
    _ ≤ 200 * (|s - s'| + |t - t'|) := by
      nlinarith [abs_nonneg (s - s'), abs_nonneg (t - t')]

theorem residualGradT_abs_sub_le (s t s' t' : ℝ) :
    |residualGradT s t - residualGradT s' t'| ≤
      200 * (|s - s'| + |t - t'|) := by
  unfold residualGradT
  rw [show -2 * sigma s * betaDeriv t * gateResidual s t -
      (-2 * sigma s' * betaDeriv t' * gateResidual s' t') =
      -2 * (sigma s * betaDeriv t * gateResidual s t -
        sigma s' * betaDeriv t' * gateResidual s' t') by ring,
    abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have htri := abs_triple_sub_le (sigma s) (betaDeriv t) (gateResidual s t)
    (sigma s') (betaDeriv t') (gateResidual s' t')
  have hs := sigma_abs_sub_le s s'
  have hs' := sigma_abs_le_one s'
  have hb := betaDeriv_abs_sub_le t t'
  have hb0 := betaDeriv_abs_le_two t
  have hb' := betaDeriv_abs_le_two t'
  have hr := gateResidual_abs_sub_le s t s' t'
  have hr0 := gateResidual_nonneg s t
  have hr2 := gateResidual_le_two s t
  rw [abs_of_nonneg (gateResidual_nonneg s t)] at htri
  have h1 : |sigma s - sigma s'| * |betaDeriv t| * gateResidual s t ≤
      (2 * |s - s'|) * 2 * 2 := by gcongr
  have h2 : |sigma s'| * |betaDeriv t - betaDeriv t'| *
      gateResidual s t ≤ 1 * (8 * |t - t'|) * 2 := by gcongr
  have h3 : |sigma s'| * |betaDeriv t'| *
      |gateResidual s t - gateResidual s' t'| ≤
        1 * 2 * (4 * |s - s'| + 2 * |t - t'|) := by gcongr
  calc
    2 * |sigma s * betaDeriv t * gateResidual s t -
        sigma s' * betaDeriv t' * gateResidual s' t'| ≤ 2 *
        (|sigma s - sigma s'| * |betaDeriv t| * gateResidual s t +
          |sigma s'| * |betaDeriv t - betaDeriv t'| * gateResidual s t +
          |sigma s'| * |betaDeriv t'| *
            |gateResidual s t - gateResidual s' t'|) :=
      mul_le_mul_of_nonneg_left htri (by norm_num)
    _ ≤ 2 * ((2 * |s - s'|) * 2 * 2 +
        1 * (8 * |t - t'|) * 2 +
        1 * 2 * (4 * |s - s'| + 2 * |t - t'|)) := by gcongr
    _ ≤ 200 * (|s - s'| + |t - t'|) := by
      nlinarith [abs_nonneg (s - s'), abs_nonneg (t - t')]

theorem residualWeightedGradS_abs_sub_le (s t s' t' : ℝ) :
    |residualWeightedGradS s t - residualWeightedGradS s' t'| ≤
      400 * (|s - s'| + |t - t'|) := by
  unfold residualWeightedGradS
  rw [show -2 * sigmaWeightedDeriv s * beta t * gateResidual s t -
      (-2 * sigmaWeightedDeriv s' * beta t' * gateResidual s' t') =
      -2 * (sigmaWeightedDeriv s * beta t * gateResidual s t -
        sigmaWeightedDeriv s' * beta t' * gateResidual s' t') by ring,
    abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have htri := abs_triple_sub_le (sigmaWeightedDeriv s) (beta t)
    (gateResidual s t) (sigmaWeightedDeriv s') (beta t')
    (gateResidual s' t')
  have hs := sigmaWeightedDeriv_abs_sub_le s s'
  have hs' := sigmaWeightedDeriv_abs_le_two s'
  have hb := beta_abs_sub_le t t'
  have hb0 := beta_abs_le_two t
  have hb' := beta_abs_le_two t'
  have hr := gateResidual_abs_sub_le s t s' t'
  have hr0 := gateResidual_nonneg s t
  have hr2 := gateResidual_le_two s t
  rw [abs_of_nonneg (gateResidual_nonneg s t)] at htri
  have h1 : |sigmaWeightedDeriv s - sigmaWeightedDeriv s'| * |beta t| *
      gateResidual s t ≤ (30 * |s - s'|) * 2 * 2 := by gcongr
  have h2 : |sigmaWeightedDeriv s'| * |beta t - beta t'| *
      gateResidual s t ≤ 2 * (2 * |t - t'|) * 2 := by gcongr
  have h3 : |sigmaWeightedDeriv s'| * |beta t'| *
      |gateResidual s t - gateResidual s' t'| ≤
        2 * 2 * (4 * |s - s'| + 2 * |t - t'|) := by gcongr
  calc
    2 * |sigmaWeightedDeriv s * beta t * gateResidual s t -
        sigmaWeightedDeriv s' * beta t' * gateResidual s' t'| ≤ 2 *
        (|sigmaWeightedDeriv s - sigmaWeightedDeriv s'| * |beta t| *
            gateResidual s t +
          |sigmaWeightedDeriv s'| * |beta t - beta t'| * gateResidual s t +
          |sigmaWeightedDeriv s'| * |beta t'| *
            |gateResidual s t - gateResidual s' t'|) :=
      mul_le_mul_of_nonneg_left htri (by norm_num)
    _ ≤ 2 * ((30 * |s - s'|) * 2 * 2 +
        2 * (2 * |t - t'|) * 2 +
        2 * 2 * (4 * |s - s'| + 2 * |t - t'|)) := by gcongr
    _ ≤ 400 * (|s - s'| + |t - t'|) := by
      nlinarith [abs_nonneg (s - s'), abs_nonneg (t - t')]

theorem residualWeightedGradT_abs_sub_le (s t s' t' : ℝ) :
    |residualWeightedGradT s t - residualWeightedGradT s' t'| ≤
      400 * (|s - s'| + |t - t'|) := by
  unfold residualWeightedGradT
  rw [show -2 * sigma s * betaWeightedDeriv t * gateResidual s t -
      (-2 * sigma s' * betaWeightedDeriv t' * gateResidual s' t') =
      -2 * (sigma s * betaWeightedDeriv t * gateResidual s t -
        sigma s' * betaWeightedDeriv t' * gateResidual s' t') by ring,
    abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have htri := abs_triple_sub_le (sigma s) (betaWeightedDeriv t)
    (gateResidual s t) (sigma s') (betaWeightedDeriv t')
    (gateResidual s' t')
  have hs := sigma_abs_sub_le s s'
  have hs' := sigma_abs_le_one s'
  have hb := betaWeightedDeriv_abs_sub_le t t'
  have hb0 := betaWeightedDeriv_abs_le_four t
  have hb' := betaWeightedDeriv_abs_le_four t'
  have hr := gateResidual_abs_sub_le s t s' t'
  have hr0 := gateResidual_nonneg s t
  have hr2 := gateResidual_le_two s t
  rw [abs_of_nonneg (gateResidual_nonneg s t)] at htri
  have h1 : |sigma s - sigma s'| * |betaWeightedDeriv t| *
      gateResidual s t ≤ (2 * |s - s'|) * 4 * 2 := by gcongr
  have h2 : |sigma s'| * |betaWeightedDeriv t - betaWeightedDeriv t'| *
      gateResidual s t ≤ 1 * (18 * |t - t'|) * 2 := by gcongr
  have h3 : |sigma s'| * |betaWeightedDeriv t'| *
      |gateResidual s t - gateResidual s' t'| ≤
        1 * 4 * (4 * |s - s'| + 2 * |t - t'|) := by gcongr
  calc
    2 * |sigma s * betaWeightedDeriv t * gateResidual s t -
        sigma s' * betaWeightedDeriv t' * gateResidual s' t'| ≤ 2 *
        (|sigma s - sigma s'| * |betaWeightedDeriv t| * gateResidual s t +
          |sigma s'| * |betaWeightedDeriv t - betaWeightedDeriv t'| *
            gateResidual s t +
          |sigma s'| * |betaWeightedDeriv t'| *
            |gateResidual s t - gateResidual s' t'|) :=
      mul_le_mul_of_nonneg_left htri (by norm_num)
    _ ≤ 2 * ((2 * |s - s'|) * 4 * 2 +
        1 * (18 * |t - t'|) * 2 +
        1 * 4 * (4 * |s - s'| + 2 * |t - t'|)) := by gcongr
    _ ≤ 400 * (|s - s'| + |t - t'|) := by
      nlinarith [abs_nonneg (s - s'), abs_nonneg (t - t')]

theorem residualRadialField_abs_sub_le (s t s' t' : ℝ) :
    |residualRadialField s t - residualRadialField s' t'| ≤
      1000 * (|s - s'| + |t - t'|) := by
  unfold residualRadialField
  have hf := residualSqKernel_abs_sub_le s t s' t'
  have hs := residualWeightedGradS_abs_sub_le s t s' t'
  have ht := residualWeightedGradT_abs_sub_le s t s' t'
  have htri1 := abs_sub
    (2 * (residualSqKernel s t - residualSqKernel s' t'))
    (residualWeightedGradS s t - residualWeightedGradS s' t')
  have htri2 := abs_sub
    (2 * (residualSqKernel s t - residualSqKernel s' t') -
      (residualWeightedGradS s t - residualWeightedGradS s' t'))
    (residualWeightedGradT s t - residualWeightedGradT s' t')
  have heq :
      (2 * residualSqKernel s t - residualWeightedGradS s t -
          residualWeightedGradT s t) -
        (2 * residualSqKernel s' t' - residualWeightedGradS s' t' -
          residualWeightedGradT s' t') =
      2 * (residualSqKernel s t - residualSqKernel s' t') -
        (residualWeightedGradS s t - residualWeightedGradS s' t') -
        (residualWeightedGradT s t - residualWeightedGradT s' t') := by ring
  rw [heq]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at htri1
  nlinarith [abs_nonneg (s - s'), abs_nonneg (t - t')]

theorem gateResidual_scale_abs_sub_le {r R a b : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    r * |gateResidual (a / r) (b / r) -
      gateResidual (a / R) (b / R)| ≤ 8 * (R - r) := by
  have hs := sigma_scale_abs_sub_le hr hrR (v := a)
  have hb := beta_scale_abs_sub_le hr hrR (v := b)
  have hpos := posPart_abs_sub_le
    (1 - sigma (a / r) * beta (b / r))
    (1 - sigma (a / R) * beta (b / R))
  have hprod :
      |sigma (a / r) * beta (b / r) -
          sigma (a / R) * beta (b / R)| ≤
        |sigma (a / r) - sigma (a / R)| * |beta (b / r)| +
          |sigma (a / R)| * |beta (b / r) - beta (b / R)| := by
    have heq :
        sigma (a / r) * beta (b / r) - sigma (a / R) * beta (b / R) =
          (sigma (a / r) - sigma (a / R)) * beta (b / r) +
            sigma (a / R) * (beta (b / r) - beta (b / R)) := by ring
    rw [heq]
    calc
      |(sigma (a / r) - sigma (a / R)) * beta (b / r) +
          sigma (a / R) * (beta (b / r) - beta (b / R))| ≤
          |(sigma (a / r) - sigma (a / R)) * beta (b / r)| +
            |sigma (a / R) * (beta (b / r) - beta (b / R))| :=
        abs_add_le _ _
      _ = _ := by repeat' rw [abs_mul]
  unfold gateResidual
  have heq :
      (1 - sigma (a / r) * beta (b / r)) -
        (1 - sigma (a / R) * beta (b / R)) =
      -(sigma (a / r) * beta (b / r) -
        sigma (a / R) * beta (b / R)) := by ring
  rw [heq, abs_neg] at hpos
  have hbnd := beta_abs_le_two (b / r)
  have hsnd := sigma_abs_le_one (a / R)
  have h1 : r *
      (|sigma (a / r) - sigma (a / R)| * |beta (b / r)|) ≤
        (2 * (R - r)) * 2 := by
    calc
      r * (|sigma (a / r) - sigma (a / R)| * |beta (b / r)|) =
          (r * |sigma (a / r) - sigma (a / R)|) *
            |beta (b / r)| := by ring
      _ ≤ (2 * (R - r)) * 2 := by gcongr
  have h2 : r *
      (|sigma (a / R)| * |beta (b / r) - beta (b / R)|) ≤
        1 * (4 * (R - r)) := by
    calc
      r * (|sigma (a / R)| * |beta (b / r) - beta (b / R)|) =
          |sigma (a / R)| *
            (r * |beta (b / r) - beta (b / R)|) := by ring
      _ ≤ 1 * (4 * (R - r)) := by gcongr
  have hm := mul_le_mul_of_nonneg_left hprod hr.le
  rw [mul_add] at hm
  have hres := (mul_le_mul_of_nonneg_left hpos hr.le).trans
    (hm.trans (add_le_add h1 h2))
  nlinarith [sub_nonneg.mpr hrR]

private theorem scaled_triple_bound
    {r x x' y y' z z' A B C : ℝ} (hr : 0 ≤ r)
    (hx : r * |x - x'| ≤ A) (hy : r * |y - y'| ≤ B)
    (hz : r * |z - z'| ≤ C)
    (hx' : |x'| ≤ 2) (hy0 : |y| ≤ 4) (hy' : |y'| ≤ 4)
    (hz0 : |z| ≤ 2) :
    r * |x * y * z - x' * y' * z'| ≤
      A * 4 * 2 + 2 * B * 2 + 2 * 4 * C := by
  have htri := abs_triple_sub_le x y z x' y' z'
  have hm := mul_le_mul_of_nonneg_left htri hr
  rw [mul_add, mul_add] at hm
  have hA0 : 0 ≤ A := (mul_nonneg hr (abs_nonneg (x - x'))).trans hx
  have hB0 : 0 ≤ B := (mul_nonneg hr (abs_nonneg (y - y'))).trans hy
  have hC0 : 0 ≤ C := (mul_nonneg hr (abs_nonneg (z - z'))).trans hz
  have h1 : r * (|x - x'| * |y| * |z|) ≤ A * 4 * 2 := by
    calc
      r * (|x - x'| * |y| * |z|) =
          (r * |x - x'|) * |y| * |z| := by ring
      _ ≤ A * 4 * 2 := by gcongr
  have h2 : r * (|x'| * |y - y'| * |z|) ≤ 2 * B * 2 := by
    calc
      r * (|x'| * |y - y'| * |z|) =
          |x'| * (r * |y - y'|) * |z| := by ring
      _ ≤ 2 * B * 2 := by gcongr
  have h3 : r * (|x'| * |y'| * |z - z'|) ≤ 2 * 4 * C := by
    calc
      r * (|x'| * |y'| * |z - z'|) =
          |x'| * |y'| * (r * |z - z'|) := by ring
      _ ≤ 2 * 4 * C := by gcongr
  exact hm.trans (add_le_add (add_le_add h1 h2) h3)

theorem residualGradS_scale_abs_sub_le {r R a b : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    r * |residualGradS (a / r) (b / r) -
      residualGradS (a / R) (b / R)| ≤ 300 * (R - r) := by
  unfold residualGradS
  rw [show -2 * sigmaDeriv (a / r) * beta (b / r) *
      gateResidual (a / r) (b / r) -
      (-2 * sigmaDeriv (a / R) * beta (b / R) *
        gateResidual (a / R) (b / R)) =
      -2 * (sigmaDeriv (a / r) * beta (b / r) *
        gateResidual (a / r) (b / r) -
        sigmaDeriv (a / R) * beta (b / R) *
          gateResidual (a / R) (b / R)) by ring,
    abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := scaled_triple_bound hr.le
    (sigmaDeriv_scale_abs_sub_le hr hrR)
    (beta_scale_abs_sub_le hr hrR)
    (gateResidual_scale_abs_sub_le hr hrR)
    (sigmaDeriv_abs_le_two (a / R))
    (by nlinarith [beta_abs_le_two (b / r)])
    (by nlinarith [beta_abs_le_two (b / R)])
    (by simpa [abs_of_nonneg (gateResidual_nonneg _ _)] using
      gateResidual_le_two (a / r) (b / r))
  calc
    r * (2 * |sigmaDeriv (a / r) * beta (b / r) *
        gateResidual (a / r) (b / r) -
        sigmaDeriv (a / R) * beta (b / R) *
          gateResidual (a / R) (b / R)|) =
        2 * (r * |sigmaDeriv (a / r) * beta (b / r) *
          gateResidual (a / r) (b / r) -
          sigmaDeriv (a / R) * beta (b / R) *
            gateResidual (a / R) (b / R)|) := by ring
    _ ≤ 2 * ((6 * (R - r)) * 4 * 2 +
        2 * (4 * (R - r)) * 2 + 2 * 4 * (8 * (R - r))) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 300 * (R - r) := by nlinarith [sub_nonneg.mpr hrR]

theorem residualGradT_scale_abs_sub_le {r R a b : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    r * |residualGradT (a / r) (b / r) -
      residualGradT (a / R) (b / R)| ≤ 300 * (R - r) := by
  unfold residualGradT
  rw [show -2 * sigma (a / r) * betaDeriv (b / r) *
      gateResidual (a / r) (b / r) -
      (-2 * sigma (a / R) * betaDeriv (b / R) *
        gateResidual (a / R) (b / R)) =
      -2 * (sigma (a / r) * betaDeriv (b / r) *
        gateResidual (a / r) (b / r) -
        sigma (a / R) * betaDeriv (b / R) *
          gateResidual (a / R) (b / R)) by ring,
    abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := scaled_triple_bound hr.le
    (sigma_scale_abs_sub_le hr hrR)
    (betaDeriv_scale_abs_sub_le hr hrR)
    (gateResidual_scale_abs_sub_le hr hrR)
    (by nlinarith [sigma_abs_le_one (a / R)])
    (by nlinarith [betaDeriv_abs_le_two (b / r)])
    (by nlinarith [betaDeriv_abs_le_two (b / R)])
    (by simpa [abs_of_nonneg (gateResidual_nonneg _ _)] using
      gateResidual_le_two (a / r) (b / r))
  calc
    r * (2 * |sigma (a / r) * betaDeriv (b / r) *
        gateResidual (a / r) (b / r) -
        sigma (a / R) * betaDeriv (b / R) *
          gateResidual (a / R) (b / R)|) =
        2 * (r * |sigma (a / r) * betaDeriv (b / r) *
          gateResidual (a / r) (b / r) -
          sigma (a / R) * betaDeriv (b / R) *
            gateResidual (a / R) (b / R)|) := by ring
    _ ≤ 2 * ((2 * (R - r)) * 4 * 2 +
        2 * (16 * (R - r)) * 2 + 2 * 4 * (8 * (R - r))) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 300 * (R - r) := by nlinarith [sub_nonneg.mpr hrR]

theorem residualWeightedGradS_scale_abs_sub_le {r R a b : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    r * |residualWeightedGradS (a / r) (b / r) -
      residualWeightedGradS (a / R) (b / R)| ≤ 700 * (R - r) := by
  unfold residualWeightedGradS
  rw [show -2 * sigmaWeightedDeriv (a / r) * beta (b / r) *
      gateResidual (a / r) (b / r) -
      (-2 * sigmaWeightedDeriv (a / R) * beta (b / R) *
        gateResidual (a / R) (b / R)) =
      -2 * (sigmaWeightedDeriv (a / r) * beta (b / r) *
        gateResidual (a / r) (b / r) -
        sigmaWeightedDeriv (a / R) * beta (b / R) *
          gateResidual (a / R) (b / R)) by ring,
    abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := scaled_triple_bound hr.le
    (sigmaWeightedDeriv_scale_abs_sub_le hr hrR)
    (beta_scale_abs_sub_le hr hrR)
    (gateResidual_scale_abs_sub_le hr hrR)
    (sigmaWeightedDeriv_abs_le_two (a / R))
    (by nlinarith [beta_abs_le_two (b / r)])
    (by nlinarith [beta_abs_le_two (b / R)])
    (by simpa [abs_of_nonneg (gateResidual_nonneg _ _)] using
      gateResidual_le_two (a / r) (b / r))
  calc
    r * (2 * |sigmaWeightedDeriv (a / r) * beta (b / r) *
        gateResidual (a / r) (b / r) -
        sigmaWeightedDeriv (a / R) * beta (b / R) *
          gateResidual (a / R) (b / R)|) =
        2 * (r * |sigmaWeightedDeriv (a / r) * beta (b / r) *
          gateResidual (a / r) (b / r) -
          sigmaWeightedDeriv (a / R) * beta (b / R) *
            gateResidual (a / R) (b / R)|) := by ring
    _ ≤ 2 * ((30 * (R - r)) * 4 * 2 +
        2 * (4 * (R - r)) * 2 + 2 * 4 * (8 * (R - r))) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 700 * (R - r) := by nlinarith [sub_nonneg.mpr hrR]

theorem residualWeightedGradT_scale_abs_sub_le {r R a b : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    r * |residualWeightedGradT (a / r) (b / r) -
      residualWeightedGradT (a / R) (b / R)| ≤ 500 * (R - r) := by
  unfold residualWeightedGradT
  rw [show -2 * sigma (a / r) * betaWeightedDeriv (b / r) *
      gateResidual (a / r) (b / r) -
      (-2 * sigma (a / R) * betaWeightedDeriv (b / R) *
        gateResidual (a / R) (b / R)) =
      -2 * (sigma (a / r) * betaWeightedDeriv (b / r) *
        gateResidual (a / r) (b / r) -
        sigma (a / R) * betaWeightedDeriv (b / R) *
          gateResidual (a / R) (b / R)) by ring,
    abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have h := scaled_triple_bound hr.le
    (sigma_scale_abs_sub_le hr hrR)
    (betaWeightedDeriv_scale_abs_sub_le hr hrR)
    (gateResidual_scale_abs_sub_le hr hrR)
    (by nlinarith [sigma_abs_le_one (a / R)])
    (betaWeightedDeriv_abs_le_four (b / r))
    (betaWeightedDeriv_abs_le_four (b / R))
    (by simpa [abs_of_nonneg (gateResidual_nonneg _ _)] using
      gateResidual_le_two (a / r) (b / r))
  calc
    r * (2 * |sigma (a / r) * betaWeightedDeriv (b / r) *
        gateResidual (a / r) (b / r) -
        sigma (a / R) * betaWeightedDeriv (b / R) *
          gateResidual (a / R) (b / R)|) =
        2 * (r * |sigma (a / r) * betaWeightedDeriv (b / r) *
          gateResidual (a / r) (b / r) -
          sigma (a / R) * betaWeightedDeriv (b / R) *
            gateResidual (a / R) (b / R)|) := by ring
    _ ≤ 2 * ((2 * (R - r)) * 4 * 2 +
        2 * (36 * (R - r)) * 2 + 2 * 4 * (8 * (R - r))) :=
      mul_le_mul_of_nonneg_left h (by norm_num)
    _ ≤ 500 * (R - r) := by nlinarith [sub_nonneg.mpr hrR]

theorem residualSqKernel_scale_abs_sub_le {r R a b : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    r * |residualSqKernel (a / r) (b / r) -
      residualSqKernel (a / R) (b / R)| ≤ 32 * (R - r) := by
  let z := gateResidual (a / r) (b / r)
  let w := gateResidual (a / R) (b / R)
  have hz0 := gateResidual_nonneg (a / r) (b / r)
  have hw0 := gateResidual_nonneg (a / R) (b / R)
  have hz2 := gateResidual_le_two (a / r) (b / r)
  have hw2 := gateResidual_le_two (a / R) (b / R)
  have hd := gateResidual_scale_abs_sub_le hr hrR (a := a) (b := b)
  have heq : residualSqKernel (a / r) (b / r) -
      residualSqKernel (a / R) (b / R) = (z - w) * (z + w) := by
    unfold residualSqKernel z w
    ring
  rw [heq, abs_mul]
  have hsum : |z + w| ≤ 4 := by
    rw [abs_of_nonneg (add_nonneg hz0 hw0)]
    linarith
  calc
    r * (|z - w| * |z + w|) = (r * |z - w|) * |z + w| := by ring
    _ ≤ (8 * (R - r)) * 4 := by gcongr
    _ = 32 * (R - r) := by ring

theorem residualRadialField_scale_abs_sub_le {r R a b : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) :
    r * |residualRadialField (a / r) (b / r) -
      residualRadialField (a / R) (b / R)| ≤ 1500 * (R - r) := by
  have hf := residualSqKernel_scale_abs_sub_le hr hrR (a := a) (b := b)
  have hs := residualWeightedGradS_scale_abs_sub_le hr hrR (a := a) (b := b)
  have ht := residualWeightedGradT_scale_abs_sub_le hr hrR (a := a) (b := b)
  unfold residualRadialField
  have heq :
      (2 * residualSqKernel (a / r) (b / r) -
          residualWeightedGradS (a / r) (b / r) -
          residualWeightedGradT (a / r) (b / r)) -
        (2 * residualSqKernel (a / R) (b / R) -
          residualWeightedGradS (a / R) (b / R) -
          residualWeightedGradT (a / R) (b / R)) =
      2 * (residualSqKernel (a / r) (b / r) -
          residualSqKernel (a / R) (b / R)) -
        (residualWeightedGradS (a / r) (b / r) -
          residualWeightedGradS (a / R) (b / R)) -
        (residualWeightedGradT (a / r) (b / r) -
          residualWeightedGradT (a / R) (b / R)) := by ring
  rw [heq]
  have htri1 := abs_sub
    (2 * (residualSqKernel (a / r) (b / r) -
      residualSqKernel (a / R) (b / R)))
    (residualWeightedGradS (a / r) (b / r) -
      residualWeightedGradS (a / R) (b / R))
  have htri2 := abs_sub
    (2 * (residualSqKernel (a / r) (b / r) -
        residualSqKernel (a / R) (b / R)) -
      (residualWeightedGradS (a / r) (b / r) -
        residualWeightedGradS (a / R) (b / R)))
    (residualWeightedGradT (a / r) (b / r) -
      residualWeightedGradT (a / R) (b / R))
  have hm1 := mul_le_mul_of_nonneg_left htri1 hr.le
  have hm2 := mul_le_mul_of_nonneg_left htri2 hr.le
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hm1
  rw [mul_add] at hm1 hm2
  have hf2 : r * (2 * |residualSqKernel (a / r) (b / r) -
      residualSqKernel (a / R) (b / R)|) ≤ 64 * (R - r) := by
    calc
      r * (2 * |residualSqKernel (a / r) (b / r) -
          residualSqKernel (a / R) (b / R)|) =
          2 * (r * |residualSqKernel (a / r) (b / r) -
            residualSqKernel (a / R) (b / R)|) := by ring
      _ ≤ 2 * (32 * (R - r)) :=
        mul_le_mul_of_nonneg_left hf (by norm_num)
      _ = 64 * (R - r) := by ring
  have hmiddle :
      r * |2 * (residualSqKernel (a / r) (b / r) -
          residualSqKernel (a / R) (b / R)) -
        (residualWeightedGradS (a / r) (b / r) -
          residualWeightedGradS (a / R) (b / R))| ≤
        64 * (R - r) + 700 * (R - r) := by
    exact hm1.trans (add_le_add hf2 hs)
  exact hm2.trans <| (add_le_add hmiddle ht).trans <| by
    nlinarith [sub_nonneg.mpr hrR]

end

end NCPLVerification
