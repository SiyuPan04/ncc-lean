import NCCLowerBoundVerification.Basic

/-!
# Algebraic core of the relative FOAM block

This module formalizes the independently checkable part of TeX
910--1213: `ub:eq:foam-parameters`, `ub:eq:relative-energy`, the extrapolated
centres and residuals, `ub:eq:relative-residual`, the slow updates,
`ub:eq:projected-micro`, the geometric finite-horizon stopping calculation,
`ub:eq:one-step-contraction` to `ub:eq:block-contraction`, and
`ub:lem:fast-readout`.

The analytic facts not yet available in the project are exposed as theorem
parameters at their exact point of use:

* contraction of one projected step toward a solution;
* the residual and reverse-triangle estimates for that projected step;
* contraction of one composite FOAM macrostep;
* strong convexity of `P` and nonexpansiveness of the primal projection.

No convergence statement is stored in a state or output structure.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace RelativeFOAM

noncomputable section

/-- TeX `ub:eq:foam-parameters`. -/
def theta (mu : ℝ) : ℝ := 8 / mu

def alpha (mu r : ℝ) : ℝ := Real.sqrt (theta mu * r)

def etaQ (mu : ℝ) : ℝ := mu / 2

def etaY (mu r : ℝ) : ℝ := theta mu / (2 * alpha mu r)

/-- Numerical constants in TeX `ub:eq:projected-micro`. -/
def M0 : ℝ := 32

def projectedEta : ℝ := M0⁻¹ ^ 2

def projectedChi : ℝ := Real.sqrt (1 - M0⁻¹ ^ 2)

theorem theta_pos {mu : ℝ} (hmu : 0 < mu) : 0 < theta mu := by
  unfold theta
  positivity

theorem alpha_pos {mu r : ℝ} (hmu : 0 < mu) (hr : 0 < r) :
    0 < alpha mu r := by
  unfold alpha
  exact Real.sqrt_pos.2 (mul_pos (theta_pos hmu) hr)

/-- Under the paper's range `r ≤ mu / 8`, the contraction parameter is at most one. -/
theorem alpha_le_one {mu r : ℝ} (hmu : 0 < mu) (hr : 0 ≤ r)
    (hrmu : r ≤ mu / 8) : alpha mu r ≤ 1 := by
  have harg0 : 0 ≤ theta mu * r := mul_nonneg (theta_pos hmu).le hr
  have h8r : 8 * r ≤ mu := by nlinarith
  have harg1 : theta mu * r ≤ 1 := by
    unfold theta
    calc
      8 / mu * r = (8 * r) / mu := by ring
      _ ≤ 1 := (div_le_iff₀ hmu).2 (by simpa using h8r)
  have hsqrt := Real.sq_sqrt harg0
  have hsqrt0 := Real.sqrt_nonneg (theta mu * r)
  unfold alpha
  nlinarith

/-- Slow and fast variables retained by one relative FOAM component. -/
structure State (m n : Nat) where
  q : EVec m
  y : EVec n
  qFast : EVec m
  yFast : EVec n

/-- Data returned by the feasible micro-solver; no correctness is hidden here. -/
structure MicroOutput (m n : Nat) where
  xFast : EVec m
  yFastNext : EVec n
  qFastNext : EVec m
  wFastNext : EVec n

/-- TeX `ub:eq:relative-energy`, with `P`, its optimum, and its minimizer explicit. -/
def energy {m n : Nat} (mu r : ℝ) (qStar : EVec m) (yStar : EVec n)
    (P : EVec m → EVec n → ℝ) (PStar : ℝ) (S : State m n) : ℝ :=
  2 * alpha mu r / mu * vecSq (S.q - qStar) +
    2 * r * vecSq (S.y - yStar) +
    2 * (P S.qFast S.yFast - PStar)

def qCenter {m n : Nat} (mu r : ℝ) (S : State m n) : EVec m :=
  alpha mu r • S.q + (1 - alpha mu r) • S.qFast

def yCenter {m n : Nat} (mu r : ℝ) (S : State m n) : EVec n :=
  alpha mu r • S.y + (1 - alpha mu r) • S.yFast

/-- The two residuals immediately preceding TeX `ub:eq:relative-residual`. -/
def residualX {m n : Nat} (mu r : ℝ) (S : State m n)
    (O : MicroOutput m n) : EVec m :=
  O.qFastNext + (mu / 2) • (O.xFast - mu⁻¹ • qCenter mu r S)

def residualY {m n : Nat} (mu r : ℝ) (S : State m n)
    (O : MicroOutput m n) : EVec n :=
  O.wFastNext + r • O.yFastNext +
    (theta mu)⁻¹ • (O.yFastNext - yCenter mu r S)

/-- TeX `ub:eq:relative-residual`, in the paper's explicit squared norm. -/
def RelativeResidual {m n : Nat} (mu r : ℝ) (S : State m n)
    (O : MicroOutput m n) : Prop :=
  8 / mu * vecSq (residualX mu r S O) +
      theta mu * vecSq (residualY mu r S O) ≤
    mu / 8 * vecSq (O.xFast + mu⁻¹ • qCenter mu r S) +
      (theta mu)⁻¹ * vecSq (O.yFastNext - yCenter mu r S)

/-- TeX `ub:eq:slow-q-update`. -/
def slowQNext {m n : Nat} (mu _r : ℝ) (S : State m n)
    (O : MicroOutput m n) : EVec m :=
  S.q + etaQ mu • (mu⁻¹ • (O.qFastNext - S.q)) -
    etaQ mu • (O.xFast + mu⁻¹ • O.qFastNext)

/-- TeX `ub:eq:slow-y-update`. -/
def slowYNext {m n : Nat} (mu r : ℝ) (S : State m n)
    (O : MicroOutput m n) : EVec n :=
  S.y + etaY mu r • (r • (O.yFastNext - S.y)) -
    etaY mu r • (O.wFastNext + r • O.yFastNext)

/-- The explicit state update denoted `RF` in the paper. -/
def update {m n : Nat} (mu r : ℝ) (S : State m n)
    (O : MicroOutput m n) : State m n where
  q := slowQNext mu r S O
  y := slowYNext mu r S O
  qFast := O.qFastNext
  yFast := O.yFastNext

/-- Coordinate definition of the Euclidean normal cone used by the micro relations. -/
def IsEuclideanNormal {d : Nat} (C : Set (EVec d))
    (x b : EVec d) : Prop :=
  ∀ z ∈ C, (∑ i : Fin d, b i * (z i - x i)) ≤ 0

theorem IsEuclideanNormal.nonneg_smul {d : Nat} {C : Set (EVec d)}
    {x b : EVec d} (hb : IsEuclideanNormal C x b) {a : ℝ} (ha : 0 ≤ a) :
    IsEuclideanNormal C x (a • b) := by
  intro z hz
  have h := hb z hz
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i : Fin d, a * b i * (z i - x i)) =
        a * ∑ i : Fin d, b i * (z i - x i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha h

/-- TeX `ub:eq:micro-normal-x` and `ub:eq:micro-normal-y`. -/
def MicroNormalRelations {m n : Nat} (X : Set (EVec m)) (Y : Set (EVec n))
    (gradXHat : EVec m → EVec n → EVec m)
    (gradYHat : EVec m → EVec n → EVec n)
    (O : MicroOutput m n) : Prop :=
  IsEuclideanNormal X O.xFast
      (O.qFastNext - gradXHat O.xFast O.yFastNext) ∧
    IsEuclideanNormal Y O.yFastNext
      (O.wFastNext + gradYHat O.xFast O.yFastNext)

/-! ## Projected micro-solver recurrence -/

/-- TeX `ub:eq:projected-micro`, for an explicit projection map and operator. -/
def projectedIterate {d : Nat} (project : EVec d → EVec d)
    (A : EVec d → EVec d) (eta : ℝ) (uMinusOne : EVec d) :
    Nat → EVec d
  | 0 => project uMinusOne
  | s + 1 => project (projectedIterate project A eta uMinusOne s -
      eta • A (projectedIterate project A eta uMinusOne s))

/-- Every projected iterate is feasible if the projection has feasible range. -/
theorem projectedIterate_mem {d : Nat} {C : Set (EVec d)}
    (project : EVec d → EVec d) (A : EVec d → EVec d)
    (eta : ℝ) (uMinusOne : EVec d)
    (hproject : ∀ u, project u ∈ C) (s : Nat) :
    projectedIterate project A eta uMinusOne s ∈ C := by
  cases s with
  | zero => exact hproject uMinusOne
  | succ s => exact hproject _

/-- The vector `b_{s+1}` associated with one projected step. -/
def projectedB {d : Nat} (project : EVec d → EVec d)
    (A : EVec d → EVec d) (eta : ℝ) (uMinusOne : EVec d)
    (s : Nat) : EVec d :=
  eta⁻¹ •
    (projectedIterate project A eta uMinusOne s -
      eta • A (projectedIterate project A eta uMinusOne s) -
      projectedIterate project A eta uMinusOne (s + 1))

/-- Algebraic residual identity used in the feasible-micro proof. -/
theorem operator_add_projectedB {d : Nat} (project : EVec d → EVec d)
    (A : EVec d → EVec d) {eta : ℝ} (heta : eta ≠ 0)
    (uMinusOne : EVec d) (s : Nat) :
    A (projectedIterate project A eta uMinusOne (s + 1)) +
        projectedB project A eta uMinusOne s =
      A (projectedIterate project A eta uMinusOne (s + 1)) -
        A (projectedIterate project A eta uMinusOne s) +
        eta⁻¹ •
          (projectedIterate project A eta uMinusOne s -
            projectedIterate project A eta uMinusOne (s + 1)) := by
  funext i
  simp only [projectedB, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp [heta]
  ring

/-- A projection-normality specification implies `b_{s+1}` is a true normal. -/
theorem projectedB_normal {d : Nat} {C : Set (EVec d)}
    (project : EVec d → EVec d) (A : EVec d → EVec d)
    {eta : ℝ} (heta : 0 < eta) (uMinusOne : EVec d)
    (hprojectNormal : ∀ u,
      IsEuclideanNormal C (project u) (u - project u)) (s : Nat) :
    IsEuclideanNormal C
      (projectedIterate project A eta uMinusOne (s + 1))
      (projectedB project A eta uMinusOne s) := by
  let u := projectedIterate project A eta uMinusOne s
  let pre := u - eta • A u
  have hnext : projectedIterate project A eta uMinusOne (s + 1) = project pre := by
    simp [projectedIterate, pre, u]
  have hnormal := hprojectNormal pre
  rw [hnext]
  have hscaled := hnormal.nonneg_smul (inv_nonneg.2 heta.le)
  simpa [projectedB, u, pre, hnext] using hscaled

/-! ## Geometric stopping calculation in `ub:lem:feasible-micro` -/

/-- Iterating a scalar one-step contraction gives its geometric bound. -/
theorem geometric_bound (chi R : ℝ) (d : Nat → ℝ)
    (hchi : 0 ≤ chi) (h0 : d 0 ≤ R)
    (hstep : ∀ s, d (s + 1) ≤ chi * d s) :
    ∀ s, d s ≤ chi ^ s * R := by
  intro s
  induction s with
  | zero => simpa using h0
  | succ s ih =>
      calc
        d (s + 1) ≤ chi * d s := hstep s
        _ ≤ chi * (chi ^ s * R) := mul_le_mul_of_nonneg_left ih hchi
        _ = chi ^ (s + 1) * R := by rw [pow_succ]; ring

/-- The consecutive-step estimate appearing in the residual calculation. -/
theorem step_size_geometric_bound {chi R : ℝ} {d stepSize : Nat → ℝ}
    (_hchi : 0 ≤ chi) (_hR : 0 ≤ R)
    (hd : ∀ s, d s ≤ chi ^ s * R)
    (hstepSize : ∀ s, stepSize (s + 1) ≤ d (s + 1) + d s) :
    ∀ s, stepSize (s + 1) ≤ (1 + chi) * chi ^ s * R := by
  intro s
  calc
    stepSize (s + 1) ≤ d (s + 1) + d s := hstepSize s
    _ ≤ chi ^ (s + 1) * R + chi ^ s * R := add_le_add (hd _) (hd _)
    _ = (1 + chi) * chi ^ s * R := by rw [pow_succ]; ring

/-- Combining the operator estimate with the step-size estimate gives the TeX residual bound. -/
theorem residual_geometric_bound {M chi R : ℝ}
    {stepSize residualSize : Nat → ℝ} (hcoeff : 0 ≤ M + M ^ 2)
    (hstep : ∀ s, stepSize (s + 1) ≤ (1 + chi) * chi ^ s * R)
    (hresidual : ∀ s,
      residualSize (s + 1) ≤ (M + M ^ 2) * stepSize (s + 1)) :
    ∀ s, residualSize (s + 1) ≤
      (M + M ^ 2) * (1 + chi) * chi ^ s * R := by
  intro s
  exact (hresidual s).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hstep s) hcoeff)

/-- The reverse-triangle lower bound used for the stopping-test denominator. -/
theorem center_distance_lower_bound {chi R : ℝ}
    {d centerDistance : Nat → ℝ} (_hR : 0 ≤ R)
    (hd : ∀ s, d s ≤ chi ^ s * R)
    (hreverse : ∀ s, R ≤ centerDistance s + d s) :
    ∀ s, (1 - chi ^ s) * R ≤ centerDistance s := by
  intro s
  have hs := hd s
  have hr := hreverse s
  linarith

/--
The numerical stopping implication.  The two vector-analytic estimates are
the explicit hypotheses `hresidual` and `hcenter`; the remaining argument is
pure scalar algebra.
-/
theorem scaled_stopping_of_geometric_bounds {M chi R : ℝ}
    {N : Nat} (_hM : 0 ≤ M) (hR : 0 ≤ R)
    (residualSize centerDistance : Nat → ℝ)
    (hresidual : residualSize N ≤
      (M + M ^ 2) * (1 + chi) * chi ^ (N - 1) * R)
    (hcenter : (1 - chi ^ N) * R ≤ centerDistance N)
    (hN : (M + M ^ 2) * (1 + chi) * chi ^ (N - 1) ≤
      1 - chi ^ N) :
    residualSize N ≤ centerDistance N := by
  calc
    residualSize N ≤
        (M + M ^ 2) * (1 + chi) * chi ^ (N - 1) * R := hresidual
    _ ≤ (1 - chi ^ N) * R := mul_le_mul_of_nonneg_right hN hR
    _ ≤ centerDistance N := hcenter

/-! ## Relative contraction and exact iteration costs -/

/-- Repeated application of the one-step energy contraction. -/
theorem iterate_energy_le {S : Type*} (step : S → S) (E : S → ℝ)
    (c : ℝ) (hc : 0 ≤ c) (hone : ∀ s, E (step s) ≤ c * E s) :
    ∀ k s, E (step^[k] s) ≤ c ^ k * E s := by
  intro k
  induction k with
  | zero => intro s; simp
  | succ k ih =>
      intro s
      rw [Function.iterate_succ_apply]
      calc
        E ((step^[k]) (step s)) ≤ c ^ k * E (step s) := ih _
        _ ≤ c ^ k * (c * E s) :=
          mul_le_mul_of_nonneg_left (hone s) (pow_nonneg hc k)
        _ = c ^ (k + 1) * E s := by rw [pow_succ]; ring

/-- TeX `ub:eq:block-contraction`, with the scalar exponential estimate explicit. -/
theorem block_energy_le {S : Type*} (step : S → S) (E : S → ℝ)
    (alpha rho : ℝ) (K : Nat) (S0 : S)
    (halpha : alpha ≤ 2) (hE : 0 ≤ E S0)
    (hone : ∀ s, E (step s) ≤ (1 - alpha / 2) * E s)
    (hgeometric : (1 - alpha / 2) ^ K ≤ rho) :
    E (step^[K] S0) ≤ rho * E S0 := by
  have hc : 0 ≤ 1 - alpha / 2 := by linarith
  calc
    E (step^[K] S0) ≤ (1 - alpha / 2) ^ K * E S0 :=
      iterate_energy_le step E _ hc hone K S0
    _ ≤ rho * E S0 := mul_le_mul_of_nonneg_right hgeometric hE

/-- The TeX choice before `ub:eq:block-contraction`. -/
def blockIterations (alpha rho : ℝ) : Nat :=
  ⌈(2 / alpha * Real.log (1 / rho))⌉₊

/-- The TeX ceiling choice really reduces the geometric factor below `rho`. -/
theorem blockIterations_geometric {alpha rho : ℝ}
    (halpha : 0 < alpha) (halpha2 : alpha ≤ 2)
    (hrho : 0 < rho) (_hrho1 : rho < 1) :
    (1 - alpha / 2) ^ blockIterations alpha rho ≤ rho := by
  have hc0 : 0 ≤ 1 - alpha / 2 := by linarith
  have hbase : 1 - alpha / 2 ≤ Real.exp (-(alpha / 2)) :=
    Real.one_sub_le_exp_neg (alpha / 2)
  have hpow :
      (1 - alpha / 2) ^ blockIterations alpha rho ≤
        (Real.exp (-(alpha / 2))) ^ blockIterations alpha rho := by
    gcongr
  have hceil :
      2 / alpha * Real.log (1 / rho) ≤
        (blockIterations alpha rho : ℝ) := by
    exact Nat.le_ceil _
  have hneg :
      (blockIterations alpha rho : ℝ) * (-(alpha / 2)) ≤
        -Real.log (1 / rho) := by
    calc
      (blockIterations alpha rho : ℝ) * (-(alpha / 2)) ≤
          (2 / alpha * Real.log (1 / rho)) * (-(alpha / 2)) :=
        mul_le_mul_of_nonpos_right hceil (by linarith)
      _ = -Real.log (1 / rho) := by field_simp [ne_of_gt halpha]
  calc
    (1 - alpha / 2) ^ blockIterations alpha rho ≤
        (Real.exp (-(alpha / 2))) ^ blockIterations alpha rho := hpow
    _ = Real.exp ((blockIterations alpha rho : ℝ) * (-(alpha / 2))) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp (-Real.log (1 / rho)) := Real.exp_le_exp.mpr hneg
    _ = rho := by
      rw [Real.exp_neg, Real.exp_log (div_pos one_pos hrho)]
      field_simp [ne_of_gt hrho]

/-- The ceiling incurs less than one additional macrostep. -/
theorem blockIterations_lt {alpha rho : ℝ}
    (halpha : 0 < alpha) (hrho : 0 < rho) (hrho1 : rho < 1) :
    (blockIterations alpha rho : ℝ) <
      2 / alpha * Real.log (1 / rho) + 1 := by
  have hinv : 1 < 1 / rho := (lt_div_iff₀ hrho).2 (by simpa using hrho1)
  have hlog : 0 < Real.log (1 / rho) := Real.log_pos hinv
  have harg : 0 ≤ 2 / alpha * Real.log (1 / rho) := by positivity
  exact Nat.ceil_lt_add_one harg

/-- Relative contraction for exactly the block length specified in the TeX. -/
theorem block_energy_le_at_blockIterations {S : Type*}
    (step : S → S) (E : S → ℝ) (alpha rho : ℝ) (S0 : S)
    (halpha : 0 < alpha) (halpha2 : alpha ≤ 2)
    (hrho : 0 < rho) (hrho1 : rho < 1) (hE : 0 ≤ E S0)
    (hone : ∀ s, E (step s) ≤ (1 - alpha / 2) * E s) :
    E (step^[blockIterations alpha rho] S0) ≤ rho * E S0 :=
  block_energy_le step E alpha rho (blockIterations alpha rho) S0
    halpha2 hE hone (blockIterations_geometric halpha halpha2 hrho hrho1)

/-- Exact accounting behind the asymptotic block-cost statement. -/
structure Cost where
  oracleCalls : Nat
  projections : Nat

def blockCost (oneStep : Cost) (K : Nat) : Cost where
  oracleCalls := K * oneStep.oracleCalls
  projections := K * oneStep.projections

@[simp] theorem blockCost_oracleCalls (oneStep : Cost) (K : Nat) :
    (blockCost oneStep K).oracleCalls = K * oneStep.oracleCalls := rfl

@[simp] theorem blockCost_projections (oneStep : Cost) (K : Nat) :
    (blockCost oneStep K).projections = K * oneStep.projections := rfl

/-- Initial projection plus `N` projected updates and their reused oracle tests. -/
def projectedMicroCost (N : Nat) : Cost where
  oracleCalls := N + 1
  projections := N + 1

@[simp] theorem projectedMicroCost_oracleCalls (N : Nat) :
    (projectedMicroCost N).oracleCalls = N + 1 := rfl

@[simp] theorem projectedMicroCost_projections (N : Nat) :
    (projectedMicroCost N).projections = N + 1 := rfl

/-! ## Fast-state readout -/

/--
Algebraic form of `ub:lem:fast-readout`.  `hstrong` is exactly the strong
convexity gap bound, and `hproject` is exactly projection nonexpansiveness.
-/
theorem fastState_readout {m n : Nat} {mu alphaR r : ℝ}
    (hmu : 0 < mu) (halphaR : 0 ≤ alphaR) (hr : 0 ≤ r)
    {qStar : EVec m} {yStar : EVec n} {xStar : EVec m}
    {P : EVec m → EVec n → ℝ} {PStar : ℝ}
    {projectX : EVec m → EVec m} (S : State m n)
    (hqStar : qStar = (-mu) • xStar)
    (hstrong : 1 / mu * vecSq (S.qFast - qStar) ≤
      2 * (P S.qFast S.yFast - PStar))
    (hproject : vecSq (projectX ((-mu⁻¹) • S.qFast) - xStar) ≤
      vecSq (((-mu⁻¹) • S.qFast) - xStar)) :
    mu * vecSq (projectX ((-mu⁻¹) • S.qFast) - xStar) ≤
      alphaR * vecSq (S.q - qStar) +
        2 * r * vecSq (S.y - yStar) +
        2 * (P S.qFast S.yFast - PStar) := by
  have hscale :
      mu * vecSq (((-mu⁻¹) • S.qFast) - xStar) =
        1 / mu * vecSq (S.qFast - qStar) := by
    subst qStar
    unfold vecSq NCPLVerification.vecSq
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    field_simp [ne_of_gt hmu]
    ring
  have hprojScaled := mul_le_mul_of_nonneg_left hproject hmu.le
  rw [hscale] at hprojScaled
  have hslowQ : 0 ≤ alphaR * vecSq (S.q - qStar) := by
    apply mul_nonneg halphaR
    unfold vecSq NCPLVerification.vecSq
    exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hslowY : 0 ≤ 2 * r * vecSq (S.y - yStar) := by
    apply mul_nonneg (mul_nonneg (by norm_num) hr)
    unfold vecSq NCPLVerification.vecSq
    exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  linarith

/-- `fastState_readout` stated directly with TeX `ub:eq:relative-energy`. -/
theorem fastState_readout_energy {m n : Nat} {mu r : ℝ}
    (hmu : 0 < mu) (hr : 0 ≤ r)
    {qStar : EVec m} {yStar : EVec n} {xStar : EVec m}
    {P : EVec m → EVec n → ℝ} {PStar : ℝ}
    {projectX : EVec m → EVec m} (S : State m n)
    (hqStar : qStar = (-mu) • xStar)
    (hstrong : 1 / mu * vecSq (S.qFast - qStar) ≤
      2 * (P S.qFast S.yFast - PStar))
    (hproject : vecSq (projectX ((-mu⁻¹) • S.qFast) - xStar) ≤
      vecSq (((-mu⁻¹) • S.qFast) - xStar)) :
    mu * vecSq (projectX ((-mu⁻¹) • S.qFast) - xStar) ≤
      energy mu r qStar yStar P PStar S := by
  unfold energy
  exact fastState_readout hmu
    (div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) hmu.le)
    hr S hqStar hstrong hproject

end

end RelativeFOAM
end Upper
end NCCLowerBoundVerification
