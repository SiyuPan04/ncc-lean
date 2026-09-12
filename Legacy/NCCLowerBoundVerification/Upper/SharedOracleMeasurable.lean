import NCCLowerBoundVerification.Upper.SharedOracle
import NCCLowerBoundVerification.Upper.PaperSharedOracle
import NCCLowerBoundVerification.Oracle.PaperHittingComplexity

/-!
# Borel measurability of the shared-oracle algorithm

The reply space carries the Euclidean pullback Borel structure from
`Oracle.MeasurableModel`.  This file verifies the finite-history query maps
of the explicit shared-oracle program without changing that structure.
-/

namespace NCCLowerBoundVerification
namespace Upper
namespace SharedOracleMeasurable

noncomputable section

open Oracle
open RelativeFOAM ProjectionGeometry ScaledOperator ProjectedMicro
open SharedOracle
open PaperSharedOracle
open ProjectedVIExistence

theorem measurable_oracleReply_toProduct {m n : Nat} :
    Measurable (Oracle.OracleReply.toProduct (m := m) (n := n)) := by
  exact comap_measurable _

@[measurability] theorem measurable_oracleReply_value {m n : Nat} :
    Measurable (fun r : Oracle.OracleReply m n => r.value) := by
  exact measurable_fst.comp measurable_oracleReply_toProduct

@[measurability] theorem measurable_oracleReply_gradX {m n : Nat} :
    Measurable (fun r : Oracle.OracleReply m n => r.gradX) := by
  exact measurable_fst.comp (measurable_snd.comp measurable_oracleReply_toProduct)

@[measurability] theorem measurable_oracleReply_gradY {m n : Nat} :
    Measurable (fun r : Oracle.OracleReply m n => r.gradY) := by
  exact measurable_snd.comp (measurable_snd.comp measurable_oracleReply_toProduct)

/-- The variational-inequality projection used by the executable program is
continuous.  The proof transports its coordinate-Euclidean nonexpansiveness
to `EuclideanSpace`; it does not assume an arbitrary chosen map measurable. -/
theorem continuous_euclideanProjection {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project) :
    Continuous project := by
  let toLinear : EVec d →ₗ[ℝ] EuclideanVec d :=
    { toFun := ProjectedVIExistence.toEuclidean
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  let conjugate : EuclideanVec d → EuclideanVec d := fun x =>
    ProjectedVIExistence.toEuclidean
      (project (ProjectedVIExistence.fromEuclidean x))
  have hconjugate : LipschitzWith 1 conjugate := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    change ‖ProjectedVIExistence.toEuclidean
          (project (ProjectedVIExistence.fromEuclidean x)) -
        ProjectedVIExistence.toEuclidean
          (project (ProjectedVIExistence.fromEuclidean y))‖ ≤ ‖x - y‖
    rw [← ProjectedVIExistence.toEuclidean_sub,
      ProjectedVIExistence.norm_toEuclidean,
      ProjectedVIExistence.norm_euclidean]
    apply Real.sqrt_le_sqrt
    simpa only [fromEuclidean_sub] using
      ProjectionGeometry.projection_nonexpansive hp
        (ProjectedVIExistence.fromEuclidean x)
        (ProjectedVIExistence.fromEuclidean y)
  have hto : Continuous ProjectedVIExistence.toEuclidean :=
    toLinear.continuous_of_finiteDimensional
  have hfrom : Continuous ProjectedVIExistence.fromEuclidean :=
    (ProjectedVIExistence.fromEuclideanLinear d).continuous_of_finiteDimensional
  have hcomp : Continuous (fun x : EVec d =>
      ProjectedVIExistence.fromEuclidean
        (conjugate (ProjectedVIExistence.toEuclidean x))) :=
    hfrom.comp (hconjugate.continuous.comp hto)
  simpa [conjugate] using hcomp

theorem measurable_euclideanProjection {d : Nat} {C : Set (EVec d)}
    {project : EVec d → EVec d} (hp : IsEuclideanProjection C project) :
    Measurable project :=
  (continuous_euclideanProjection hp).measurable

/-! ## Fixed-depth measurable program families -/

def historyTake {m n a b : Nat} (h : Oracle.ReplyHistory m n (a + b)) :
    Oracle.ReplyHistory m n a := fun i => h (Fin.castAdd b i)

def historyDrop {m n a b : Nat} (h : Oracle.ReplyHistory m n (a + b)) :
    Oracle.ReplyHistory m n b := fun i => h (Fin.natAdd a i)

def historyAppend {m n a b : Nat} (ha : Oracle.ReplyHistory m n a)
    (hb : Oracle.ReplyHistory m n b) : Oracle.ReplyHistory m n (a + b) :=
  Fin.append ha hb

def castHistory {m n a b : Nat} (e : a = b)
    (h : Oracle.ReplyHistory m n a) : Oracle.ReplyHistory m n b :=
  fun i => h (Fin.cast e.symm i)

theorem afterHistory_cast {m n : Nat} {X : Set (EVec m)}
    {Y : Set (EVec n)} {α : Type} (p : Oracle.Program X Y α)
    {a b : Nat} (e : a = b) (h : Oracle.ReplyHistory m n a) :
    Oracle.Program.afterHistory p a h =
      Oracle.Program.afterHistory p b (castHistory e h) := by
  subst b
  rfl

@[simp] theorem historyTake_append {m n a b : Nat}
    (ha : Oracle.ReplyHistory m n a) (hb : Oracle.ReplyHistory m n b) :
    historyTake (historyAppend ha hb) = ha := by
  funext i
  simp [historyTake, historyAppend]

@[simp] theorem historyDrop_append {m n a b : Nat}
    (ha : Oracle.ReplyHistory m n a) (hb : Oracle.ReplyHistory m n b) :
    historyDrop (historyAppend ha hb) = hb := by
  funext i
  simp [historyDrop, historyAppend]

theorem historyAppend_take_drop {m n a b : Nat}
    (h : Oracle.ReplyHistory m n (a + b)) :
    historyAppend (historyTake h) (historyDrop h) = h := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    simp [historyAppend, historyTake, historyDrop]

theorem measurable_historyTake {m n a b : Nat} :
    Measurable (historyTake (m := m) (n := n) (a := a) (b := b)) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply (Fin.castAdd b i)

theorem measurable_historyDrop {m n a b : Nat} :
    Measurable (historyDrop (m := m) (n := n) (a := a) (b := b)) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_pi_apply (Fin.natAdd a i)

theorem measurable_historyAppend_left {m n a b : Nat}
    (hb : Oracle.ReplyHistory m n b) :
    Measurable (fun ha : Oracle.ReplyHistory m n a => historyAppend ha hb) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simpa [historyAppend] using
      (measurable_pi_apply j :
        Measurable (fun ha : Oracle.ReplyHistory m n a => ha j))
  · simp only [historyAppend, Fin.append_right]
    exact measurable_const

theorem measurable_historyAppend_right {m n a b : Nat}
    (ha : Oracle.ReplyHistory m n a) :
    Measurable (fun hb : Oracle.ReplyHistory m n b => historyAppend ha hb) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [historyAppend, Fin.append_left]
    exact measurable_const
  · simpa [historyAppend] using
      (measurable_pi_apply j :
        Measurable (fun hb : Oracle.ReplyHistory m n b => hb j))

@[simp] theorem afterHistory_pure {m n : Nat} {X : Set (EVec m)}
    {Y : Set (EVec n)} {α : Type} (a : α) (t : Nat)
    (h : Oracle.ReplyHistory m n t) :
    Oracle.Program.afterHistory (Oracle.Program.pure a : Oracle.Program X Y α)
      t h = Oracle.Program.pure a := by
  cases t <;> simp [Oracle.Program.afterHistory]

@[simp] theorem afterHistory_zero' {m n : Nat} {X : Set (EVec m)}
    {Y : Set (EVec n)} {α : Type} (p : Oracle.Program X Y α)
    (h : Oracle.ReplyHistory m n 0) :
    Oracle.Program.afterHistory p 0 h = p := by
  rw [Oracle.Program.afterHistory]

@[simp] theorem afterHistory_succ_query {m n t : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} {α : Type}
    (q : Oracle.Query m n) (hq : q.1 ∈ X ∧ q.2 ∈ Y)
    (next : Oracle.OracleReply m n → Oracle.Program X Y α)
    (h : Oracle.ReplyHistory m n (t + 1)) :
    Oracle.Program.afterHistory (.query q hq next) (t + 1) h =
      Oracle.Program.afterHistory (next (h 0)) t (fun i => h i.succ) := by
  rw [Oracle.Program.afterHistory]

theorem afterHistory_query_of_eq_succ {m n t u : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} {α : Type}
    (q : Oracle.Query m n) (hq : q.1 ∈ X ∧ q.2 ∈ Y)
    (next : Oracle.OracleReply m n → Oracle.Program X Y α)
    (e : t = u + 1) (h : Oracle.ReplyHistory m n t) :
    Oracle.Program.afterHistory (.query q hq next) t h =
      Oracle.Program.afterHistory
        (next ((castHistory e h) 0)) u
        (fun i => (castHistory e h) i.succ) := by
  rw [afterHistory_cast (.query q hq next) e h]
  exact afterHistory_succ_query q hq next (castHistory e h)

@[simp] theorem bind_pure' {m n : Nat} {X : Set (EVec m)}
    {Y : Set (EVec n)} {α β : Type} (a : α)
    (k : α → Oracle.Program X Y β) :
    (Oracle.Program.pure a : Oracle.Program X Y α) >>= k = k a := by
  rfl

@[simp] theorem bind_query' {m n : Nat} {X : Set (EVec m)}
    {Y : Set (EVec n)} {α β : Type}
    (q : Oracle.Query m n) (hq : q.1 ∈ X ∧ q.2 ∈ Y)
    (next : Oracle.OracleReply m n → Oracle.Program X Y α)
    (k : α → Oracle.Program X Y β) :
    (Oracle.Program.query q hq next : Oracle.Program X Y α) >>= k =
      Oracle.Program.query q hq (fun r => next r >>= k) := by
  rfl

theorem afterHistory_append {m n : Nat} {X : Set (EVec m)}
    {Y : Set (EVec n)} {α : Type} (p : Oracle.Program X Y α)
    {a b : Nat} (ha : Oracle.ReplyHistory m n a)
    (hb : Oracle.ReplyHistory m n b) :
    Oracle.Program.afterHistory p (a + b) (historyAppend ha hb) =
      Oracle.Program.afterHistory
        (Oracle.Program.afterHistory p a ha) b hb := by
  induction a generalizing p with
  | zero =>
      have hnil : ha = Oracle.emptyHistory m n := Subsingleton.elim _ _
      subst ha
      let e : 0 + b = b := Nat.zero_add b
      rw [afterHistory_cast p e]
      rw [afterHistory_zero']
      congr 1
      funext i
      unfold castHistory historyAppend
      have hi : Fin.cast e.symm i = Fin.natAdd 0 i := by
        apply Fin.ext
        simp
      rw [hi, Fin.append_right]
  | succ a ih =>
      cases p with
      | pure result => simp
      | query q hq next =>
          let haTail : Oracle.ReplyHistory m n a := fun i => ha i.succ
          have hrec := ih (next (ha 0)) haTail
          let e : a + 1 + b = (a + b) + 1 := by omega
          have hstep := afterHistory_query_of_eq_succ q hq next e
            (historyAppend ha hb)
          have hhead : (castHistory e (historyAppend ha hb)) 0 = ha 0 := by
            unfold castHistory historyAppend
            have hi : Fin.cast e.symm (0 : Fin ((a + b) + 1)) =
                Fin.castAdd b (0 : Fin (a + 1)) := by
              apply Fin.ext
              rfl
            rw [hi, Fin.append_left]
          have htail :
              (fun i : Fin (a + b) =>
                (castHistory e (historyAppend ha hb)) i.succ) =
                historyAppend haTail hb := by
            funext i
            refine Fin.addCases (fun j => ?_) (fun j => ?_) i
            · unfold castHistory historyAppend
              have hi : Fin.cast e.symm (Fin.castAdd b j).succ =
                  Fin.castAdd b j.succ := by
                apply Fin.ext
                rfl
              rw [hi, Fin.append_left]
              rw [Fin.append_left]
            · unfold castHistory historyAppend
              have hi : Fin.cast e.symm (Fin.natAdd a j).succ =
                  Fin.natAdd (a + 1) j := by
                apply Fin.ext
                change a + j.val + 1 = a + 1 + j.val
                omega
              rw [hi, Fin.append_right]
              rw [Fin.append_right]
          rw [hstep, hhead, htail, hrec]
          rw [afterHistory_succ_query]

theorem exactDepth_afterHistory_terminal {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} {α : Type}
    {p : Oracle.Program X Y α} {d : Nat} (hp : SharedOracle.ExactDepth p d)
    (h : Oracle.ReplyHistory m n d) :
    ∃ a, Oracle.Program.afterHistory p d h = Oracle.Program.pure a := by
  induction hp with
  | pure a => exact ⟨a, by simp [Oracle.Program.afterHistory]⟩
  | query q hq next k hnext ih =>
      simpa only [Oracle.Program.afterHistory] using
        ih (h 0) (fun i => h i.succ)

theorem exactDepth_afterHistory_bind_at_depth {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} {α β : Type}
    {p : Oracle.Program X Y α} {d : Nat} (hp : SharedOracle.ExactDepth p d)
    (k : α → Oracle.Program X Y β) (h : Oracle.ReplyHistory m n d) :
    Oracle.Program.afterHistory (p >>= k) d h =
      Oracle.Program.afterHistory p d h >>= k := by
  induction hp with
  | pure a => simp [Oracle.Program.afterHistory, Oracle.Program.bind]
  | query q hq next c hnext ih =>
      simpa only [bind_query', afterHistory_succ_query] using
        ih (h 0) (fun i => h i.succ)

theorem exactDepth_queryAfterHistory_bind_before {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} {α β : Type}
    {p : Oracle.Program X Y α} {d t : Nat}
    (hp : SharedOracle.ExactDepth p d) (ht : t < d)
    (k : α → Oracle.Program X Y β) (fallback : Oracle.Query m n)
    (h : Oracle.ReplyHistory m n t) :
    Oracle.Program.queryAfterHistory (p >>= k) fallback t h =
      Oracle.Program.queryAfterHistory p fallback t h := by
  induction hp generalizing t with
  | pure a => omega
  | query q hq next c hnext ih =>
      cases t with
      | zero =>
          simp [Oracle.Program.queryAfterHistory]
      | succ t =>
          simp only [Oracle.Program.queryAfterHistory, bind_query',
            afterHistory_succ_query]
          exact ih (h 0) (by omega) (fun i => h i.succ)

theorem exactDepth_queryAfterHistory_bind_after {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} {α β : Type}
    {p : Oracle.Program X Y α} {d e : Nat}
    (hp : SharedOracle.ExactDepth p d) (k : α → Oracle.Program X Y β)
    (fallback : Oracle.Query m n) (ha : Oracle.ReplyHistory m n d)
    (hb : Oracle.ReplyHistory m n e) (a : α)
    (hterminal : Oracle.Program.afterHistory p d ha = Oracle.Program.pure a) :
    Oracle.Program.queryAfterHistory (p >>= k) fallback (d + e)
        (historyAppend ha hb) =
      Oracle.Program.queryAfterHistory (k a) fallback e hb := by
  unfold Oracle.Program.queryAfterHistory
  rw [afterHistory_append]
  rw [exactDepth_afterHistory_bind_at_depth hp k ha]
  rw [hterminal]
  rfl

/-- A parameterized fixed-depth program whose counterfactual query maps and
terminal value are Borel measurable jointly in the parameter and history. -/
structure FixedBorelFamily {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    (S α : Type) [MeasurableSpace S] [MeasurableSpace α]
    (fallback : Oracle.Query m n) (p : S → Oracle.Program X Y α)
    (depth : Nat) where
  result : S × Oracle.ReplyHistory m n depth → α
  exactDepth : ∀ s, SharedOracle.ExactDepth (p s) depth
  terminal : ∀ sh, Oracle.Program.afterHistory (p sh.1) depth sh.2 =
    Oracle.Program.pure (result sh)
  measurable_query : ∀ t, Measurable (fun sh : S × Oracle.ReplyHistory m n t =>
    Oracle.Program.queryAfterHistory (p sh.1) fallback t sh.2)
  measurable_result : Measurable result

namespace FixedBorelFamily

variable {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
variable {S R α β : Type} [MeasurableSpace S] [MeasurableSpace R]
variable [MeasurableSpace α] [MeasurableSpace β]
variable {fallback : Oracle.Query m n}

def castDepth {p : S → Oracle.Program X Y α} {d e : Nat}
    (h : d = e) (hp : FixedBorelFamily S α fallback p d) :
    FixedBorelFamily S α fallback p e := by
  subst e
  exact hp

def congrProgram {p q : S → Oracle.Program X Y α} {d : Nat}
    (h : p = q) (hp : FixedBorelFamily S α fallback p d) :
    FixedBorelFamily S α fallback q d := by
  subst q
  exact hp

def pure (f : S → α) (hf : Measurable f) :
    FixedBorelFamily S α fallback
      (fun s => (Oracle.Program.pure (f s) : Oracle.Program X Y α)) 0 where
  result := fun sh => f sh.1
  exactDepth := fun s => SharedOracle.ExactDepth.pure (f s)
  terminal := by
    intro sh
    simp
  measurable_query := by
    intro t
    have heq : (fun sh : S × Oracle.ReplyHistory m n t =>
        Oracle.Program.queryAfterHistory
          (Oracle.Program.pure (f sh.1) : Oracle.Program X Y α)
          fallback t sh.2) = fun _ => fallback := by
      funext sh
      unfold Oracle.Program.queryAfterHistory
      rw [afterHistory_pure]
    rw [heq]
    exact measurable_const
  measurable_result := hf.comp measurable_fst

def stepInput (t : Nat) :
    S × Oracle.ReplyHistory m n (t + 1) →
      (S × Oracle.OracleReply m n) × Oracle.ReplyHistory m n t := fun sh =>
  ((sh.1, sh.2 0), fun i => sh.2 i.succ)

theorem measurable_stepInput (t : Nat) :
    Measurable (stepInput (S := S) (m := m) (n := n) t) := by
  unfold stepInput
  apply Measurable.prodMk
  · exact measurable_fst.prodMk (measurable_pi_apply 0 |>.comp measurable_snd)
  · rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply i.succ |>.comp measurable_snd

def query (q : S → Oracle.Query m n) (hq : ∀ s, (q s).1 ∈ X ∧ (q s).2 ∈ Y)
    (hqMeas : Measurable q)
    (next : (S × Oracle.OracleReply m n) → Oracle.Program X Y α)
    {d : Nat}
    (hn : FixedBorelFamily (S × Oracle.OracleReply m n) α fallback next d) :
    FixedBorelFamily S α fallback
      (fun s => Oracle.Program.query (q s) (hq s) (fun r => next (s, r)))
      (d + 1) where
  result := fun sh => hn.result (stepInput d sh)
  exactDepth := fun s => SharedOracle.ExactDepth.query (q s) (hq s)
    (fun r => next (s, r)) d (fun r => hn.exactDepth (s, r))
  terminal := by
    intro sh
    rw [afterHistory_succ_query]
    exact hn.terminal (stepInput d sh)
  measurable_query := by
    intro t
    cases t with
    | zero =>
        have heq : (fun sh : S × Oracle.ReplyHistory m n 0 =>
            Oracle.Program.queryAfterHistory
              (Oracle.Program.query (q sh.1) (hq sh.1)
                (fun r => next (sh.1, r))) fallback 0 sh.2) =
            fun sh => q sh.1 := by
          funext sh
          simp [Oracle.Program.queryAfterHistory]
        rw [heq]
        exact hqMeas.comp measurable_fst
    | succ t =>
        have heq : (fun sh : S × Oracle.ReplyHistory m n (t + 1) =>
            Oracle.Program.queryAfterHistory
              (Oracle.Program.query (q sh.1) (hq sh.1)
                (fun r => next (sh.1, r))) fallback (t + 1) sh.2) =
            fun sh => Oracle.Program.queryAfterHistory
              (next (sh.1, sh.2 0)) fallback t (fun i => sh.2 i.succ) := by
          funext sh
          unfold Oracle.Program.queryAfterHistory
          rw [afterHistory_succ_query]
        rw [heq]
        exact (hn.measurable_query t).comp (measurable_stepInput t)
  measurable_result := hn.measurable_result.comp (measurable_stepInput d)

def reparam (f : R → S) (hf : Measurable f)
    {p : S → Oracle.Program X Y α} {d : Nat}
    (hp : FixedBorelFamily S α fallback p d) :
    FixedBorelFamily R α fallback (fun r => p (f r)) d where
  result := fun rh => hp.result (f rh.1, rh.2)
  exactDepth := fun r => hp.exactDepth (f r)
  terminal := fun rh => hp.terminal (f rh.1, rh.2)
  measurable_query := by
    intro t
    exact (hp.measurable_query t).comp
      ((hf.comp measurable_fst).prodMk measurable_snd)
  measurable_result := hp.measurable_result.comp
    ((hf.comp measurable_fst).prodMk measurable_snd)

def bind {p : S → Oracle.Program X Y α} {dp dk : Nat}
    (hp : FixedBorelFamily S α fallback p dp)
    (k : S → α → Oracle.Program X Y β)
    (hk : FixedBorelFamily (S × α) β fallback
      (fun sa => k sa.1 sa.2) dk) :
    FixedBorelFamily S β fallback (fun s => p s >>= k s) (dp + dk) where
  result := fun sh =>
    let pre := historyTake (a := dp) (b := dk) sh.2
    let suf := historyDrop (a := dp) (b := dk) sh.2
    hk.result ((sh.1, hp.result (sh.1, pre)), suf)
  exactDepth := fun s => (hp.exactDepth s).bind (k s)
    (fun a => hk.exactDepth (s, a))
  terminal := by
    intro sh
    let pre := historyTake (a := dp) (b := dk) sh.2
    let suf := historyDrop (a := dp) (b := dk) sh.2
    have happ : historyAppend pre suf = sh.2 :=
      historyAppend_take_drop sh.2
    rw [← happ]
    rw [afterHistory_append]
    rw [exactDepth_afterHistory_bind_at_depth (hp.exactDepth sh.1) (k sh.1)]
    rw [hp.terminal (sh.1, pre)]
    rw [bind_pure']
    simpa using hk.terminal ((sh.1, hp.result (sh.1, pre)), suf)
  measurable_query := by
    intro t
    by_cases ht : t < dp
    · have heq : (fun sh : S × Oracle.ReplyHistory m n t =>
          Oracle.Program.queryAfterHistory (p sh.1 >>= k sh.1)
            fallback t sh.2) =
          fun sh => Oracle.Program.queryAfterHistory (p sh.1)
            fallback t sh.2 := by
        funext sh
        exact exactDepth_queryAfterHistory_bind_before
          (hp.exactDepth sh.1) ht (k sh.1) fallback sh.2
      rw [heq]
      exact hp.measurable_query t
    · have hle : dp ≤ t := Nat.le_of_not_gt ht
      obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hle
      let intoK : S × Oracle.ReplyHistory m n (dp + e) →
          (S × α) × Oracle.ReplyHistory m n e := fun sh =>
        ((sh.1, hp.result
          (sh.1, historyTake (a := dp) (b := e) sh.2)),
          historyDrop (a := dp) (b := e) sh.2)
      have hIntoK : Measurable intoK := by
        unfold intoK
        have htake : Measurable (fun sh : S × Oracle.ReplyHistory m n (dp + e) =>
            historyTake (a := dp) (b := e) sh.2) :=
          measurable_historyTake.comp measurable_snd
        have hdrop : Measurable (fun sh : S × Oracle.ReplyHistory m n (dp + e) =>
            historyDrop (a := dp) (b := e) sh.2) :=
          measurable_historyDrop.comp measurable_snd
        have hres : Measurable (fun sh : S × Oracle.ReplyHistory m n (dp + e) =>
            hp.result (sh.1, historyTake (a := dp) (b := e) sh.2)) :=
          hp.measurable_result.comp (measurable_fst.prodMk htake)
        exact (measurable_fst.prodMk hres).prodMk hdrop
      have hmeas := (hk.measurable_query e).comp hIntoK
      have heq : (fun sh : S × Oracle.ReplyHistory m n (dp + e) =>
          Oracle.Program.queryAfterHistory (p sh.1 >>= k sh.1)
            fallback (dp + e) sh.2) =
          (fun sh => Oracle.Program.queryAfterHistory
            (k sh.1.1 sh.1.2) fallback e sh.2) ∘ intoK := by
        funext sh
        unfold intoK
        rw [← historyAppend_take_drop sh.2]
        exact exactDepth_queryAfterHistory_bind_after
          (hp.exactDepth sh.1) (k sh.1) fallback
          (historyTake sh.2) (historyDrop sh.2)
          (hp.result (sh.1, historyTake sh.2))
          (hp.terminal (sh.1, historyTake sh.2))
      rw [heq]
      exact hmeas
  measurable_result := by
    have htake : Measurable (fun sh : S × Oracle.ReplyHistory m n (dp + dk) =>
        historyTake (a := dp) (b := dk) sh.2) :=
      measurable_historyTake.comp measurable_snd
    have hdrop : Measurable (fun sh : S × Oracle.ReplyHistory m n (dp + dk) =>
        historyDrop (a := dp) (b := dk) sh.2) :=
      measurable_historyDrop.comp measurable_snd
    have hres : Measurable (fun sh : S × Oracle.ReplyHistory m n (dp + dk) =>
        hp.result (sh.1, historyTake (a := dp) (b := dk) sh.2)) :=
      hp.measurable_result.comp (measurable_fst.prodMk htake)
    exact hk.measurable_result.comp
      ((measurable_fst.prodMk hres).prodMk hdrop)

end FixedBorelFamily

/-! ## Standard Borel structures for finite algorithm states -/

def stateToProduct {m n : Nat} (S : RelativeFOAM.State m n) :
    EVec m × (EVec n × (EVec m × EVec n)) :=
  (S.q, (S.y, (S.qFast, S.yFast)))

instance stateMeasurableSpace (m n : Nat) :
    MeasurableSpace (RelativeFOAM.State m n) :=
  MeasurableSpace.comap stateToProduct inferInstance

theorem measurable_stateToProduct {m n : Nat} :
    Measurable (stateToProduct (m := m) (n := n)) :=
  comap_measurable _

@[measurability] theorem measurable_state_q {m n : Nat} :
    Measurable (fun S : RelativeFOAM.State m n => S.q) :=
  measurable_fst.comp measurable_stateToProduct

@[measurability] theorem measurable_state_y {m n : Nat} :
    Measurable (fun S : RelativeFOAM.State m n => S.y) :=
  measurable_fst.comp (measurable_snd.comp measurable_stateToProduct)

@[measurability] theorem measurable_state_qFast {m n : Nat} :
    Measurable (fun S : RelativeFOAM.State m n => S.qFast) :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp measurable_stateToProduct))

@[measurability] theorem measurable_state_yFast {m n : Nat} :
    Measurable (fun S : RelativeFOAM.State m n => S.yFast) :=
  measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_stateToProduct))

@[measurability] theorem measurable_state_mk {T : Type} [MeasurableSpace T]
    {m n : Nat} {q : T → EVec m} {y : T → EVec n}
    {qf : T → EVec m} {yf : T → EVec n}
    (hq : Measurable q) (hy : Measurable y)
    (hqf : Measurable qf) (hyf : Measurable yf) :
    Measurable (fun t =>
      (⟨q t, y t, qf t, yf t⟩ : RelativeFOAM.State m n)) := by
  rw [measurable_comap_iff]
  exact hq.prodMk (hy.prodMk (hqf.prodMk hyf))

def microOutputToProduct {m n : Nat} (O : RelativeFOAM.MicroOutput m n) :
    EVec m × (EVec n × (EVec m × EVec n)) :=
  (O.xFast, (O.yFastNext, (O.qFastNext, O.wFastNext)))

instance microOutputMeasurableSpace (m n : Nat) :
    MeasurableSpace (RelativeFOAM.MicroOutput m n) :=
  MeasurableSpace.comap microOutputToProduct inferInstance

theorem measurable_microOutputToProduct {m n : Nat} :
    Measurable (microOutputToProduct (m := m) (n := n)) :=
  comap_measurable _

@[measurability] theorem measurable_microOutput_xFast {m n : Nat} :
    Measurable (fun O : RelativeFOAM.MicroOutput m n => O.xFast) :=
  measurable_fst.comp measurable_microOutputToProduct

@[measurability] theorem measurable_microOutput_yFastNext {m n : Nat} :
    Measurable (fun O : RelativeFOAM.MicroOutput m n => O.yFastNext) :=
  measurable_fst.comp (measurable_snd.comp measurable_microOutputToProduct)

@[measurability] theorem measurable_microOutput_qFastNext {m n : Nat} :
    Measurable (fun O : RelativeFOAM.MicroOutput m n => O.qFastNext) :=
  measurable_fst.comp (measurable_snd.comp
    (measurable_snd.comp measurable_microOutputToProduct))

@[measurability] theorem measurable_microOutput_wFastNext {m n : Nat} :
    Measurable (fun O : RelativeFOAM.MicroOutput m n => O.wFastNext) :=
  measurable_snd.comp (measurable_snd.comp
    (measurable_snd.comp measurable_microOutputToProduct))

@[measurability] theorem measurable_microOutput_mk
    {T : Type} [MeasurableSpace T] {m n : Nat}
    {x : T → EVec m} {yn : T → EVec n}
    {qn : T → EVec m} {w : T → EVec n}
    (hx : Measurable x) (hyn : Measurable yn)
    (hqn : Measurable qn) (hw : Measurable w) :
    Measurable (fun t =>
      (⟨x t, yn t, qn t, w t⟩ : RelativeFOAM.MicroOutput m n)) := by
  rw [measurable_comap_iff]
  exact hx.prodMk (hyn.prodMk (hqn.prodMk hw))

def snapshotToProduct {m n : Nat} {Y : Set (EVec n)}
    (R : OuterTrajectoryConcrete.Snapshot (m := m) Y) :
    EVec m × (RelativeFOAMContraction.ValidState (m := m) Y × ℝ) :=
  (R.z, (R.state, R.B))

instance snapshotMeasurableSpace (m n : Nat) (Y : Set (EVec n)) :
    MeasurableSpace (OuterTrajectoryConcrete.Snapshot (m := m) Y) :=
  MeasurableSpace.comap snapshotToProduct inferInstance

theorem measurable_snapshotToProduct {m n : Nat} {Y : Set (EVec n)} :
    Measurable (snapshotToProduct (m := m) (Y := Y)) :=
  comap_measurable _

@[measurability] theorem measurable_snapshot_z {m n : Nat}
    {Y : Set (EVec n)} :
    Measurable (fun R : OuterTrajectoryConcrete.Snapshot (m := m) Y => R.z) :=
  measurable_fst.comp measurable_snapshotToProduct

@[measurability] theorem measurable_snapshot_state {m n : Nat}
    {Y : Set (EVec n)} :
    Measurable (fun R : OuterTrajectoryConcrete.Snapshot (m := m) Y => R.state) :=
  measurable_fst.comp (measurable_snd.comp measurable_snapshotToProduct)

@[measurability] theorem measurable_snapshot_B {m n : Nat}
    {Y : Set (EVec n)} :
    Measurable (fun R : OuterTrajectoryConcrete.Snapshot (m := m) Y => R.B) :=
  measurable_snd.comp (measurable_snd.comp measurable_snapshotToProduct)

@[measurability] theorem measurable_snapshot_mk
    {T : Type} [MeasurableSpace T] {m n : Nat} {Y : Set (EVec n)}
    {z : T → EVec m}
    {st : T → RelativeFOAMContraction.ValidState (m := m) Y}
    {B : T → ℝ} (hz : Measurable z) (hst : Measurable st)
    (hB : Measurable B) :
    Measurable (fun t =>
      ({ z := z t, state := st t, B := B t } :
        OuterTrajectoryConcrete.Snapshot (m := m) Y)) := by
  rw [measurable_comap_iff]
  exact hz.prodMk (hst.prodMk hB)

/-! ## Measurable numerical primitives -/

theorem measurable_const_smul_family
    {T : Type} [MeasurableSpace T] {d : Nat} (c : ℝ)
    {v : T → EVec d} (hv : Measurable v) :
    Measurable (fun t => c • v t) := by
  rw [measurable_pi_iff]
  intro i
  change Measurable (fun t => c * v t i)
  have hi : Measurable ((fun w : EVec d => w i) ∘ v) :=
    (measurable_pi_apply i).comp hv
  exact measurable_const.mul hi

theorem measurable_scaledQuery_family
    {T : Type} [MeasurableSpace T] {m n : Nat} {ell : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    {u : T → ScaledFeasible ell X Y} (hu : Measurable u) :
    Measurable (fun t => scaledQuery (u t)) := by
  have hux : Measurable (fun t => ScaledOperator.unpackX (u t).1) := by
    rw [measurable_pi_iff]
    intro i
    change Measurable ((fun w : Pair m n => w (Fin.castAdd n i)) ∘
      (fun t => (u t).1))
    exact (measurable_pi_apply (Fin.castAdd n i)).comp hu.subtype_val
  have huy : Measurable (fun t => ScaledOperator.unpackY (u t).1) := by
    rw [measurable_pi_iff]
    intro j
    change Measurable ((fun w : Pair m n => w (Fin.natAdd m j)) ∘
      (fun t => (u t).1))
    exact (measurable_pi_apply (Fin.natAdd m j)).comp hu.subtype_val
  apply Measurable.prodMk
  · simpa only [scaledQuery, ScaledOperator.unscaleX] using
      measurable_const_smul_family (ScaledOperator.scaleRoot ell) hux
  · simpa only [scaledQuery, ScaledOperator.unscaleY] using
      measurable_const_smul_family (ScaledOperator.scaleRoot ell) huy

theorem measurable_unpackX_family
    {T : Type} [MeasurableSpace T] {m n : Nat}
    {u : T → Pair m n} (hu : Measurable u) :
    Measurable (fun t => ScaledOperator.unpackX (u t)) := by
  rw [measurable_pi_iff]
  intro i
  exact (measurable_pi_apply (Fin.castAdd n i)).comp hu

theorem measurable_unpackY_family
    {T : Type} [MeasurableSpace T] {m n : Nat}
    {u : T → Pair m n} (hu : Measurable u) :
    Measurable (fun t => ScaledOperator.unpackY (u t)) := by
  rw [measurable_pi_iff]
  intro j
  exact (measurable_pi_apply (Fin.natAdd m j)).comp hu

theorem measurable_pack_family
    {T : Type} [MeasurableSpace T] {m n : Nat}
    {x : T → EVec m} {y : T → EVec n}
    (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun t => ScaledOperator.pack (x t) (y t)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [show (fun t => ScaledOperator.pack (x t) (y t) (Fin.castAdd n j)) =
        (fun w : EVec m => w j) ∘ x by
      funext t
      simp only [ScaledOperator.pack, Fin.append_left, Function.comp_apply]]
    exact (measurable_pi_apply j).comp hx
  · rw [show (fun t => ScaledOperator.pack (x t) (y t) (Fin.natAdd m j)) =
        (fun w : EVec n => w j) ∘ y by
      funext t
      simp only [ScaledOperator.pack, Fin.append_right, Function.comp_apply]]
    exact (measurable_pi_apply j).comp hy

theorem measurable_unscaleX_family
    {T : Type} [MeasurableSpace T] {m n : Nat} (ell : ℝ)
    {u : T → Pair m n} (hu : Measurable u) :
    Measurable (fun t => ScaledOperator.unscaleX ell (u t)) :=
  measurable_const_smul_family (ScaledOperator.scaleRoot ell)
    (measurable_unpackX_family hu)

theorem measurable_unscaleY_family
    {T : Type} [MeasurableSpace T] {m n : Nat} (ell : ℝ)
    {u : T → Pair m n} (hu : Measurable u) :
    Measurable (fun t => ScaledOperator.unscaleY ell (u t)) :=
  measurable_const_smul_family (ScaledOperator.scaleRoot ell)
    (measurable_unpackY_family hu)

theorem measurable_replyOperator_family
    {T : Type} [MeasurableSpace T] {m n : Nat} (ell r : ℝ)
    {z qg : T → EVec m} {yg : T → EVec n}
    {u : T → Pair m n} {reply : T → Oracle.OracleReply m n}
    (hz : Measurable z) (hqg : Measurable qg) (hyg : Measurable yg)
    (hu : Measurable u) (hreply : Measurable reply) :
    Measurable (fun t => replyOperator ell r (z t) (qg t) (yg t)
      (u t) (reply t)) := by
  let hx : T → EVec m := fun t => ScaledOperator.unscaleX ell (u t)
  let hy : T → EVec n := fun t => ScaledOperator.unscaleY ell (u t)
  have hxmeas : Measurable hx := measurable_unscaleX_family ell hu
  have hymeas : Measurable hy := measurable_unscaleY_family ell hu
  have hgx := measurable_oracleReply_gradX.comp hreply
  have hgy := measurable_oracleReply_gradY.comp hreply
  unfold replyOperator
  dsimp only
  apply measurable_pack_family
  · exact measurable_const_smul_family (ScaledOperator.scaleRoot ell)
      (((hgx.add (measurable_const_smul_family ell hxmeas)).sub
        (measurable_const_smul_family (2 * ell) hz)).add
        (measurable_const_smul_family (ell / 2)
          (hxmeas.sub (measurable_const_smul_family ell⁻¹ hqg))))
  · exact measurable_const_smul_family (ScaledOperator.scaleRoot ell)
      ((hgy.neg.add (measurable_const_smul_family r hymeas)).add
        (measurable_const_smul_family (ScaledOperator.gamma ell)⁻¹
          (hymeas.sub hyg)))

theorem measurable_scaledProject_family
    {T : Type} [MeasurableSpace T] {m n : Nat} (ell : ℝ)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    {u : T → Pair m n} (hu : Measurable u) :
    Measurable (fun t => scaledProject ell projectX projectY (u t)) := by
  have hx := (measurable_euclideanProjection hprojX).comp
    (measurable_unscaleX_family ell hu)
  have hy := (measurable_euclideanProjection hprojY).comp
    (measurable_unscaleY_family ell hu)
  unfold ScaledOperator.scaledProject ScaledOperator.scalePair
  exact measurable_pack_family
    (measurable_const_smul_family (ScaledOperator.scaleRoot ell)⁻¹ hx)
    (measurable_const_smul_family (ScaledOperator.scaleRoot ell)⁻¹ hy)

theorem measurable_microAdvance_family
    {T : Type} [MeasurableSpace T] {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    {z qg : T → EVec m} {yg : T → EVec n}
    {u : T → ScaledFeasible ell X Y}
    {reply : T → Oracle.OracleReply m n}
    (hz : Measurable z) (hqg : Measurable qg) (hyg : Measurable yg)
    (hu : Measurable u) (hreply : Measurable reply) :
    Measurable (fun t => microAdvance (r := r) hell projectX projectY
      hprojX hprojY (z t) (qg t) (yg t) (u t) (reply t)) := by
  apply Measurable.subtype_mk
  apply measurable_scaledProject_family ell projectX projectY hprojX hprojY
  exact hu.subtype_val.sub
    (measurable_const_smul_family (M0 ^ 2)⁻¹
      (measurable_replyOperator_family ell r hz hqg hyg
        hu.subtype_val hreply))

theorem measurable_qCenter_family
    {T : Type} [MeasurableSpace T] {m n : Nat} (ell r : ℝ)
    {S : T → RelativeFOAM.State m n} (hS : Measurable S) :
    Measurable (fun t => qCenter ell r (S t)) := by
  unfold qCenter
  fun_prop

theorem measurable_yCenter_family
    {T : Type} [MeasurableSpace T] {m n : Nat} (ell r : ℝ)
    {S : T → RelativeFOAM.State m n} (hS : Measurable S) :
    Measurable (fun t => yCenter ell r (S t)) := by
  unfold yCenter
  fun_prop

theorem measurable_microInitial_family
    {T : Type} [MeasurableSpace T] {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    {S : T → RelativeFOAM.State m n} (hS : Measurable S) :
    Measurable (fun t => microInitial (r := r) hell projectX projectY
      hprojX hprojY (S t)) := by
  apply Measurable.subtype_mk
  apply measurable_scaledProject_family ell projectX projectY hprojX hprojY
  have hq := measurable_qCenter_family ell r hS
  have hy := measurable_yCenter_family ell r hS
  unfold ScaledOperator.scaledCenter ScaledOperator.scalePair
  exact measurable_pack_family
    (measurable_const_smul_family (ScaledOperator.scaleRoot ell)⁻¹
      (measurable_const_smul_family (-ell⁻¹) hq))
    (measurable_const_smul_family (ScaledOperator.scaleRoot ell)⁻¹ hy)

theorem measurable_outputFromReplies_family
    {T : Type} [MeasurableSpace T] {m n : Nat} (ell : ℝ)
    {z : T → EVec m} {uPrev uFinal : T → Pair m n}
    {replyPrev replyFinal : T → Oracle.OracleReply m n}
    {operatorPrev : T → Pair m n}
    (hz : Measurable z) (huPrev : Measurable uPrev)
    (huFinal : Measurable uFinal) (hreplyPrev : Measurable replyPrev)
    (hreplyFinal : Measurable replyFinal)
    (hoperatorPrev : Measurable operatorPrev) :
    Measurable (fun t => outputFromReplies ell (z t) (uPrev t) (uFinal t)
      (replyPrev t) (replyFinal t) (operatorPrev t)) := by
  let hb : Measurable (fun t => (M0 ^ 2) •
      (uPrev t - (M0 ^ 2)⁻¹ • operatorPrev t - uFinal t)) :=
    measurable_const_smul_family (M0 ^ 2)
      ((huPrev.sub (measurable_const_smul_family (M0 ^ 2)⁻¹
        hoperatorPrev)).sub huFinal)
  have hx := measurable_unscaleX_family ell huFinal
  have hy := measurable_unscaleY_family ell huFinal
  have hnx : Measurable (fun t => ScaledOperator.unscaledNormalX ell
      ((M0 ^ 2) •
        (uPrev t - (M0 ^ 2)⁻¹ • operatorPrev t - uFinal t))) :=
    measurable_const_smul_family (ScaledOperator.scaleRoot ell)⁻¹
      (measurable_unpackX_family hb)
  have hny : Measurable (fun t => ScaledOperator.unscaledNormalY ell
      ((M0 ^ 2) •
        (uPrev t - (M0 ^ 2)⁻¹ • operatorPrev t - uFinal t))) :=
    measurable_const_smul_family (ScaledOperator.scaleRoot ell)⁻¹
      (measurable_unpackY_family hb)
  have hgx := measurable_oracleReply_gradX.comp hreplyFinal
  have hgy := measurable_oracleReply_gradY.comp hreplyFinal
  unfold outputFromReplies
  dsimp only
  apply measurable_microOutput_mk
  · exact hx
  · exact hy
  · exact (((hgx.add (measurable_const_smul_family ell hx)).sub
      (measurable_const_smul_family (2 * ell) hz)).add hnx)
  · exact hgy.neg.add hny

/-! ## Finite measurable selection -/

theorem measurable_fin_variable_eval
    {S A : Type} [MeasurableSpace S] [MeasurableSpace A] {k : Nat}
    (data : S → Fin k → A) (idx : S → Fin k)
    (hdata : ∀ i, Measurable (fun s => data s i))
    (hidx : Measurable idx) :
    Measurable (fun s => data s (idx s)) := by
  intro t ht
  have heq : (fun s => data s (idx s)) ⁻¹' t =
      ⋃ i : Fin k, {s | idx s = i} ∩ (fun s => data s i) ⁻¹' t := by
    ext s
    simp
  rw [heq]
  apply MeasurableSet.iUnion
  intro i
  exact ((measurableSet_singleton i).preimage hidx).inter (hdata i ht)

theorem measurable_earliestMinIndex (k : Nat) :
    Measurable (earliestMinIndex k) := by
  induction k with
  | zero =>
      simpa [earliestMinIndex] using
        (measurable_const : Measurable
          (fun _score : Fin (0 + 1) → ℝ => (0 : Fin (0 + 1))))
  | succ k ih =>
      have hrestrict : Measurable
          (fun score : Fin ((k + 1) + 1) → ℝ =>
            fun i : Fin (k + 1) => score i.castSucc) := by
        rw [measurable_pi_iff]
        intro i
        exact measurable_pi_apply i.castSucc
      have hold : Measurable
          (fun score : Fin ((k + 1) + 1) → ℝ =>
            earliestMinIndex k (fun i : Fin (k + 1) => score i.castSucc)) :=
        ih.comp hrestrict
      have hcastSucc : Measurable
          (fun i : Fin (k + 1) => i.castSucc :
            Fin (k + 1) → Fin ((k + 1) + 1)) :=
        measurable_of_finite _
      have holdCast : Measurable
          (fun score : Fin ((k + 1) + 1) → ℝ =>
            (earliestMinIndex k
              (fun i : Fin (k + 1) => score i.castSucc)).castSucc) :=
        hcastSucc.comp hold
      have holdScore : Measurable
          (fun score : Fin ((k + 1) + 1) → ℝ =>
            score ((earliestMinIndex k
              (fun i : Fin (k + 1) => score i.castSucc)).castSucc)) :=
        measurable_fin_variable_eval
          (data := fun score => score)
          (idx := fun score =>
            (earliestMinIndex k
              (fun i : Fin (k + 1) => score i.castSucc)).castSucc)
          (fun i => measurable_pi_apply i) holdCast
      have hlastScore : Measurable
          (fun score : Fin ((k + 1) + 1) → ℝ =>
            score (Fin.last (k + 1))) :=
        measurable_pi_apply (Fin.last (k + 1))
      have hcond : MeasurableSet
          {score : Fin ((k + 1) + 1) → ℝ |
            score (Fin.last (k + 1)) <
              score ((earliestMinIndex k
                (fun i : Fin (k + 1) => score i.castSucc)).castSucc)} :=
        measurableSet_lt hlastScore holdScore
      simpa only [earliestMinIndex] using
        (Measurable.ite hcond
          (measurable_const : Measurable
            (fun _score : Fin ((k + 1) + 1) → ℝ => Fin.last (k + 1)))
          holdCast)

theorem measurable_selectedTrajectoryIndex
    {S : Type} [MeasurableSpace S]
    {m n T : Nat} (hT : 0 < T)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (ell : ℝ) (projectX : EVec m → EVec m)
    (data : S → FeasibleTrajectory T X Y)
    (hscore : ∀ i, Measurable (fun s =>
      computableCertificate ell projectX (data s i).1)) :
    Measurable (fun s =>
      selectedTrajectoryIndex hT ell projectX (data s)) := by
  have hne : T ≠ 0 := Nat.ne_of_gt hT
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
  subst T
  have hpoint : ∀ s,
      selectedTrajectoryIndex hT ell projectX (data s) =
        earliestMinIndex k (fun i : Fin (k + 1) =>
          computableCertificate ell projectX (data s i).1) := by
    intro s
    rfl
  rw [show (fun s => selectedTrajectoryIndex hT ell projectX (data s)) =
      (fun s => earliestMinIndex k (fun i : Fin (k + 1) =>
        computableCertificate ell projectX (data s i).1)) from
    funext hpoint]
  have hscoreVec : Measurable (fun s =>
      fun i : Fin (k + 1) =>
        computableCertificate ell projectX (data s i).1) := by
    rw [measurable_pi_iff]
    intro i
    exact hscore i
  exact (measurable_earliestMinIndex k).comp hscoreVec

/-! ## Measurable state and certificate maps -/

theorem measurable_update_family
    {T : Type} [MeasurableSpace T] {m n : Nat} (ell r : ℝ)
    {S : T → RelativeFOAM.State m n}
    {O : T → RelativeFOAM.MicroOutput m n}
    (hS : Measurable S) (hO : Measurable O) :
    Measurable (fun t => RelativeFOAM.update ell r (S t) (O t)) := by
  unfold RelativeFOAM.update RelativeFOAM.slowQNext RelativeFOAM.slowYNext
  apply measurable_state_mk <;> fun_prop

theorem measurable_coincidentState_family
    {T : Type} [MeasurableSpace T] {m n : Nat}
    {q : T → EVec m} {y : T → EVec n}
    (hq : Measurable q) (hy : Measurable y) :
    Measurable (fun t => StartupConcrete.coincidentState (q t) (y t)) := by
  unfold StartupConcrete.coincidentState
  exact measurable_state_mk hq hy hq hy

theorem measurable_coTranslateValid_family
    {T : Type} [MeasurableSpace T] {m n : Nat} {Y : Set (EVec n)}
    (ell : ℝ) {d : T → EVec m}
    {S : T → RelativeFOAMContraction.ValidState (m := m) Y}
    (hd : Measurable d) (hS : Measurable S) :
    Measurable (fun t => OuterTrajectoryConcrete.coTranslateValid ell
      (d t) (S t)) := by
  apply Measurable.subtype_mk
  unfold Tracking.coTranslate
  apply measurable_state_mk <;> fun_prop

theorem measurable_vecSq_family
    {T : Type} [MeasurableSpace T] {d : Nat}
    {v : T → EVec d} (hv : Measurable v) :
    Measurable (fun t => vecSq (v t)) := by
  unfold vecSq NCPLVerification.vecSq
  apply Finset.measurable_sum Finset.univ
  intro i _hi
  have hi : Measurable ((fun w : EVec d => w i) ∘ v) :=
    (measurable_pi_apply i).comp hv
  exact hi.pow_const 2

theorem measurable_computableCertificate_family
    {T : Type} [MeasurableSpace T] {m n : Nat}
    {X : Set (EVec m)} {Y : Set (EVec n)} (ell : ℝ)
    (projectX : EVec m → EVec m)
    (hprojX : IsEuclideanProjection X projectX)
    {R : T → FeasibleSnapshot X Y} (hR : Measurable R) :
    Measurable (fun t => computableCertificate ell projectX (R t).1) := by
  have hsnap : Measurable (fun t => (R t).1) := hR.subtype_val
  have hstate : Measurable (fun t => (R t).1.state) :=
    measurable_snapshot_state.comp hsnap
  have hqFast : Measurable (fun t => (R t).1.state.1.qFast) :=
    measurable_state_qFast.comp hstate.subtype_val
  have hread : Measurable (fun t =>
      projectX ((-ell⁻¹) • (R t).1.state.1.qFast)) :=
    (measurable_euclideanProjection hprojX).comp
      (measurable_const_smul_family (-ell⁻¹) hqFast)
  have hz : Measurable (fun t => (R t).1.z) :=
    measurable_snapshot_z.comp hsnap
  have hd2 : Measurable (fun t =>
      vecSq (projectX ((-ell⁻¹) • (R t).1.state.1.qFast) - (R t).1.z)) :=
    measurable_vecSq_family (hread.sub hz)
  have hB : Measurable (fun t => (R t).1.B) :=
    measurable_snapshot_B.comp hsnap
  have hsqrtD : Measurable (fun t => Real.sqrt
      (vecSq (projectX ((-ell⁻¹) • (R t).1.state.1.qFast) - (R t).1.z))) :=
    Real.continuous_sqrt.measurable.comp hd2
  have hellB : Measurable (fun t => ell * (R t).1.B) :=
    (measurable_const : Measurable (fun _ : T => ell)).mul hB
  have hsqrtB : Measurable (fun t => Real.sqrt (ell * (R t).1.B)) :=
    Real.continuous_sqrt.measurable.comp hellB
  unfold computableCertificate Tracking.certificate
  have htermD : Measurable (fun t => (2 * ell) * Real.sqrt
      (vecSq (projectX ((-ell⁻¹) • (R t).1.state.1.qFast) - (R t).1.z))) := by
    convert ((measurable_const : Measurable (fun _ : T => 2 * ell)).mul
      hsqrtD) using 1 <;> rfl
  have htermB : Measurable (fun t => 2 * Real.sqrt (ell * (R t).1.B)) := by
    convert ((measurable_const : Measurable (fun _ : T => (2 : ℝ))).mul
      hsqrtB) using 1 <;> rfl
  convert htermD.add htermB using 1 <;> rfl

theorem measurable_selectedTrajectory_family
    {Tpar : Type} [MeasurableSpace Tpar] {m n T : Nat}
    (hT : 0 < T) {X : Set (EVec m)} {Y : Set (EVec n)}
    (ell : ℝ) (projectX : EVec m → EVec m)
    (hprojX : IsEuclideanProjection X projectX)
    {data : Tpar → FeasibleTrajectory T X Y} (hdata : Measurable data) :
    Measurable (fun s =>
      data s (selectedTrajectoryIndex hT ell projectX (data s))) := by
  have hcoord : ∀ i, Measurable (fun s => data s i) := fun i =>
    (measurable_pi_apply i).comp hdata
  have hscore : ∀ i, Measurable (fun s =>
      computableCertificate ell projectX (data s i).1) := fun i =>
    measurable_computableCertificate_family ell projectX hprojX (hcoord i)
  have hidx := measurable_selectedTrajectoryIndex hT ell projectX data hscore
  exact measurable_fin_variable_eval data
    (fun s => selectedTrajectoryIndex hT ell projectX (data s)) hcoord hidx

theorem measurable_finCons_family
    {Tpar A : Type} [MeasurableSpace Tpar] [MeasurableSpace A] {k : Nat}
    {head : Tpar → A} {tail : Tpar → Fin k → A}
    (hhead : Measurable head) (htail : Measurable tail) :
    Measurable (fun t => (Fin.cons (head t) (tail t) : Fin (k + 1) → A)) := by
  rw [measurable_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.cons_zero] using hhead
  · rw [show (fun t => (Fin.cons (head t) (tail t) : Fin (k + 1) → A)
          j.succ) = (fun f : Fin k → A => f j) ∘ tail by
      funext t
      simp only [Fin.cons_succ, Function.comp_apply]]
    exact (measurable_pi_apply j).comp htail

theorem measurable_validUpdate_family
    {T : Type} [MeasurableSpace T] {m n : Nat} {Y : Set (EVec n)}
    (ell r : ℝ)
    {S : T → RelativeFOAMContraction.ValidState (m := m) Y}
    {O : T → FeasibleMicroOutput m Y}
    (hS : Measurable S) (hO : Measurable O) :
    Measurable (fun t =>
      (⟨RelativeFOAM.update ell r (S t).1 (O t).1, (O t).2⟩ :
        RelativeFOAMContraction.ValidState (m := m) Y)) := by
  apply Measurable.subtype_mk
  exact measurable_update_family ell r hS.subtype_val hO.subtype_val

theorem measurable_startupReset_family
    {T : Type} [MeasurableSpace T] {m n : Nat} {Y : Set (EVec n)}
    {O : T → FeasibleMicroOutput m Y} (hO : Measurable O) :
    Measurable (fun t =>
      (⟨StartupConcrete.coincidentState (O t).1.qFastNext
          (O t).1.yFastNext, (O t).2⟩ :
        RelativeFOAMContraction.ValidState (m := m) Y)) := by
  apply Measurable.subtype_mk
  exact measurable_coincidentState_family
    (measurable_microOutput_qFastNext.comp hO.subtype_val)
    (measurable_microOutput_yFastNext.comp hO.subtype_val)

theorem measurable_nextSnapshotResult_family
    {Tpar : Type} [MeasurableSpace Tpar] {m n : Nat}
    {ell r : ℝ} {X : Set (EVec m)} {Y : Set (EVec n)}
    (projectX : EVec m → EVec m)
    (hprojX : IsEuclideanProjection X projectX)
    {R : Tpar → FeasibleSnapshot X Y}
    {stateNext : Tpar → RelativeFOAMContraction.ValidState (m := m) Y}
    (hR : Measurable R) (hstateNext : Measurable stateNext) :
    Measurable (fun t =>
      let zNext := projectX ((-ell⁻¹) • (R t).1.state.1.qFast)
      let d := zNext - (R t).1.z
      (⟨{ z := zNext
          state := stateNext t
          B := Tracking.nextMajorant (1 / 400) ell (vecSq d) (R t).1.B },
        hprojX.mem _⟩ : FeasibleSnapshot X Y)) := by
  have hsnap : Measurable (fun t => (R t).1) := hR.subtype_val
  have hstate : Measurable (fun t => (R t).1.state) :=
    measurable_snapshot_state.comp hsnap
  have hqFast : Measurable (fun t => (R t).1.state.1.qFast) :=
    measurable_state_qFast.comp hstate.subtype_val
  have hzNext : Measurable (fun t =>
      projectX ((-ell⁻¹) • (R t).1.state.1.qFast)) :=
    (measurable_euclideanProjection hprojX).comp
      (measurable_const_smul_family (-ell⁻¹) hqFast)
  have hz : Measurable (fun t => (R t).1.z) :=
    measurable_snapshot_z.comp hsnap
  have hd := hzNext.sub hz
  have hd2 := measurable_vecSq_family hd
  have hB : Measurable (fun t => (R t).1.B) :=
    measurable_snapshot_B.comp hsnap
  have hBnext : Measurable (fun t => Tracking.nextMajorant (1 / 400) ell
      (vecSq (projectX ((-ell⁻¹) • (R t).1.state.1.qFast) - (R t).1.z))
      (R t).1.B) := by
    unfold Tracking.nextMajorant
    fun_prop
  apply Measurable.subtype_mk
  exact measurable_snapshot_mk hzNext hstateNext hBnext

theorem measurable_initialSnapshot_family
    {Tpar : Type} [MeasurableSpace Tpar] {m n : Nat}
    {ell D Delta : ℝ} {X : Set (EVec m)} {Y : Set (EVec n)}
    (J : Nat) (hzeroX : (0 : EVec m) ∈ X)
    {state : Tpar → RelativeFOAMContraction.ValidState (m := m) Y}
    (hstate : Measurable state) :
    Measurable (fun t =>
      (⟨{ z := 0
          state := state t
          B := Tracking.homotopyMajorant (ell / 8) (D ^ 2)
            (8 * (Delta + (ell / 8) * D ^ 2)) J }, hzeroX⟩ :
        FeasibleSnapshot X Y)) := by
  apply Measurable.subtype_mk
  exact measurable_snapshot_mk measurable_const hstate measurable_const

/-! ## Measurable fixed-depth micro programs -/

def borel_microIterateProgram
    {S : Type} [MeasurableSpace S]
    {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (fallback : Oracle.Query m n)
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    {z qg : S → EVec m} {yg : S → EVec n}
    {u : S → ScaledFeasible ell X Y}
    (hz : Measurable z) (hqg : Measurable qg) (hyg : Measurable yg)
    (hu : Measurable u) (k : Nat) :
    FixedBorelFamily S (ScaledFeasible ell X Y) fallback
      (fun s => microIterateProgram (r := r) hell projectX projectY
        hprojX hprojY (z s) (qg s) (yg s) k (u s)) k := by
  induction k generalizing S u with
  | zero =>
      change FixedBorelFamily S (ScaledFeasible ell X Y) fallback
        (fun s => Oracle.Program.pure (u s)) 0
      exact FixedBorelFamily.pure (fallback := fallback) u hu
  | succ k ih =>
      let nextU : S × Oracle.OracleReply m n → ScaledFeasible ell X Y :=
        fun sr => microAdvance (r := r) hell projectX projectY hprojX hprojY
          (z sr.1) (qg sr.1) (yg sr.1) (u sr.1) sr.2
      have hnextU : Measurable nextU := by
        unfold nextU
        exact measurable_microAdvance_family hell projectX projectY hprojX hprojY
          (hz.comp measurable_fst) (hqg.comp measurable_fst)
          (hyg.comp measurable_fst) (hu.comp measurable_fst) measurable_snd
      let tail : (S × Oracle.OracleReply m n) →
          Oracle.Program X Y (ScaledFeasible ell X Y) := fun sr =>
        microIterateProgram (r := r) hell projectX projectY hprojX hprojY
          (z sr.1) (qg sr.1) (yg sr.1) k (nextU sr)
      have htail : FixedBorelFamily (S × Oracle.OracleReply m n)
          (ScaledFeasible ell X Y) fallback tail k := by
        unfold tail
        exact ih (S := S × Oracle.OracleReply m n)
          (u := nextU) (hz.comp measurable_fst) (hqg.comp measurable_fst)
          (hyg.comp measurable_fst) hnextU
      have hq : Measurable (fun s => scaledQuery (u s)) :=
        measurable_scaledQuery_family hu
      have hquery := FixedBorelFamily.query (fallback := fallback)
        (fun s => scaledQuery (u s)) (fun s => scaledQuery_mem (u s)) hq tail htail
      change FixedBorelFamily S (ScaledFeasible ell X Y) fallback
        (fun s => Oracle.Program.query (scaledQuery (u s)) (scaledQuery_mem (u s))
          (fun reply => microIterateProgram (r := r) hell projectX projectY
            hprojX hprojY (z s) (qg s) (yg s) k
              (microAdvance (r := r) hell projectX projectY hprojX hprojY
                (z s) (qg s) (yg s) (u s) reply))) (k + 1)
      exact hquery

def borel_feasibleMicroContinuation
    {S : Type} [MeasurableSpace S]
    {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (fallback : Oracle.Query m n)
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    {z qg : S → EVec m} {yg : S → EVec n}
    {uPrev : S → ScaledFeasible ell X Y}
    (hz : Measurable z) (hqg : Measurable qg) (hyg : Measurable yg)
    (huPrev : Measurable uPrev) :
    FixedBorelFamily S (FeasibleMicroOutput m Y) fallback
      (fun s => do
        let replyPrev ← Oracle.Program.ask (scaledQuery (uPrev s))
          (scaledQuery_mem (uPrev s))
        let opPrev := replyOperator ell r (z s) (qg s) (yg s)
          (uPrev s).1 replyPrev
        let uFinal := microAdvance (r := r) hell projectX projectY hprojX hprojY
          (z s) (qg s) (yg s) (uPrev s) replyPrev
        let replyFinal ← Oracle.Program.ask (scaledQuery uFinal)
          (scaledQuery_mem uFinal)
        Oracle.Program.pure
          ⟨outputFromReplies ell (z s) (uPrev s).1 uFinal.1 replyPrev
              replyFinal opPrev,
            outputFromReplies_y_mem (z s) (uPrev s) uFinal replyPrev
              replyFinal opPrev⟩) 2 := by
  let uFinal : S × Oracle.OracleReply m n → ScaledFeasible ell X Y :=
    fun sr => microAdvance (r := r) hell projectX projectY hprojX hprojY
      (z sr.1) (qg sr.1) (yg sr.1) (uPrev sr.1) sr.2
  have huFinal : Measurable uFinal := by
    unfold uFinal
    exact measurable_microAdvance_family hell projectX projectY hprojX hprojY
      (hz.comp measurable_fst) (hqg.comp measurable_fst)
      (hyg.comp measurable_fst) (huPrev.comp measurable_fst) measurable_snd
  let opPrev : S × Oracle.OracleReply m n → Pair m n := fun sr =>
    replyOperator ell r (z sr.1) (qg sr.1) (yg sr.1) (uPrev sr.1).1 sr.2
  have hopPrev : Measurable opPrev := by
    unfold opPrev
    exact measurable_replyOperator_family ell r
      (hz.comp measurable_fst) (hqg.comp measurable_fst)
      (hyg.comp measurable_fst) (huPrev.subtype_val.comp measurable_fst)
      measurable_snd
  let output : (S × Oracle.OracleReply m n) × Oracle.OracleReply m n →
      FeasibleMicroOutput m Y := fun srr =>
    ⟨outputFromReplies ell (z srr.1.1) (uPrev srr.1.1).1
        (uFinal srr.1).1 srr.1.2 srr.2 (opPrev srr.1),
      outputFromReplies_y_mem (z srr.1.1) (uPrev srr.1.1)
        (uFinal srr.1) srr.1.2 srr.2 (opPrev srr.1)⟩
  have houtput : Measurable output := by
    apply Measurable.subtype_mk
    exact measurable_outputFromReplies_family ell
      (hz.comp (measurable_fst.comp measurable_fst))
      (huPrev.subtype_val.comp (measurable_fst.comp measurable_fst))
      (huFinal.subtype_val.comp measurable_fst)
      (measurable_snd.comp measurable_fst) measurable_snd
      (hopPrev.comp measurable_fst)
  let rest : S × Oracle.OracleReply m n →
      Oracle.Program X Y (FeasibleMicroOutput m Y) := fun sr =>
    Oracle.Program.query (scaledQuery (uFinal sr)) (scaledQuery_mem (uFinal sr))
      (fun replyFinal => Oracle.Program.pure (output (sr, replyFinal)))
  have hrest : FixedBorelFamily (S × Oracle.OracleReply m n)
      (FeasibleMicroOutput m Y) fallback rest 1 := by
    have hq2 : Measurable (fun sr => scaledQuery (uFinal sr)) :=
      measurable_scaledQuery_family huFinal
    have hpure : FixedBorelFamily
        ((S × Oracle.OracleReply m n) × Oracle.OracleReply m n)
        (FeasibleMicroOutput m Y) fallback
        (fun srr => (Oracle.Program.pure (output srr) :
          Oracle.Program X Y (FeasibleMicroOutput m Y))) 0 :=
      FixedBorelFamily.pure (fallback := fallback) output houtput
    exact FixedBorelFamily.query (fallback := fallback)
      (fun sr => scaledQuery (uFinal sr))
      (fun sr => scaledQuery_mem (uFinal sr)) hq2
      (fun srr => (Oracle.Program.pure (output srr) :
        Oracle.Program X Y (FeasibleMicroOutput m Y))) hpure
  have hq1 : Measurable (fun s => scaledQuery (uPrev s)) :=
    measurable_scaledQuery_family huPrev
  have hfirst := FixedBorelFamily.query (fallback := fallback)
    (fun s => scaledQuery (uPrev s)) (fun s => scaledQuery_mem (uPrev s))
    hq1 rest hrest
  change FixedBorelFamily S (FeasibleMicroOutput m Y) fallback
    (fun s => Oracle.Program.query (scaledQuery (uPrev s))
      (scaledQuery_mem (uPrev s))
      (fun replyPrev => Oracle.Program.query (scaledQuery (microAdvance (r := r)
          hell projectX projectY hprojX hprojY (z s) (qg s) (yg s)
            (uPrev s) replyPrev))
        (scaledQuery_mem (microAdvance (r := r) hell projectX projectY
          hprojX hprojY (z s) (qg s) (yg s) (uPrev s) replyPrev))
        (fun replyFinal => Oracle.Program.pure
          ⟨outputFromReplies ell (z s) (uPrev s).1
              (microAdvance (r := r) hell projectX projectY hprojX hprojY
                (z s) (qg s) (yg s) (uPrev s) replyPrev).1
              replyPrev replyFinal
              (replyOperator ell r (z s) (qg s) (yg s) (uPrev s).1 replyPrev),
            outputFromReplies_y_mem (z s) (uPrev s)
              (microAdvance (r := r) hell projectX projectY hprojX hprojY
                (z s) (qg s) (yg s) (uPrev s) replyPrev)
              replyPrev replyFinal
              (replyOperator ell r (z s) (qg s) (yg s) (uPrev s).1 replyPrev)⟩))) 2
  exact hfirst

def borel_feasibleClassMicroProgram
    {S : Type} [MeasurableSpace S]
    {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (fallback : Oracle.Query m n)
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    {z : S → EVec m} {state : S → RelativeFOAM.State m n}
    (hz : Measurable z) (hstate : Measurable state) :
    FixedBorelFamily S (FeasibleMicroOutput m Y) fallback
      (fun s => feasibleClassMicroProgram (r := r) hell projectX projectY
        hprojX hprojY (z s) (state s)) (feasibleMicroIterations + 1) := by
  let qg : S → EVec m := fun s => qCenter ell r (state s)
  let yg : S → EVec n := fun s => yCenter ell r (state s)
  let u0 : S → ScaledFeasible ell X Y := fun s =>
    microInitial (r := r) hell projectX projectY hprojX hprojY (state s)
  have hqg : Measurable qg := by
    unfold qg
    exact measurable_qCenter_family ell r hstate
  have hyg : Measurable yg := by
    unfold yg
    exact measurable_yCenter_family ell r hstate
  have hu0 : Measurable u0 := by
    unfold u0
    exact measurable_microInitial_family hell projectX projectY hprojX hprojY hstate
  let prefixProgram : S → Oracle.Program X Y (ScaledFeasible ell X Y) := fun s =>
    microIterateProgram (r := r) hell projectX projectY hprojX hprojY
      (z s) (qg s) (yg s) (feasibleMicroIterations - 1) (u0 s)
  have hprefix : FixedBorelFamily S (ScaledFeasible ell X Y) fallback
      prefixProgram (feasibleMicroIterations - 1) := by
    unfold prefixProgram
    exact borel_microIterateProgram fallback hell projectX projectY hprojX hprojY
      hz hqg hyg hu0 (feasibleMicroIterations - 1)
  let continuation : S → ScaledFeasible ell X Y →
      Oracle.Program X Y (FeasibleMicroOutput m Y) := fun s uPrev => do
    let replyPrev ← Oracle.Program.ask (scaledQuery uPrev) (scaledQuery_mem uPrev)
    let opPrev := replyOperator ell r (z s) (qg s) (yg s) uPrev.1 replyPrev
    let uFinal := microAdvance (r := r) hell projectX projectY hprojX hprojY
      (z s) (qg s) (yg s) uPrev replyPrev
    let replyFinal ← Oracle.Program.ask (scaledQuery uFinal)
      (scaledQuery_mem uFinal)
    Oracle.Program.pure
      ⟨outputFromReplies ell (z s) uPrev.1 uFinal.1 replyPrev replyFinal opPrev,
        outputFromReplies_y_mem (z s) uPrev uFinal replyPrev replyFinal opPrev⟩
  have hcontinuation : FixedBorelFamily (S × ScaledFeasible ell X Y)
      (FeasibleMicroOutput m Y) fallback
      (fun su => continuation su.1 su.2) 2 := by
    unfold continuation
    exact borel_feasibleMicroContinuation fallback hell projectX projectY
      hprojX hprojY (hz.comp measurable_fst) (hqg.comp measurable_fst)
      (hyg.comp measurable_fst) measurable_snd
  have hall := FixedBorelFamily.bind (fallback := fallback) hprefix continuation
    hcontinuation
  change FixedBorelFamily S (FeasibleMicroOutput m Y) fallback
    (fun s => prefixProgram s >>= continuation s) (feasibleMicroIterations + 1)
  convert hall using 1
  have hpos := feasibleMicroIterations_positive
  omega

/-! ## Startup -/

def borel_startupProgram
    {S : Type} [MeasurableSpace S]
    {m n : Nat} {ell : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (fallback : Oracle.Query m n)
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroY : (0 : EVec n) ∈ Y) :
    FixedBorelFamily S
      (RelativeFOAMContraction.ValidState (m := m) Y) fallback
      (fun _ => startupProgram hell projectX projectY hprojX hprojY hzeroY)
      (feasibleMicroIterations + 1) := by
  let seed : RelativeFOAMContraction.ValidState (m := m) Y :=
    sharedStartupSeed hzeroY
  let micro : S → Oracle.Program X Y (FeasibleMicroOutput m Y) := fun _ =>
    feasibleClassMicroProgram (r := ell / 8) hell projectX projectY
      hprojX hprojY 0 seed.1
  have hmicro : FixedBorelFamily S (FeasibleMicroOutput m Y) fallback
      micro (feasibleMicroIterations + 1) := by
    unfold micro seed
    exact borel_feasibleClassMicroProgram fallback hell projectX projectY
      hprojX hprojY measurable_const measurable_const
  let reset : FeasibleMicroOutput m Y →
      RelativeFOAMContraction.ValidState (m := m) Y := fun O =>
    ⟨StartupConcrete.coincidentState O.1.qFastNext O.1.yFastNext, O.2⟩
  have hreset : Measurable reset := by
    unfold reset
    exact measurable_startupReset_family measurable_id
  let finish : S → FeasibleMicroOutput m Y →
      Oracle.Program X Y (RelativeFOAMContraction.ValidState (m := m) Y) :=
    fun _ O => Oracle.Program.pure (reset O)
  have hfinish : FixedBorelFamily (S × FeasibleMicroOutput m Y)
      (RelativeFOAMContraction.ValidState (m := m) Y) fallback
      (fun so => finish so.1 so.2) 0 := by
    unfold finish
    exact FixedBorelFamily.pure (fallback := fallback)
      (fun so : S × FeasibleMicroOutput m Y => reset so.2)
      (hreset.comp measurable_snd)
  have hall := FixedBorelFamily.bind (fallback := fallback) hmicro finish hfinish
  change FixedBorelFamily S
    (RelativeFOAMContraction.ValidState (m := m) Y) fallback
    (fun s => micro s >>= fun O => Oracle.Program.pure (reset O))
    (feasibleMicroIterations + 1)
  convert hall using 1

/-! ## Macrosteps and fixed-anchor blocks -/

def borel_macroStepProgram
    {S : Type} [MeasurableSpace S]
    {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (fallback : Oracle.Query m n)
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    {z : S → EVec m}
    {state : S → RelativeFOAMContraction.ValidState (m := m) Y}
    (hz : Measurable z) (hstate : Measurable state) :
    FixedBorelFamily S (RelativeFOAMContraction.ValidState (m := m) Y)
      fallback
      (fun s => macroStepProgram (r := r) hell projectX projectY hprojX hprojY
        (z s) (state s)) (feasibleMicroIterations + 1) := by
  let micro : S → Oracle.Program X Y (FeasibleMicroOutput m Y) := fun s =>
    feasibleClassMicroProgram (r := r) hell projectX projectY hprojX hprojY
      (z s) (state s).1
  have hm : FixedBorelFamily S (FeasibleMicroOutput m Y) fallback micro
      (feasibleMicroIterations + 1) := by
    unfold micro
    exact borel_feasibleClassMicroProgram fallback hell projectX projectY
      hprojX hprojY hz hstate.subtype_val
  let nextState : S × FeasibleMicroOutput m Y →
      RelativeFOAMContraction.ValidState (m := m) Y := fun so =>
    ⟨RelativeFOAM.update ell r (state so.1).1 (so.2).1, (so.2).2⟩
  have hnext : Measurable nextState := by
    unfold nextState
    exact measurable_validUpdate_family ell r
      (hstate.comp measurable_fst) measurable_snd
  let continuation : S → FeasibleMicroOutput m Y →
      Oracle.Program X Y (RelativeFOAMContraction.ValidState (m := m) Y) :=
    fun s O => Oracle.Program.pure
      ⟨RelativeFOAM.update ell r (state s).1 O.1, O.2⟩
  have hpure : FixedBorelFamily (S × FeasibleMicroOutput m Y)
      (RelativeFOAMContraction.ValidState (m := m) Y) fallback
      (fun so => continuation so.1 so.2) 0 := by
    change FixedBorelFamily (S × FeasibleMicroOutput m Y)
      (RelativeFOAMContraction.ValidState (m := m) Y) fallback
      (fun so => (Oracle.Program.pure (nextState so) :
        Oracle.Program X Y (RelativeFOAMContraction.ValidState (m := m) Y))) 0
    exact FixedBorelFamily.pure (fallback := fallback) nextState hnext
  have hall := FixedBorelFamily.bind (fallback := fallback) hm continuation hpure
  change FixedBorelFamily S
    (RelativeFOAMContraction.ValidState (m := m) Y) fallback
    (fun s => micro s >>= continuation s) (feasibleMicroIterations + 1)
  simpa using hall

def borel_blockProgram
    {S : Type} [MeasurableSpace S]
    {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (fallback : Oracle.Query m n)
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    {z : S → EVec m}
    {state : S → RelativeFOAMContraction.ValidState (m := m) Y}
    (hz : Measurable z) (hstate : Measurable state) (k : Nat) :
    FixedBorelFamily S (RelativeFOAMContraction.ValidState (m := m) Y)
      fallback
      (fun s => blockProgram (r := r) hell projectX projectY hprojX hprojY
        (z s) k (state s)) (k * (feasibleMicroIterations + 1)) := by
  induction k generalizing S state with
  | zero =>
      simpa only [blockProgram, Nat.zero_mul] using
        (FixedBorelFamily.pure (X := X) (Y := Y)
          (fallback := fallback) state hstate)
  | succ k ih =>
      let macroProgramFamily : S → Oracle.Program X Y
          (RelativeFOAMContraction.ValidState (m := m) Y) := fun s =>
        macroStepProgram (r := r) hell projectX projectY hprojX hprojY
          (z s) (state s)
      have hm : FixedBorelFamily S
          (RelativeFOAMContraction.ValidState (m := m) Y) fallback macroProgramFamily
          (feasibleMicroIterations + 1) := by
        unfold macroProgramFamily
        exact borel_macroStepProgram fallback hell projectX projectY
          hprojX hprojY hz hstate
      let tail : S → RelativeFOAMContraction.ValidState (m := m) Y →
          Oracle.Program X Y (RelativeFOAMContraction.ValidState (m := m) Y) :=
        fun s stateNext => blockProgram (r := r) hell projectX projectY
          hprojX hprojY (z s) k stateNext
      have ht : FixedBorelFamily
          (S × RelativeFOAMContraction.ValidState (m := m) Y)
          (RelativeFOAMContraction.ValidState (m := m) Y) fallback
          (fun ss => tail ss.1 ss.2) (k * (feasibleMicroIterations + 1)) := by
        unfold tail
        exact ih (S := S × RelativeFOAMContraction.ValidState (m := m) Y)
          (state := fun ss => ss.2) (hz.comp measurable_fst) measurable_snd
      have hall := FixedBorelFamily.bind (fallback := fallback) hm tail ht
      change FixedBorelFamily S
        (RelativeFOAMContraction.ValidState (m := m) Y) fallback
        (fun s => macroProgramFamily s >>= tail s)
          ((k + 1) * (feasibleMicroIterations + 1))
      simpa [Nat.succ_mul, Nat.add_comm] using hall

/-! ## Homotopy stages -/

def borel_homotopyProgram
    {S : Type} [MeasurableSpace S]
    {m n : Nat} {ell : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (fallback : Oracle.Query m n)
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    {z : S → EVec m}
    {state : S → RelativeFOAMContraction.ValidState (m := m) Y}
    (hz : Measurable z) (hstate : Measurable state) (J : Nat) :
    FixedBorelFamily S (RelativeFOAMContraction.ValidState (m := m) Y)
      fallback
      (fun s => homotopyProgram hell projectX projectY hprojX hprojY
        (z s) J (state s)) (causalHomotopyCalls ell J) := by
  induction J generalizing S state with
  | zero =>
      simpa only [homotopyProgram, causalHomotopyCalls] using
        (FixedBorelFamily.pure (X := X) (Y := Y)
          (fallback := fallback) state hstate)
  | succ j ih =>
      let prefixProgramFamily : S → Oracle.Program X Y
          (RelativeFOAMContraction.ValidState (m := m) Y) := fun s =>
        homotopyProgram hell projectX projectY hprojX hprojY
          (z s) j (state s)
      have hp : FixedBorelFamily S
          (RelativeFOAMContraction.ValidState (m := m) Y) fallback
          prefixProgramFamily
          (causalHomotopyCalls ell j) := by
        unfold prefixProgramFamily
        exact ih (S := S) (state := state) hz hstate
      let rj := Tracking.curvature (ell / 8) (j + 1)
      let K := blockIterations (alpha ell rj) (1 / 8 : ℝ)
      let tail : S → RelativeFOAMContraction.ValidState (m := m) Y →
          Oracle.Program X Y (RelativeFOAMContraction.ValidState (m := m) Y) :=
        fun s old => blockProgram (r := rj) hell projectX projectY
          hprojX hprojY (z s) K old
      have ht : FixedBorelFamily
          (S × RelativeFOAMContraction.ValidState (m := m) Y)
          (RelativeFOAMContraction.ValidState (m := m) Y) fallback
          (fun so => tail so.1 so.2)
          (K * (feasibleMicroIterations + 1)) := by
        unfold tail
        exact borel_blockProgram fallback hell projectX projectY hprojX hprojY
          (hz.comp measurable_fst) measurable_snd K
      have hall := FixedBorelFamily.bind (fallback := fallback) hp tail ht
      change FixedBorelFamily S
        (RelativeFOAMContraction.ValidState (m := m) Y) fallback
        (fun s => prefixProgramFamily s >>= tail s)
          (causalHomotopyCalls ell (j + 1))
      simpa only [causalHomotopyCalls, rj, K] using hall

/-! ## Outer snapshots and finite trajectories -/

def borel_nextSnapshotProgram
    {S : Type} [MeasurableSpace S]
    {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (fallback : Oracle.Query m n)
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    {snapshot : S → FeasibleSnapshot X Y} (hsnapshot : Measurable snapshot) :
    FixedBorelFamily S (FeasibleSnapshot X Y) fallback
      (fun s => nextSnapshotProgram (r := r) hell projectX projectY
        hprojX hprojY (snapshot s))
      (blockIterations (alpha ell r) (1 / 400 : ℝ) *
        (feasibleMicroIterations + 1)) := by
  let zNext : S → EVec m := fun s =>
    projectX ((-ell⁻¹) • (snapshot s).1.state.1.qFast)
  have hzNext : Measurable zNext := by
    unfold zNext
    have hsnap : Measurable (fun s => (snapshot s).1) := hsnapshot.subtype_val
    have hstate : Measurable (fun s => (snapshot s).1.state) :=
      measurable_snapshot_state.comp hsnap
    have hqFast : Measurable (fun s => (snapshot s).1.state.1.qFast) :=
      measurable_state_qFast.comp hstate.subtype_val
    exact (measurable_euclideanProjection hprojX).comp
      (measurable_const_smul_family (-ell⁻¹) hqFast)
  let displacement : S → EVec m := fun s => zNext s - (snapshot s).1.z
  have hdisplacement : Measurable displacement := by
    unfold displacement
    exact hzNext.sub (measurable_snapshot_z.comp hsnapshot.subtype_val)
  let shifted : S → RelativeFOAMContraction.ValidState (m := m) Y := fun s =>
    OuterTrajectoryConcrete.coTranslateValid ell (displacement s) (snapshot s).1.state
  have hshifted : Measurable shifted := by
    unfold shifted
    exact measurable_coTranslateValid_family ell hdisplacement
      (measurable_snapshot_state.comp hsnapshot.subtype_val)
  let K := blockIterations (alpha ell r) (1 / 400 : ℝ)
  let blockFamily : S → Oracle.Program X Y
      (RelativeFOAMContraction.ValidState (m := m) Y) := fun s =>
    blockProgram (r := r) hell projectX projectY hprojX hprojY
      (zNext s) K (shifted s)
  have hblock : FixedBorelFamily S
      (RelativeFOAMContraction.ValidState (m := m) Y) fallback blockFamily
      (K * (feasibleMicroIterations + 1)) := by
    unfold blockFamily
    exact borel_blockProgram fallback hell projectX projectY hprojX hprojY
      hzNext hshifted K
  let nextResult : S × RelativeFOAMContraction.ValidState (m := m) Y →
      FeasibleSnapshot X Y := fun ss =>
    let zN := projectX ((-ell⁻¹) • (snapshot ss.1).1.state.1.qFast)
    let d := zN - (snapshot ss.1).1.z
    ⟨{ z := zN
       state := ss.2
       B := Tracking.nextMajorant (1 / 400) ell (vecSq d)
         (snapshot ss.1).1.B }, hprojX.mem _⟩
  have hnextResult : Measurable nextResult := by
    unfold nextResult
    exact measurable_nextSnapshotResult_family (r := r) projectX hprojX
      (hsnapshot.comp measurable_fst) measurable_snd
  let continuation : S → RelativeFOAMContraction.ValidState (m := m) Y →
      Oracle.Program X Y (FeasibleSnapshot X Y) := fun s stateNext =>
    Oracle.Program.pure (nextResult (s, stateNext))
  have hpure : FixedBorelFamily
      (S × RelativeFOAMContraction.ValidState (m := m) Y)
      (FeasibleSnapshot X Y) fallback
      (fun ss => continuation ss.1 ss.2) 0 := by
    change FixedBorelFamily
      (S × RelativeFOAMContraction.ValidState (m := m) Y)
      (FeasibleSnapshot X Y) fallback
      (fun ss => (Oracle.Program.pure (nextResult ss) :
        Oracle.Program X Y (FeasibleSnapshot X Y))) 0
    exact FixedBorelFamily.pure (fallback := fallback) nextResult hnextResult
  have hall := FixedBorelFamily.bind (fallback := fallback) hblock continuation hpure
  change FixedBorelFamily S (FeasibleSnapshot X Y) fallback
    (fun s => blockFamily s >>= continuation s)
    (K * (feasibleMicroIterations + 1))
  simpa using hall

def borel_trajectoryProgram
    {m n : Nat} {ell r : ℝ}
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (fallback : Oracle.Query m n)
    (hell : 0 < ell)
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (T : Nat) {S : Type} [MeasurableSpace S]
    {snapshot : S → FeasibleSnapshot X Y} (hsnapshot : Measurable snapshot) :
    FixedBorelFamily S (FeasibleTrajectory T X Y) fallback
      (fun s => trajectoryProgram (r := r) hell projectX projectY
        hprojX hprojY T (snapshot s)) (outerPrefixCalls ell r T) := by
  induction T using Nat.strongRecOn generalizing S with
  | ind T ih =>
      cases T with
      | zero =>
          let emptyTrajectory : S → FeasibleTrajectory 0 X Y :=
            fun _ i => Fin.elim0 i
          have hempty : Measurable emptyTrajectory := by
            rw [measurable_pi_iff]
            intro i
            exact Fin.elim0 i
          simpa only [trajectoryProgram, outerPrefixCalls, Nat.zero_sub,
            Nat.zero_mul] using
            (FixedBorelFamily.pure (X := X) (Y := Y)
              (fallback := fallback) emptyTrajectory hempty)
      | succ T =>
          cases T with
          | zero =>
              let singletonTrajectory : S → FeasibleTrajectory 1 X Y :=
                fun s _ => snapshot s
              have hsingleton : Measurable singletonTrajectory := by
                rw [measurable_pi_iff]
                intro i
                have hi : i = 0 := Fin.eq_zero i
                subst i
                simpa only [singletonTrajectory] using hsnapshot
              simpa only [trajectoryProgram, outerPrefixCalls, Nat.add_sub_cancel,
                Nat.zero_mul] using
                (FixedBorelFamily.pure (X := X) (Y := Y)
                  (fallback := fallback) singletonTrajectory hsingleton)
          | succ k =>
              let nextFamily : S → Oracle.Program X Y (FeasibleSnapshot X Y) :=
                fun s => nextSnapshotProgram (r := r) hell projectX projectY
                  hprojX hprojY (snapshot s)
              have hnext : FixedBorelFamily S (FeasibleSnapshot X Y) fallback
                  nextFamily
                  (blockIterations (alpha ell r) (1 / 400 : ℝ) *
                    (feasibleMicroIterations + 1)) := by
                unfold nextFamily
                exact borel_nextSnapshotProgram fallback hell projectX projectY
                  hprojX hprojY hsnapshot
              let continuation : S → FeasibleSnapshot X Y →
                  Oracle.Program X Y (FeasibleTrajectory (k + 2) X Y) :=
                fun s snapshotNext => do
                  let tail ← trajectoryProgram (r := r) hell projectX projectY
                    hprojX hprojY (k + 1) snapshotNext
                  Oracle.Program.pure (Fin.cons (snapshot s) tail)
              have hcontinuation : FixedBorelFamily
                  (S × FeasibleSnapshot X Y) (FeasibleTrajectory (k + 2) X Y)
                  fallback (fun ss => continuation ss.1 ss.2)
                  (outerPrefixCalls ell r (k + 1)) := by
                let tailFamily : S × FeasibleSnapshot X Y →
                    Oracle.Program X Y (FeasibleTrajectory (k + 1) X Y) :=
                  fun ss => trajectoryProgram (r := r) hell projectX projectY
                    hprojX hprojY (k + 1) ss.2
                have htail : FixedBorelFamily (S × FeasibleSnapshot X Y)
                    (FeasibleTrajectory (k + 1) X Y) fallback tailFamily
                    (outerPrefixCalls ell r (k + 1)) := by
                  unfold tailFamily
                  exact ih (k + 1) (by omega)
                    (S := S × FeasibleSnapshot X Y) measurable_snd
                let consResult :
                    (S × FeasibleSnapshot X Y) × FeasibleTrajectory (k + 1) X Y →
                      FeasibleTrajectory (k + 2) X Y := fun sst =>
                  Fin.cons (snapshot sst.1.1) sst.2
                have hconsResult : Measurable consResult := by
                  unfold consResult
                  exact measurable_finCons_family
                    (hsnapshot.comp (measurable_fst.comp measurable_fst))
                    measurable_snd
                let finish : (S × FeasibleSnapshot X Y) →
                    FeasibleTrajectory (k + 1) X Y →
                    Oracle.Program X Y (FeasibleTrajectory (k + 2) X Y) :=
                  fun ss tail => Oracle.Program.pure
                    (Fin.cons (snapshot ss.1) tail)
                have hpure : FixedBorelFamily
                    ((S × FeasibleSnapshot X Y) ×
                      FeasibleTrajectory (k + 1) X Y)
                    (FeasibleTrajectory (k + 2) X Y) fallback
                    (fun sst => finish sst.1 sst.2) 0 := by
                  change FixedBorelFamily
                    ((S × FeasibleSnapshot X Y) ×
                      FeasibleTrajectory (k + 1) X Y)
                    (FeasibleTrajectory (k + 2) X Y) fallback
                    (fun sst => (Oracle.Program.pure (consResult sst) :
                      Oracle.Program X Y (FeasibleTrajectory (k + 2) X Y))) 0
                  exact FixedBorelFamily.pure (fallback := fallback)
                    consResult hconsResult
                have hbind := FixedBorelFamily.bind (fallback := fallback)
                  htail finish hpure
                change FixedBorelFamily (S × FeasibleSnapshot X Y)
                  (FeasibleTrajectory (k + 2) X Y) fallback
                  (fun ss => tailFamily ss >>= finish ss)
                  (outerPrefixCalls ell r (k + 1))
                simpa using hbind
              have hall := FixedBorelFamily.bind (fallback := fallback)
                hnext continuation hcontinuation
              change FixedBorelFamily S (FeasibleTrajectory (k + 2) X Y)
                fallback (fun s => nextFamily s >>= continuation s)
                (outerPrefixCalls ell r (k + 2))
              simpa [outerPrefixCalls, Nat.succ_sub_one, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm, Nat.add_mul, Nat.mul_assoc]
                using hall

/-! ## Top-level asks -/

def borel_ask
    {S : Type} [MeasurableSpace S]
    {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    (fallback : Oracle.Query m n)
    (q : S → Oracle.Query m n)
    (hq : ∀ s, (q s).1 ∈ X ∧ (q s).2 ∈ Y)
    (hqMeas : Measurable q) :
    FixedBorelFamily S (Oracle.OracleReply m n) fallback
      (fun s => Oracle.Program.ask (q s) (hq s)) 1 := by
  let next : (S × Oracle.OracleReply m n) →
      Oracle.Program X Y (Oracle.OracleReply m n) := fun sr =>
    Oracle.Program.pure sr.2
  have hnext : FixedBorelFamily (S × Oracle.OracleReply m n)
      (Oracle.OracleReply m n) fallback next 0 := by
    unfold next
    exact FixedBorelFamily.pure (fallback := fallback)
      (fun sr : S × Oracle.OracleReply m n => sr.2) measurable_snd
  have hall := FixedBorelFamily.query (fallback := fallback)
    q hq hqMeas next hnext
  simpa only [Oracle.Program.ask, next, Nat.zero_add] using hall

def borel_addFinalAsk
    {S : Type} [MeasurableSpace S]
    {m n depth : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    (fallback : Oracle.Query m n)
    (hzeroY : (0 : EVec n) ∈ Y)
    (pref : S → Oracle.Program X Y (FeasibleSnapshot X Y))
    (hprefix : FixedBorelFamily S (FeasibleSnapshot X Y) fallback
      pref depth) :
    FixedBorelFamily S (EVec m) fallback
      (fun s => do
        let selected ← pref s
        let _reply ← Oracle.Program.ask (selected.1.z, (0 : EVec n))
          ⟨selected.2, hzeroY⟩
        Oracle.Program.pure selected.1.z)
      (depth + 1) := by
  let finish : S → FeasibleSnapshot X Y → Oracle.Program X Y (EVec m) :=
    fun _ selected => do
      let _reply ← Oracle.Program.ask (selected.1.z, (0 : EVec n))
        ⟨selected.2, hzeroY⟩
      Oracle.Program.pure selected.1.z
  let q : S × FeasibleSnapshot X Y → Oracle.Query m n :=
    fun ss => (ss.2.1.z, (0 : EVec n))
  have hq : Measurable q := by
    unfold q
    exact (measurable_snapshot_z.comp measurable_snd.subtype_val).prodMk
      measurable_const
  let next : ((S × FeasibleSnapshot X Y) × Oracle.OracleReply m n) →
      Oracle.Program X Y (EVec m) := fun ssr =>
    Oracle.Program.pure ssr.1.2.1.z
  have hnext : FixedBorelFamily
      ((S × FeasibleSnapshot X Y) × Oracle.OracleReply m n)
      (EVec m) fallback next 0 := by
    unfold next
    exact FixedBorelFamily.pure (fallback := fallback)
      (fun ssr : (S × FeasibleSnapshot X Y) × Oracle.OracleReply m n =>
        ssr.1.2.1.z)
      (measurable_snapshot_z.comp
        (measurable_snd.comp measurable_fst).subtype_val)
  have hfinish : FixedBorelFamily (S × FeasibleSnapshot X Y) (EVec m)
      fallback (fun ss => finish ss.1 ss.2) 1 := by
    have hquery := FixedBorelFamily.query (fallback := fallback)
      q (fun ss => ⟨ss.2.2, hzeroY⟩) hq next hnext
    simpa [finish, q, next, Oracle.Program.ask, Oracle.Program.bind] using hquery
  have hall := FixedBorelFamily.bind (fallback := fallback)
    hprefix finish hfinish
  simpa only [finish] using hall

/-! ## The complete scheduled prefix -/

def borel_schedulePrefixProgram
    {m n : Nat} (ell D Delta eps : ℝ)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    FixedBorelFamily Unit (FeasibleSnapshot X Y)
      ((0 : EVec m), (0 : EVec n))
      (fun _ => schedulePrefixProgram ell D Delta eps hell hD hDelta heps
        projectX projectY hprojX hprojY hzeroX hzeroY)
      (prefixCalls ell D Delta eps hell hD heps) := by
  let fallback : Oracle.Query m n := ((0 : EVec m), (0 : EVec n))
  let J := scheduleStage ell D eps hell hD heps
  let r := scheduleCurvature ell D eps hell hD heps
  let T := scheduleIterations ell D Delta eps hell hD heps
  let hT : 0 < T := scheduleIterations_pos hell hD hDelta heps
  let origin : Unit → Oracle.Program X Y (Oracle.OracleReply m n) := fun _ =>
    Oracle.Program.ask ((0 : EVec m), (0 : EVec n)) ⟨hzeroX, hzeroY⟩
  have horigin : FixedBorelFamily Unit (Oracle.OracleReply m n) fallback
      origin 1 := by
    unfold origin
    exact borel_ask fallback (fun _ : Unit => ((0 : EVec m), (0 : EVec n)))
      (fun _ => ⟨hzeroX, hzeroY⟩) measurable_const
  let A := Unit × Oracle.OracleReply m n
  let startFamily : A → Oracle.Program X Y
      (RelativeFOAMContraction.ValidState (m := m) Y) := fun _ =>
    startupProgram hell projectX projectY hprojX hprojY hzeroY
  have hstart : FixedBorelFamily A
      (RelativeFOAMContraction.ValidState (m := m) Y) fallback startFamily
      (feasibleMicroIterations + 1) := by
    unfold startFamily A
    exact borel_startupProgram fallback hell projectX projectY hprojX hprojY
      hzeroY
  let afterStart : A → RelativeFOAMContraction.ValidState (m := m) Y →
      Oracle.Program X Y (FeasibleSnapshot X Y) := fun _ startup => do
    let finalState ← homotopyProgram hell projectX projectY hprojX hprojY
      0 J startup
    let R0 : FeasibleSnapshot X Y :=
      ⟨{ z := 0
         state := finalState
         B := Tracking.homotopyMajorant (ell / 8) (D ^ 2)
          (8 * (Delta + (ell / 8) * D ^ 2)) J }, hzeroX⟩
    let data ← trajectoryProgram (r := r) hell projectX projectY
      hprojX hprojY T R0
    Oracle.Program.pure
      (data (selectedTrajectoryIndex hT ell projectX data))
  let B := A × RelativeFOAMContraction.ValidState (m := m) Y
  let homFamily : B → Oracle.Program X Y
      (RelativeFOAMContraction.ValidState (m := m) Y) := fun bs =>
    homotopyProgram hell projectX projectY hprojX hprojY 0 J bs.2
  have hhom : FixedBorelFamily B
      (RelativeFOAMContraction.ValidState (m := m) Y) fallback homFamily
      (causalHomotopyCalls ell J) := by
    unfold homFamily
    exact borel_homotopyProgram fallback hell projectX projectY hprojX hprojY
      measurable_const measurable_snd J
  let C := B × RelativeFOAMContraction.ValidState (m := m) Y
  let initialSnapshot : C → FeasibleSnapshot X Y := fun cs =>
    ⟨{ z := 0
       state := cs.2
       B := Tracking.homotopyMajorant (ell / 8) (D ^ 2)
        (8 * (Delta + (ell / 8) * D ^ 2)) J }, hzeroX⟩
  have hinitialSnapshot : Measurable initialSnapshot := by
    unfold initialSnapshot
    exact measurable_initialSnapshot_family (ell := ell) (D := D)
      (Delta := Delta) J hzeroX measurable_snd
  let trajectoryFamily : C → Oracle.Program X Y
      (FeasibleTrajectory T X Y) := fun cs =>
    trajectoryProgram (r := r) hell projectX projectY hprojX hprojY T
      (initialSnapshot cs)
  have htrajectory : FixedBorelFamily C (FeasibleTrajectory T X Y) fallback
      trajectoryFamily (outerPrefixCalls ell r T) := by
    unfold trajectoryFamily
    exact borel_trajectoryProgram fallback hell projectX projectY hprojX hprojY
      T hinitialSnapshot
  let selectedResult : C × FeasibleTrajectory T X Y →
      FeasibleSnapshot X Y := fun cd =>
    cd.2 (selectedTrajectoryIndex hT ell projectX cd.2)
  have hselectedResult : Measurable selectedResult := by
    unfold selectedResult
    exact measurable_selectedTrajectory_family hT ell projectX hprojX
      (data := fun cd : C × FeasibleTrajectory T X Y => cd.2) measurable_snd
  let finishTrajectory : C → FeasibleTrajectory T X Y →
      Oracle.Program X Y (FeasibleSnapshot X Y) := fun _ data =>
    Oracle.Program.pure
      (data (selectedTrajectoryIndex hT ell projectX data))
  have hfinishTrajectory : FixedBorelFamily (C × FeasibleTrajectory T X Y)
      (FeasibleSnapshot X Y) fallback
      (fun cd => finishTrajectory cd.1 cd.2) 0 := by
    change FixedBorelFamily (C × FeasibleTrajectory T X Y)
      (FeasibleSnapshot X Y) fallback
      (fun cd => (Oracle.Program.pure (selectedResult cd) :
        Oracle.Program X Y (FeasibleSnapshot X Y))) 0
    exact FixedBorelFamily.pure (fallback := fallback)
      selectedResult hselectedResult
  let afterHom : B → RelativeFOAMContraction.ValidState (m := m) Y →
      Oracle.Program X Y (FeasibleSnapshot X Y) := fun bs finalState =>
    let R0 : FeasibleSnapshot X Y :=
      ⟨{ z := 0
         state := finalState
         B := Tracking.homotopyMajorant (ell / 8) (D ^ 2)
          (8 * (Delta + (ell / 8) * D ^ 2)) J }, hzeroX⟩
    do
      let data ← trajectoryProgram (r := r) hell projectX projectY
        hprojX hprojY T R0
      Oracle.Program.pure
        (data (selectedTrajectoryIndex hT ell projectX data))
  have hafterHom : FixedBorelFamily C (FeasibleSnapshot X Y) fallback
      (fun cs => afterHom cs.1 cs.2) (outerPrefixCalls ell r T) := by
    have hall := FixedBorelFamily.bind (fallback := fallback)
      htrajectory finishTrajectory hfinishTrajectory
    change FixedBorelFamily C (FeasibleSnapshot X Y) fallback
      (fun cs => trajectoryFamily cs >>= finishTrajectory cs)
      (outerPrefixCalls ell r T)
    simpa [trajectoryFamily, finishTrajectory, afterHom, initialSnapshot]
      using hall
  have hafterStart : FixedBorelFamily B (FeasibleSnapshot X Y) fallback
      (fun bs => afterStart bs.1 bs.2)
      (causalHomotopyCalls ell J + outerPrefixCalls ell r T) := by
    have hall := FixedBorelFamily.bind (fallback := fallback)
      hhom afterHom hafterHom
    change FixedBorelFamily B (FeasibleSnapshot X Y) fallback
      (fun bs => homFamily bs >>= afterHom bs)
      (causalHomotopyCalls ell J + outerPrefixCalls ell r T)
    simpa [homFamily, afterHom, afterStart] using hall
  let afterOrigin : Unit → Oracle.OracleReply m n →
      Oracle.Program X Y (FeasibleSnapshot X Y) := fun u reply => do
    let startup ← startupProgram hell projectX projectY hprojX hprojY hzeroY
    afterStart (u, reply) startup
  have hafterOrigin : FixedBorelFamily A (FeasibleSnapshot X Y) fallback
      (fun ar => afterOrigin ar.1 ar.2)
      ((feasibleMicroIterations + 1) +
        (causalHomotopyCalls ell J + outerPrefixCalls ell r T)) := by
    have hall := FixedBorelFamily.bind (fallback := fallback)
      hstart afterStart hafterStart
    change FixedBorelFamily A (FeasibleSnapshot X Y) fallback
      (fun ar => startFamily ar >>= afterStart ar)
      ((feasibleMicroIterations + 1) +
        (causalHomotopyCalls ell J + outerPrefixCalls ell r T))
    simpa [startFamily, afterOrigin, A] using hall
  have hall := FixedBorelFamily.bind (fallback := fallback)
    horigin afterOrigin hafterOrigin
  simpa [schedulePrefixProgram, prefixCalls, origin, afterOrigin, afterStart,
    fallback, J, r, T, hT, A, Nat.add_assoc] using hall

/-! ## From program certificates to measurable components -/

theorem compiled_isMeasurable_of_fixedBorelFamily
    {S α : Type} [MeasurableSpace S] [MeasurableSpace α]
    {m n : Nat} {X : Set (EVec m)} {Y : Set (EVec n)}
    (fallback : Oracle.Query m n)
    (p : S → Oracle.Program X Y α) {depth : Nat}
    (hp : FixedBorelFamily S α fallback p depth) (s : S)
    (hfallback : fallback.1 ∈ X ∧ fallback.2 ∈ Y)
    (hfirst : Oracle.Program.queryAfterHistory (p s) fallback 0
      (Oracle.emptyHistory m n) = (0, 0)) :
    (Oracle.Program.compile (p s) fallback hfallback hfirst).IsMeasurable := by
  intro t
  change Measurable (fun h : Oracle.ReplyHistory m n t =>
    Oracle.Program.queryAfterHistory (p s) fallback t h)
  exact (hp.measurable_query t).comp
    (measurable_const.prodMk measurable_id)

/-! ## Full client, measurable algorithm, and paper complexity -/

def borel_sharedOracleProgram
    {m n : Nat} (ell D Delta eps : ℝ)
    (hell : 0 < ell) (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    {X : Set (EVec m)} {Y : Set (EVec n)}
    (projectX : EVec m → EVec m) (projectY : EVec n → EVec n)
    (hprojX : IsEuclideanProjection X projectX)
    (hprojY : IsEuclideanProjection Y projectY)
    (hzeroX : (0 : EVec m) ∈ X) (hzeroY : (0 : EVec n) ∈ Y) :
    FixedBorelFamily Unit (EVec m) ((0 : EVec m), (0 : EVec n))
      (fun _ => sharedOracleProgram ell D Delta eps hell hD hDelta heps
        projectX projectY hprojX hprojY hzeroX hzeroY)
      (sharedOracleCalls ell D Delta eps hell hD heps) := by
  let fallback : Oracle.Query m n := ((0 : EVec m), (0 : EVec n))
  let pref : Unit → Oracle.Program X Y (FeasibleSnapshot X Y) := fun _ =>
    schedulePrefixProgram ell D Delta eps hell hD hDelta heps
      projectX projectY hprojX hprojY hzeroX hzeroY
  have hpref : FixedBorelFamily Unit (FeasibleSnapshot X Y) fallback pref
      (prefixCalls ell D Delta eps hell hD heps) := by
    unfold pref fallback
    exact borel_schedulePrefixProgram ell D Delta eps hell hD hDelta heps
      projectX projectY hprojX hprojY hzeroX hzeroY
  have hall := borel_addFinalAsk fallback hzeroY pref hpref
  simpa [sharedOracleProgram, sharedOracleCalls, pref, fallback] using hall

theorem sharedComponent_isMeasurable
    (ell D Delta eps : ℝ) (hell : 0 < ell)
    (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (Q : Oracle.AdmissibleDomainPair) :
    (sharedComponent ell D Delta eps hell hD hDelta heps Q).IsMeasurable := by
  let fallback : Oracle.Query Q.m Q.n :=
    ((0 : EVec Q.m), (0 : EVec Q.n))
  let p : Unit → Oracle.Program Q.X Q.Y (EVec Q.m) := fun _ =>
    sharedOracleProgram ell D Delta eps hell hD hDelta heps
      (domainProjectX Q) (domainProjectY Q)
      (domainProjectX_spec Q) (domainProjectY_spec Q)
      Q.zero_mem_X Q.zero_mem_Y
  have hp : FixedBorelFamily Unit (EVec Q.m) fallback p
      (sharedOracleCalls ell D Delta eps hell hD heps) := by
    unfold p fallback
    exact borel_sharedOracleProgram ell D Delta eps hell hD hDelta heps
      (domainProjectX Q) (domainProjectY Q)
      (domainProjectX_spec Q) (domainProjectY_spec Q)
      Q.zero_mem_X Q.zero_mem_Y
  change (Oracle.Program.compile (p ()) fallback
    ⟨Q.zero_mem_X, Q.zero_mem_Y⟩
    (sharedOracleProgram_firstQuery ell D Delta eps hell hD hDelta heps
      (domainProjectX Q) (domainProjectY Q)
      (domainProjectX_spec Q) (domainProjectY_spec Q)
      Q.zero_mem_X Q.zero_mem_Y)).IsMeasurable
  exact compiled_isMeasurable_of_fixedBorelFamily fallback p hp ()
    ⟨Q.zero_mem_X, Q.zero_mem_Y⟩
    (sharedOracleProgram_firstQuery ell D Delta eps hell hD hDelta heps
      (domainProjectX Q) (domainProjectY Q)
      (domainProjectX_spec Q) (domainProjectY_spec Q)
      Q.zero_mem_X Q.zero_mem_Y)

/-- The executable causal client belongs to the paper's literal measurable
domain-wise algorithm class. -/
def measurableSharedDomainAlgorithm
    (ell D Delta eps : ℝ) (hell : 0 < ell)
    (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps) :
    Oracle.MeasurableDomainWiseDeterministicAlgorithm where
  component Q := sharedComponent ell D Delta eps hell hD hDelta heps Q
  measurable_component Q :=
    sharedComponent_isMeasurable ell D Delta eps hell hD hDelta heps Q

theorem measurableSharedDomainAlgorithm_toCausal
    (ell D Delta eps : ℝ) (hell : 0 < ell)
    (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps) :
    (measurableSharedDomainAlgorithm ell D Delta eps
      hell hD hDelta heps).toCausal =
      sharedDomainAlgorithm ell D Delta eps hell hD hDelta heps := by
  rfl

/-- Literal measurable-algorithm upper threshold for the paper class. -/
theorem measurablePaperComplexityAtMost_sharedOracle
    (ell D Delta eps : ℝ) (hell : 0 < ell)
    (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps) :
    Oracle.MeasurablePaperComplexityAtMost ell D Delta eps
      (sharedOracleBudget ell D Delta eps hell hD heps) := by
  let A := measurableSharedDomainAlgorithm ell D Delta eps
    hell hD hDelta heps
  refine ⟨A, ?_⟩
  change Oracle.PaperSolvesWithin A.toCausal ell D Delta eps
    (sharedOracleBudget ell D Delta eps hell hD heps)
  apply Oracle.paperSolvesWithin_of_solvesWithin
  simpa only [A, measurableSharedDomainAlgorithm,
    Oracle.MeasurableDomainWiseDeterministicAlgorithm.toCausal,
    sharedOracleBudget, sharedDomainAlgorithm] using
    (sharedDomainAlgorithm_solvesWithin ell D Delta eps
      hell hD hDelta heps)

/-- Upper inequality for the literal infimum--supremum hitting complexity. -/
theorem measurablePaperHittingComplexity_le_sharedOracleBudget
    (ell D Delta eps : ℝ) (hell : 0 < ell)
    (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps) :
    Oracle.measurablePaperHittingComplexity ell D Delta eps ≤
      (sharedOracleBudget ell D Delta eps hell hD heps : WithTop Nat) :=
  Oracle.measurablePaperHittingComplexity_le_of_atMost
    (measurablePaperComplexityAtMost_sharedOracle ell D Delta eps
      hell hD hDelta heps)

theorem measurable_paper_shared_upper_rate
    (ell D Delta eps : ℝ) (hell : 0 < ell)
    (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps) :
    Oracle.MeasurablePaperComplexityAtMost ell D Delta eps
        (sharedOracleBudget ell D Delta eps hell hD heps) ∧
      (sharedOracleBudget ell D Delta eps hell hD heps : ℝ) ≤
        UniformCost.uniformCostConstant *
          ((ell * Delta / eps ^ 2 + 1) * max 1 (ell * D / eps)) :=
  ⟨measurablePaperComplexityAtMost_sharedOracle ell D Delta eps
      hell hD hDelta heps,
    sharedOracleBudget_uniform_bound ell D Delta eps
      hell hD hDelta heps⟩

theorem measurable_paper_shared_logFree_upper_rate
    (ell D Delta eps : ℝ) (hell : 0 < ell)
    (hD : 0 < D) (hDelta : 0 < Delta) (heps : 0 < eps)
    (hepsD : eps ≤ ell * D)
    (hgap : (1 / 4 : ℝ) ≤ ell * Delta / eps ^ 2) :
    Oracle.MeasurablePaperComplexityAtMost ell D Delta eps
        (sharedOracleBudget ell D Delta eps hell hD heps) ∧
      (sharedOracleBudget ell D Delta eps hell hD heps : ℝ) ≤
        LogFreeCorollary.logFreeCostConstant *
          (ell ^ 2 * D * Delta / eps ^ 3) :=
  ⟨measurablePaperComplexityAtMost_sharedOracle ell D Delta eps
      hell hD hDelta heps,
    sharedOracleBudget_logFree_bound ell D Delta eps
      hell hD hDelta heps hepsD hgap⟩

end

end SharedOracleMeasurable
end Upper
end NCCLowerBoundVerification
