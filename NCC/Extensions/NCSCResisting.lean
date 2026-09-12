import NCPLVerification.ResistingOracle
import NCC.Extensions.NCSCZeroChainObstruction
import NCC.Extensions.NCSCAuxiliary

/-!
# Corrected-quadratic resisting transcripts on full spaces

The hidden-basis construction is applied to the concave auxiliary objective.
The deterministic method sees the exact records obtained by subtracting a
known global dual quadratic. This is a transcript identity, not a change in
the oracle model or an assumption about the method's discovered support.
-/

namespace NCC.Extensions.NCSCResisting

noncomputable section

open NCCLowerBoundVerification hiding EVec
open NCPLVerification
open NCCLowerBoundVerification.Upper

set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

/-- Subtract the known global dual quadratic from one auxiliary record. -/
def subtractQuadratic {m n : ℕ} (mu : ℝ) (r : FirstOrderRecord m n) :
    FirstOrderRecord m n :=
  { r with value := r.value - quadraticCorrection mu r.queryY
           gradY := r.gradY - mu • r.queryY }

/-- A causal method for the auxiliary oracle, simulating `A` on the corrected
oracle. No objective or future reply enters this definition. -/
def correctedMethod {m n : ℕ} (mu : ℝ) (A : DeterministicFOBlackBox m n) :
    DeterministicFOBlackBox m n where
  nextQuery hist := A.nextQuery (hist.map (subtractQuadratic mu))
  output hist := A.output (hist.map (subtractQuadratic mu))

theorem subtractQuadratic_record {m n : ℕ} (mu : ℝ)
    (f : EVec m → EVec n → ℝ)
    (gx : EVec m → EVec n → EVec m) (gy : EVec m → EVec n → EVec n)
    (q : EVec m × EVec n) :
    subtractQuadratic mu (firstOrderRecord f gx gy q) =
      firstOrderRecord (fun x y => f x y - quadraticCorrection mu y)
        gx (fun x y => gy x y - mu • y) q := rfl

theorem correctedMethod_run {m n : ℕ} (mu : ℝ) (A : DeterministicFOBlackBox m n)
    (f : EVec m → EVec n → ℝ)
    (gx : EVec m → EVec n → EVec m) (gy : EVec m → EVec n → EVec n) (t : ℕ) :
    (runHistory (correctedMethod mu A) f gx gy t).map (subtractQuadratic mu) =
      runHistory A (fun x y => f x y - quadraticCorrection mu y)
        gx (fun x y => gy x y - mu • y) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [runHistory, List.map_append, List.map_cons, List.map_nil,
        subtractQuadratic_record]
      change _ ++ [firstOrderRecord _ _ _ (A.nextQuery
        ((runHistory (correctedMethod mu A) f gx gy t).map (subtractQuadratic mu)))] = _
      rw [ih]

theorem fits_supported {T N DX DY s K : ℕ}
    {f : EVec T → EVec (T * N) → ℝ}
    {gx : EVec T → EVec (T * N) → EVec T}
    {gy : EVec T → EVec (T * N) → EVec (T * N)}
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    {hist : List (FirstOrderRecord DX DY)}
    (hf : ResistingFits f gx gy U V s hist) (hK : s + hist.length ≤ K) :
    ∀ r ∈ hist, SupportedBelow K
      (orderedJoint (frameProject U r.queryX) (frameProject V r.queryY)) := by
  induction hist generalizing s with
  | nil => simp
  | cons r rs ih =>
      simp only [ResistingFits] at hf
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hf.2.1.mono (by simp at hK; omega)
      · exact ih hf.2.2 (by simp at hK ⊢; omega) a ha

/-- Every queried point, not merely a selected output, has the required
projected support in one final, fixed pair of orthonormal frames. -/
theorem hidden_basis_all_records {T N DX DY K : ℕ}
    (A : DeterministicFOBlackBox DX DY)
    (f : EVec T → EVec (T * N) → ℝ)
    (gx : EVec T → EVec (T * N) → EVec T)
    (gy : EVec T → EVec (T * N) → EVec (T * N))
    (hchain : IsFirstOrderZeroChain (orderedSaddleFieldOf gx gy))
    (hK : K < T * (N + 1))
    (hcapX : T + (K + 1) < DX) (hcapY : T * N + (K + 1) < DY) :
    ∃ U : Fin T → EVec DX, ∃ V : Fin (T * N) → EVec DY,
      IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      ∀ r ∈ runHistory A (rotatedF U V f) (rotatedGradX U V gx)
          (rotatedGradY U V gy) K,
        SupportedBelow K (orderedJoint (frameProject U r.queryX) (frameProject V r.queryY)) := by
  obtain ⟨Up, Vp, hist, hlen, hcausal, hpU, hpV, hz, hu, hf⟩ :=
    exists_partial_resisting_state A f gx gy hchain hK hcapX hcapY K le_rfl
  let qX := hist.map FirstOrderRecord.queryX
  let qY := hist.map FirstOrderRecord.queryY
  obtain ⟨U, V, hU, hV, hprojX, hprojY, hembed⟩ :=
    exists_product_frame_completion qX qY (Nat.le_of_lt hK)
      (by simp [qX, hlen]; omega) (by simp [qY, hlen]; omega) hpU hpV hz hu
  have hf' : ResistingFits f gx gy U V 0 hist := by
    apply hf.of_completion hprojX hprojY hembed hchain (by simp [hlen])
    · intro a ha
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
    · intro a ha
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hr := causal_actual_history_eq_run A (rotatedF U V f)
    (rotatedGradX U V gx) (rotatedGradY U V gy) hcausal hf'.forall_records
  rw [hlen] at hr
  refine ⟨U, V, hU, hV, ?_⟩
  rw [← hr]
  exact fits_supported hf' (by simp [hlen])

theorem corrected_hidden_basis_all_records {T N DX DY K : ℕ}
    (mu : ℝ) (A : DeterministicFOBlackBox DX DY)
    (f : EVec T → EVec (T * N) → ℝ)
    (gx : EVec T → EVec (T * N) → EVec T)
    (gy : EVec T → EVec (T * N) → EVec (T * N))
    (hchain : IsFirstOrderZeroChain (orderedSaddleFieldOf gx gy))
    (hK : K < T * (N + 1))
    (hcapX : T + (K + 1) < DX) (hcapY : T * N + (K + 1) < DY) :
    ∃ U : Fin T → EVec DX, ∃ V : Fin (T * N) → EVec DY,
      IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      ∀ r ∈ runHistory A
          (fun x y => rotatedF U V f x y - quadraticCorrection mu y)
          (rotatedGradX U V gx) (fun x y => rotatedGradY U V gy x y - mu • y) K,
        SupportedBelow K (orderedJoint (frameProject U r.queryX) (frameProject V r.queryY)) := by
  obtain ⟨U, V, hU, hV, hs⟩ := hidden_basis_all_records (correctedMethod mu A)
    f gx gy hchain hK hcapX hcapY
  refine ⟨U, V, hU, hV, ?_⟩
  rw [← correctedMethod_run]
  intro r hr
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
  exact hs a ha

def recordReply {m n : ℕ} (r : FirstOrderRecord m n) : Oracle.OracleReply m n :=
  ⟨r.value, r.gradX, r.gradY⟩

/-- Embed the manuscript's reply-history causal maps into the unrestricted
record-history interface. Stored queries are ignored by this adapter. -/
def componentBlackBox {m n : ℕ}
    (A : Oracle.DeterministicFOComponent (Set.univ : Set (EVec m))
      (Set.univ : Set (EVec n))) : DeterministicFOBlackBox m n where
  nextQuery hist := A.nextQuery hist.length (fun i => recordReply (hist.get i))
  output _ := 0

def actualRecord {m n : ℕ}
    (A : Oracle.DeterministicFOComponent (Set.univ : Set (EVec m))
      (Set.univ : Set (EVec n))) (P : NCCInstance m n) (t : ℕ) : FirstOrderRecord m n :=
  firstOrderRecord P.f P.gradX P.gradY (A.queriedAt P t)

theorem nextQuery_cast {m n t s : ℕ}
    (A : Oracle.DeterministicFOComponent (Set.univ : Set (EVec m))
      (Set.univ : Set (EVec n))) (h : t = s) (hist : Oracle.ReplyHistory m n t) :
    A.nextQuery t hist = A.nextQuery s (fun i => hist (Fin.cast h.symm i)) := by
  subst s
  rfl

theorem componentBlackBox_next_ofFn {m n : ℕ}
    (A : Oracle.DeterministicFOComponent (Set.univ : Set (EVec m))
      (Set.univ : Set (EVec n))) (P : NCCInstance m n) (t : ℕ) :
    (componentBlackBox A).nextQuery (List.ofFn (fun i : Fin t => actualRecord A P i)) =
      A.queriedAt P t := by
  change A.nextQuery _ (fun i => recordReply ((List.ofFn
    (fun j : Fin t => actualRecord A P j)).get i)) = _
  rw [nextQuery_cast A (List.length_ofFn (f := fun j : Fin t => actualRecord A P j))]
  rw [Oracle.DeterministicFOComponent.queriedAt_eq_nextQuery]
  congr 1
  funext i
  simp only [List.get_ofFn]
  rfl

theorem componentBlackBox_run {m n : ℕ}
    (A : Oracle.DeterministicFOComponent (Set.univ : Set (EVec m))
      (Set.univ : Set (EVec n))) (P : NCCInstance m n) (t : ℕ) :
    runHistory (componentBlackBox A) P.f P.gradX P.gradY t =
      List.ofFn (fun i : Fin t => actualRecord A P i) := by
  induction t with
  | zero => simp [runHistory]
  | succ t ih =>
      rw [runHistory, ih, componentBlackBox_next_ofFn, List.ofFn_succ']
      simp only [List.concat_eq_append, Fin.val_castSucc, Fin.val_last, actualRecord]

theorem actualRecord_mem_run {m n K : ℕ}
    (A : Oracle.DeterministicFOComponent (Set.univ : Set (EVec m))
      (Set.univ : Set (EVec n))) (P : NCCInstance m n) {t : ℕ} (ht : t < K) :
    actualRecord A P t ∈ runHistory (componentBlackBox A) P.f P.gradX P.gradY K := by
  rw [componentBlackBox_run]
  exact List.mem_ofFn.mpr ⟨⟨t, ht⟩, rfl⟩

theorem orderedDual_supported_one {N k : ℕ} {z : EVec (1 * (N + 1))}
    (hz : SupportedBelow k z) : SupportedBelow k (orderedDual z) := by
  intro j hj
  rcases hp : finProdFinEquiv.symm j with ⟨a, b⟩
  have ha : a.val = 0 := by omega
  have heq : j = finProdFinEquiv (a, b) := by
    rw [← hp]
    exact (finProdFinEquiv.apply_symm_apply j).symm
  have hv : j.val = b.val := by rw [heq, finProdFinEquiv_val, ha]; simp
  change z (finProdFinEquiv ((finProdFinEquiv.symm j).1,
    (finProdFinEquiv.symm j).2.castSucc)) = 0
  rw [hp]
  apply hz
  simp only [finProdFinEquiv_val, ha, zero_mul, zero_add, Fin.val_castSucc]
  omega

theorem ordered_chain_one {N : ℕ} (G : EVec (1 * N) → EVec (1 * N))
    (hG : IsFirstOrderZeroChain G) :
    IsFirstOrderZeroChain (orderedSaddleFieldOf (fun _ _ => (0 : EVec 1)) (fun _ y => G y)) := by
  intro k z hz i hi
  rcases hp : finProdFinEquiv.symm i with ⟨a, b⟩
  have ha : a.val = 0 := by omega
  have heq : i = finProdFinEquiv (a, b) := by
    rw [← hp]
    exact (finProdFinEquiv.apply_symm_apply i).symm
  have hv : i.val = b.val := by rw [heq, finProdFinEquiv_val, ha]; simp
  unfold orderedSaddleFieldOf orderedJoint
  rw [hp]
  dsimp only
  split_ifs with hb
  · change -G (orderedDual z) (finProdFinEquiv (a, ⟨b.val, hb⟩)) = 0
    rw [hG k _ (orderedDual_supported_one hz) _]
    · simp
    · rw [finProdFinEquiv_val, ha]
      simpa using (show k + 1 ≤ b.val by omega)
  · rfl

theorem auxiliary_gradient_chain (n : ℕ) (c : ℝ) :
    IsFirstOrderZeroChain (fun y : EVec (n + 1) =>
      NCSCZeroChainObstruction.gradient n c y + y) := by
  intro k y hy i hi
  change NCSCZeroChainObstruction.gradient n c y i + y i = 0
  rw [NCSCZeroChainObstruction.gradient_zero_of_zero_tail c y hy i hi, hy i (by omega)]
  simp

theorem one_block_corrected_records {N DX DY K : ℕ}
    (mu : ℝ) (A : DeterministicFOBlackBox DX DY)
    (f : EVec 1 → EVec (1 * N) → ℝ) (G : EVec (1 * N) → EVec (1 * N))
    (hG : IsFirstOrderZeroChain G) (hK : K ≤ 1 * N)
    (hcapX : 1 + (K + 1) < DX) (hcapY : 1 * N + (K + 1) < DY) :
    ∃ U : Fin 1 → EVec DX, ∃ V : Fin (1 * N) → EVec DY,
      IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      ∀ r ∈ runHistory A
          (fun x y => f (frameProject U x) (frameProject V y) - quadraticCorrection mu y)
          (fun _ _ => 0) (fun _ y => frameEmbed V (G (frameProject V y)) - mu • y) K,
        SupportedBelow K (frameProject V r.queryY) := by
  obtain ⟨U, V, hU, hV, hr⟩ := corrected_hidden_basis_all_records mu A f (fun _ _ => 0)
    (fun _ y => G y) (ordered_chain_one G hG) (by simp only [Nat.one_mul] at hK ⊢; omega)
      hcapX hcapY
  refine ⟨U, V, hU, hV, ?_⟩
  intro r hmem
  have hgx : rotatedGradX U V (fun _ _ => (0 : EVec 1)) = fun _ _ => 0 := by
    funext x y
    exact frameEmbed_zero U
  have hmem' : r ∈ runHistory A
      (fun x y => rotatedF U V f x y - quadraticCorrection mu y)
      (rotatedGradX U V (fun _ _ => 0))
      (fun x y => rotatedGradY U V (fun _ y => G y) x y - mu • y) K := by
    simpa only [rotatedF, hgx, rotatedGradY] using hmem
  have hs := hr r hmem'
  have hh := orderedDual_supported_one hs
  simpa only [orderedDual_orderedJoint] using hh

end

end NCC.Extensions.NCSCResisting
