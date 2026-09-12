import NCCLowerBoundVerification.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Globalizing a `C¹` extension defined near a closed domain

The paper defines differentiability on `X × Y` by requiring a `C¹` function
on some open neighborhood.  Several analytic files are simpler when given a
global `C¹` representative.  This module proves—using smooth cutoffs, not an
assumption—that the two representations are equivalent in finite-dimensional
Euclidean space.
-/

namespace NCCLowerBoundVerification

noncomputable section

open Set Function Filter

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A global `C¹` function agreeing with `f` on an entire neighborhood of
every point of the closed set.  The neighborhood equality preserves both
values and derivatives. -/
structure GlobalC1Extension (s : Set E) (f : E → ℝ) where
  toFun : E → ℝ
  contDiff : ContDiff ℝ 1 toFun
  eventuallyEq : ∀ x ∈ s, toFun =ᶠ[nhds x] f

/-- A smooth cutoff equal to one on a closed set and with topological support
inside a prescribed open set. -/
theorem exists_contDiff_cutoff {s U : Set E} (hs : IsClosed s)
    (hU : IsOpen U) (hsU : s ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ 1 χ ∧
      (∀ x, χ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x ∈ s, χ x = 1) ∧ tsupport χ ⊆ U := by
  obtain ⟨V, hVopen, hsV, hVclosure⟩ :=
    normal_exists_closure_subset hs hU hsU
  obtain ⟨f, hfsupport, hfDiff, hfRange⟩ :=
    hVopen.exists_contDiff_support_eq (n := (1 : ℕ∞))
  obtain ⟨g, hgsupport, hgDiff, hgRange⟩ :=
    hs.isOpen_compl.exists_contDiff_support_eq (n := (1 : ℕ∞))
  have hf0 : ∀ x, 0 ≤ f x := by
    intro x
    exact (hfRange (mem_range_self x)).1
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    exact (hgRange (mem_range_self x)).1
  have hdenom : ∀ x, 0 < f x + g x := by
    intro x
    by_cases hx : x ∈ V
    · have hfnz : f x ≠ 0 := by
        rw [← mem_support, hfsupport]
        exact hx
      exact add_pos_of_pos_of_nonneg (lt_of_le_of_ne (hf0 x) (Ne.symm hfnz)) (hg0 x)
    · have hxs : x ∉ s := fun hxs ↦ hx (hsV hxs)
      have hgnz : g x ≠ 0 := by
        rw [← mem_support, hgsupport]
        exact hxs
      exact add_pos_of_nonneg_of_pos (hf0 x)
        (lt_of_le_of_ne (hg0 x) (Ne.symm hgnz))
  let χ : E → ℝ := fun x => f x / (f x + g x)
  have hχDiff : ContDiff ℝ 1 χ := by
    exact hfDiff.div (hfDiff.add hgDiff) (fun x => (hdenom x).ne')
  have hχRange : ∀ x, χ x ∈ Icc (0 : ℝ) 1 := by
    intro x
    refine ⟨div_nonneg (hf0 x) (hdenom x).le, ?_⟩
    exact div_le_one_of_le₀ (le_add_of_nonneg_right (hg0 x)) (hdenom x).le
  have hχsupport : support χ = V := by
    have hsum : support (fun x => f x + g x) = univ :=
      eq_univ_of_forall fun x => (hdenom x).ne'
    change support (fun x => f x / (f x + g x)) = V
    rw [support_div, hfsupport, hsum, inter_univ]
  have hχone : ∀ x ∈ s, χ x = 1 := by
    intro x hx
    have hgin : x ∉ support g := by
      rw [hgsupport]
      simpa using hx
    have hgzero : g x = 0 := notMem_support.mp hgin
    have hfx : 0 < f x := by
      have hfnz : f x ≠ 0 := by
        rw [← mem_support, hfsupport]
        exact hsV hx
      exact lt_of_le_of_ne (hf0 x) (Ne.symm hfnz)
    dsimp [χ]
    rw [hgzero, add_zero, div_self hfx.ne']
  refine ⟨χ, hχDiff, hχRange, hχone, ?_⟩
  change closure (support χ) ⊆ U
  rw [hχsupport]
  exact hVclosure

/-- A function that is `C¹` on an open neighborhood of a closed set has a
global `C¹` representative agreeing with it locally along the closed set. -/
theorem exists_globalC1Extension {s U : Set E} {f : E → ℝ}
    (hs : IsClosed s) (hU : IsOpen U) (hsU : s ⊆ U)
    (hf : ContDiffOn ℝ 1 f U) : Nonempty (GlobalC1Extension s f) := by
  obtain ⟨W, hWopen, hsW, hWclosure⟩ :=
    normal_exists_closure_subset hs hU hsU
  obtain ⟨χ, hχDiff, _hχRange, hχone, hχsupport⟩ :=
    exists_contDiff_cutoff (isClosed_closure : IsClosed (closure W)) hU hWclosure
  let F : E → ℝ := fun x => χ x * f x
  have hFonU : ContDiffOn ℝ 1 F U := by
    exact hχDiff.contDiffOn.mul hf
  have hFoutside : ContDiffOn ℝ 1 F (tsupport χ)ᶜ := by
    intro x hx
    have hχzero : χ =ᶠ[nhds x] (0 : E → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hx
    have hFzero : F =ᶠ[nhds x] (0 : E → ℝ) := by
      filter_upwards [hχzero] with y hy
      simp [F, hy]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      hFzero |>.contDiffWithinAt
  have hcover : U ∪ (tsupport χ)ᶜ = univ := by
    apply eq_univ_of_forall
    intro x
    by_cases hx : x ∈ U
    · exact Or.inl hx
    · exact Or.inr (fun hxt => hx (hχsupport hxt))
  have hFglobal : ContDiff ℝ 1 F :=
    contDiff_of_contDiffOn_union_of_isOpen hFonU hFoutside hcover
      hU (show IsOpen (tsupport χ)ᶜ by
        exact (show IsClosed (tsupport χ) by exact isClosed_closure).isOpen_compl)
  refine ⟨{ toFun := F, contDiff := hFglobal, eventuallyEq := ?_ }⟩
  intro x hx
  have hxW : x ∈ W := hsW hx
  have hWevent : ∀ᶠ y in nhds x, y ∈ W := hWopen.mem_nhds hxW
  filter_upwards [hWevent] with y hy
  have hχ : χ y = 1 := hχone y (subset_closure hy)
  simp [F, hχ]

theorem GlobalC1Extension.eqOn {s : Set E} {f : E → ℝ}
    (G : GlobalC1Extension s f) : EqOn G.toFun f s := by
  intro x hx
  exact (G.eventuallyEq x hx).eq_of_nhds

theorem GlobalC1Extension.hasFDerivAt_iff {s : Set E} {f : E → ℝ}
    (G : GlobalC1Extension s f) {x : E} (hx : x ∈ s)
    {f' : E →L[ℝ] ℝ} :
    HasFDerivAt G.toFun f' x ↔ HasFDerivAt f f' x := by
  constructor
  · intro h
    exact h.congr_of_eventuallyEq (G.eventuallyEq x hx).symm
  · intro h
    exact h.congr_of_eventuallyEq (G.eventuallyEq x hx)

end

end NCCLowerBoundVerification
