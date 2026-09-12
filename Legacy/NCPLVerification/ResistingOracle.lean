import NCPLVerification.DeterministicBlackBox

/-!
# Finite-horizon resisting oracle

This file develops the product-preserving hidden-basis construction used for
deterministic saddle black-box methods.  The interleaved base coordinates are
dual coordinates of a block followed by its primal coordinate.
-/

namespace NCPLVerification

noncomputable section

def orderedJoint {T N : Nat} (x : EVec T) (y : EVec (T * N)) :
    EVec (T * (N + 1)) := fun k ↦
  let p := finProdFinEquiv.symm k
  if hdual : p.2.1 < N then
    y (finProdFinEquiv (p.1, ⟨p.2.1, hdual⟩))
  else
    x p.1

theorem orderedPrimal_orderedJoint {T N : Nat}
    (x : EVec T) (y : EVec (T * N)) :
    orderedPrimal (orderedJoint x y) = x := by
  funext i
  unfold orderedPrimal orderedJoint
  simp

theorem orderedDual_orderedJoint {T N : Nat}
    (x : EVec T) (y : EVec (T * N)) :
    orderedDual (orderedJoint x y) = y := by
  funext k
  rcases hp : finProdFinEquiv.symm k with ⟨i, j⟩
  have hk : k = finProdFinEquiv (i, j) := by
    rw [← hp]
    exact (finProdFinEquiv.apply_symm_apply k).symm
  subst k
  simp [orderedDual, orderedJoint]

theorem orderedJoint_ordered {T N : Nat}
    (z : EVec (T * (N + 1))) :
    orderedJoint (orderedPrimal z) (orderedDual z) = z := by
  funext k
  rcases hp : finProdFinEquiv.symm k with ⟨i, s⟩
  have hk : k = finProdFinEquiv (i, s) := by
    rw [← hp]
    exact (finProdFinEquiv.apply_symm_apply k).symm
  subst k
  unfold orderedJoint
  simp only [finProdFinEquiv.symm_apply_apply]
  by_cases hs : s.1 < N
  · rw [dif_pos hs]
    simp [orderedDual]
  · have hsN : s = Fin.last N := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    rw [dif_neg hs, hsN]
    rfl

def orderedSaddleFieldOf {T N : Nat}
    (gradX : EVec T → EVec (T * N) → EVec T)
    (gradY : EVec T → EVec (T * N) → EVec (T * N))
    (z : EVec (T * (N + 1))) : EVec (T * (N + 1)) :=
  orderedJoint (gradX (orderedPrimal z) (orderedDual z))
    (-gradY (orderedPrimal z) (orderedDual z))

theorem orderedPrimal_orderedSaddleFieldOf {T N : Nat}
    (gradX : EVec T → EVec (T * N) → EVec T)
    (gradY : EVec T → EVec (T * N) → EVec (T * N)) (z) :
    orderedPrimal (orderedSaddleFieldOf gradX gradY z) =
      gradX (orderedPrimal z) (orderedDual z) := by
  exact orderedPrimal_orderedJoint _ _

theorem orderedDual_orderedSaddleFieldOf {T N : Nat}
    (gradX : EVec T → EVec (T * N) → EVec T)
    (gradY : EVec T → EVec (T * N) → EVec (T * N)) (z) :
    orderedDual (orderedSaddleFieldOf gradX gradY z) =
      -gradY (orderedPrimal z) (orderedDual z) := by
  exact orderedDual_orderedJoint _ _

def ProductFramesZeroFrom {T N DX DY : Nat} (t : Nat)
    (U : Fin T → EVec DX) (V : Fin (T * N) → EVec DY) : Prop :=
  ∀ k : Fin (T * (N + 1)), t ≤ k.1 →
    let p := finProdFinEquiv.symm k
    if hdual : p.2.1 < N then
      V (finProdFinEquiv (p.1, ⟨p.2.1, hdual⟩)) = 0
    else
      U p.1 = 0

def ProductFramesUnitBelow {T N DX DY : Nat} (t : Nat)
    (U : Fin T → EVec DX) (V : Fin (T * N) → EVec DY) : Prop :=
  ∀ k : Fin (T * (N + 1)), k.1 < t →
    let p := finProdFinEquiv.symm k
    if hdual : p.2.1 < N then
      evecDotValue
        (V (finProdFinEquiv (p.1, ⟨p.2.1, hdual⟩)))
        (V (finProdFinEquiv (p.1, ⟨p.2.1, hdual⟩))) = 1
    else
      evecDotValue (U p.1) (U p.1) = 1

def IsPartialOrthonormalFrame {m D : Nat} (U : Fin m → EVec D) : Prop :=
  (∀ i, U i = 0 ∨ evecDotValue (U i) (U i) = 1) ∧
  ∀ i j, i ≠ j → evecDotValue (U i) (U j) = 0

theorem isPartialOrthonormalFrame_zero {m D : Nat} :
    IsPartialOrthonormalFrame (0 : Fin m → EVec D) := by
  constructor
  · intro i
    exact Or.inl rfl
  · intros
    unfold evecDotValue
    simp

theorem IsPartialOrthonormalFrame.update_zero {m D : Nat}
    {U : Fin m → EVec D} (hU : IsPartialOrthonormalFrame U)
    (i : Fin m) (hi : U i = 0) (u : EVec D)
    (hu : evecDotValue u u = 1)
    (horth : ∀ j, evecDotValue (U j) u = 0) :
    IsPartialOrthonormalFrame (Function.update U i u) := by
  constructor
  · intro j
    by_cases hji : j = i
    · subst j
      simp [hu]
    · simp only [Function.update, hji]
      exact hU.1 j
  · intro j k hjk
    by_cases hji : j = i
    · subst j
      have hh : evecDotValue u (U k) = 0 := by
        rw [evecDotValue_comm]
        exact horth k
      simpa [Function.update, hjk, Ne.symm hjk] using hh
    · simp only [Function.update, hji]
      by_cases hki : k = i
      · subst k
        simpa [Function.update, hji] using horth j
      · simp only [hki]
        exact hU.2 j k hjk

theorem supportedBelow_orderedProjection_of_zeroFrom {T N DX DY t : Nat}
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    (hzero : ProductFramesZeroFrom t U V) (X : EVec DX) (Y : EVec DY) :
    SupportedBelow t
      (orderedJoint (frameProject U X) (frameProject V Y)) := by
  intro k hk
  unfold orderedJoint
  rcases hp : finProdFinEquiv.symm k with ⟨i, s⟩
  have hz := hzero k hk
  simp only [hp] at hz
  by_cases hs : s.1 < N
  · rw [dif_pos hs] at hz ⊢
    unfold frameProject
    rw [hz]
    unfold evecDotValue
    simp
  · rw [dif_neg hs] at hz ⊢
    unfold frameProject
    rw [hz]
    unfold evecDotValue
    simp

theorem ordered_dual_index_injective {T N : Nat}
    {k l : Fin (T * (N + 1))}
    (hk : (finProdFinEquiv.symm k).2.1 < N)
    (hl : (finProdFinEquiv.symm l).2.1 < N)
    (heq : finProdFinEquiv
        ((finProdFinEquiv.symm k).1,
          ⟨(finProdFinEquiv.symm k).2.1, hk⟩) =
      finProdFinEquiv
        ((finProdFinEquiv.symm l).1,
          ⟨(finProdFinEquiv.symm l).2.1, hl⟩)) : k = l := by
  have hp := finProdFinEquiv.injective heq
  have hfirst : (finProdFinEquiv.symm k).1 =
      (finProdFinEquiv.symm l).1 :=
    congrArg (fun q : Fin T × Fin N ↦ q.1) hp
  have hsecond : (finProdFinEquiv.symm k).2.1 =
      (finProdFinEquiv.symm l).2.1 :=
    congrArg (fun q : Fin T × Fin N ↦ q.2.1) hp
  have hpfull : finProdFinEquiv.symm k = finProdFinEquiv.symm l := by
    apply Prod.ext
    · exact hfirst
    · apply Fin.ext
      exact hsecond
  exact finProdFinEquiv.symm.injective hpfull

theorem ordered_primal_index_injective {T N : Nat}
    {k l : Fin (T * (N + 1))}
    (hk : ¬(finProdFinEquiv.symm k).2.1 < N)
    (hl : ¬(finProdFinEquiv.symm l).2.1 < N)
    (heq : (finProdFinEquiv.symm k).1 =
      (finProdFinEquiv.symm l).1) : k = l := by
  apply finProdFinEquiv.symm.injective
  apply Prod.ext
  · exact heq
  · apply Fin.ext
    have hkTop : (finProdFinEquiv.symm k).2.1 = N := by omega
    have hlTop : (finProdFinEquiv.symm l).2.1 = N := by omega
    omega

theorem isOrthonormalFrame_of_partial_complete {m D : Nat}
    {U : Fin m → EVec D} (hpartial : IsPartialOrthonormalFrame U)
    (hunit : ∀ i, evecDotValue (U i) (U i) = 1) :
    IsOrthonormalFrame U := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact hunit i
  · rw [if_neg hij]
    exact hpartial.2 i j hij

def FrameConstraints {m D : Nat} (U : Fin m → EVec D)
    (q : List (EVec D)) : List (EVec D) :=
  List.ofFn U ++ q

theorem exists_unit_orthogonal_to_frame_constraints {m D : Nat}
    (U : Fin m → EVec D) (q : List (EVec D))
    (hcapacity : m + q.length < D) :
    ∃ u : EVec D,
      evecDotValue u u = 1 ∧
      (∀ i, evecDotValue (U i) u = 0) ∧
      ∀ X ∈ q, evecDotValue X u = 0 := by
  have hlen : (FrameConstraints U q).length < D := by
    simpa [FrameConstraints] using hcapacity
  obtain ⟨u, hu, horth⟩ :=
    exists_unit_orthogonal_to_list (FrameConstraints U q) hlen
  refine ⟨u, hu, ?_, ?_⟩
  · intro i
    apply horth (U i)
    unfold FrameConstraints
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  · intro X hX
    apply horth X
    unfold FrameConstraints
    exact List.mem_append_right _ hX

def ProductFrameReveal {T N DX DY : Nat}
    (k : Fin (T * (N + 1)))
    (qX : List (EVec DX)) (qY : List (EVec DY))
    (U : Fin T → EVec DX) (V : Fin (T * N) → EVec DY)
    (U' : Fin T → EVec DX) (V' : Fin (T * N) → EVec DY) : Prop :=
  let p := finProdFinEquiv.symm k
    if hdual : p.2.1 < N then
      U' = U ∧ ∃ u : EVec DY,
        V' = Function.update V
          (finProdFinEquiv (p.1, ⟨p.2.1, hdual⟩)) u ∧
        evecDotValue u u = 1 ∧
        (∀ j, evecDotValue (V j) u = 0) ∧
        ∀ Y ∈ qY, evecDotValue Y u = 0
    else
      V' = V ∧ ∃ u : EVec DX,
        U' = Function.update U p.1 u ∧
        evecDotValue u u = 1 ∧
        (∀ i, evecDotValue (U i) u = 0) ∧
        ∀ X ∈ qX, evecDotValue X u = 0

theorem exists_product_frame_reveal {T N DX DY t : Nat}
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    (qX : List (EVec DX)) (qY : List (EVec DY))
    (ht : t < T * (N + 1))
    (hcapX : T + qX.length < DX)
    (hcapY : T * N + qY.length < DY)
    (hpartialU : IsPartialOrthonormalFrame U)
    (hpartialV : IsPartialOrthonormalFrame V)
    (hzero : ProductFramesZeroFrom t U V)
    (hunit : ProductFramesUnitBelow t U V) :
    ∃ U' V',
      ProductFrameReveal (⟨t, ht⟩ : Fin (T * (N + 1)))
        qX qY U V U' V' ∧
      IsPartialOrthonormalFrame U' ∧
      IsPartialOrthonormalFrame V' ∧
      ProductFramesZeroFrom (t + 1) U' V' ∧
      ProductFramesUnitBelow (t + 1) U' V' := by
  let kt : Fin (T * (N + 1)) := ⟨t, ht⟩
  rcases hp : finProdFinEquiv.symm kt with ⟨i, s⟩
  by_cases hs : s.1 < N
  · let j : Fin (T * N) := finProdFinEquiv (i, ⟨s.1, hs⟩)
    have hjzero : V j = 0 := by
      have hz := hzero kt (by simp [kt])
      simp only [hp, dif_pos hs] at hz
      exact hz
    obtain ⟨u, hu, hVu, hqu⟩ :=
      exists_unit_orthogonal_to_frame_constraints V qY hcapY
    let V' := Function.update V j u
    refine ⟨U, V', ?_, hpartialU,
      hpartialV.update_zero j hjzero u hu hVu, ?_, ?_⟩
    · change ProductFrameReveal kt qX qY U V U V'
      unfold ProductFrameReveal
      rw [hp, dif_pos hs]
      exact ⟨rfl, u, rfl, hu, hVu, hqu⟩
    · intro k hk
      rcases hpk : finProdFinEquiv.symm k with ⟨a, b⟩
      by_cases hb : b.1 < N
      · rw [dif_pos hb]
        let jb : Fin (T * N) := finProdFinEquiv (a, ⟨b.1, hb⟩)
        have hjb : jb ≠ j := by
          intro heq
          have hkk : k = kt := ordered_dual_index_injective
            (by simpa [hpk] using hb) (by simpa [hp] using hs)
            (by simpa [hpk, hp, jb, j] using heq)
          subst k
          simp [kt] at hk
        have hold := hzero k (by omega)
        simp only [hpk, dif_pos hb] at hold
        simpa [V', Function.update, jb, j, hjb] using hold
      · rw [dif_neg hb]
        have hold := hzero k (by omega)
        simpa only [hpk, dif_neg hb] using hold
    · intro k hk
      by_cases hkt : k.1 < t
      · rcases hpk : finProdFinEquiv.symm k with ⟨a, b⟩
        have hold := hunit k hkt
        simp only [hpk] at hold ⊢
        by_cases hb : b.1 < N
        · rw [dif_pos hb] at hold ⊢
          let jb : Fin (T * N) := finProdFinEquiv (a, ⟨b.1, hb⟩)
          have hjb : jb ≠ j := by
            intro heq
            have hkk : k = kt := ordered_dual_index_injective
              (by simpa [hpk] using hb) (by simpa [hp] using hs)
              (by simpa [hpk, hp, jb, j] using heq)
            subst k
            simp [kt] at hkt
          simpa [V', Function.update, jb, j, hjb] using hold
        · rw [dif_neg hb] at hold ⊢
          exact hold
      · have hkeq : k = kt := by
          apply Fin.ext
          simp [kt]
          omega
        subst k
        simp only [hp, dif_pos hs]
        simp [V', j, hu]
  · have hsTop : s.1 = N := by omega
    have hizero : U i = 0 := by
      have hz := hzero kt (by simp [kt])
      simp only [hp, dif_neg hs] at hz
      exact hz
    obtain ⟨u, hu, hUu, hqu⟩ :=
      exists_unit_orthogonal_to_frame_constraints U qX hcapX
    let U' := Function.update U i u
    refine ⟨U', V, ?_, hpartialU.update_zero i hizero u hu hUu,
      hpartialV, ?_, ?_⟩
    · change ProductFrameReveal kt qX qY U V U' V
      unfold ProductFrameReveal
      rw [hp, dif_neg hs]
      exact ⟨rfl, u, rfl, hu, hUu, hqu⟩
    · intro k hk
      rcases hpk : finProdFinEquiv.symm k with ⟨a, b⟩
      by_cases hb : b.1 < N
      · rw [dif_pos hb]
        have hold := hzero k (by omega)
        simpa only [hpk, dif_pos hb] using hold
      · rw [dif_neg hb]
        have hai : a ≠ i := by
          intro heq
          have hkk : k = kt := ordered_primal_index_injective
            (by simpa [hpk] using hb) (by simpa [hp] using hs)
            (by simpa [hpk, hp] using heq)
          subst k
          simp [kt] at hk
        have hold := hzero k (by omega)
        simp only [hpk, dif_neg hb] at hold
        simpa [U', Function.update, hai] using hold
    · intro k hk
      by_cases hkt : k.1 < t
      · rcases hpk : finProdFinEquiv.symm k with ⟨a, b⟩
        have hold := hunit k hkt
        simp only [hpk] at hold ⊢
        by_cases hb : b.1 < N
        · rw [dif_pos hb] at hold ⊢
          exact hold
        · rw [dif_neg hb] at hold ⊢
          have hai : a ≠ i := by
            intro heq
            have hkk : k = kt := ordered_primal_index_injective
              (by simpa [hpk] using hb) (by simpa [hp] using hs)
              (by simpa [hpk, hp] using heq)
            subst k
            simp [kt] at hkt
          simpa [U', Function.update, hai] using hold
      · have hkeq : k = kt := by
          apply Fin.ext
          simp [kt]
          omega
        subst k
        simp only [hp, dif_neg hs]
        simp [U', hu]

theorem frameProject_update_eq_of_dots {m D : Nat}
    (U : Fin m → EVec D) (i : Fin m) (u X : EVec D)
    (hold : evecDotValue (U i) X = 0)
    (hnew : evecDotValue u X = 0) :
    frameProject (Function.update U i u) X = frameProject U X := by
  funext j
  unfold frameProject
  by_cases hji : j = i
  · subst j
    simp [Function.update, hold, hnew]
  · simp [Function.update, hji]

theorem frameEmbed_update_eq_of_coeff_zero {m D : Nat}
    (U : Fin m → EVec D) (i : Fin m) (u : EVec D) (g : EVec m)
    (hg : g i = 0) :
    frameEmbed (Function.update U i u) g = frameEmbed U g := by
  funext k
  unfold frameEmbed
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j = i
  · subst j
    simp [Function.update, hg]
  · simp [Function.update, hji]

theorem ProductFrameReveal.project_eq {T N DX DY : Nat}
    {k : Fin (T * (N + 1))}
    {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    {U' : Fin T → EVec DX} {V' : Fin (T * N) → EVec DY}
    (hr : ProductFrameReveal k qX qY U V U' V')
    (hzero : ProductFramesZeroFrom k.1 U V) :
    (∀ X ∈ qX, frameProject U' X = frameProject U X) ∧
    ∀ Y ∈ qY, frameProject V' Y = frameProject V Y := by
  unfold ProductFrameReveal at hr
  rcases hp : finProdFinEquiv.symm k with ⟨i, s⟩
  simp only [hp] at hr
  by_cases hs : s.1 < N
  · rw [dif_pos hs] at hr
    rcases hr with ⟨rfl, u, rfl, hu, hVu, hqu⟩
    constructor
    · intro X hX
      rfl
    · intro Y hY
      apply frameProject_update_eq_of_dots
      · have hv0 := hzero k le_rfl
        simp only [hp, dif_pos hs] at hv0
        rw [hv0]
        unfold evecDotValue
        simp
      · rw [evecDotValue_comm]
        exact hqu Y hY
  · rw [dif_neg hs] at hr
    rcases hr with ⟨rfl, u, rfl, hu, hUu, hqu⟩
    constructor
    · intro X hX
      apply frameProject_update_eq_of_dots
      · have hu0 := hzero k le_rfl
        simp only [hp, dif_neg hs] at hu0
        rw [hu0]
        unfold evecDotValue
        simp
      · rw [evecDotValue_comm]
        exact hqu X hX
    · intro Y hY
      rfl

theorem ProductFrameReveal.embed_eq_of_supported {T N DX DY : Nat}
    {k : Fin (T * (N + 1))}
    {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    {U' : Fin T → EVec DX} {V' : Fin (T * N) → EVec DY}
    (hr : ProductFrameReveal k qX qY U V U' V')
    {z : EVec (T * (N + 1))} (hz : SupportedBelow k.1 z) :
    frameEmbed U' (orderedPrimal z) = frameEmbed U (orderedPrimal z) ∧
    frameEmbed V' (orderedDual z) = frameEmbed V (orderedDual z) := by
  unfold ProductFrameReveal at hr
  rcases hp : finProdFinEquiv.symm k with ⟨i, s⟩
  simp only [hp] at hr
  have hzk : z k = 0 := hz k le_rfl
  by_cases hs : s.1 < N
  · rw [dif_pos hs] at hr
    rcases hr with ⟨rfl, u, rfl, hu, hVu, hqu⟩
    constructor
    · rfl
    · apply frameEmbed_update_eq_of_coeff_zero
      have hk : k = finProdFinEquiv (i, s) := by
        rw [← hp]
        exact (finProdFinEquiv.apply_symm_apply k).symm
      have hsCast : s = (⟨s.1, hs⟩ : Fin N).castSucc := by
        apply Fin.ext
        rfl
      change dualBlock (orderedDual z) i ⟨s.1, hs⟩ = 0
      rw [orderedDual_block_apply]
      rw [← hsCast, ← hk]
      exact hzk
  · rw [dif_neg hs] at hr
    rcases hr with ⟨rfl, u, rfl, hu, hUu, hqu⟩
    constructor
    · apply frameEmbed_update_eq_of_coeff_zero
      have hsTop : s = Fin.last N := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      have hk : k = finProdFinEquiv (i, s) := by
        rw [← hp]
        exact (finProdFinEquiv.apply_symm_apply k).symm
      change z (finProdFinEquiv (i, Fin.last N)) = 0
      rw [← hsTop, ← hk]
      exact hzk
    · rfl

/-- Complete every still-zero ordered column.  Projections of the fixed
constraint queries, and embeddings of every vector supported in the already
revealed prefix, remain unchanged. -/
theorem exists_product_frame_completion_aux
    {T N DX DY t n : Nat}
    (qX : List (EVec DX)) (qY : List (EVec DY))
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    (hend : t + n = T * (N + 1))
    (hcapX : T + qX.length < DX)
    (hcapY : T * N + qY.length < DY)
    (hpartialU : IsPartialOrthonormalFrame U)
    (hpartialV : IsPartialOrthonormalFrame V)
    (hzero : ProductFramesZeroFrom t U V)
    (hunit : ProductFramesUnitBelow t U V) :
    ∃ U' V',
      IsOrthonormalFrame U' ∧ IsOrthonormalFrame V' ∧
      (∀ X ∈ qX, frameProject U' X = frameProject U X) ∧
      (∀ Y ∈ qY, frameProject V' Y = frameProject V Y) ∧
      ∀ z : EVec (T * (N + 1)), SupportedBelow t z →
        frameEmbed U' (orderedPrimal z) = frameEmbed U (orderedPrimal z) ∧
        frameEmbed V' (orderedDual z) = frameEmbed V (orderedDual z) := by
  induction n generalizing t U V with
  | zero =>
      have htM : t = T * (N + 1) := by omega
      have hUunit : ∀ i, evecDotValue (U i) (U i) = 1 := by
        intro i
        let k : Fin (T * (N + 1)) := finProdFinEquiv (i, Fin.last N)
        have hk : k.1 < t := by
          rw [htM]
          exact k.isLt
        have hu := hunit k hk
        simp [k] at hu
        exact hu
      have hVunit : ∀ j, evecDotValue (V j) (V j) = 1 := by
        intro j
        rcases hp : finProdFinEquiv.symm j with ⟨i, s⟩
        let k : Fin (T * (N + 1)) :=
          finProdFinEquiv (i, s.castSucc)
        have hk : k.1 < t := by
          rw [htM]
          exact k.isLt
        have hv := hunit k hk
        simp [k] at hv
        have hj : j = finProdFinEquiv (i, s) := by
          rw [← hp]
          exact (finProdFinEquiv.apply_symm_apply j).symm
        simpa [hj] using hv
      refine ⟨U, V,
        isOrthonormalFrame_of_partial_complete hpartialU hUunit,
        isOrthonormalFrame_of_partial_complete hpartialV hVunit,
        ?_, ?_, ?_⟩
      · intros
        rfl
      · intros
        rfl
      · intro z hz
        exact ⟨rfl, rfl⟩
  | succ n ih =>
      have ht : t < T * (N + 1) := by omega
      obtain ⟨U1, V1, hr, hpU1, hpV1, hz1, hu1⟩ :=
        exists_product_frame_reveal qX qY ht hcapX hcapY
          hpartialU hpartialV hzero hunit
      have hend1 : (t + 1) + n = T * (N + 1) := by omega
      obtain ⟨U2, V2, hU2, hV2, hprojX2, hprojY2, hembed2⟩ :=
        ih hend1 hpU1 hpV1 hz1 hu1
      have hproj1 := hr.project_eq hzero
      refine ⟨U2, V2, hU2, hV2, ?_, ?_, ?_⟩
      · intro X hX
        rw [hprojX2 X hX, hproj1.1 X hX]
      · intro Y hY
        rw [hprojY2 Y hY, hproj1.2 Y hY]
      · intro z hz
        have hz' : SupportedBelow (t + 1) z := hz.mono (by omega)
        have h2 := hembed2 z hz'
        have h1 := hr.embed_eq_of_supported hz
        exact ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

theorem exists_product_frame_completion
    {T N DX DY t : Nat}
    (qX : List (EVec DX)) (qY : List (EVec DY))
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    (ht : t ≤ T * (N + 1))
    (hcapX : T + qX.length < DX)
    (hcapY : T * N + qY.length < DY)
    (hpartialU : IsPartialOrthonormalFrame U)
    (hpartialV : IsPartialOrthonormalFrame V)
    (hzero : ProductFramesZeroFrom t U V)
    (hunit : ProductFramesUnitBelow t U V) :
    ∃ U' V',
      IsOrthonormalFrame U' ∧ IsOrthonormalFrame V' ∧
      (∀ X ∈ qX, frameProject U' X = frameProject U X) ∧
      (∀ Y ∈ qY, frameProject V' Y = frameProject V Y) ∧
      ∀ z : EVec (T * (N + 1)), SupportedBelow t z →
        frameEmbed U' (orderedPrimal z) = frameEmbed U (orderedPrimal z) ∧
        frameEmbed V' (orderedDual z) = frameEmbed V (orderedDual z) := by
  apply exists_product_frame_completion_aux qX qY
    (n := T * (N + 1) - t)
  · omega
  · exact hcapX
  · exact hcapY
  · exact hpartialU
  · exact hpartialV
  · exact hzero
  · exact hunit

theorem frameEmbed_neg {m D : Nat} (U : Fin m → EVec D) (g : EVec m) :
    frameEmbed U (-g) = -frameEmbed U g := by
  funext k
  unfold frameEmbed
  simp only [Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem firstOrderRecord_rotated_eq_of_reveal
    {T N DX DY : Nat}
    {F : EVec T → EVec (T * N) → ℝ}
    {gradX : EVec T → EVec (T * N) → EVec T}
    {gradY : EVec T → EVec (T * N) → EVec (T * N)}
    {k : Fin (T * (N + 1))}
    {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    {U' : Fin T → EVec DX} {V' : Fin (T * N) → EVec DY}
    (hr : ProductFrameReveal k qX qY U V U' V')
    (hzero : ProductFramesZeroFrom k.1 U V)
    (hchain : IsFirstOrderZeroChain
      (orderedSaddleFieldOf gradX gradY))
    {r : Nat} (hrk : r < k.1)
    {X : EVec DX} {Y : EVec DY} (hX : X ∈ qX) (hY : Y ∈ qY)
    (hsupp : SupportedBelow r
      (orderedJoint (frameProject U X) (frameProject V Y))) :
    firstOrderRecord (rotatedF U' V' F)
        (rotatedGradX U' V' gradX) (rotatedGradY U' V' gradY) (X, Y) =
      firstOrderRecord (rotatedF U V F)
        (rotatedGradX U V gradX) (rotatedGradY U V gradY) (X, Y) := by
  have hp := hr.project_eq hzero
  have hpX := hp.1 X hX
  have hpY := hp.2 Y hY
  let z := orderedJoint (frameProject U X) (frameProject V Y)
  have hresponse : SupportedBelow (r + 1)
      (orderedSaddleFieldOf gradX gradY z) :=
    hchain r z hsupp
  have hresponse' : SupportedBelow k.1
      (orderedSaddleFieldOf gradX gradY z) := by
    exact hresponse.mono (by omega)
  have he := hr.embed_eq_of_supported hresponse'
  have heX : frameEmbed U'
      (gradX (frameProject U X) (frameProject V Y)) =
      frameEmbed U
        (gradX (frameProject U X) (frameProject V Y)) := by
    simpa [z, orderedPrimal_orderedSaddleFieldOf,
      orderedPrimal_orderedJoint, orderedDual_orderedJoint] using he.1
  have heYneg : frameEmbed V'
      (-gradY (frameProject U X) (frameProject V Y)) =
      frameEmbed V
        (-gradY (frameProject U X) (frameProject V Y)) := by
    simpa [z, orderedDual_orderedSaddleFieldOf,
      orderedPrimal_orderedJoint, orderedDual_orderedJoint] using he.2
  have heY : frameEmbed V'
      (gradY (frameProject U X) (frameProject V Y)) =
      frameEmbed V
        (gradY (frameProject U X) (frameProject V Y)) := by
    rw [frameEmbed_neg, frameEmbed_neg] at heYneg
    exact neg_injective heYneg
  simp [firstOrderRecord, rotatedF, rotatedGradX, rotatedGradY,
    hpX, hpY, heX, heY]

def CausalExtension {DX DY : Nat} (A : DeterministicFOBlackBox DX DY) :
    List (FirstOrderRecord DX DY) → List (FirstOrderRecord DX DY) → Prop
  | _, [] => True
  | pre, r :: rs =>
      (r.queryX, r.queryY) = A.nextQuery pre ∧
        CausalExtension A (pre ++ [r]) rs

def IsCausalHistory {DX DY : Nat} (A : DeterministicFOBlackBox DX DY)
    (hist : List (FirstOrderRecord DX DY)) : Prop :=
  CausalExtension A [] hist

theorem CausalExtension.snoc {DX DY : Nat}
    {A : DeterministicFOBlackBox DX DY}
    {pre hist : List (FirstOrderRecord DX DY)}
    (hcausal : CausalExtension A pre hist)
    (r : FirstOrderRecord DX DY)
    (hq : (r.queryX, r.queryY) = A.nextQuery (pre ++ hist)) :
    CausalExtension A pre (hist ++ [r]) := by
  induction hist generalizing pre with
  | nil =>
      simpa [CausalExtension] using hq
  | cons a hist ih =>
      simp only [CausalExtension] at hcausal ⊢
      refine ⟨hcausal.1, ?_⟩
      apply ih hcausal.2
      simpa [List.append_assoc] using hq

def ResistingFits {T N DX DY : Nat}
    (F : EVec T → EVec (T * N) → ℝ)
    (gradX : EVec T → EVec (T * N) → EVec T)
    (gradY : EVec T → EVec (T * N) → EVec (T * N))
    (U : Fin T → EVec DX) (V : Fin (T * N) → EVec DY) :
    Nat → List (FirstOrderRecord DX DY) → Prop
  | _, [] => True
  | s, r :: rs =>
      r = firstOrderRecord (rotatedF U V F)
        (rotatedGradX U V gradX) (rotatedGradY U V gradY)
        (r.queryX, r.queryY) ∧
      SupportedBelow s
        (orderedJoint (frameProject U r.queryX) (frameProject V r.queryY)) ∧
      ResistingFits F gradX gradY U V (s + 1) rs

theorem ResistingFits.snoc {T N DX DY : Nat}
    {F : EVec T → EVec (T * N) → ℝ}
    {gradX : EVec T → EVec (T * N) → EVec T}
    {gradY : EVec T → EVec (T * N) → EVec (T * N)}
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    {s : Nat} {hist : List (FirstOrderRecord DX DY)}
    (hfits : ResistingFits F gradX gradY U V s hist)
    (r : FirstOrderRecord DX DY)
    (hrecord : r = firstOrderRecord (rotatedF U V F)
      (rotatedGradX U V gradX) (rotatedGradY U V gradY)
      (r.queryX, r.queryY))
    (hsupp : SupportedBelow (s + hist.length)
      (orderedJoint (frameProject U r.queryX) (frameProject V r.queryY))) :
    ResistingFits F gradX gradY U V s (hist ++ [r]) := by
  induction hist generalizing s with
  | nil =>
      simpa [ResistingFits] using And.intro hrecord (And.intro hsupp True.intro)
  | cons a hist ih =>
      simp only [ResistingFits] at hfits ⊢
      refine ⟨hfits.1, hfits.2.1, ?_⟩
      apply ih hfits.2.2
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsupp

theorem ResistingFits.of_reveal {T N DX DY : Nat}
    {F : EVec T → EVec (T * N) → ℝ}
    {gradX : EVec T → EVec (T * N) → EVec T}
    {gradY : EVec T → EVec (T * N) → EVec (T * N)}
    {k : Fin (T * (N + 1))}
    {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    {U' : Fin T → EVec DX} {V' : Fin (T * N) → EVec DY}
    (hr : ProductFrameReveal k qX qY U V U' V')
    (hzero : ProductFramesZeroFrom k.1 U V)
    (hchain : IsFirstOrderZeroChain (orderedSaddleFieldOf gradX gradY))
    {s : Nat} {hist : List (FirstOrderRecord DX DY)}
    (hend : s + hist.length = k.1)
    (hmemX : ∀ r ∈ hist, r.queryX ∈ qX)
    (hmemY : ∀ r ∈ hist, r.queryY ∈ qY)
    (hfits : ResistingFits F gradX gradY U V s hist) :
    ResistingFits F gradX gradY U' V' s hist := by
  induction hist generalizing s with
  | nil => trivial
  | cons a hist ih =>
      simp only [ResistingFits] at hfits ⊢
      have hsk : s < k.1 := by simp at hend; omega
      have haX : a.queryX ∈ qX := hmemX a (by simp)
      have haY : a.queryY ∈ qY := hmemY a (by simp)
      have hstable := firstOrderRecord_rotated_eq_of_reveal
        (F := F) hr hzero hchain hsk haX haY hfits.2.1
      have hp := hr.project_eq hzero
      refine ⟨hfits.1.trans hstable.symm, ?_, ?_⟩
      · rw [hp.1 a.queryX haX, hp.2 a.queryY haY]
        exact hfits.2.1
      · apply ih (s := s + 1)
        · simp at hend ⊢
          omega
        · intro r hrmem
          exact hmemX r (by simp [hrmem])
        · intro r hrmem
          exact hmemY r (by simp [hrmem])
        · exact hfits.2.2

/-- Online part of the resisting-oracle construction.  After `t` calls the
partial product frame contains exactly the first `t` ordered directions, and
the stored history is both causal for the arbitrary deterministic method and
an exact first-order transcript for that partial frame. -/
theorem exists_partial_resisting_state
    {T N DX DY K : Nat}
    (A : DeterministicFOBlackBox DX DY)
    (F : EVec T → EVec (T * N) → ℝ)
    (gradX : EVec T → EVec (T * N) → EVec T)
    (gradY : EVec T → EVec (T * N) → EVec (T * N))
    (hchain : IsFirstOrderZeroChain (orderedSaddleFieldOf gradX gradY))
    (hKM : K < T * (N + 1))
    (hcapX : T + (K + 1) < DX)
    (hcapY : T * N + (K + 1) < DY) :
    ∀ t ≤ K, ∃ U : Fin T → EVec DX, ∃ V : Fin (T * N) → EVec DY,
      ∃ hist : List (FirstOrderRecord DX DY),
      hist.length = t ∧
      IsCausalHistory A hist ∧
      IsPartialOrthonormalFrame U ∧
      IsPartialOrthonormalFrame V ∧
      ProductFramesZeroFrom t U V ∧
      ProductFramesUnitBelow t U V ∧
      ResistingFits F gradX gradY U V 0 hist := by
  intro t htK
  induction t with
  | zero =>
      refine ⟨0, 0, [], rfl, ?_,
        isPartialOrthonormalFrame_zero,
        isPartialOrthonormalFrame_zero, ?_, ?_, ?_⟩
      · simp [IsCausalHistory, CausalExtension]
      · intro k hk
        simp
      · intro k hk
        omega
      · simp [ResistingFits]
  | succ t ih =>
      have htK' : t ≤ K := by omega
      obtain ⟨U, V, hist, hlen, hcausal, hpU, hpV, hz, hu, hfits⟩ :=
        ih htK'
      let q := A.nextQuery hist
      let qX : List (EVec DX) := hist.map FirstOrderRecord.queryX ++ [q.1]
      let qY : List (EVec DY) := hist.map FirstOrderRecord.queryY ++ [q.2]
      have htM : t < T * (N + 1) := by omega
      have hcapXt : T + qX.length < DX := by
        simp [qX, hlen]
        omega
      have hcapYt : T * N + qY.length < DY := by
        simp [qY, hlen]
        omega
      obtain ⟨U1, V1, hr, hpU1, hpV1, hz1, hu1⟩ :=
        exists_product_frame_reveal qX qY htM hcapXt hcapYt hpU hpV hz hu
      have hmemX : ∀ r ∈ hist, r.queryX ∈ qX := by
        intro r hrmem
        unfold qX
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨r, hrmem, rfl⟩
      have hmemY : ∀ r ∈ hist, r.queryY ∈ qY := by
        intro r hrmem
        unfold qY
        apply List.mem_append_left
        exact List.mem_map.mpr ⟨r, hrmem, rfl⟩
      have hfits1 : ResistingFits F gradX gradY U1 V1 0 hist := by
        apply hfits.of_reveal hr hz hchain
        · simp [hlen]
        · exact hmemX
        · exact hmemY
      have hqX : q.1 ∈ qX := by simp [qX]
      have hqY : q.2 ∈ qY := by simp [qY]
      have hproj := hr.project_eq hz
      have hqsuppOld : SupportedBelow t
          (orderedJoint (frameProject U q.1) (frameProject V q.2)) :=
        supportedBelow_orderedProjection_of_zeroFrom hz q.1 q.2
      have hqsupp : SupportedBelow t
          (orderedJoint (frameProject U1 q.1) (frameProject V1 q.2)) := by
        rw [hproj.1 q.1 hqX, hproj.2 q.2 hqY]
        exact hqsuppOld
      let rnew : FirstOrderRecord DX DY :=
        firstOrderRecord (rotatedF U1 V1 F)
          (rotatedGradX U1 V1 gradX) (rotatedGradY U1 V1 gradY) q
      have hrquery : (rnew.queryX, rnew.queryY) = q := by rfl
      have hfitsNew : ResistingFits F gradX gradY U1 V1 0
          (hist ++ [rnew]) := by
        apply hfits1.snoc rnew
        · rfl
        · simpa [hlen, rnew, firstOrderRecord] using hqsupp
      have hcausalNew : IsCausalHistory A (hist ++ [rnew]) := by
        unfold IsCausalHistory at hcausal ⊢
        apply hcausal.snoc rnew
        simp [q, hrquery]
      refine ⟨U1, V1, hist ++ [rnew], ?_, hcausalNew,
        hpU1, hpV1, hz1, hu1, hfitsNew⟩
      simp [hlen]

theorem firstOrderRecord_rotated_eq_of_completion
    {T N DX DY K r : Nat}
    {F : EVec T → EVec (T * N) → ℝ}
    {gradX : EVec T → EVec (T * N) → EVec T}
    {gradY : EVec T → EVec (T * N) → EVec (T * N)}
    {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    {U' : Fin T → EVec DX} {V' : Fin (T * N) → EVec DY}
    (hprojX : ∀ X ∈ qX, frameProject U' X = frameProject U X)
    (hprojY : ∀ Y ∈ qY, frameProject V' Y = frameProject V Y)
    (hembed : ∀ z : EVec (T * (N + 1)), SupportedBelow K z →
      frameEmbed U' (orderedPrimal z) = frameEmbed U (orderedPrimal z) ∧
      frameEmbed V' (orderedDual z) = frameEmbed V (orderedDual z))
    (hchain : IsFirstOrderZeroChain (orderedSaddleFieldOf gradX gradY))
    (hrK : r < K) {X : EVec DX} {Y : EVec DY}
    (hX : X ∈ qX) (hY : Y ∈ qY)
    (hsupp : SupportedBelow r
      (orderedJoint (frameProject U X) (frameProject V Y))) :
    firstOrderRecord (rotatedF U' V' F)
        (rotatedGradX U' V' gradX) (rotatedGradY U' V' gradY) (X, Y) =
      firstOrderRecord (rotatedF U V F)
        (rotatedGradX U V gradX) (rotatedGradY U V gradY) (X, Y) := by
  have hpX := hprojX X hX
  have hpY := hprojY Y hY
  let z := orderedJoint (frameProject U X) (frameProject V Y)
  have hresp : SupportedBelow (r + 1)
      (orderedSaddleFieldOf gradX gradY z) := hchain r z hsupp
  have hrespK : SupportedBelow K (orderedSaddleFieldOf gradX gradY z) :=
    hresp.mono (by omega)
  have he := hembed _ hrespK
  have heX : frameEmbed U'
      (gradX (frameProject U X) (frameProject V Y)) =
      frameEmbed U (gradX (frameProject U X) (frameProject V Y)) := by
    simpa [z, orderedPrimal_orderedSaddleFieldOf,
      orderedPrimal_orderedJoint, orderedDual_orderedJoint] using he.1
  have heYneg : frameEmbed V'
      (-gradY (frameProject U X) (frameProject V Y)) =
      frameEmbed V (-gradY (frameProject U X) (frameProject V Y)) := by
    simpa [z, orderedDual_orderedSaddleFieldOf,
      orderedPrimal_orderedJoint, orderedDual_orderedJoint] using he.2
  have heY : frameEmbed V'
      (gradY (frameProject U X) (frameProject V Y)) =
      frameEmbed V (gradY (frameProject U X) (frameProject V Y)) := by
    rw [frameEmbed_neg, frameEmbed_neg] at heYneg
    exact neg_injective heYneg
  simp [firstOrderRecord, rotatedF, rotatedGradX, rotatedGradY,
    hpX, hpY, heX, heY]

theorem ResistingFits.of_completion {T N DX DY K : Nat}
    {F : EVec T → EVec (T * N) → ℝ}
    {gradX : EVec T → EVec (T * N) → EVec T}
    {gradY : EVec T → EVec (T * N) → EVec (T * N)}
    {qX : List (EVec DX)} {qY : List (EVec DY)}
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    {U' : Fin T → EVec DX} {V' : Fin (T * N) → EVec DY}
    (hprojX : ∀ X ∈ qX, frameProject U' X = frameProject U X)
    (hprojY : ∀ Y ∈ qY, frameProject V' Y = frameProject V Y)
    (hembed : ∀ z : EVec (T * (N + 1)), SupportedBelow K z →
      frameEmbed U' (orderedPrimal z) = frameEmbed U (orderedPrimal z) ∧
      frameEmbed V' (orderedDual z) = frameEmbed V (orderedDual z))
    (hchain : IsFirstOrderZeroChain (orderedSaddleFieldOf gradX gradY))
    {s : Nat} {hist : List (FirstOrderRecord DX DY)}
    (hend : s + hist.length = K)
    (hmemX : ∀ a ∈ hist, a.queryX ∈ qX)
    (hmemY : ∀ a ∈ hist, a.queryY ∈ qY)
    (hfits : ResistingFits F gradX gradY U V s hist) :
    ResistingFits F gradX gradY U' V' s hist := by
  induction hist generalizing s with
  | nil => trivial
  | cons a hist ih =>
      simp only [ResistingFits] at hfits ⊢
      have hsK : s < K := by simp at hend; omega
      have haX := hmemX a (by simp)
      have haY := hmemY a (by simp)
      have hstable := firstOrderRecord_rotated_eq_of_completion
        (F := F) hprojX hprojY hembed hchain hsK haX haY hfits.2.1
      refine ⟨hfits.1.trans hstable.symm, ?_, ?_⟩
      · rw [hprojX a.queryX haX, hprojY a.queryY haY]
        exact hfits.2.1
      · apply ih (s := s + 1)
        · simp at hend ⊢
          omega
        · intro b hb
          exact hmemX b (by simp [hb])
        · intro b hb
          exact hmemY b (by simp [hb])
        · exact hfits.2.2

theorem ResistingFits.forall_records {T N DX DY s : Nat}
    {F : EVec T → EVec (T * N) → ℝ}
    {gradX : EVec T → EVec (T * N) → EVec T}
    {gradY : EVec T → EVec (T * N) → EVec (T * N)}
    {U : Fin T → EVec DX} {V : Fin (T * N) → EVec DY}
    {hist : List (FirstOrderRecord DX DY)}
    (hfits : ResistingFits F gradX gradY U V s hist) :
    ∀ a ∈ hist, a = firstOrderRecord (rotatedF U V F)
      (rotatedGradX U V gradX) (rotatedGradY U V gradY)
      (a.queryX, a.queryY) := by
  induction hist generalizing s with
  | nil => simp
  | cons a hist ih =>
      simp only [ResistingFits] at hfits
      intro b hb
      simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact hfits.1
      · exact ih hfits.2.2 b hb

theorem causal_actual_history_eq_run {DX DY : Nat}
    (A : DeterministicFOBlackBox DX DY)
    (F : EVec DX → EVec DY → ℝ)
    (gradX : EVec DX → EVec DY → EVec DX)
    (gradY : EVec DX → EVec DY → EVec DY)
    {hist : List (FirstOrderRecord DX DY)}
    (hcausal : IsCausalHistory A hist)
    (hactual : ∀ a ∈ hist,
      a = firstOrderRecord F gradX gradY (a.queryX, a.queryY)) :
    hist = runHistory A F gradX gradY hist.length := by
  have helper : ∀ (pre rest : List (FirstOrderRecord DX DY)),
      pre = runHistory A F gradX gradY pre.length →
      CausalExtension A pre rest →
      (∀ a ∈ rest, a = firstOrderRecord F gradX gradY
        (a.queryX, a.queryY)) →
      pre ++ rest = runHistory A F gradX gradY (pre.length + rest.length) := by
    intro pre rest
    induction rest generalizing pre with
    | nil =>
        intro hpre hc ha
        simpa using hpre
    | cons a rest ih =>
        intro hpre hc ha
        simp only [CausalExtension] at hc
        have harec := ha a (by simp)
        have hpre1 : pre ++ [a] =
            runHistory A F gradX gradY (pre ++ [a]).length := by
          rw [show (pre ++ [a]).length = pre.length + 1 by simp,
            runHistory, ← hpre]
          congr 2
          rw [← hc.1]
          exact harec
        have htail : ∀ b ∈ rest,
            b = firstOrderRecord F gradX gradY (b.queryX, b.queryY) := by
          intro b hb
          exact ha b (by simp [hb])
        have hh := ih (pre := pre ++ [a]) hpre1 hc.2 htail
        simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hh
  have h0 : ([] : List (FirstOrderRecord DX DY)) =
      runHistory A F gradX gradY 0 := rfl
  have hh := helper [] hist h0 hcausal hactual
  simpa using hh

/-- Standard finite-horizon hidden-basis theorem for an arbitrary
deterministic first-order method.  The final primal output has zero terminal
base coordinate.  The displayed ambient bounds are conservative explicit
"sufficiently high dimensional" bounds; the sharper list-completion lemma in
`HiddenBasisLinearAlgebra` proves that only `K+1` spare dimensions are needed. -/
theorem finite_horizon_hidden_basis
    {T N DX DY K : Nat}
    (A : DeterministicFOBlackBox DX DY)
    (F : EVec T → EVec (T * N) → ℝ)
    (gradX : EVec T → EVec (T * N) → EVec T)
    (gradY : EVec T → EVec (T * N) → EVec (T * N))
    (hchain : IsFirstOrderZeroChain (orderedSaddleFieldOf gradX gradY))
    (hKM : K < T * (N + 1))
    (hcapX : T + (K + 1) < DX)
    (hcapY : T * N + (K + 1) < DY) :
    ∃ U : Fin T → EVec DX, ∃ V : Fin (T * N) → EVec DY,
      IsOrthonormalFrame U ∧ IsOrthonormalFrame V ∧
      let hist := runHistory A (rotatedF U V F)
        (rotatedGradX U V gradX) (rotatedGradY U V gradY) K
      ∃ i : Fin T, i.1 = T - 1 ∧ frameProject U (A.output hist) i = 0 := by
  obtain ⟨Up, Vp, hist, hlen, hcausal, hpU, hpV, hz, hu, hfits⟩ :=
    exists_partial_resisting_state A F gradX gradY hchain hKM hcapX hcapY K le_rfl
  have hT : 0 < T := by
    by_contra h
    have : T = 0 := Nat.eq_zero_of_not_pos h
    subst T
    simp at hKM
  let xout : EVec DX := A.output hist
  let qX : List (EVec DX) := hist.map FirstOrderRecord.queryX ++ [xout]
  let qY : List (EVec DY) := hist.map FirstOrderRecord.queryY
  have hcompX : T + qX.length < DX := by
    simp [qX, hlen]
    omega
  have hcompY : T * N + qY.length < DY := by
    simp [qY, hlen]
    omega
  obtain ⟨U, V, hU, hV, hprojX, hprojY, hembed⟩ :=
    exists_product_frame_completion qX qY (by omega) hcompX hcompY
      hpU hpV hz hu
  have hmemX : ∀ a ∈ hist, a.queryX ∈ qX := by
    intro a ha
    unfold qX
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hmemY : ∀ a ∈ hist, a.queryY ∈ qY := by
    intro a ha
    unfold qY
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hfitsFinal : ResistingFits F gradX gradY U V 0 hist := by
    apply hfits.of_completion hprojX hprojY hembed hchain
    · simp [hlen]
    · exact hmemX
    · exact hmemY
  have hactual := hfitsFinal.forall_records
  have hrun0 := causal_actual_history_eq_run A (rotatedF U V F)
    (rotatedGradX U V gradX) (rotatedGradY U V gradY)
    hcausal hactual
  have hrun : hist = runHistory A (rotatedF U V F)
      (rotatedGradX U V gradX) (rotatedGradY U V gradY) K := by
    simpa [hlen] using hrun0
  let ilast : Fin T := carmonLastIndex T hT
  let klast : Fin (T * (N + 1)) := finProdFinEquiv (ilast, Fin.last N)
  have hKlast : K ≤ klast.1 := by
    unfold klast
    rw [finProdFinEquiv_val]
    unfold ilast carmonLastIndex
    simp only [Fin.val_last]
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hT)
    rw [hm] at hKM ⊢
    simp only [Nat.succ_sub_one, Nat.succ_mul] at hKM ⊢
    omega
  have hUpLast : Up ilast = 0 := by
    have hh := hz klast hKlast
    simp [klast] at hh
    exact hh
  have hxmem : xout ∈ qX := by simp [qX]
  have houtProj := congrFun (hprojX xout hxmem) ilast
  have hterminal : frameProject U xout ilast = 0 := by
    rw [houtProj]
    unfold frameProject
    rw [hUpLast]
    unfold evecDotValue
    simp
  refine ⟨U, V, hU, hV, ilast, rfl, ?_⟩
  rw [← hrun]
  exact hterminal
end

end NCPLVerification
