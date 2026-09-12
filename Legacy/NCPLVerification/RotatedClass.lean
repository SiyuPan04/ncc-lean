import NCPLVerification.OrthogonalFrames

/-!
# Orthogonal lifting of NC--PL instances

This file implements the finite-dimensional rotation used in the resisting-
oracle argument.  A base instance is evaluated after orthogonal projection,
and its gradients are embedded back into the ambient spaces.  All constants
in `NCPLClass` are preserved exactly.
-/

namespace NCPLVerification

noncomputable section

def rotatedF {dx dy DX DY : Nat}
    (U : Fin dx → EVec DX) (V : Fin dy → EVec DY)
    (F : EVec dx → EVec dy → ℝ) (X : EVec DX) (Y : EVec DY) : ℝ :=
  F (frameProject U X) (frameProject V Y)

def rotatedGradX {dx dy DX DY : Nat}
    (U : Fin dx → EVec DX) (V : Fin dy → EVec DY)
    (gradX : EVec dx → EVec dy → EVec dx)
    (X : EVec DX) (Y : EVec DY) : EVec DX :=
  frameEmbed U (gradX (frameProject U X) (frameProject V Y))

def rotatedGradY {dx dy DX DY : Nat}
    (U : Fin dx → EVec DX) (V : Fin dy → EVec DY)
    (gradY : EVec dx → EVec dy → EVec dy)
    (X : EVec DX) (Y : EVec DY) : EVec DY :=
  frameEmbed V (gradY (frameProject U X) (frameProject V Y))

def frameProductProjectCLM {dx dy DX DY : Nat}
    (U : Fin dx → EVec DX) (V : Fin dy → EVec DY) :
    (EVec DX × EVec DY) →L[ℝ] (EVec dx × EVec dy) :=
  ((frameProjectCLM U).comp
      (ContinuousLinearMap.fst ℝ (EVec DX) (EVec DY))).prod
    ((frameProjectCLM V).comp
      (ContinuousLinearMap.snd ℝ (EVec DX) (EVec DY)))

@[simp] theorem frameProductProjectCLM_apply {dx dy DX DY : Nat}
    (U : Fin dx → EVec DX) (V : Fin dy → EVec DY)
    (p : EVec DX × EVec DY) :
    frameProductProjectCLM U V p =
      (frameProject U p.1, frameProject V p.2) := by
  rfl

theorem rotatedF_representsJointGradient {dx dy DX DY : Nat}
    {F : EVec dx → EVec dy → ℝ}
    {gradX : EVec dx → EVec dy → EVec dx}
    {gradY : EVec dx → EVec dy → EVec dy}
    (hrep : RepresentsJointGradient F gradX gradY)
    (U : Fin dx → EVec DX) (V : Fin dy → EVec DY) :
    RepresentsJointGradient (rotatedF U V F)
      (rotatedGradX U V gradX) (rotatedGradY U V gradY) := by
  constructor
  · intro p
    have hP : HasFDerivAt
        (fun q : EVec DX × EVec DY ↦
          (frameProject U q.1, frameProject V q.2))
        (frameProductProjectCLM U V) p :=
      (frameProductProjectCLM U V).hasFDerivAt
    have hB := (hrep.1.differentiableAt).hasFDerivAt.comp p hP
    change DifferentiableAt ℝ
      (Function.uncurry F ∘ fun q : EVec DX × EVec DY ↦
        (frameProject U q.1, frameProject V q.2)) p
    exact hB.differentiableAt
  · intro X Y hX hY
    let P : (EVec DX × EVec DY) →L[ℝ] (EVec dx × EVec dy) :=
      frameProductProjectCLM U V
    have hP : HasFDerivAt
        (fun q : EVec DX × EVec DY ↦
          (frameProject U q.1, frameProject V q.2)) P (X, Y) :=
      P.hasFDerivAt
    have hB : HasFDerivAt (Function.uncurry F)
        (fderiv ℝ (Function.uncurry F)
          (frameProject U X, frameProject V Y))
        (frameProject U X, frameProject V Y) :=
      (hrep.1 (frameProject U X, frameProject V Y)).hasFDerivAt
    have hc := hB.comp (X, Y) hP
    have hrot : HasFDerivAt
        (Function.uncurry (rotatedF U V F))
        ((fderiv ℝ (Function.uncurry F)
          (frameProject U X, frameProject V Y)).comp P) (X, Y) := by
      change HasFDerivAt
        (Function.uncurry F ∘ fun q : EVec DX × EVec DY ↦
          (frameProject U q.1, frameProject V q.2))
        ((fderiv ℝ (Function.uncurry F)
          (frameProject U X, frameProject V Y)).comp P) (X, Y)
      exact hc
    rw [hrot.fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    change (fderiv ℝ (Function.uncurry F)
      (frameProject U X, frameProject V Y))
        (frameProject U hX, frameProject V hY) = _
    rw [hrep.2 (frameProject U X) (frameProject V Y)
      (frameProject U hX) (frameProject V hY)]
    unfold rotatedGradX rotatedGradY
    change
      evecDotValue (gradX (frameProject U X) (frameProject V Y))
          (frameProject U hX) +
        evecDotValue (gradY (frameProject U X) (frameProject V Y))
          (frameProject V hY) =
      evecDotValue
          (frameEmbed U (gradX (frameProject U X) (frameProject V Y))) hX +
        evecDotValue
          (frameEmbed V (gradY (frameProject U X) (frameProject V Y))) hY
    rw [evecDotValue_frameEmbed_left, evecDotValue_frameEmbed_left]
    rfl

theorem jointSq_frameEmbed {dx dy DX DY : Nat}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    (x : EVec dx) (y : EVec dy) :
    jointSq (frameEmbed U x) (frameEmbed V y) = jointSq x y := by
  unfold jointSq
  rw [vecSq_frameEmbed hU, vecSq_frameEmbed hV]

theorem jointSq_frameProject_le {dx dy DX DY : Nat}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    (X : EVec DX) (Y : EVec DY) :
    jointSq (frameProject U X) (frameProject V Y) ≤ jointSq X Y := by
  unfold jointSq
  exact add_le_add (vecSq_frameProject_le hU X)
    (vecSq_frameProject_le hV Y)

theorem rotatedF_isJointlySmooth {dx dy DX DY : Nat} {L : ℝ}
    {gradX : EVec dx → EVec dy → EVec dx}
    {gradY : EVec dx → EVec dy → EVec dy}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    (hsmooth : IsJointlySmooth L gradX gradY) :
    IsJointlySmooth L (rotatedGradX U V gradX)
      (rotatedGradY U V gradY) := by
  intro X Y X' Y'
  let x := frameProject U X
  let x' := frameProject U X'
  let y := frameProject V Y
  let y' := frameProject V Y'
  have hbase := hsmooth x y x' y'
  have hin : jointSq (x - x') (y - y') ≤
      jointSq (X - X') (Y - Y') := by
    rw [frameProject_sub U X X', frameProject_sub V Y Y']
    exact jointSq_frameProject_le hU hV (X - X') (Y - Y')
  have hmul := mul_le_mul_of_nonneg_left hin (sq_nonneg L)
  unfold rotatedGradX rotatedGradY
  rw [frameEmbed_sub, frameEmbed_sub, jointSq_frameEmbed hU hV]
  exact hbase.trans hmul

theorem rotatedF_isMaximizer {dx dy DX DY : Nat}
    {F : EVec dx → EVec dy → ℝ}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hV : IsOrthonormalFrame V) {X : EVec DX} {y : EVec dy}
    (hy : IsMaximizer F (frameProject U X) y) :
    IsMaximizer (rotatedF U V F) X (frameEmbed V y) := by
  intro Y
  unfold rotatedF
  rw [frameProject_frameEmbed hV]
  exact hy (frameProject V Y)

theorem rotatedEnvelope_eq {dx dy DX DY : Nat}
    {F : EVec dx → EVec dy → ℝ}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hV : IsOrthonormalFrame V) (X : EVec DX) :
    Envelope (rotatedF U V F) X = Envelope F (frameProject U X) := by
  unfold Envelope
  congr 1
  ext z
  constructor
  · rintro ⟨Y, rfl⟩
    exact ⟨frameProject V Y, rfl⟩
  · rintro ⟨y, rfl⟩
    refine ⟨frameEmbed V y, ?_⟩
    simp [rotatedF, frameProject_frameEmbed hV]

theorem range_rotatedEnvelope_eq {dx dy DX DY : Nat}
    {F : EVec dx → EVec dy → ℝ}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V) :
    Set.range (Envelope (rotatedF U V F)) = Set.range (Envelope F) := by
  ext z
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨frameProject U X, (rotatedEnvelope_eq hV X).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨frameEmbed U x, ?_⟩
    rw [rotatedEnvelope_eq hV, frameProject_frameEmbed hU]

theorem NCPLClass.rotate {dx dy DX DY : Nat} {L mu Delta : ℝ}
    {F : EVec dx → EVec dy → ℝ}
    {gradX : EVec dx → EVec dy → EVec dx}
    {gradY : EVec dx → EVec dy → EVec dy}
    {U : Fin dx → EVec DX} {V : Fin dy → EVec DY}
    (hclass : NCPLClass L mu Delta F gradX gradY)
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V) :
    NCPLClass L mu Delta (rotatedF U V F)
      (rotatedGradX U V gradX) (rotatedGradY U V gradY) := by
  refine
    { L_nonneg := hclass.L_nonneg
      mu_nonneg := hclass.mu_nonneg
      Delta_nonneg := hclass.Delta_nonneg
      gradient_representation := rotatedF_representsJointGradient
        hclass.gradient_representation U V
      jointly_smooth := rotatedF_isJointlySmooth hU hV hclass.jointly_smooth
      maximum_attained := ?_
      maximization_PL := ?_
      envelope_bddBelow := ?_
      initial_gap := ?_ }
  · intro X
    obtain ⟨y, hy⟩ := hclass.maximum_attained (frameProject U X)
    exact ⟨frameEmbed V y, rotatedF_isMaximizer hV hy⟩
  · intro X Y
    rw [rotatedEnvelope_eq hV]
    unfold rotatedGradY rotatedF
    rw [vecSq_frameEmbed hV]
    exact hclass.maximization_PL (frameProject U X) (frameProject V Y)
  · rw [range_rotatedEnvelope_eq hU hV]
    exact hclass.envelope_bddBelow
  · rw [rotatedEnvelope_eq hV, frameProject_zero,
      range_rotatedEnvelope_eq hU hV]
    exact hclass.initial_gap

end

end NCPLVerification
