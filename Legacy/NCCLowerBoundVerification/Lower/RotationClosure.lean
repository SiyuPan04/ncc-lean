import NCCLowerBoundVerification.Lower.OrthogonalCovariance
import NCPLVerification.RotatedClass

/-!
# Closure of the bounded-dual NC--C class under hidden orthogonal frames

This is `lem:rotation-closure`.  Both visible domains are fixed (`Set.univ`
and the Euclidean diameter ball), so the frames are present only in the
objective and its genuine gradients.
-/

namespace NCCLowerBoundVerification

noncomputable section

open NCPLVerification

def rotatedNCCInstance {m n M N : Nat} (D : ℝ)
    (U : Fin m → EVec M) (V : Fin n → EVec N)
    (P : NCCInstance m n) : NCCInstance M N where
  X := Set.univ
  Y := diameterBall N D
  f := rotatedF U V P.f
  gradX := rotatedGradX U V P.gradX
  gradY := rotatedGradY U V P.gradY
  x0 := 0

theorem jointSq_frameEmbed_eq {m n M N : Nat}
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    (x : EVec m) (y : EVec n) :
    jointSq (frameEmbed U x) (frameEmbed V y) = jointSq x y := by
  change NCPLVerification.jointSq (frameEmbed U x) (frameEmbed V y) =
    NCPLVerification.jointSq x y
  exact NCPLVerification.jointSq_frameEmbed hU hV x y

theorem jointSq_frameProject_le_eq {m n M N : Nat}
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    (X : EVec M) (Y : EVec N) :
    jointSq (frameProject U X) (frameProject V Y) ≤ jointSq X Y := by
  change NCPLVerification.jointSq (frameProject U X) (frameProject V Y) ≤
    NCPLVerification.jointSq X Y
  exact NCPLVerification.jointSq_frameProject_le hU hV X Y

theorem rotatedValue_eq {m n M N : Nat}
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hV : IsOrthonormalFrame V) {P : NCCInstance m n} {D : ℝ}
    (hY : P.Y = diameterBall n D)
    (hmax : ∀ x, ∃ y, IsMaximizerOn P.Y P.f x y)
    (X : EVec M) :
    ValueOn (diameterBall N D) (rotatedF U V P.f) X =
      ValueOn P.Y P.f (frameProject U X) := by
  rw [hY]
  exact liftedValue_eq hV (by simpa [hY] using hmax (frameProject U X))

theorem range_rotatedValue_eq {m n M N : Nat}
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V)
    {P : NCCInstance m n} {D : ℝ}
    (hY : P.Y = diameterBall n D)
    (hmax : ∀ x, ∃ y, IsMaximizerOn P.Y P.f x y) :
    Set.range (ValueOn (diameterBall N D) (rotatedF U V P.f)) =
      Set.range (ValueOn P.Y P.f) := by
  ext z
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨frameProject U X, (rotatedValue_eq hV hY hmax X).symm⟩
  · rintro ⟨x, rfl⟩
    refine ⟨frameEmbed U x, ?_⟩
    rw [rotatedValue_eq hV hY hmax, frameProject_frameEmbed hU]

/-- `lem:rotation-closure`, for the symmetric domains used by the paper. -/
theorem IsNCCClass.rotate_symmetric {m n M N : Nat}
    {ell D Delta : ℝ} {P : NCCInstance m n}
    (hclass : IsNCCClass ell D Delta P)
    (hX : P.X = Set.univ) (hY : P.Y = diameterBall n D)
    (hx0 : P.x0 = 0)
    {U : Fin m → EVec M} {V : Fin n → EVec N}
    (hU : IsOrthonormalFrame U) (hV : IsOrthonormalFrame V) :
    IsNCCClass ell D Delta (rotatedNCCInstance D U V P) := by
  refine
    { ell_pos := hclass.ell_pos
      D_pos := hclass.D_pos
      Delta_pos := hclass.Delta_pos
      x0_mem := Set.mem_univ _
      X_nonempty := Set.univ_nonempty
      X_closed := isClosed_univ
      X_convex := convex_univ
      Y_nonempty := diameterBall_nonempty N D hclass.D_pos.le
      Y_closed := diameterBall_closed N D
      Y_convex := diameterBall_convex N D
      gradient_representation := ?_
      jointly_smooth := ?_
      dual_concave := ?_
      maximum_attained := ?_
      value_bddBelow := ?_
      initial_gap := ?_
      dual_diameter := ?_ }
  · exact rotatedF_representsJointGradient
      hclass.gradient_representation U V
  · intro X _ Y hYmem X' _ Y' hY'mem
    have hx : frameProject U X ∈ P.X := by rw [hX]; simp
    have hx' : frameProject U X' ∈ P.X := by rw [hX]; simp
    have hy : frameProject V Y ∈ P.Y := by
      rw [hY]
      exact frameProject_mem_diameterBall hV hYmem
    have hy' : frameProject V Y' ∈ P.Y := by
      rw [hY]
      exact frameProject_mem_diameterBall hV hY'mem
    have hbase := hclass.jointly_smooth _ hx _ hy _ hx' _ hy'
    have hin : jointSq
        (frameProject U X - frameProject U X')
        (frameProject V Y - frameProject V Y') ≤
        jointSq (X - X') (Y - Y') := by
      rw [frameProject_sub U X X', frameProject_sub V Y Y']
      exact jointSq_frameProject_le_eq hU hV (X - X') (Y - Y')
    have hscaled := mul_le_mul_of_nonneg_left hin (sq_nonneg ell)
    unfold rotatedNCCInstance rotatedGradX rotatedGradY
    rw [frameEmbed_sub, frameEmbed_sub, jointSq_frameEmbed_eq hU hV]
    exact hbase.trans hscaled
  · intro X _
    have hx : frameProject U X ∈ P.X := by rw [hX]; simp
    have hconc := hclass.dual_concave _ hx
    have hcomp := hconc.comp_linearMap (frameProjectCLM V).toLinearMap
    apply hcomp.subset
    · intro Y hYmem
      change frameProject V Y ∈ P.Y
      rw [hY]
      exact frameProject_mem_diameterBall hV hYmem
    · exact diameterBall_convex N D
  · intro X _
    have hx : frameProject U X ∈ P.X := by rw [hX]; simp
    obtain ⟨y, hy⟩ := hclass.maximum_attained _ hx
    refine ⟨frameEmbed V y, ?_⟩
    change IsMaximizerOn (diameterBall N D) (liftedSaddle U V P.f) X
      (frameEmbed V y)
    exact liftedSaddle_maximizer hV (by simpa [hY] using hy)
  · have hbase : BddBelow (Set.range (ValueOn P.Y P.f)) := by
      simpa [hX] using hclass.value_bddBelow
    have hrot : BddBelow
        (Set.range (ValueOn (diameterBall N D) (rotatedF U V P.f))) := by
      rw [range_rotatedValue_eq hU hV hY (fun x ↦
        hclass.maximum_attained x (by rw [hX]; simp))]
      exact hbase
    simpa [rotatedNCCInstance] using hrot
  · have hbase :
        ValueOn P.Y P.f 0 - sInf (Set.range (ValueOn P.Y P.f)) ≤ Delta := by
      simpa [hX, hx0] using hclass.initial_gap
    have hrange := range_rotatedValue_eq hU hV hY (fun x ↦
      hclass.maximum_attained x (by rw [hX]; simp))
    change ValueOn (diameterBall N D) (rotatedF U V P.f) 0 -
      sInf (ValueOn (diameterBall N D) (rotatedF U V P.f) '' Set.univ) ≤ Delta
    rw [Set.image_univ, rotatedValue_eq hV hY (fun x ↦
      hclass.maximum_attained x (by rw [hX]; simp)), frameProject_zero, hrange]
    exact hbase
  · intro Y hYmem Y' hY'mem
    exact diameterBall_vecSq_sub_le hclass.D_pos.le hYmem hY'mem

end

end NCCLowerBoundVerification
