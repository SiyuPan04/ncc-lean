import NCC.Extensions.NCSCQueriedOS

/-! The actual program is independent of the objective on fixed domains.
Only genuine oracle replies, not the class proof used in its construction,
can carry objective-dependent information into the executed algorithm. -/
namespace NCC.Extensions.NCSCUniform
noncomputable section
open NCCLowerBoundVerification NCCLowerBoundVerification.Upper Oracle
open NCC.Extensions.NCSC
set_option maxHeartbeats 3000000

variable {m n : ℕ} {ell mu Delta : ℝ} {P Q : NCCInstance m n}

theorem initializer_same_domains (hP : NCSCClass ell mu Delta P) (hQ : NCSCClass ell mu Delta Q)
    (hX : P.X = Q.X) (hY : P.Y = Q.Y) :
    HEq (NCSCTheorem.initializer hP) (NCSCTheorem.initializer hQ) := by
  cases P with
  | mk X Y f gx gy x0 =>
    cases Q with
    | mk X' Y' f' gx' gy' x0' =>
      dsimp only at hX hY
      subst X'
      subst Y'
      rfl

theorem run_same_domains (hP : NCSCClass ell mu Delta P) (hQ : NCSCClass ell mu Delta Q)
    (hX : P.X = Q.X) (hY : P.Y = Q.Y) (eps rho : ℝ) :
    HEq (NCSCTheorem.run hP eps rho) (NCSCTheorem.run hQ eps rho) := by
  cases P with
  | mk X Y f gx gy x0 =>
    cases Q with
    | mk X' Y' f' gx' gy' x0' =>
      dsimp only at hX hY
      subst X'
      subst Y'
      rfl

theorem queriedRun_same_domains (hP : NCSCClass ell mu Delta P) (hQ : NCSCClass ell mu Delta Q)
    (hX : P.X = Q.X) (hY : P.Y = Q.Y) (eps rho : ℝ) :
    HEq (NCSCQueriedOS.queriedRun hP eps rho) (NCSCQueriedOS.queriedRun hQ eps rho) := by
  cases P with
  | mk X Y f gx gy x0 =>
    cases Q with
    | mk X' Y' f' gx' gy' x0' =>
      dsimp only at hX hY
      subst X'
      subst Y'
      rfl

end
end NCC.Extensions.NCSCUniform
