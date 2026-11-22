module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

@[expose] public section

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pLiftEx :
    LiftEx := by
  unfold UpperTheory.Gal.W2.Seed.LiftEx
  intro E _ _ τ₀
  let sA : E →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra E (AlgebraicClosure ℚ) := sA.toRingHom.toAlgebra
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (sA.commutes x).symm)
  haveI hQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic E (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let iA : AlgebraicClosure ℚ →ₐ[E] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨sA.toRingHom, iA.toRingHom, fun x => ?_⟩
  exact iA.commutes x
