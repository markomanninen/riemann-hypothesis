module

public import Mathlib
public import Formalism.LocalRingCardinality.DataKerI

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory.PadicPlaceExt

theorem exists_lam {p : ℕ} [Fact p.Prime] {L : Type} [Field L] [NumberField L] (e : L →+* ℂ) (φ : L →+* ℂ_[p]) :
    ∃ lam : (algebraicClosure ℚ ℂ) →+* ℂ_[p], ∀ z : L, φ z = lamV lam (e z) := by
  have hmem : ∀ z : L, e z ∈ algebraicClosure ℚ ℂ := fun z =>
    mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) z).algHom e.toRatAlgHom)
  let e' : L →+* algebraicClosure ℚ ℂ := e.codRestrict (algebraicClosure ℚ ℂ) hmem
  let : Algebra L (algebraicClosure ℚ ℂ) := e'.toAlgebra
  let : Algebra L ℂ_[p] := φ.toAlgebra
  have : IsScalarTower ℚ L (algebraicClosure ℚ ℂ) :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have : Algebra.IsAlgebraic L (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  let f : algebraicClosure ℚ ℂ →ₐ[L] ℂ_[p] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨f.toRingHom, fun z => ?_⟩
  rw [lamV, dite_eq_left (hmem z)]
  exact (f.commutes z).symm

end GlobalTheory.PadicPlaceExt
