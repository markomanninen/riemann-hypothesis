module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAlgebraicStdCharHalfSymplecticRealPartZeroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemFrameLatticeIffIntegralCoords
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitPlaceUnitaryPointMemHeckeClosureStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitCharacterValueAlgebraic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitPlaceStabiliserVacuumStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomSplitHeckeVacuumStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitVacAlg

open GlobalTheory.MovedAlg

theorem isAlg_sqrt_inv (n : ℕ) : IsAlgebraic ℚ (((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹) := by
  have h : IsAlgebraic ℚ (((Real.sqrt (n : ℝ) : ℝ) : ℂ)) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C (n : ℚ), Polynomial.X_pow_sub_C_ne_zero (by norm_num) _, ?_⟩
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, eq_ratCast, Rat.cast_natCast]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
    simp
  rw [← mem_algebraicClosure_iff] at h ⊢
  exact inv_mem h

section Comb

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f₀ : WO S T → ℂ}

theorem isAlgComb_heis {u : WO S T} (hu : u.map (infPart D) = 0) : IsAlgComb ψ S T f₀ (heisO ψ S T u f₀) :=
  ⟨1, fun _ => 1, fun _ => u, fun _ => isAlgebraic_one, fun _ => hu, by simp⟩

theorem isAlgComb_sum (Δ : Finset (WO S T)) (hΔ : ∀ u ∈ Δ, u.map (infPart D) = 0) :
    IsAlgComb ψ S T f₀ (∑ u ∈ Δ, heisO ψ S T u f₀) := by
  classical
  induction Δ using Finset.induction_on with
  | empty => simpa using (IsAlgComb.zero : IsAlgComb ψ S T f₀ 0)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (isAlgComb_heis (hΔ a (Finset.mem_insert_self a s))).add
      (ih fun u hu => hΔ u (Finset.mem_insert_of_mem hu))

theorem isAlgComb_self : IsAlgComb ψ S T f₀ f₀ := by
  have := isAlgComb_heis (ψ := ψ) (f₀ := f₀) (u := (0 : WO S T)) (by simp)
  rwa [GlobalTheory.SplitScalar.heisO_zero ψ S T f₀] at this

end Comb


end GlobalTheory.SplitVacAlg

end
