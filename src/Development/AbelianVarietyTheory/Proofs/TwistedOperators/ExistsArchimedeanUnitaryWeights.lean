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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeMemUnitary
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRealPointFockVectorPositiveDefiniteDet
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeightedAverageHaarLifted
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplittingHeckeCharExistsArchimedeanExponent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterInfinityExponentGroupLaws
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndexStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealUnitaryFockColumnActionSurjectiveStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

open scoped Matrix

namespace GlobalTheory.BottomRealAct

theorem substF_one_eq_colSub {ι : Type} {N n : ℕ} (M : ι → Matrix (Fin n) (Fin n) ℂ) :
    GlobalTheory.CompactHowe.substF (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) M = GlobalTheory.MinorFrame.colSub M := by
  refine MvPolynomial.algHom_ext fun v => ?_
  rw [GlobalTheory.CompactHowe.substF_X]
  simp only [GlobalTheory.MinorFrame.colSub, MvPolynomial.aeval_X]
  rw [Finset.sum_eq_single v.2.1]
  · simp only [Matrix.one_apply_eq, one_mul]
  · intro x _ hx
    simp only [Matrix.one_apply_ne hx, zero_mul, MvPolynomial.C_0, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem rightRegularAction_list_dLR_eq_append {G : Type*} [CommGroup G] (a x y e c : G) : a * x * e / (c * e) = a * y * e / (c * e) * (x * y⁻¹) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_inv]
  abel

end GlobalTheory.BottomRealAct
