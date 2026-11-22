module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitriangularOfRationalMulMemCompact
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitriangular_of_rational_mul_mem_compact : ∀ (D : D7) (n ρ : ℕ) (x₀ : Matrix (Fin n) (Fin ρ) D.host.E), LinearIndependent D.host.E x₀.transpose → ∀ K : Set (Mx D n ρ), IsCompact K → IsCompact {u : UX D ρ | rat x₀ ⬝ u.1.1 ∈ K} := by
  first | exact @GlobalTheory.AscFin.isCompact_setOf_rat_mul_mem | exact GlobalTheory.AscFin.isCompact_setOf_rat_mul_mem | (intros; apply GlobalTheory.AscFin.isCompact_setOf_rat_mul_mem <;> assumption)
