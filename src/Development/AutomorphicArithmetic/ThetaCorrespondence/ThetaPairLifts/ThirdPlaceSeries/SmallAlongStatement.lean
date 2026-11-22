module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Formalism.LocalToGlobal.IndefiniteReal.RealTB
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
public import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
public import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PassIn3OfRows
public import Formalism.LocalToGlobal.IndefiniteReal.RealPins
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfSEEofTT
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourFRLeMinGOfSizeG
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SmallAlong

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_small_of_seeEx_primitive : ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.VisibleExamplePointSummands 𝒜 σ → AtAll _root_.GlobalTheory.Fc.Ind.summandPrimitive 𝒜 σ → EvWC (fun _ => True) _root_.GlobalTheory.Fc.Ind.SmallPointSummands 𝒜 σ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.small_along_alt | exact _root_.GlobalTheory.Fc.Ind.small_along_alt | (intros; apply _root_.GlobalTheory.Fc.Ind.small_along_alt <;> assumption)
end
