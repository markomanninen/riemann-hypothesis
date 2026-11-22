module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToRatHyp0
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesBaseTwistedUniversalRationalStatement
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartRealisationWithScalarsCharOfWeakStatement
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
public import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterUpdateOfWeakRealisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VStdOfOrthonormalSpan
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TwoRunDatumBoundUnitAtIndefinitePoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullHeckeRealDatMovedReadings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLeOfAntilinear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JEvExistsAndJEvBar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadingsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesRationalityBackFromMovedReadingsStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatUnframeStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPoint

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.BigOn GlobalTheory.BigOn.Exp
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.BigOn.Exp
theorem rowAt_of_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.ConditionAtPlace := by
  intro hP hA hR hS hL hT
  refine _root_.GlobalTheory.BigOn.Exp.twist_at_statement_of_ratHypAt ?_ (GlobalTheory.T.thetaSeries_base_twisted_universal_rational hA hR hS)
  exact _root_.GlobalTheory.BigOn.Exp.TwistConditions.imp (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hL hT) fun Fm x hx i p hp hM w _ j h =>
    _root_.GlobalTheory.T.exists_rational_data_realization_alt hP Fm x hx i p hp hM _ j (_root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hp hM _ h.2.2.2 h.1 j)
end GlobalTheory.BigOn.Exp
end
end
