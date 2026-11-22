module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEquivarianceWeilModel
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartRealisationWithScalarsCharOfWeakStatement
public import Formalism.LocalToGlobal.IndefiniteReal.PrimitivePackageFullHecke
public import Formalism.LocalToGlobal.IndefiniteReal.PackageFromPrimitiveStatements
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CharacterUpdateOfWeakRealisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitRowsBarPhaseCompatibility
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftPrincipal

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLevelLift_at_twisted_points : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ g0 : G0 (R2 p).Pg (Fm.D x i).R.r,
  ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc (Fm.D x i) j) ((R2 p).βW j) ((R2 p).datWp j (R2 p).triv) g0 κ' := by
  first | exact @_root_.GlobalTheory.TieLift.lift_principal_alt | exact _root_.GlobalTheory.TieLift.lift_principal_alt | (intros; apply _root_.GlobalTheory.TieLift.lift_principal_alt <;> assumption)
end
