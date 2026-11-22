module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HenselianAlgClosedResidue
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.IsPolarisationOfRelAmple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearIsIsoOfIsProperOfFinitePresentation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeneratorExtendsFromGenericFibreValuationRing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSmulSecNonzeroOnSpecialFibre
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelExtensionOverDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymTranslate
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.StrictModelTranslatesTwistCompatible
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RigidifiedSymDescendToSubring

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.CechPic GlobalTheory.AbDual
open GlobalTheory.IndefiniteRowSideFullHecke.ZeroSectionBase (IsPrincipalPol sqToBase)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.henselian_alg_closed_residue : ∀ (C : Type) [Field C] [IsAlgClosed C] (R : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra R C] [IsFractionRing R C],
    HenselianLocalRing R ∧ IsAlgClosed (IsLocalRing.ResidueField R) := by
  first | exact @GlobalTheory.CompanionTheory.CommAlg.Hens.henselian_and_residueField_isAlgClosed | exact GlobalTheory.CompanionTheory.CommAlg.Hens.henselian_and_residueField_isAlgClosed | (intros; apply GlobalTheory.CompanionTheory.CommAlg.Hens.henselian_and_residueField_isAlgClosed <;> assumption)
