module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ResidualIrreducibilityFormsEquivalent
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HtCard
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import ReciprocityTheory.Hypotheses.GalCoh
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinityTypeEtaTildeAtCmTypeEmbeddingsEqHalfStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightInfinitesimalCharacterParamOfLevelCompatibStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InfWtEqInfOfStatement
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.NPin GlobalTheory.NFacts
namespace GlobalTheory
theorem weightParam_of_pin_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.WeightParam D := by
  intro hL D P
  exact GlobalTheory.T.weightInfinitesimalCharacterParam_of_levelCompatible D P.M P.tp.tup P.H.level (GlobalTheory.T.infinityType_etaTilde_at_cmTypeEmbeddings_eq_half D P.cf P.C P.tp P.chr) (_root_.GlobalTheory.T.infWt_eq_infOf_of_isDual D P.M P.tp.tup P.H)
end GlobalTheory
end
