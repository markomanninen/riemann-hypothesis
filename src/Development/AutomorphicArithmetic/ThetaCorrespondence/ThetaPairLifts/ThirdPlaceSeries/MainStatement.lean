module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleDictionaryOfParams
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAlt

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admDict_of_weight_blockChar : GlobalTheory.TwSys.Cheb → ∀ D : D7, _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → WeightParam D → BlockCharParam D → AdmissibleParameterJ.AdmDict D := by
  first | exact @_root_.GlobalTheory.BridgeAdmDict.main_alt_alt | exact _root_.GlobalTheory.BridgeAdmDict.main_alt_alt | (intros; apply _root_.GlobalTheory.BridgeAdmDict.main_alt_alt <;> assumption)
end
