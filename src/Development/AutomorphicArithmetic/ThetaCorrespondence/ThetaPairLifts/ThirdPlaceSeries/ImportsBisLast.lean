module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsobaricDiscreteSelfDualStrongMultiplicityOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapEqProdOfValuationSubring
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapPrimeToPartFbar
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationPowApplyDivSubOneLt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFrobeniusConjInertiaPowModWildStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DownMemRecOfTies
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodPartRecursion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharEtaBack
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BlockSplitAll
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NotMemPlacesOverOfNe
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParUpRecOfTies
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalStrongMultiplicityOneOfAnalytic
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOneOfCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LabelSettingTameGenerator
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthOfAvTied
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalPointThetaExhaustion
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PointOfConditions
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PartsGive
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspidalGaloisUnramified
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisExtra
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.JointCondRho
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SEtaChi
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SEtaSig
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisRestStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameGeneratorResidual
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsLast
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisTer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeOrthOfPinStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EigAtStatement
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TrivialLocalCondition

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.RowsCClose
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.GlobalTheory.NPin.CharacterChoiceJoin P → _root_.GlobalTheory.NRows.RowsAAlt D →
    GlobalTheory.NRows.RowsB D → Formalism.MainNotions.SumRepresentations.adm1 D → Formalism.MainNotions.SumRepresentations.adm8 D → _root_.Formalism.MainNotions.SumRepresentations.provisionFirst D →
    (∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i) → GlobalTheory.NRows.RowsC D := by
  intro hL D P J hA hB a1 a8 p1 hi
  obtain ⟨p41, _, p42⟩ := p1
  obtain ⟨tl, lt, io, rb⟩ := _root_.GlobalTheory.TieLabAt.main_alt_alt hL D P
  have iface := _root_.GlobalTheory.AdmIface.main_alt_alt D
  have bc : ∀ i, BCEx D.nd D.naut i := iface.1 a1
  have lift : ∀ i, GlobalTheory.ThetaExh.LiftParam D.nd D.naut i := iface.2.2.1 p42
  have isot : Rows.IsotInternal D.what₂ := iface.2.2.2.2.2.mp a8
  have rho : GlobalDatumResidualRepCondition D :=
    _root_.GlobalTheory.ParamRep.jointCond_33_rho_of_signature_adm5 D hA.tie0 hA.a2 hB.a4 hA.a5 p41 (GlobalTheory.GoodCuspPoint.main D tl)
      (_root_.GlobalTheory.XiOver.main_alt_alt_alt D P.cf P.C P.tp P.chr P.val hA.tie0 hA.a2 hA.a5)
  have rp : _root_.UpperTheory.GalS.RowRepAtGN D :=
    _root_.GlobalTheory.RowRepOcc.repAtGN_of_point_split D hA.tie0 hA.a2 hA.a5 p42 rho hA.gsp (_root_.GlobalTheory.T.point_of_aux42_aux41 hL D P p42 p41)
  exact
    { c4b := _root_.GlobalTheory.RowTie.tameGenerator_residual_alt_alt D rb io lt rp
      rho := rho
      dz := _root_.GlobalTheory.GoodDepthZero.main_alt_alt D hA.tie0 hB.a4 p41 hA.gsp
      parUp := GlobalTheory.RowTie.parUpRec_of_ties D P.T hB.thetaOne (fun i => (hi i).1) bc (fun i => (hi i).2.1)
        (fun i => (hi i).2.2)
      downMem := GlobalTheory.RowTie.downMemRec_of_ties D P.T hB.thetaOne isot
        (fun i => _root_.GlobalTheory.PartOrthPin.main_alt_alt hL D P i ⟨J.rowM i⟩) (fun i => _root_.GlobalTheory.T.type_orthogonality_of_form' hL D P i (J.form i))
        (fun i => (hi i).1) bc (fun i => (hi i).2.1)
      goodPart := GlobalTheory.Proof.GoodComponentRecursion.goodPartRec_of_ties D P.T hB.thetaOne lift (fun i => _root_.GlobalTheory.T.ptLocal_theta_exhaustion hL D P i) bc
        (fun i => (hi i).2.1) }
end GlobalTheory.RowsCClose
end
