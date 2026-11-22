module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowParamOfCuspidal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodRowCuspParam
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverRowsAndMono
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterUnramifiedInf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsotypicRealNonzero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalInertiaOfIsotypic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InfinityTypeOfLift
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsLocS
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalAwayFromTypes
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParameterLawsEmptyStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoicesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitarisableOfIsSpehOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangeDefiniteOfCmDatumRecLaws
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryOfLocalLanglands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodPlaceCuspidalType
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceLocalIndex
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemNonzeroPlacesOfResidueChar
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsStagesClauses
public import Development.AbelianVarietyTheory.Counterexamples.HeckeCharacterExamples.PeriodBoundOfPlaceBound
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemImpAltAlt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CuspParameterAtMemberOfParallelCopy
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocalizationAtMember
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedAtAtMemStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocWOfNTrue
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.GalLoc.RowParamAt
theorem localGalois_parameter_mem_at_place_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (w.D Z) Rw := by
  intro hN _ hL
  refine _root_.GlobalTheory.GalLoc.atMem_mono (_root_.GlobalTheory.GalLoc.atMem_and' (_root_.GlobalTheory.GalLoc.atMem_and' (_root_.GlobalTheory.T.good_cusp_param_at_member_of_heq_locR hN hL) (_root_.GlobalTheory.T.exists_loc_with_place_and_index_at_member hN hL))
    (_root_.GlobalTheory.T.exists_twisted_place_at_member hL)) ?_
  intro K B f T w Z Wt p0 t nch n xd c _ H Rw hRw
  obtain ⟨⟨hp, hl⟩, v, hv⟩ := H
  have hW := _root_.GlobalTheory.GalLoc.RowParamAt.locW_of_nTrue_alt c.a.nt Rw hRw
  refine GlobalTheory.TwInputs.rowParam_of_cuspParam (w.D Z) Rw (hp Rw hRw) ?_ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw _)
  intro j h1 h2 σ hσ hg
  obtain ⟨i, -, -⟩ := hl v hv j h1 h2 σ hσ
  exact GlobalTheory.HeightCounting.CuspOfParam.goodRow_cuspidal (w.D Z) Rw ⟨i⟩ hW (hp Rw hRw) j h1 h2 σ hσ hg
end GlobalTheory.GalLoc.RowParamAt
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_param_at_member_of_serN : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c =>
    ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.TwInputs.RowParam (w.D Z) Rw := by
  first | exact @_root_.GlobalTheory.GalLoc.RowParamAt.localGalois_parameter_mem_at_place_alt | exact _root_.GlobalTheory.GalLoc.RowParamAt.localGalois_parameter_mem_at_place_alt | (intros; apply _root_.GlobalTheory.GalLoc.RowParamAt.localGalois_parameter_mem_at_place_alt <;> assumption)
end
end
