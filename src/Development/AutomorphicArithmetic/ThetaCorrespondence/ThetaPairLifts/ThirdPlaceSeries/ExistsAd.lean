module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralRationalAtMember
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ActionReadAtMember
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFinEMemDivisorStandard
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateBlockUpperOfEigenfunctionUnipotentTypeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralFrameSplitNontrivialAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueNeZeroOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.G0LiftUnitaryCentralFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjParahoricBlockLiftStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CenRatAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ActReadAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameAtOfLayerStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.CenLocAt
theorem exists_ad_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ _ _ _ _ t _ _ c => Nonempty (MtAd t.r.Y c.a.all.gal.mt) :=
  GlobalTheory.HeightCounting.JumpsAt.evLgG_of_forall fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hE _ _ => hE.elim fun e => ⟨_root_.GlobalTheory.HeightCounting.RealExpansionExtraData.ad e⟩
set_option maxHeartbeats 2000000 in
theorem cenLoc_at_member : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ c => CenLoc (w.D Z) c.a.all.gal.mt := fun hL =>
  _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.cenRat_at_members hL) (_root_.GlobalTheory.T.actRead_at_member_of_recT hL)) (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.frameAt_of_tup_eq_mu_at_members hL) (_root_.GlobalTheory.CenLocAt.exists_ad_alt hL)))
    fun _ _ _ _ _ _ _ _ t _ _ _ h => h.2.2.elim fun ad => cenLoc_of t.r.Y t.r.z.cG _ ad h.1.1 h.1.2 (h.2.1 ad)
end GlobalTheory.CenLocAt
end
