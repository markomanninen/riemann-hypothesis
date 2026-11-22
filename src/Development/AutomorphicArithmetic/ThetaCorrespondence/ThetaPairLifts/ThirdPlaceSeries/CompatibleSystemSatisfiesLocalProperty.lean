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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabFixedOfTypesTrue
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsClassMapCorrespondence
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupled
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameSupportCompatible
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelignStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCompatibilityOfClassMaps
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneLabelsAllPlacesOfFixedAndConjStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGreenCuspidalLabellingSameGeneratorsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AuxiliaryPlacesSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuationFixedLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyInPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralLocalStableIntegral
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemberImp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OPin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SpecializationAtMemberOfLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OpinAtMemStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ZlStableAtStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabFixedIff
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalSeriesConcreteOfDzSwap
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
namespace GlobalTheory.SerFinished
set_option maxHeartbeats 2000000 in
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.TypeLeaf.SerLoc (w.D Z) := by
  intro hP hL
  refine _root_.GlobalTheory.HeightCounting.Up.Model.AtMem.at_member_imp (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.exists_character_choice_pin_at_of_third_layer hP hL)
    (_root_.GlobalTheory.HeightCounting.Up.Model.AtMem.and_z (_root_.GlobalTheory.T.coefficient_duty_pin_at_each_member hL) (_root_.GlobalTheory.T.cenLoc_zlStable_cenInt_at_members hL))) ?_
  rintro K B f T w Z Wt p0 t nch n c ⟨⟨P, hPin⟩, hO, hC, -, -⟩
  have hlab : GlobalTheory.SerSys.LabTie (w.D Z) fun k => @GlobalTheory.Mem.TypePl.labDat ((w.D Z).host.g k) ⟨(w.D Z).host.g_prime k⟩ :=
    (_root_.GlobalTheory.CoefDuty.OPinModel.labFixed_iff_alt c.a).2 hO.lab
  have htame : ∀ D', D' = withLoc c.a.nt.L → ∀ k (v : D'.nd.PlG k),
      ∃ κ : IsLocalRing.ResidueField (D'.nd.plOm.1 (D'.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D'.host.g k),
        TameCoupled (D'.nd.plOm.1 (D'.naut.plGw k v)) κ (D'.ntypes.tg k v)
          (@GlobalTheory.Mem.TypePl.labDat (D'.host.g k) ⟨D'.host.g_prime k⟩).gen := by
    rintro _ rfl k v
    exact ⟨c.a.nt.A.grp.kv k v, _root_.GlobalTheory.CoefDuty.OPinModel.labDat_gen_tame_at_plGw hO k v⟩
  refine _root_.UpperTheory.Lit.Dz.compatibleSystemLocalProperty hP.what₂ hP.green hP.zel hL (w.D Z) P _ hlab (htame _ c.a.nt.eq) ?_
  rw [hPin.M_eq]
  exact hC
end GlobalTheory.SerFinished
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.serLoc_at_member_of_published_inputs : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ _ _ _ _ => GlobalTheory.TypeLeaf.SerLoc (w.D Z) := by
  first | exact @_root_.GlobalTheory.SerFinished.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.SerFinished.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.SerFinished.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
