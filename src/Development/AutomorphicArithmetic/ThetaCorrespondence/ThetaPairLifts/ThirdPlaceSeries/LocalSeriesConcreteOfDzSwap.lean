module

public import Mathlib
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisTwistType
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsRepresentationComponent
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GlobalArtinReciprocityTrivial
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemLocalProperty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTypeGlobalOfSeriesLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjSelfDualGaloisRepCMDatum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameUniformizerPower
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTypeSplitProp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTypeGlobalOfRegularLocal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalGlobalCompatibilityCMDatum
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LabelTameCharacter
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalBesselMultiplicityOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowTruthOfLabelTie
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CompatibleSystemLocalPropertyExplicit
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionAllStages
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodFTAllStA

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
namespace UpperTheory.Lit.Dz
theorem dz_swap_compatible_alt : _root_.GlobalTheory.T.ConjSelfDualGaloisRepCMDatumThirdPlace :=
  fun hL => _root_.DiscreteGroups.sglob.DzType.Rt.tame_uniformizer_power_alt (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem localGlobalCompatibility_cmDatum_alt : _root_.GlobalTheory.T.LocalGlobalCompatibilityCMDatum' :=
  fun hL => _root_.DiscreteGroups.sglob.DzType.Rt.labAt_ofDet_tame_eq_X_sub_C (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem blockTypeSplitProp : _root_.GlobalTheory.T.BlockTypeSplitThirdPlace :=
  fun a hL => _root_.DiscreteGroups.sglob.DzType.Rt.regLoc_of_depth_zero_inertia_big_greenLab a (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem nonGaloisTwistType : _root_.GlobalTheory.T.NonGaloisTwistType' :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.exists_representation_component_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem firstTermCondition_all_stages : _root_.GlobalTheory.GoodFirst.FirstTermConditionAllStagesAlt :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.goodFTAll_stA_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem compatibleSystemLocalProperty : _root_.GlobalTheory.T.CompatibleSystemLocalPropertyThirdPlace :=
  fun a b c hL => _root_.DiscreteGroups.sglob.DzType.Rt.serLoc_of_tame_coupled_and_cenLoc a b c (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem compatibleSystemLocalProperty_explicit : _root_.GlobalTheory.SerSys.Assembly.CompatibleSystemLocalPropertyExplicitAlt :=
  fun a b c hL => _root_.DiscreteGroups.sglob.DzType.Rt.depthZeroType_series_local_explicit_alt a b c (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
theorem localBesselMultiplicityOne : _root_.GlobalTheory.T.LocalBesselMultiplicityOne' :=
  fun a b hL => _root_.DiscreteGroups.sglob.DzType.Rt.rowTruth_of_labelTie_alt a b (_root_.UpperTheory.Lit.Dz.global_artin_reciprocity_trivial hL) hL
end UpperTheory.Lit.Dz
end
end
