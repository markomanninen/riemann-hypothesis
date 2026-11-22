module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStepScalarsOfRealisationStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainStepAdjointScalarStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ArchimedeanThetaCorrespondenceTowersRealDataStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealTupleTwistedChainOfScalarHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchurProductTypingsAgreeThetaChainStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealMeasureUniformInTupleOfThetaLiftScalarStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealLastStageNormalizedOfScalarHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealDatumNormShrinkOfScalarHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealFormsRangeMultiplicityOfScalarHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfPartHavePartParamsFirstChainMemberStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepConstantsTupleIndepStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealQuotientVolumeGrowthOfScalarHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainStepExactInnerProductStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainDatumLawsUnderLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainLevelIntegralRealZetaOfTwistedTransformLawsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainLValueQuotientFactorizationStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainFirstStageLValuesPositiveStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistPlacesIntegralPeelOfDoublingStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterOfOneNonzeroValueStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainRealZetaNonvanishingStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainTwistEulerFactorsRestoreProofStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStageSoftPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftsAdjointOfCuspRapidDecayStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpParameterOfTransferStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpLowerBlockParameterProofStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainThetaLiftUpSpanStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpEqAdjointValueStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

namespace GlobalTheory.ChainTw

theorem scalars_of_given_all : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.UnramifiedDoublingGL → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → GlobalTheory.Core.Rk.SW.HeckeFormNS D → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  intro hHCF hCRD hDSC hHCM hCW hHowe hUDG D G _ _ Pl0 T A Ks _ _ _ R F g hNG hHecke
  have soft : SoftQ D := GlobalTheory.T.twistedChain_stage_soft_properties hHCF hCRD D
  have law : LevelLawQ D := GlobalTheory.T.twistedChain_datum_laws_under_levels D
  have restore : Restore D := GlobalTheory.T.chainTwistEulerFactorsRestore_proof D
  have lfull : LFull D := GlobalTheory.T.twistedThetaChain_LValue_quotientFactorization D
  have upSpan : UpSpanQ D := GlobalTheory.T.twistedChain_thetaLiftUpSpan hDSC hHCM hCRD hCW D law
  have upAdj : UpAdjQ D := GlobalTheory.T.chainThetaLiftsAdjoint_of_cuspRapidDecay hCRD D
  have upVal : UpVal D := GlobalTheory.T.chain_theta_lift_up_eq_adjoint_value D soft upSpan upAdj
  have exact : StepExactNS D :=
    GlobalTheory.T.thetaLiftChainStep_exact_innerProduct D hHecke soft (GlobalTheory.T.chainTwistPlacesIntegralPeel_of_doubling hUDG hCRD D) (GlobalTheory.T.chainLevelIntegralRealZeta_of_twisted_transform_laws D law)
  have lam : StepLam D := GlobalTheory.T.twistedThetaChain_step_adjoint_scalar D soft (GlobalTheory.T.chainThetaLiftUp_parameter_of_transfer hCRD hHowe D) (GlobalTheory.T.chainThetaLiftUpLowerBlockParameter_proof hCRD D)
    (GlobalTheory.T.lowerBlockParameter_of_one_nonzeroValue D soft) upVal exact lfull restore
  have hX : RangeX R := GlobalTheory.T.realFormsRangeMultiplicity_of_scalarHypotheses R F g
  have chain : ∀ h : RangeX R, RChain R h := GlobalTheory.T.realTupleTwistedChain_of_scalarHypotheses R F g
  have zeta : RealZetaQ D := GlobalTheory.T.twistedChain_realZeta_nonvanishing hHCM D (GlobalTheory.T.archimedeanThetaCorrespondence_towers_real_data hDSC hHCM D)
  have unif : RUnif R hX := GlobalTheory.T.twistedChain_step_constants_tuple_indep R F g hNG zeta restore hX (chain hX)
    (GlobalTheory.T.realMeasureUniformInTuple_of_thetaLiftScalar R F g chain hX) (GlobalTheory.T.realQuotientVolumeGrowth_of_scalarHypotheses R F g chain hX) (GlobalTheory.T.realDatumNormShrink_of_scalarHypotheses R F g)
  exact GlobalTheory.T.chainStep_scalars_of_realisation R F g hNG soft (GlobalTheory.T.lowerBlockParameter_of_one_nonzeroValue D soft) (GlobalTheory.T.chain_first_stage_L_values_positive hCRD D) lfull lam hX
    (chain hX) (GlobalTheory.T.realLastStageNormalized_of_scalarHypotheses R F g hX) unif (GlobalTheory.T.rows_of_part_have_part_params_first_chain_member hCRD R F g chain hX) (GlobalTheory.T.schurProduct_typings_agree_thetaChain R F g)

end GlobalTheory.ChainTw
