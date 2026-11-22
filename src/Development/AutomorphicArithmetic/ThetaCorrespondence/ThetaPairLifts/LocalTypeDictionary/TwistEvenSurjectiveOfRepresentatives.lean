module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankThetaChainLiftSurjectiveOfAdjointNonzeroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainParamsTrivialBoundRapidDecayStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainSpannedParamsOfValueIndependentStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainFiniteDimensionalAndPeterssonProduStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepRealZetaNonvanishingStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepAdjointNonzeroTransferredParamsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UpwardThetaLiftNeZeroOfLValueNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainUpwardLiftHeckeParamTransferredStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUpwardCuspSpanAndAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaStepSemilocalZetaNeZeroOfRealStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HeckeFormOfDoubling

@[expose] public section

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EvenOnto
theorem even_surjective_of_representatives : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D := by
  intro hHC hCusp hDS hHCM hCW hHowe hWeil hSW hSWc hDoub hUnr D
  have hHecke := _root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' hWeil hCusp hSW hSWc hDoub hUnr D
  obtain ⟨hFin, hMet⟩ := GlobalTheory.T.evenThetaChain_finiteDimensional_and_peterssonProducts hHC hCusp D
  obtain ⟨hEig, hPoV, hInd⟩ := GlobalTheory.T.even_theta_chain_spanned_params_of_value_independent hCusp D hFin hMet
  have hBd := GlobalTheory.T.evenRankChain_params_trivialBound_rapidDecay hCusp D
  obtain ⟨hSpan, hAdj⟩ := GlobalTheory.T.thetaLiftUpward_cuspSpan_and_adjoint hDS hHCM hCusp hCW D
  have hPar := GlobalTheory.T.evenThetaChainUpwardLift_heckeParam_transferred hCusp hHowe D
  have hRZ := GlobalTheory.T.evenThetaStep_realZeta_nonvanishing hDS hHCM D
  have hZN := GlobalTheory.T.evenThetaStep_semilocalZeta_ne_zero_of_real D hMet hRZ
  have hNe := GlobalTheory.T.upwardThetaLift_ne_zero_of_lValue_ne_zero D hHecke hMet hZN
  have hStep := GlobalTheory.T.even_theta_step_adjoint_nonzero_transferred_params D hFin hPoV hSpan hAdj hPar hNe
  exact GlobalTheory.T.evenRankThetaChainLift_surjective_of_adjoint_nonzero D hFin hMet hEig hInd hBd hStep
end GlobalTheory.EvenOnto
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_even_surjective_of_representatives : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Hk3.HoweUnram → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.WeilSiegelFormulaUnitary → GlobalTheory.Published.SiegelWeilUnitaryConvergent → _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals → GlobalTheory.Published.UnramifiedDoublingGL → ∀ D : D7, OntoAll D := by
  first | exact @_root_.GlobalTheory.EvenOnto.even_surjective_of_representatives | exact _root_.GlobalTheory.EvenOnto.even_surjective_of_representatives | (intros; apply _root_.GlobalTheory.EvenOnto.even_surjective_of_representatives <;> assumption)
end
