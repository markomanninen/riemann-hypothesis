module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.WsIIOfPrintsH
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PotentialModularityTower
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SeedIIZ
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Hypotheses4Z
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.IndAutLOfSplit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsPrimeIndex

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
namespace UpperTheory.V.Z.Bc
theorem seedIIs_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.Ws.SeedIIAlt :=
  have hA := hH.toClassicalTheorems
  _root_.UpperTheory.V.Z.Bc.seedII_Z_alt ⟨hH, Published.hilbert_eisenstein_weight_one_holds, Lit.oneUse⟩
    (_root_.UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.E.indAutLP_of_printsH_upQuad_upSol_indCs hH (_root_.UpperTheory.V.Z.Bc.upQuadI_of_alt hA (quadLiftRealToComplex_of_base_change hH.bc)) (_root_.UpperTheory.V.Z.Bc.upSolI_of_alt hA (cyclicLiftRankTwo_of_cyclic_base_change hH.cyc)) indCs)
end UpperTheory.V.Z.Bc
end
