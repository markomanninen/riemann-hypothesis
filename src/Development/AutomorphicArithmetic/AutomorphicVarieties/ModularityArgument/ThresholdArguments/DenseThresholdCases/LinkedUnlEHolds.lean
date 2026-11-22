module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CrystallineCardinalities.TanA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SdStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryRankTwoFlags
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocPublished
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.MultiplicityOne.CompOfFree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModNOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThFinal

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.Z.J
open UpperTheory.V.HV UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.J
theorem linkedUnlE_holds_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (s2 : _root_.UpperTheory.V.Sd.Seed2Alt) (s3 : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense) : LinkedUnlE :=
  have hN := hH.litN
  have hA := hH.toClassicalTheorems
  _root_.UpperTheory.Gal.projectedFormsSystemPart.linkedUnlE_alt hN.aut.art (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN) (_root_.UpperTheory.V.HV.Core.modU_of_printsH hH) (_root_.UpperTheory.V.Z.J.D.modularity_n_of_printed_mult_comp hH Z.Mult.mult_free Z.Mult.compOf_free) levEx
    (lamEx (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN)) (b0Ex (phiAll (_root_.UpperTheory.V.W.cohP_alt hN))) s3 s2 (_root_.UpperTheory.V.Sd.twist_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hA)
    (tanA (_root_.UpperTheory.V.W.global_compat_printed_of_literal_automorphy_n hN) (_root_.UpperTheory.V.W.locPrints_of_litN hN)) (_root_.UpperTheory.V.Th.core_alt_bis hH (_root_.UpperTheory.V.W.cohP_alt hN))
end UpperTheory.V.Z.J
end
