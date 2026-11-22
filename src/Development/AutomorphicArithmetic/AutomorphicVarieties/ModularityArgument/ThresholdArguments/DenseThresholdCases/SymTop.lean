module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.ResidualAutomorphyOfLinkedEnds
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfDesc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SdStmt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SymUse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PlDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LinkedEndE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocPublished
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAlgRes

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.Z.Sym.Top
open UpperTheory.V.Lit UpperTheory.V.W UpperTheory.V.HV UpperTheory.V.Z.Sym.Pl
theorem linkedEnd_alt (hH : _root_.UpperTheory.V.Af.HypothesesH') (s2 : _root_.UpperTheory.V.Sd.Seed2Alt) (s3 : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense) : _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt :=
  have hA := hH.toClassicalTheorems
  have hN := hA.litN
  _root_.UpperTheory.Gal.projectedFormsSystemPart.linked_endomorphism_dense hN.aut.art (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN) (_root_.UpperTheory.V.HV.Core.modU_of_printsH hH) levEx (lamEx (_root_.UpperTheory.V.W.local_class_field_theory_all_of_literal_automorphy hN)) (b0Ex (phiAll (_root_.UpperTheory.V.W.cohP_alt hN))) s3 s2
    (_root_.UpperTheory.V.Sd.twist_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_cyclotomic_of_printed_results hA) (_root_.UpperTheory.V.Sd.alg_restriction_of_printed_results hA)
end UpperTheory.V.Z.Sym.Top
end
