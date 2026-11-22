module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfLitN
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVFinalU

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology
namespace UpperTheory.V.ZK
theorem lemmaK_of_litN_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hB : BOdd) : ∃ CK, LemmaK CK :=
  lemmaK hB (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK
end UpperTheory.V.ZK
end
