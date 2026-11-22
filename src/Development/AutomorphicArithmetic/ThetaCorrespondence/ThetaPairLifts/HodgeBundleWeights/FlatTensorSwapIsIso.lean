module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.WeilBound.CoreStatements.ComplexPeriods.FlatDegreeResidues.FlatSlim
public import Development.WeilBound.CoreStatements.ResolutionCharZero.PlugResK
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatDegreeHypotheses

@[expose] public section

section
theorem UpperTheory.Lit.Flat.flat_tensor_swap_isIso : _root_.GlobalTheory.T.FlatDegreeHypotheses :=
  fun _ _ _ => FlatDegreeResidue.flatDegreeSt_of_resK PositivityTheory.ResPlug.FromRes.resK
end
