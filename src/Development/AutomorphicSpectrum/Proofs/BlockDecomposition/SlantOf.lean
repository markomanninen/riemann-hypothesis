module

public import Mathlib
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethProductProperSmoothStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KuennethIsoProperSmoothStatement

@[expose] public section

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto

namespace GlobalTheory.CompanionTheory.KunGlue

theorem slantOf : CrystallineSemistableComparison.Onto.TopRes → CrystallineSemistableComparison.Onto.SlantOf :=
  fun hT hS hM hC hZ hA hK => GlobalTheory.T.slant_of_hodge_kuenneth hT hS (fun K _ _ X X' P q q' _ _ _ _ p₁ p₂ hP h₁ h₂ =>
    GlobalTheory.T.kuenneth_product_proper_smooth hS hM hC hZ hA hK K X X' P q q' p₁ p₂ hP h₁ h₂)

end GlobalTheory.CompanionTheory.KunGlue
