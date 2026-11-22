module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.IwahoriSubgroup
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IwahoriEigenvaluesOfNewton

@[expose] public section

namespace GlobalTheory.IwahoriEigenObj

theorem iwahoriEigenvalues : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriSubgroup.IwahoriEigenvalues :=
  GlobalTheory.IwahoriEigen.iwahoriEigenvalues

end GlobalTheory.IwahoriEigenObj
