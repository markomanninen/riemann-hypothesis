module

public import Mathlib
public import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual

@[expose] public section

namespace GlobalTheory

theorem dualFrLattice_holds : Formalism.L2.DIV.DualFrLattice :=
  GlobalTheory.DualLat.dualFr_lattice_and_hdual.1

end GlobalTheory
