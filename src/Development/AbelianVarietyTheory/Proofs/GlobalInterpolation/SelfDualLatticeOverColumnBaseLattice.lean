module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocLatOverLat

@[expose] public section

namespace GlobalTheory.OverObj

theorem selfDualOverBase : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase :=
  GlobalTheory.OverCompare.overLattice_iff_selfDualOverBase.mp GlobalTheory.OverLat.overLattice

end GlobalTheory.OverObj
