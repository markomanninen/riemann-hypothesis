module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeComplements
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitVectorPerpAllIff
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasComplementOfBasis

@[expose] public section

namespace GlobalTheory.UnitPerpObj

theorem unitVectorPerp (D : Formalism.BasicNotions.D7) : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeComplements.UnitVectorPerp D :=
  (GlobalTheory.UnitVectorPerpCompare.unitVectorPerp_iff D).1 (GlobalTheory.UnitPerp.unitVectorPerp D)

end GlobalTheory.UnitPerpObj
