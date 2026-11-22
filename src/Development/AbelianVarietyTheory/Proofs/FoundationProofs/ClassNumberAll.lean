module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassSelfDualLatticeFirstSpaceEq
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeOverColumnBaseLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabiliserSelfDualLatticeLevelIndexFormulaStatement

@[expose] public section

namespace GlobalTheory.ColClassNumber

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice

theorem classNumber_all (D : D7) (Lv : LevelData D) : ClassNumberFormula₂ D Lv :=
  classNumber_of_index GlobalTheory.T.selfDualLattice_over_columnBaseLattice GlobalTheory.T.stabiliser_self_dual_lattice_level_index_formula D Lv

end GlobalTheory.ColClassNumber
