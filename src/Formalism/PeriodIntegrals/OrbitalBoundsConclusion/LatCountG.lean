module

public import Mathlib
public import Formalism.PeriodIntegrals.LatCountG
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDet

@[expose] public section

theorem lattice_count_all : PI.LatCountG.LatCountAll :=
  PI.UnitaryGroupMassFormula.LCG.latCountAll_of_idx PI.UnitaryGroupMassFormula.LCG.determinant_index_formula PI.UnitaryGroupMassFormula.LCG.lattice_indexOf
