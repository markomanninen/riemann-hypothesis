module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Assemble
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Blocks
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.DimStep
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Weights
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Formula

@[expose] public section

theorem weylForK_of : PI.WeylForU → PI.WeylForK :=
  PI.WeylForKWork.weylForK_of_leaves PI.WeylForKWork.block_reindex_holds PI.WeylForKWork.block_diagonal_torus_holds
    PI.WeylForKWork.torus_weight_exists PI.WeylForKWork.weight_unique_holds PI.WeylForKWork.minimal_irreducible_exists
    PI.WeylForKWork.dominant_restriction_holds PI.WeylForKWork.dimension_induction_holds PI.WeylForKWork.weyl_formula_compact
