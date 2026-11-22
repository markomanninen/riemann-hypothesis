module

public import Mathlib
public import Formalism.PeriodIntegrals.FoldDCUnfold
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.FoldUnfold
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.FoldDCUnfoldOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.TranslationIndependent
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FoldingUnfolding.DoubleCosetTranslation

@[expose] public section

theorem fold_dc_unfold : PI.FoldDCUnfold.FoldDCUnfold :=
  PI.FoldDCUnfold.W.foldDCUnfold_of PI.FoldDCUnfold.W.translation_exists
    PI.FoldDCUnfold.W.translation_independent PI.FoldDCUnfold.W.translation_product
    PI.FoldDCUnfold.W.double_coset_translation lintegralTransversalSum
