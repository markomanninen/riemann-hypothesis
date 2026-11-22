module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.OrdFEqOfClassOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.FinprodNormEmbedding
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.EvFLocalIdeleSelf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.FactorOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AlgebraicValuesFinite.IsIntegralOfMemCompo

@[expose] public section

noncomputable section

namespace PI.AlgValsFin.W

theorem algValsFin_of_tors (L : Type) [Field L] [NumberField L] (hT : TorsUnits L) : AlgValsFin L :=
  assemble hT (keyIdOf decomp locVal prodNorm) classPow classSame

end PI.AlgValsFin.W
