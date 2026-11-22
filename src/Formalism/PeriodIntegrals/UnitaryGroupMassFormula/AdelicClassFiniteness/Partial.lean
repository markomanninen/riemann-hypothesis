module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.IsImgTrans
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.KsetMulVecMem
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.StHOfOpen

@[expose] public section

noncomputable section

namespace PIW.AdelClassFin

theorem stKFin : StKFin := stKFin_of (stLatFin_of lattice_dense)

theorem adelClassFin_of_H (h : StH) : PI.AdelClassFin.AdelClassFin :=
  stTop stCong stKFin (stGenusOf stDict h)

theorem adelClassFin_of_open (h1 : SpOne) (h2 : IdealBoundAll) (h3 : SvMajE) (h4 : SvCodiff) (h5 : SvBasis)
    (h6 : SvGramDet) (h7 : SvReal) : PI.AdelClassFin.AdelClassFin :=
  adelClassFin_of_H (stH_of_open h1 h2 h3 h4 h5 h6 h7)

end PIW.AdelClassFin
