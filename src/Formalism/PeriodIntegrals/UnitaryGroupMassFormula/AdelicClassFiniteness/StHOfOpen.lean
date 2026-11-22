module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HmkFactor
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.UnitsModSq
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartShortOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.PartSplitOfOne
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSmulRight

@[expose] public section

namespace PIW.AdelClassFin

theorem stH_of_open (hO : SpOne) (hI : IdealBoundAll) (h1 : SvMajE) (h2 : SvCodiff) (h3 : SvBasis) (h4 : SvGramDet)
    (h5 : SvReal) : StH :=
  stH_of_parts (partShort_of partMink h1 h2 h3 h4 h5) partUnits (partIso_of hI) (partSplit_of_one hO)

end PIW.AdelClassFin
