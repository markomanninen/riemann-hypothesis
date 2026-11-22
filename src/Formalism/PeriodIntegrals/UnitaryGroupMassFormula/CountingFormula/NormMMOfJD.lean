module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ProdAbsNormDifferentIdealPowers
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.NMPseudoOf
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CountCoeEqMultiplicity
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DeterminantLocal

@[expose] public section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

theorem normMM_of_JD (hE : JordanExists) (hD : DetLocal) : Formalism.L2.SG.Pf.Cnt.NormMM :=
  normMM_of_NM (nMPseudo_of hE hD count_extension norm_mass_assembly)

theorem normMM_of_J (hE : JordanExists) : Formalism.L2.SG.Pf.Cnt.NormMM :=
  normMM_of_JD hE determinant_local

end PI.UnitaryGroupMassFormula.CntFormula.R6
