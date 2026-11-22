module

public import Formalism.PeriodIntegrals.GTLower
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HwIrred
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GTBranch
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SchurFock
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.GTLowerOf

@[expose] public section

theorem gTLower_of (h2 : Formalism.BasicNotions.FactDelDualNabla) : PI.GTLower :=
  PI.WGL.gTLower_of h2 highest_weight_irreducible gelfand_tsetlin_branching schur_fock
