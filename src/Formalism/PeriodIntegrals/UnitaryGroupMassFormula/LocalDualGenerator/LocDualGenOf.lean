module

public import Mathlib
public import Formalism.PeriodIntegrals.LocDualGen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.PsiTower
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.AddCharKernel
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.FpDual
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDualGenerator.EpSelfDual

@[expose] public section

namespace PI.LocDualGen.Of

theorem locDualGen_of (h : PI.LocDualGen.W.FpDualUnram) : PI.LocDualGen.Stmt :=
  PI.LocDualGen.Top.stmt_of PI.LocDualGen.Psi.addCharKernel PI.LocDualGen.FpD.existsDifferentGenerator h
    PI.LocDualGen.EpG.quadraticSelfDual

end PI.LocDualGen.Of
