module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SizeAbsorption.SizeDel
public import Development.AutomorphicArithmetic.OrbitLabellings.SzEatIFree

@[expose] public section

theorem sz_eat_identity : PI.SzEatI.SzEatI := UpperTheory.G2.szEatI_of_stepA PI.SzEatI.W.stepA
