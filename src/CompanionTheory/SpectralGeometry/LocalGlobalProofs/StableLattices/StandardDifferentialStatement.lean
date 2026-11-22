module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.StandardDifferential
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSecondOrder.HasDerivAtDOf
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.StandardDifferential : StdD := by
  first | exact @GlobalTheory.CompanionTheory.ZuckStdD.stdD | exact GlobalTheory.CompanionTheory.ZuckStdD.stdD | (intros; apply GlobalTheory.CompanionTheory.ZuckStdD.stdD <;> assumption)
