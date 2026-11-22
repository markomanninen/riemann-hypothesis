module

public import Mathlib
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirDiagonalSum
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfIwasawa
public import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.CasimirScalarOfCapelliDeterminantEigenvalueImpor
public import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam

@[expose] public section

open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.CasimirDiagonalSum : CasDS := by
  first | exact @GlobalTheory.CompanionTheory.CasimirDS.casDS | exact GlobalTheory.CompanionTheory.CasimirDS.casDS | (intros; apply GlobalTheory.CompanionTheory.CasimirDS.casDS <;> assumption)
