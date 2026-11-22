module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NuPairOfDerivativesJacquet
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.SegmentDerivatives.DerivSub
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nu_pair_of_derivatives_jacquet : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → GlobalTheory.BZSeg.DerivJac k → GlobalTheory.BZSeg.JmTheta k → GlobalTheory.BZSeg.DerivSub k → GlobalTheory.BZSeg.NuPair k := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair | exact GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair | (intros; apply GlobalTheory.CompanionTheory.BZNuPairAsm.nuPair <;> assumption)
