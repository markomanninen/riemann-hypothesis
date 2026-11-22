module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilLagrangianTermsAbsTsumLeHeightPoly
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightOrthogonalEmbeddingLePow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StabilizerInductionLaw
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Garding
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryConjSelfDualMajorantLevelsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePowStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AnisotropicCoreWittFrame
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.ExistsNotEisContinues
public import Development.WeilBound.RepresentationTheoryGL.EisensteinResidues.AnisotropicGlobalForms.SectionTrace.SecOf
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemUpperHalf

@[expose] public section

noncomputable section

open scoped NNReal Matrix TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open PositivityTheory.RgEis ResidueKilled.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.StdChart

theorem bdet_Psi (D : D7) {n : ℕ} (χ : (AE D)ˣ →* Circle) (g : GlobalTheory.StdUnn.G D n) (a : GL (Fin n) (AE D))
    (h : GlobalTheory.StdUnn.blkA (GlobalTheory.StdUnn.mat g) = a.1) :
    bdet (Sum.inl '' (Set.univ : Set (Fin n))) (Psi D χ n g).1 = Matrix.GeneralLinearGroup.det a := by
  rw [Psi_val]
  exact bdet_eq D _ a h

theorem tStd : TStd := by
  intro hD hI D χ n
  refine ⟨Psi D χ n, ?_, ?_, ?_, ?_⟩
  · exact mem_GF D χ
  · exact mem_P D χ
  · exact mem_K D χ hD hI
  · exact bdet_Psi D χ

end GlobalTheory.CompanionTheory.StdChart

end
