module

public import Mathlib
public import CompanionTheory.RealGroups.GeneralUnitaryRepresentations.ArchimedeanJacquetSegments.SegmentSubquotients.SegTwo
public import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.ZelevinskyClassification.ZelevinskySegments.SegDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EquivOfMultiplicityOneUniqueFactor
public import CompanionTheory.AutomorphicTheory.SegmentRepresentations.IrreducibleSegments.IsIrreduciblePiTensorSegTerm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SocleOfMultiplicityOne
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjective
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.JacquetMultiplicityPosOfSocle
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult GlobalTheory.Published GlobalTheory.SegmentRepModel

namespace CompanionTheory.Pf1.SegRepC.SegTwo

def RhoNuRhoReducible : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d : ℕ), 0 < d → ∀ σ : IrrRep (GL (Fin d) k), IsCuspidal σ.ρ →
      ¬ (multiProd (consecBlocks 2 d) (segTerm σ.ρ 2)).IsIrreducible

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def revTensor {d : ℕ} (σ : IrrRep (GL (Fin d) k)) :=
  piTensor fun a : Fin 2 => segTerm σ.ρ 2 a.rev



end CompanionTheory.Pf1.SegRepC.SegTwo

end
