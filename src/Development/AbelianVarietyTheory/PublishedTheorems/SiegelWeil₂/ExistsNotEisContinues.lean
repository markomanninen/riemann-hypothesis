module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
public import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SiegelWeilAnisotropicUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBoundedUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasureFundamentalDomainLtTop
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsEtaTildeUnramified
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
public import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters

@[expose] public section

noncomputable section

open scoped ComplexConjugate Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Filter Topology Set Metric MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Cont

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Eis.ContModel

variable {D : D7} {V : HSp D} {a : GL (Fin V.rank) (AE D)} {μ : (AE D)ˣ →* Circle} {s₁ : ℂ} {φ : GA D (dblSp V) → ℂ}

theorem isEisFamily_flat (ha : IsMaj V a) (hμ : IsHeckeChar D μ) (hφ : φ ∈ degPS V a μ s₁) :
    IsEisFamily V (flat V a φ s₁) :=
  have hI := GlobalTheory.Core.Rk.IP.hasIwasawa_Khat D V a ha
  (sphConv D V a hI).isEisFamily_flat hI hφ hμ

end GlobalTheory.Eis.ContModel

end
