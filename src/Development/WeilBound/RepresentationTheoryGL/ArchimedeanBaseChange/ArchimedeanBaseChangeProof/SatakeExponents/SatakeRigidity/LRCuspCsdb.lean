module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.ThetaOfCsdR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehDataUnique
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitAtOfIsSplitPl
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PInfAsc
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PStagesB
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.AllPlaceRigidityResidual
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetOfStringsDeterminesPointsDegrees
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugate
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatakeOfIsLocComp
public import Formalism.LocalToGlobal.PlaceMapInjectivity.MapPlInjective

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig.B

open PositivityTheory.Rg.BcB.F

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem infChar_conj {a : ℕ} (P : CuspSub E a) (hn : IsNormalised P) (τ : E →+* ℂ) (m m' : Multiset ℂ)
    (hm : P.HasInfChar τ m) (hm' : P.HasInfChar (ComplexEmbedding.conjugate τ) m') :
    m' = m.map fun z => -(starRingEnd ℂ) z := by
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E a
  have := h1
  have := h2
  obtain ⟨B, hB⟩ := GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm GlobalTheory.CompanionTheory.CuspFinGL.cuspFormsBoundedGL E a μ P hn
  exact GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq E a P B hB τ m m' hm hm'

end PositivityTheory.Rg.BcB.F.Rig.B

end
