module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutive
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReducibleCuspidalPairNongenericSubquotientStatement
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPhiMinusExact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPsiMinusExact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPhiMinus
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPsiMinus
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjacentQuotientOfTwoSegment
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibRepApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteTwistedRankQuotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OmegaEquivInducedFibreStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviIntegralFacts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenNormalisedSubgroupSubset
public import GroundTheory.AutomorphicForms.FiniteLengthLattice
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmoothStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspStdSubGeneric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetPhiMinusEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionMirabolicTwistedKernel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalPairSubGeneric
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IrreducibleSubquotientParabolicProductTwoFiniteL
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideMore
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientPreservesSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIrrRepInjectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingTwistedDeterminantSubquotientStatement

@[expose] public section

noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir Zc

namespace GlobalTheory.CompanionTheory.BZCuspPair

section Proofs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nontrivial_of_irr {G : Type} [Group G] [TopologicalSpace G] (τ : IrrRep G) : Nontrivial τ.V := by
  have hi := τ.irr
  by_contra hs
  rw [not_nontrivial_iff_subsingleton] at hs
  apply (bot_ne_top : (⊥ : Subrepresentation τ.ρ) ≠ ⊤)
  apply Subrepresentation.ext
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => zero_mem _, fun _ => zero_mem _⟩

theorem continuous_inv_addChar (ψ : AddChar k Circle) (hc : Continuous ψ) : Continuous (ψ⁻¹ : AddChar k Circle) := by
  have : (⇑(ψ⁻¹ : AddChar k Circle)) = fun a => ψ (-a) := funext fun a => AddChar.inv_apply ψ a
  rw [this]
  exact hc.comp continuous_neg

end Proofs

end GlobalTheory.CompanionTheory.BZCuspPair
