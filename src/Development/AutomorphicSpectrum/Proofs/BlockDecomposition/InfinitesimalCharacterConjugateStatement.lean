module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugate
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RegularAlgebraicPurityOfClozel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsEqMulMultOfUnits
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitesimal_character_conjugate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ), IsHerm π B → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), π.HasInfChar τ m → π.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m' → m' = m.map fun z => -(starRingEnd ℂ) z := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq | exact GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq | (intros; apply GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq <;> assumption)
