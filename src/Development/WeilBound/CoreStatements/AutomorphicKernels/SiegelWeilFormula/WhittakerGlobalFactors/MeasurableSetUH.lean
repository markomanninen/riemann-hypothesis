module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicMeasureEulerProductDecomposition
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualHermMeasures
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsUnitScalingSelfdualAdelicMeasures
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsLocalApproximateIdentity
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarPiRestrictedProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarSplitsArchTimesFiniteStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelEisensteinUnfoldingIdentity

@[expose] public section

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def UH (σ : E →ₐ[F] E) {d : ℕ} (bs : Module.Basis (Fin d) F E) (n : ℕ) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Set (HermR (AF F) σ n) :=
  {b | hermFin σ b ∈ intH σ bs n S}

theorem measurableSet_UH (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (bs : Module.Basis (Fin d) F E) (n : ℕ)
    (S : Finset (HeightOneSpectrum (𝓞 F))) : MeasurableSet (UH σ bs n S) :=
  GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.measurableSet_intH σ bs S

end PositivityTheory.SiegelWeilFormula.GFac

end
