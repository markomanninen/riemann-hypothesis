module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrablePowerNormCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarModulusOfUnitCompletionsAtPlacesEqProdNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRestrictScalarsMatrixLeftRightMulAdeleTens

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.LemF.QuotInv

open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (tensNU)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem continuous_compFinV (v : HeightOneSpectrum (𝓞 F)) : Continuous (compFin F E v) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  exact GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
    ((RestrictedProduct.continuous_eval v).comp continuous_snd)


end GlobalTheory.ThK.LemF.QuotInv

end
