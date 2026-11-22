module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBlockMatrixTwoByTwoFinEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GlobalUnitScalingHaarProductFormula
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockMatrixTwoByTwoFinTranspose
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
public import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocallyConstantSplitOm
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianInvariantFormsProportionalFinitePlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatAnyCharacter
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictedProductMemSchwartz
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EventuallyLocalLatticeCompletionEqCoordinateLatt
public import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStdMulShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlace

@[expose] public section

open scoped Matrix NNReal TensorProduct
open MeasureTheory NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.WeilM GlobalTheory.LocIntw
open GlobalTheory GlobalTheory.LFun GlobalTheory.ThK GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.SWLit

noncomputable section
namespace GlobalTheory.AwayFix.Chart

open GlobalTheory.AwayFix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_smul_away (v : HeightOneSpectrum (𝓞 F)) (a : AF F) (z : AF F ⊗[F] E) :
    compFin F E v (a • z) = evFin F v a • compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evFin F v) a b)
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem compInf_smul_away (w : InfinitePlace F) (a : AF F) (z : AF F ⊗[F] E) :
    compInf F E w (a • z) = evInf F w a • compInf F E w z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul b x => exact congrArg (· ⊗ₜ[F] x) (map_mul (evInf F w) a b)
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

variable {σ : E →ₐ[F] E} {N : ℕ} {Q : Matrix (Fin N) (Fin N) E}

end GlobalTheory.AwayFix.Chart

namespace GlobalTheory.AwayFix

open GlobalTheory.AwayFix.Chart

end GlobalTheory.AwayFix
