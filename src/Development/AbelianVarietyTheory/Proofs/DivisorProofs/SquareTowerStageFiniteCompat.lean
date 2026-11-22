module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsThOEqOfIsLatVacThetaFun
public import Development.AutomorphicArithmetic.DivisorFrames.IsSBHalfThetaFunOfHalfIdempotentPlaces
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsGlStdFstEqProductLocal
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsGlStdSndEqProductLocal
public import Development.AutomorphicArithmetic.DivisorFrames.BigPStdSchwartzTranslateEqSmallPOfIsUnif
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsPolynomialOfIsFinFThetaLiftPureTensor
public import Development.AutomorphicArithmetic.DivisorFrames.IdempotentSumFixesIffHalfEl
public import Development.AutomorphicArithmetic.DivisorFrames.StdAStdBMemSchwartzBruhat
public import Development.AutomorphicArithmetic.DivisorFrames.ExistsLatticeThetaDataOfRamificationPlacesCMDatu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartFrSgnFalseRigFr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridSquareInfinityExponentGapLargeGridsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageFinitePlacesUnramifiedOrSplit
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockAlgebraicThetaVectorsStableFiniteAdelesLieStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawFramesWeilEquivalence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilIntertwiningValue
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilLocalFactorEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilArchimedeanFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanOneParamLineTransposeGramUnitarStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealLieOperatorThetaQuotientLineStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DarbouxModelAlgebraicVectorsLeAdelicSchwartzStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilFactorization
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLineOperatorPolynomial
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionLineOperatorSum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaIdentity
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilGlobalFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivOfKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerStageSeesawDictionaryFramesSignatures

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.StageFinNonzero

theorem gBig_of_two {Q₁ Q₂ Q₃ : GlobalTheory.SqTop.GP} (h₁ : GlobalTheory.SqTop.GBig Q₁) (h₂ : GlobalTheory.SqTop.GBig Q₂)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q₁ G μ₀ C x b → Q₂ G μ₀ C x b → Q₃ G μ₀ C x b) : GlobalTheory.SqTop.GBig Q₃ := by
  obtain ⟨a₁, h₁⟩ := h₁
  obtain ⟨a₂, h₂⟩ := h₂
  refine ⟨max a₁ a₂, fun ε CF hCF => ?_⟩
  obtain ⟨C₁, x₁, h₁⟩ := h₁ ε CF (le_of_max_le_left hCF)
  obtain ⟨C₂, x₂, h₂⟩ := h₂ ε CF (le_of_max_le_right hCF)
  exact ⟨max C₁ C₂, max x₁ x₂, fun C hC D large₂ he hx r T Lc μ hLc G =>
    H G μ C _ _ (h₁ C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) r T Lc μ hLc G)
      (h₂ C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) r T Lc μ hLc G)⟩

end GlobalTheory.StageFinNonzero
