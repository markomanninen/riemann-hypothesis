module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicD
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinOfRest
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomial
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaVanishing
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairListAction

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LineDerivSplit

theorem pure_add₀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul₀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pure_listSum {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} (l : List ι)
    (h : ι → SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (l.map h).sum φ = (l.map fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (h i) φ).sum := by
  induction l with
  | nil => funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  | cons a l ih => simp [pure_add₀, ih]

theorem sum_listSum {α ι : Type} [AddCommMonoid α] {m : ℕ} (l : List ι) (a : Fin m → ι → α) :
    ∑ j, (l.map (a j)).sum = (l.map fun i => ∑ j, a j i).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [Finset.sum_add_distrib, ih]

end GlobalTheory.LineDerivSplit
