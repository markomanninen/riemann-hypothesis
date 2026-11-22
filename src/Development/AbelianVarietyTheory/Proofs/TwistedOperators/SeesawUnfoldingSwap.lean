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
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanOneParamEqProdCmTypeLinesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairListProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPairReading
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaTransformDarbouxModelLinearInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinOfRest
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineGoodModelPolynomial
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
namespace GlobalTheory.LineKillV

theorem isDatum_list_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd}
    {ψ : AddChar (AF F) ℂ} {Z : Type} {crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) → Z}
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) {ι : Type} (l : List ι) (Ψ : ι → (Fin n × Fin d → AF F) → ℂ) (f : ι → Z → ℂ)
    (h : ∀ i, IsDatum M ψ crd (Ψ i) (f i)) : IsDatum M ψ crd (l.map Ψ).sum (l.map f).sum := by
  induction l with
  | nil => simpa using (GlobalTheory.SquareAgree.CoinvPass.isDatum_zero (M := M) (ψ := ψ) (crd := crd))
  | cons a l ih => simpa [List.map_cons, List.sum_cons] using GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ (h a) ih

end GlobalTheory.LineKillV

end
