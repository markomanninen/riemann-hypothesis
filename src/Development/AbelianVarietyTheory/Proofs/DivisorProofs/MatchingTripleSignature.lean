module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatInOfUnit
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightTranslate
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelLeftInvariantRationalUnitary
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoCptOfIsAnisoOrPosDef
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairVrGramPRatPosDef
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralDefiniteSourceConvergesContinuousInStatement
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MassFormulaPositivity
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsStdIsVacVec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupFockOrbitFiniteDimensionalStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.DefIrred

theorem integrable_algF {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {M X : HSp D} (A : GlobalTheory.ChainFr.Fr M) (B : GlobalTheory.ChainFr.Fr X) {χ χ' : (AE D)ˣ →* Circle} {ω : GlobalTheory.Grid.WRep M X}
    (hω : GlobalTheory.Grid.IsWeil ψ false M X χ χ' ω) (hs : ∀ τ, Formalism.UG.HasSignature (gramAt D M τ) M.rank 0)
    {ν : Measure (GA D M)} {𝓕 : Set (GA D M)} (hν : IsHaarFD M ν 𝓕) :
    ∀ Φ ∈ algF ψ θ false A B, ∀ h, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν := by
  intro Φ hΦ
  have hth : IsThetaFunO ψ (GlobalTheory.Grid.sgn false M) X Φ := by
    induction hΦ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, P, hf, rfl⟩ := hx
      exact GlobalTheory.Chain.InnerSteps.theta_pureTensorO hψ hθ _ _ _ _ hf.1 P
    | zero => exact GlobalTheory.OrientedHeis.theta_zero
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul c hx
  exact (GlobalTheory.T.thetaIntegral_definiteSource_converges_continuous_invariant D ψ false M X χ χ' ω ν 𝓕 Φ hω (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.posDef_of_hasSignature (hs τ)) hν.1 hν.2
    hth).1

end GlobalTheory.DefIrred

end
