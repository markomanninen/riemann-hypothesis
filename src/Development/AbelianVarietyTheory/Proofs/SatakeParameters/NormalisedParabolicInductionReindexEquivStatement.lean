module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormalisedParabolicInductionReindexEquiv
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInSupportOfMultiProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleTensorOfJacquetSubquotient
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSphericalTwistOfJacquetConstituentEmptyBlock

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedParabolicInduction_reindex_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (α : Type) [Fintype α] [LinearOrder α] (m : α → Type) [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (e : (Σ a, m a) ≃ n) (ψ : n ≃ n')
    (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Levi k m) W),
    Nonempty ((parInd e ρ).Equiv ((parInd (e.trans ψ) ρ).comp (GlobalTheory.EmptyFirstBlock.reindexGL (R := k) ψ))) := by
  first | exact @GlobalTheory.SmGL.Relabel.parInd_reindex | exact GlobalTheory.SmGL.Relabel.parInd_reindex | (intros; apply GlobalTheory.SmGL.Relabel.parInd_reindex <;> assumption)
