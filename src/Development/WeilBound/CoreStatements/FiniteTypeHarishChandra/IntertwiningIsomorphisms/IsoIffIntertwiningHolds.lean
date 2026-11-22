module

public import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.ConjugateCharacterFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducibleStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralIdempotentPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceCompLeftFunLeft
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.FrobeniusSumFormula
public import GroundTheory.AutomorphicForms.FiniteBruhat
public import Formalism.PadicSubsetSums.CentralIdempotents.IsConstituent
public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducible
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Simple
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalWhittaker
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalOfUnipotentSumsVanishStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCuspidalWithLabelStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalLabelUniqueStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalParametrization

@[expose] public section

open Polynomial CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace ReciprocityTheory.Ty.Fin

section Gen

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem isIrr_of_simple (τ : FDRep ℂ Γ) [h : Simple τ] : IsIrr τ.ρ := (GlobalTheory.T.simple_iff_irreducible.1 Γ τ).1 h

theorem zIdemIdemCentral_holds (Γ : Type) [Group Γ] [Fintype Γ] (τ : FDRep ℂ Γ) (hτ : Simple τ) :
    zIdem τ * zIdem τ = zIdem τ ∧ ∀ a, zIdem τ * a = a * zIdem τ := GlobalTheory.T.central_idempotent_properties.1 Γ τ hτ

theorem zIdemOrthogonal_holds (Γ : Type) [Group Γ] [Fintype Γ] (τ σ : FDRep ℂ Γ) (hτ : Simple τ) (hσ : Simple σ)
    (h : ¬ Nonempty (τ ≅ σ)) : zIdem τ * zIdem σ = 0 := GlobalTheory.T.central_idempotent_properties.2.1 Γ τ σ hτ hσ h

end Gen

section GeneralLinearIntegers

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]






end GeneralLinearIntegers

end ReciprocityTheory.Ty.Fin
