module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
public import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BzfinHolds
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharInCuspidalSupportOfJacquetSubquotientFactor
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthFilterFinRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricLemmaFiltrationHolds
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaOfFiltration
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StdMaxParabolicRadicalLeBlockUnipotentRadical
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBijectiveOfIsSubquotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot

@[expose] public section

noncomputable section

namespace GlobalTheory.ReducedFactor

section General

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem nontrivial_of_irr {ρ : Representation ℂ G V} (h : ρ.IsIrreducible) : Nontrivial V := by
  have : IsSimpleOrder (Subrepresentation ρ) := h
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext x
  rw [Subsingleton.elim x 0]
  exact iff_of_true (zero_mem _) (zero_mem _)

end General

section Tensor

variable {G H V V' U : Type} [Group G] [Group H] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
  [AddCommGroup U] [Module ℂ U]

end Tensor

end GlobalTheory.ReducedFactor

namespace GlobalTheory.ReducedFactor

end GlobalTheory.ReducedFactor
