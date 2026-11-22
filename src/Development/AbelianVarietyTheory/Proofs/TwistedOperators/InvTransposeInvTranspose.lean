module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilTensorLiftConclusion
public import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantCosetInd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmIndCoinvariants

@[expose] public section

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.OpTrace Matrix
open scoped TensorProduct

namespace GlobalTheory.LocalThetaGL

section Abstract

variable {H V W U Y Γ : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup Y] [Module ℂ Y] {P : Subgroup H}

end Abstract

section Regular

variable {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [MeasurableSpace G] [BorelSpace G] (ν : Measure G) [ν.IsHaarMeasure] {π : Representation ℂ G V}

end Regular

section Local

open GlobalTheory.IndefiniteRowSideFullHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {V Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]

theorem compact_open_basis (n : Type) [Fintype n] [DecidableEq n] : ∀ U ∈ nhds (1 : GL n k),
    ∃ K : Subgroup (GL n k), IsOpen (K : Set (GL n k)) ∧ IsCompact (K : Set (GL n k)) ∧ (K : Set (GL n k)) ⊆ U := by
  intro U hU
  obtain ⟨J, h1, h2, h3, -⟩ := exists_open_normalised_subgroup_subset k n U hU
  exact ⟨J, h1, SplitFlip.isCompact_KO.of_isClosed_subset (J.isClosed_of_isOpen h1) h3, h2⟩

end Local

section Main

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Published

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Main

section Final

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.Published

variable {G V W Y : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


end Final

end GlobalTheory.LocalThetaGL
