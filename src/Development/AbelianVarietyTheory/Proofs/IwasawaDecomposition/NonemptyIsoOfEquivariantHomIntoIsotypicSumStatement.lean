module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyIsoOfEquivariantHomIntoIsotypicSum
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockFrameConjugationIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKilledEqOfEqualMultiplicitiesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqual

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_iso_of_equivariantHom_into_isotypicSum : ∀ (H S0 S X : Type) [Group H] [AddCommGroup S0] [Module ℂ S0] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X] (σ0 : Representation ℂ H S0) (σ : Representation ℂ H S) (ρ : Representation ℂ H X) (C : Submodule ℂ X), σ0.IsIrreducible → σ.IsIrreducible → ∀ f ∈ homInto σ ρ (⨆ g ∈ homInto σ0 ρ C, LinearMap.range g), f ≠ 0 → Nonempty (σ.asModule ≃ₗ[MonoidAlgebra ℂ H] σ0.asModule) := by
  first | exact @GlobalTheory.IsoRankMult.iso_of_hom_into_sum | exact GlobalTheory.IsoRankMult.iso_of_hom_into_sum | (intros; apply GlobalTheory.IsoRankMult.iso_of_hom_into_sum <;> assumption)
