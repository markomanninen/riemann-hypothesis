module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
public import Formalism.LocalToGlobal.IndefiniteReal.MultLemmas
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSumOfMemMultSpan

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

structure IsLocSub (τ : D.what₂.Tau) (B : Submodule ℂ (GA D V → ℂ)) : Prop where
  k : ∀ g, GlobalTheory.CuspGK.InK M τ g → ∀ f ∈ B, rTr V (atTau θ V τ g) f ∈ B
  lie : ∀ X ∈ lieAt V τ, ∀ f ∈ B, Rder θ V τ X f ∈ B

def locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : Submodule ℂ (GA D V → ℂ) :=
  sInf {B | ψ ∈ B ∧ IsLocSub θ M τ B}

theorem mem_locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : ψ ∈ locGen θ M τ ψ :=
  Submodule.mem_sInf.2 fun _ h => h.1

theorem isLocSub_locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : IsLocSub θ M τ (locGen θ M τ ψ) := by
  constructor
  · intro g hg f hf
    exact Submodule.mem_sInf.2 fun B hB => hB.2.k g hg f (Submodule.mem_sInf.1 hf B hB)
  · intro X hX f hf
    exact Submodule.mem_sInf.2 fun B hB => hB.2.lie X hX f (Submodule.mem_sInf.1 hf B hB)

theorem locGen_le {τ : D.what₂.Tau} {ψ : GA D V → ℂ} {B : Submodule ℂ (GA D V → ℂ)} (hψ : ψ ∈ B)
    (hB : IsLocSub θ M τ B) : locGen θ M τ ψ ≤ B :=
  sInf_le ⟨hψ, hB⟩

end GlobalTheory.CuspGKId

end
