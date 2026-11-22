module

public import Mathlib
public import Formalism.LocalRingCardinality.HeightBoundGeFourthPowerRank
public import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
public import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift Formalism.IndefR.Links
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def SplitsCompletely (D : D7) (p : ℕ) : Prop :=
  p.Prime ∧ ∀ w : HeightOneSpectrum (𝓞 D.host.E), (p : 𝓞 D.host.E) ∈ w.asIdeal →
    Ideal.absNorm w.asIdeal = p ∧ (p : 𝓞 D.host.E) ∉ w.asIdeal ^ 2

def PsiUnramAt (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  ∀ α : Af D.host.F, (∀ v', v' ≠ v → evalV D.host.F v' α = 0) →
    ((∀ β ∈ intAf D.host.F, ψ (pairA D.host.F 0 (α * β)) = 1) ↔
      evalV D.host.F v α ∈ v.adicCompletionIntegers D.host.F)

def SideCond (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) : Prop :=
  IsSplit (E := D.host.E) v ∧ (2 : 𝓞 D.host.F) ∉ v.asIdeal ∧ PsiUnramAt ψ v ∧
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → w.valuation D.host.E D.host.xi0 = 1

def excluded (q t : ℕ) : Set ℂ :=
  {(((q : ℝ) ^ (((t : ℝ) - 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) - 1) / 2)) : ℝ) : ℂ),
    (((q : ℝ) ^ (((t : ℝ) + 1) / 2) : ℝ) : ℂ), (((q : ℝ) ^ (-(((t : ℝ) + 1) / 2)) : ℝ) : ℂ)}

section Cusp

variable (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]

variable {V ν} {W : Submodule ℂ (DividedPowerChartLift V ν)}


end Cusp

section Chain

variable (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ)
  (th : ∀ k, GA D (Yc D k) → GA D (Yc D (k + 1)) → (WO (Yc D k) (Yc D (k + 1)) → ℂ) → ℂ)
  (ν : ∀ k, Measure (GA D (Yc D k))) [∀ k, (ν k).IsHaarMeasure] [∀ k, (ν k).IsMulRightInvariant]
  (𝓕 : ∀ k, Set (GA D (Yc D k))) (σ : Submodule ℂ (DividedPowerChartLift (Yc D 0) (ν 0)))

end Chain

end GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains

end
