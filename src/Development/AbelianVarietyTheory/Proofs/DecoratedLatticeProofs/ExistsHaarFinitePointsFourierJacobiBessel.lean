module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumTransportSourceRationalIsometry
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProduct
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PairForm
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TailRd
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqZeroOfRootOfSUnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.HaarExist

theorem haar_exists : ∀ (D : D7) (V : HSp D), (∃ μ : Measure (GfC V), μ.IsHaarMeasure) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), (∃ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∃ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure := by
  intro D V
  have hf := GlobalTheory.AdelicSplit.isClosed_GfC' V
  haveI : LocallyCompactSpace (GfC V) := hf.locallyCompactSpace
  refine ⟨⟨Measure.haar, inferInstance⟩, fun V₀ ρ d => ⟨?_, fun A L o => ?_⟩⟩
  · have hJ := GlobalTheory.jacGrp_isClosed D V V₀ ρ d
    have hc : IsClosed (((jacGrp d).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hJ.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((jacGrp d).subgroupOf (GfC V)) := hc.locallyCompactSpace
    exact ⟨Measure.haar, inferInstance⟩
  · have hB := GlobalTheory.BesClosed.besGrp_isClosed D V V₀ A L ρ d o
    have hc : IsClosed (((besGrp d o).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) :=
      hB.preimage continuous_subtype_val
    haveI : LocallyCompactSpace ((besGrp d o).subgroupOf (GfC V)) := hc.locallyCompactSpace
    exact ⟨Measure.haar, inferInstance⟩

end GlobalTheory.HaarExist
