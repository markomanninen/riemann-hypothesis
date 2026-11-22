module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConsequencesOfDsClass
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesOfHasParamCoverStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParamCoverDiscreteSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoverDiscreteSeriesUnitarilyEquivOfSameParamStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroupStatement

@[expose] public section

open Formalism.BasicNotions.TH GlobalTheory.RealPar

noncomputable section

namespace GlobalTheory.CoverDS

theorem discreteSeriesCover_of_classification :
    GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.DiscreteSeriesCover := by
  intro hcl
  obtain ⟨hExists, hExhaust, hUnique, hInfChar, hLowK, hKTypes, -⟩ :=
    GlobalTheory.ClassificationConsequences.consequences_of_dsClass
      (GlobalTheory.Published.discreteSeriesClassification_iff.1 hcl)
  have hC : GlobalTheory.Published.DiscreteSeriesCoverExists :=
    GlobalTheory.Published.CoverSeries.of_upq
      (GlobalTheory.Published.discreteSeriesUpqExists_iff_dsExists.2 hExists)
      (fun p q h T U hU => ((GlobalTheory.T.harishChandraModules_indefiniteUnitaryGroup.1 p q h T).1 U hU).2.1)
  intro p q hn T
  choose D hD using fun lam : {lam : Ix p q → ℚ // IsParam lam} => hC p q T lam.1 lam.2
  refine ⟨D, ?_, ?_⟩
  · intro lam
    exact GlobalTheory.T.hasDiscreteSeriesKTypes_of_hasParam_cover
      hLowK hKTypes hInfChar p q hn T (D lam) lam.1 lam.2 (hD lam)
  · intro R
    obtain ⟨lam, hl, hR⟩ := GlobalTheory.T.exists_param_coverDiscreteSeries hExhaust p q hn T R
    exact ⟨⟨lam, hl⟩, GlobalTheory.T.coverDiscreteSeriesUnitarilyEquiv_of_sameParam
      hUnique p q hn T R (D ⟨lam, hl⟩) lam hl hR (hD ⟨lam, hl⟩)⟩

end GlobalTheory.CoverDS

end
