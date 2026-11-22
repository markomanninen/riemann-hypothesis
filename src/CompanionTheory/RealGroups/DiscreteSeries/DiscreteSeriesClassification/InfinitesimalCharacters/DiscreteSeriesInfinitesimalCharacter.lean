module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InfinitesimalCharacters.DsInfCharOf
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceElementsActByGelfandValues
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitActGlRel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapQdetEtr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EwordCoef
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumCycWordEqEtr
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KFinSmoothBoth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsDSSkImpUpqRep
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefSmoothOnG

@[expose] public section

namespace CompanionTheory.RgDsInf

theorem dsInfChar' : GlobalTheory.Dec.DSInfChar :=
  dsInfChar_of
    (fun V _ _ => GlobalTheory.CompanionTheory.CapelliGelfand.etr_eq_gelfVal_of_capelli V)
    GlobalTheory.CompanionTheory.SmoothVecGl.unitAct_glRel
    GlobalTheory.CompanionTheory.CapelliMap.map_qdet_etr
    GlobalTheory.CompanionTheory.CoefWord.eword_coef
    GlobalTheory.CompanionTheory.CycWordTrace.sum_cycWord_eq_etr
    GlobalTheory.CompanionTheory.KFinSmoothBoth.kFin_smooth_both
    GlobalTheory.CompanionTheory.DiscreteSeries.isDS_sk_imp_upqRep
    GlobalTheory.CompanionTheory.CoefSmooth.coef_smooth
    CompanionTheory.D.DSIC.discrete_series_infinitesimal_character

end CompanionTheory.RgDsInf
