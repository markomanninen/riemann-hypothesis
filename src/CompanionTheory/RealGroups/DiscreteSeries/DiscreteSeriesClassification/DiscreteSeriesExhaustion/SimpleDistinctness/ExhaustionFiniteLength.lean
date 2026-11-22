module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ScalarOfCommute
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteDimensionalComapSubtype
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.GoodPathReplicate
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.PathEndEqAddNat
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SimpleDistinct
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ScalarOfSeparatingSmoothL2Maps
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.UnitarizableOfSeparatingSmoothL2Maps
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.IsWeightOfIntertwine
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsPermOfCapPEq
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsIsoOfHighest
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestRenumber
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ContinuousUnitsRenSymm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KHighestOfPerm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.KModOf
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsUniqueParam
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharOfScalChar

@[expose] public section

namespace CompanionTheory.RgExh.Fin

theorem exhaustion_finite_length : CompanionTheory.RgExh.Finish :=
  GlobalTheory.CompanionTheory.RgExhFin.finish
    GlobalTheory.CompanionTheory.RgStart.startMod
    GlobalTheory.CompanionTheory.RgSteps.pathFin
    GlobalTheory.CompanionTheory.RgPath.pathExists
    GlobalTheory.CompanionTheory.RgPath.pathEndNat
    GlobalTheory.CompanionTheory.RgExhFin.simpleDistinct
    GlobalTheory.CompanionTheory.AdjointSignNormality.scalar_of_separating_smooth_l2_maps
    GlobalTheory.CompanionTheory.RgExhFin.unitarizable_of_separating_smooth_l2_maps
    GlobalTheory.CompanionTheory.RgIso.isoFacts
    GlobalTheory.CompanionTheory.CharOfLowK.charOfAlgDS
    GlobalTheory.CompanionTheory.LowestDataIso.algUniq
    GlobalTheory.CompanionTheory.LowestData.dataUniq
    GlobalTheory.CompanionTheory.RenumDS.dsOfArr
    GlobalTheory.CompanionTheory.DSData.dsOfData
    GlobalTheory.CompanionTheory.KModOfStep.kModOf
    GlobalTheory.CompanionTheory.ArrCount.arrCount

end CompanionTheory.RgExh.Fin
