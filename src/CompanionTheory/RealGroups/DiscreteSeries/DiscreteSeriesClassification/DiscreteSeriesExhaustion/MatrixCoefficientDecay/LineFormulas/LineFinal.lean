module

public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineFacts
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FubiniParabolicMultiple
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineFormulaOfFubiniAndParabolic

@[expose] public section

namespace CompanionTheory.RgExh.Dec.N.S

theorem line_formula : CompanionTheory.RgExh.Dec.L.LineFormula :=
  GlobalTheory.CompanionTheory.RgLineFormula.lineFormula
    GlobalTheory.CompanionTheory.FubNM.fub2
    GlobalTheory.CompanionTheory.GradLine.lineFacts
    GlobalTheory.CompanionTheory.PSubFlag.psubEq

end CompanionTheory.RgExh.Dec.N.S
