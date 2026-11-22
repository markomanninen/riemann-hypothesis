module

public import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.QuotCop
public import Development.EtaleCohomology.EtaleSheaves.SpectrumLimits.TensCop

@[expose] public section

namespace LateralTheory.E.LevelsGenPf

theorem LevelsGen_of_specLim (hS : SpecLim) : LateralTheory.E.LevelsPf.LevelsGen := LevelsGen_of tensCop quotCop hS

end LateralTheory.E.LevelsGenPf
