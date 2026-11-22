module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HypothesesX
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.LiteralAutomorphy

namespace GlobalTheory.SerStdFit

theorem seriesRat_of_seriesRatS : GlobalTheory.SerStd.SeriesRatS → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat := fun h => h

end GlobalTheory.SerStdFit
