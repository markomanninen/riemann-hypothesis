module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.ImportsAlt

@[expose] public section

namespace GlobalTheory

theorem semiAbelianHomExtension_holds : GlobalTheory.Published.SemiAbelianHomExtension :=
  GlobalTheory.CompanionTheory.SAH.semiAbelianHomExtension

end GlobalTheory
