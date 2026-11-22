module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.GlobalTheory.BernsteinZelevinskyFiniteness

@[expose] public section

namespace GlobalTheory.Laid

theorem bzfin_holds : GlobalTheory.Published.BernsteinZelevinskyFiniteness := by
  intro k _ _ _ _

  exact ⟨CompanionTheory.SmGLBridge.irreducibleAdmissible k, CompanionTheory.JacquetBridge.jacquetFiniteLength k,
    CompanionTheory.BZInd.inductionFiniteLength k, SmGL.IndDual.inductionContragredient k⟩

end GlobalTheory.Laid
