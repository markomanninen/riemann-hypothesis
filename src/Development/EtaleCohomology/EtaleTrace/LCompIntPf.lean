module

public import Development.EtaleCohomology.EtaleTrace.LCompDecPf
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LateralTheory.EtaleTrace

theorem LCompInt_of : LCompInt := by
  intro k _ _ d X p hp hc
  have := hp.2
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  exact GlobalTheory.isIntegral_of_smooth_field_of_connectedSpace p

end LateralTheory.EtaleTrace
