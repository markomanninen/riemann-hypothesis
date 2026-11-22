module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHolomorphyOfHeights
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_holomorphy_of_heights : HtExist → EisHol := by
  first | exact @GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist | exact GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist | (intros; apply GlobalTheory.CompanionTheory.EisHolFam.eisHol_of_htExist <;> assumption)
