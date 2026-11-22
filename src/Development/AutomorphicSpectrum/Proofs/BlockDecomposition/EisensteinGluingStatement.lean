module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinGluing
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.IwasawaUnipotent.IwaU

@[expose] public section

open PositivityTheory.Rg.SwEis
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_gluing : Glue := by
  first | exact @GlobalTheory.CompanionTheory.PolyDenominator.glue | exact GlobalTheory.CompanionTheory.PolyDenominator.glue | (intros; apply GlobalTheory.CompanionTheory.PolyDenominator.glue <;> assumption)
