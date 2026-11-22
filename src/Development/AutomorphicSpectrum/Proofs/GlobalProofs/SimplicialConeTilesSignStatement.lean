module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SimplicialConeTilesSign
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup

@[expose] public section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicial_cone_tiles_sign : ∀ {V : Type} [AddCommGroup V] [Module ℚ V] (P : ConvexCone ℚ V) (l : V →ₗ[ℚ] ℚ) (s : Finset V), LinearIndepOn ℚ id (s : Set V) → (s : Set V) ⊆ P →
    Tile (P : Set V) (SignConst l) (coneOn s) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign.main | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign.main | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones.TileSign.main <;> assumption)
