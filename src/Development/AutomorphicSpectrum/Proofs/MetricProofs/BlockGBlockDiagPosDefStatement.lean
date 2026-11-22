module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.BlockGBlockDiagPosDef
public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.RootOnFund
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ContDiffUncentre
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG

@[expose] public section

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockG_blockDiag_posDef : ∀ (p q : ℕ) (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ), Γ.PosDef → IsBlockDiag p (blockG Γ) ∧ (blockG Γ).PosDef := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef | exact GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.BMx.blockG_isBlockDiag_posDef <;> assumption)
