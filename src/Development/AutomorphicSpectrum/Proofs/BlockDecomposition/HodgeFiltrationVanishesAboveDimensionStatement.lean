module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFiltrationVanishesAboveDimension
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCohomologyRestrictionBijectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CohomologyVanishingAlongIdealFiltrationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClassStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequenceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverCohomologyFiniteStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechVanishingFromCoverStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmoothCoordinateCoverStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphismStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenFiniteInfIffStatement

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_filtration_vanishes_above_dimension : KH.LocGr → KH.LocVan → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → KH.KIso → KH.GrAff → ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsProper q] (d : ℕ)
    [SmoothOfRelativeDimension d q] (j : ℕ), ∀ x ∈ FilR q j (d + 1), x = 0 := by
  first | exact @GlobalTheory.CompanionTheory.FilTop.fil_top_vanish | exact GlobalTheory.CompanionTheory.FilTop.fil_top_vanish | (intros; apply GlobalTheory.CompanionTheory.FilTop.fil_top_vanish <;> assumption)
