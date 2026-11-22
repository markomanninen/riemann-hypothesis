module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedCechCohomologyFinite
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
theorem _root_.GlobalTheory.T.graded_cech_cohomology_finite : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GlobVanSt → ∀ {O : Type} [CommRing O] [IsNoetherianRing O] (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < s) (p : ℕ),
    Module.Finite O ((cechH (sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1)))
      (fun α => St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {U.U α}) r).cx.H p) := by
  first | exact @GlobalTheory.CompanionTheory.GrCech.main_thm | exact GlobalTheory.CompanionTheory.GrCech.main_thm | (intros; apply GlobalTheory.CompanionTheory.GrCech.main_thm <;> assumption)
