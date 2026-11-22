module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteOnCompactsOrbitMeasureStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureConcentratedOnQuadricStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureTranslationInvariantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureGLRightScalingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LawOfOrbitMeasureStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureUnitaryGroupInvariantStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitMeasureIntegralPointsNonzeroStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainPropertyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrbitFinitenessOfLatticeBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFrameIdentitiesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbscissaConvergenceIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedProjectionFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinedBlockFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExtensionByZeroOrbitFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentShiftInvarianceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedSectionLocalIntegrabilityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedIntegralsFourFactorsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelProductStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelFibersStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOrbitalIntegralUnipotentStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetNeZeroOfGramNondegenerateStatement

@[expose] public section

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.CompanionTheory.ColumnSplitting

namespace GlobalTheory.CompanionTheory.ColumnSplitting

theorem main : IdemEx → LatBound → QK → IkSch → ThetaSideMeasure := by
  intro _ hLat hQK hIk D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx
  have hdx := GlobalTheory.T.det_ne_zero_of_gram_nondegenerate D W b₀ hb x₀ hx
  have hDom := GlobalTheory.T.fundamental_domain_property
  have hOF := GlobalTheory.T.orbit_finiteness_of_lattice_bound hLat
  have hZ := GlobalTheory.T.zeta_polynomial_identity
  have hA := GlobalTheory.T.abscissa_convergence_identity
  have hJ := GlobalTheory.T.joined_projection_formula
  have hB := GlobalTheory.T.joined_block_formula
  have hE := GlobalTheory.T.extension_by_zero_orbit_formula
  have hS := GlobalTheory.T.unipotent_shift_invariance
  have hL := GlobalTheory.T.induced_section_local_integrability
  have hF := GlobalTheory.T.iterated_integrals_four_factors
  refine ⟨nuT hn I μ x₀, ⟨GlobalTheory.T.finite_on_compacts_orbit_measure D n t B W d hn I μ hμ b₀ hb x₀ hx, GlobalTheory.T.orbit_measure_concentrated_on_quadric hZ hA D n t B W d hn I μ hμ b₀ hb x₀ hx,
    fun h _ => GlobalTheory.T.orbit_measure_unitary_group_invariant hQK GlobalTheory.T.law_of_orbit_measure D n t B W d hn I μ hμ x₀ h,
    fun y _ => GlobalTheory.T.orbit_measure_translation_invariant D n t B W d hn I μ hμ x₀ y,
    fun g _ => GlobalTheory.T.orbit_measure_GL_right_scaling D n t B W d hn I μ hμ x₀ g⟩,
    GlobalTheory.T.orbit_measure_integral_points_nonzero D n t B W d hn I μ hμ x₀, fun Φ hΦ η hη => ?_⟩
  have hc := GlobalTheory.T.integrable_theta_kernel_product hIk hDom hOF hS hL hF hB D n t B W d hn I θ hθ μ hμ x₀ hdx Φ hΦ η hη
  obtain ⟨h1, h2⟩ := GlobalTheory.T.integrable_theta_kernel_fibers hZ hA hJ hE hF D n t B W d hn I θ hθ μ hμ b₀ hb x₀ hx Φ hΦ η hη hc
  exact ⟨h1, GlobalTheory.T.continuous_orbital_integral_unipotent hIk hDom hOF hS hB hE D n t B W d hn I θ hθ x₀ hdx Φ hΦ, h2⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

end
