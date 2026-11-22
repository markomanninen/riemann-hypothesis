module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageMembershipStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AverageInvarianceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnfoldingOfAverageStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiagonalTermGoodStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGoodStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryTermGoodStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MasterIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVSmulStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VecKapMulStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaIntegralOfEpsteinConvStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermUnfoldingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SideTermConvergenceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionSphericalKStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZetaValueAtOneStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PrincipalIdentityAssemblyStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicGenerationStatement

@[expose] public section

namespace PositivityTheory.RgEis.MG

theorem mirGen : SecLaw → StdGood → BdetLaw → EpConv → EpMain → TestFun → TestSph → MirGen :=
  fun hS hG hB hC hM hT hSph =>
    have hO := GlobalTheory.T.side_term_identity hG hB
    have hZ := GlobalTheory.T.zeta_integral_of_epstein_conv hC
    GlobalTheory.T.mirabolic_generation hS hSph GlobalTheory.T.average_membership (GlobalTheory.T.average_invariance GlobalTheory.T.average_membership) hO (GlobalTheory.T.test_function_spherical_K hG hB hT)
      (GlobalTheory.T.principal_identity_assembly hM GlobalTheory.T.diagonal_term_good (GlobalTheory.T.master_identity GlobalTheory.T.average_membership GlobalTheory.T.diagonal_term_good GlobalTheory.T.height_term_good GlobalTheory.T.boundary_term_good) hO GlobalTheory.T.block_term_identity hZ
        (GlobalTheory.T.side_term_unfolding hC (GlobalTheory.T.unfolding_of_average hS GlobalTheory.T.average_membership) GlobalTheory.T.lines_decomposition GlobalTheory.T.block_term_identity hZ) (GlobalTheory.T.side_term_convergence hC hSph GlobalTheory.T.lines_decomposition GlobalTheory.T.block_term_identity) (GlobalTheory.T.zeta_value_at_one hM))

end PositivityTheory.RgEis.MG
