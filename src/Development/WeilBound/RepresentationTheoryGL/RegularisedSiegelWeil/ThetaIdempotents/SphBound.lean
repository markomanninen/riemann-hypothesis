module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExistStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightFunctionsExistStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiUnfoldingStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTwistIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiEisensteinStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantTermBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularSectionOfHeightsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinHolomorphyOfHeightsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTotalOfHeckeEtaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiCoefficientOfBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialConstantFourierCoefficientStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalBoundOfHeightsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCharacterEtaConditionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightIdentityStatementStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PoleRealityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueMeasureIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolarPartIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHoldsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExistsStatement

@[expose] public section

namespace PositivityTheory.Rg.Rsw

theorem mapsExist : MapsExist := GlobalTheory.T.jacobi_maps_exist
theorem htExist : HtExist := GlobalTheory.T.height_functions_exist
theorem heckeEta : HeckeEta := GlobalTheory.T.hecke_character_eta_condition
theorem fjEis : FJEis := GlobalTheory.T.fourier_jacobi_eisenstein GlobalTheory.T.fourier_jacobi_unfolding GlobalTheory.T.theta_twist_identity
theorem pcBound : PcBound := GlobalTheory.T.partial_constant_term_bound
theorem rSec : RSec := GlobalTheory.T.regular_section_of_heights htExist
theorem eisHol : EisHol := GlobalTheory.T.eisenstein_holomorphy_of_heights htExist
theorem thTotal : ThTotal := GlobalTheory.T.theta_total_of_hecke_eta heckeEta
theorem cfFJ : CfFJ := GlobalTheory.T.fourier_jacobi_coefficient_of_bound pcBound
theorem pcFc : PcFc := GlobalTheory.T.partial_constant_fourier_coefficient mapsExist GlobalTheory.T.fourier_zero_holds
theorem sphBound : SphBound := GlobalTheory.T.spherical_bound_of_heights htExist
theorem resMu : ResMu :=
  GlobalTheory.T.residue_measure_identity mapsExist htExist heckeEta fjEis pcBound rSec eisHol thTotal pcFc sphBound GlobalTheory.T.fourier_zero_holds GlobalTheory.T.coefficient_data_exists
theorem polar : Polar :=
  GlobalTheory.T.polar_part_identity mapsExist htExist heckeEta GlobalTheory.T.right_identity_statement GlobalTheory.T.pole_reality fjEis pcBound rSec eisHol thTotal cfFJ pcFc sphBound

end PositivityTheory.Rg.Rsw
