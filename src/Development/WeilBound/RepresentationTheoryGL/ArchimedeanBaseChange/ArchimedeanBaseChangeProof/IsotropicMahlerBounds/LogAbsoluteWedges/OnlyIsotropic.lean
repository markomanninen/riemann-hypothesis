module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityFinitePlacesStatement
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.Mahler
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeterminantMonotonicityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlacesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundFinitePlacesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeBoundInfinitePlacesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeSubspaceBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundFinitePlacesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingBoundInfinitePlacesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LogAbsBasicFactsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeFinitePlacesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteSupportOfSizeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicDegreeFormulaStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBasisGeneralStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegBasisOfDegBasisGStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwoBasesComparisonStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeSubmoduleBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeRationalSubspaceStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeUnderTranslationStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreeBoundedOfBasisStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeBasicOfConjPlacesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFactsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFactsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DegreePairingIdentityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MahlerBoundOfDegreeStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyStableSubspacesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OnlyIsotropicSubspacesStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EllipticTermOfIsotropicStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightIndicatorStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightSupportBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SignConeWeightTranslationStatement

@[expose] public section

namespace PositivityTheory.Rg.BcB.D1

theorem mulF : MulF := GlobalTheory.T.multiplicativity_finite_places
theorem detMono : DetMono := GlobalTheory.T.determinant_monotonicity
theorem mulI : MulI := GlobalTheory.T.multiplicativity_infinite_places detMono
theorem wedgeF : WedgeF := GlobalTheory.T.wedge_bound_finite_places mulF
theorem wedgeI : WedgeI := GlobalTheory.T.wedgeI_of_detMono_mulI_var detMono mulI
theorem wedgeSub : WedgeSub := GlobalTheory.T.wedge_subspace_bound
theorem pairF : PairF := GlobalTheory.T.pairing_bound_finite_places mulF
theorem pairI : PairI := GlobalTheory.T.pairing_bound_infinite_places detMono
theorem logAbsBasic : LogAbsBasic := GlobalTheory.T.log_abs_basic_facts
theorem szFin : SzFin := GlobalTheory.T.size_finite_places
theorem finSupp : FinSupp := GlobalTheory.T.finite_support_of_size mulF mulI szFin
theorem degAdelic : DegAdelic := GlobalTheory.T.adelic_degree_formula mulF mulI logAbsBasic finSupp
theorem degBasisG : DegBasisG := GlobalTheory.T.degree_basis_general wedgeF wedgeI mulF mulI logAbsBasic finSupp
theorem degBasis : DegBasis := GlobalTheory.T.degBasis_of_degBasisG' degBasisG
theorem degSubmod : DegSubmod := GlobalTheory.T.degree_submodule_bound wedgeF wedgeI wedgeSub finSupp degBasisG GlobalTheory.T.two_bases_comparison
theorem degRat : DegRat := GlobalTheory.T.degree_rational_subspace degBasisG
theorem degMove : DegMove := GlobalTheory.T.degree_under_translation mulF mulI szFin finSupp degBasisG
theorem degBdd : DegBdd := GlobalTheory.T.degree_bounded_of_basis wedgeF wedgeI mulF mulI szFin finSupp logAbsBasic degBasisG
theorem conjPlaces : ConjPlaces := GlobalTheory.T.conjugate_places_facts
theorem sizeBasic : SizeBasic := GlobalTheory.T.size_basic_of_conj_places szFin conjPlaces
theorem degPairing : DegPairing :=
  GlobalTheory.T.degree_pairing_identity wedgeF wedgeI mulF mulI pairF pairI szFin finSupp logAbsBasic conjPlaces degBasisG GlobalTheory.T.radical_subspace_facts
theorem mahler_of_c (h : MahlerC) : Mahler := GlobalTheory.T.mahler_bound_of_degree degBdd degRat h
theorem mahler : Mahler := mahler_of_c (PositivityTheory.Rg.BcB.E1.mahlerC_of_deg degBasis degAdelic degBdd degRat)
theorem onlyStable : OnlyStable := GlobalTheory.T.only_stable_subspaces degSubmod degMove degBdd degPairing sizeBasic
theorem onlyIsotropic : OnlyIsotropic := GlobalTheory.T.only_isotropic_subspaces onlyStable degPairing sizeBasic
theorem ellTerm : EllTerm := GlobalTheory.T.elliptic_term_of_isotropic onlyIsotropic
theorem chainSum : ChainSum := fun m =>
  ⟨GlobalTheory.T.sign_cone_weight_indicator m, GlobalTheory.T.sign_cone_weight_support_bound m, (GlobalTheory.T.sign_cone_weight_translation m).1, (GlobalTheory.T.sign_cone_weight_translation m).2.1, (GlobalTheory.T.sign_cone_weight_translation m).2.2⟩

end PositivityTheory.Rg.BcB.D1
