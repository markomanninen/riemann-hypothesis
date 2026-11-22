module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvIsoOfLocalTateDualityStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinIsoDualLatticeOfLocalTateDualityStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLocalDualityOfLocalTateDualityStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLocalDualityOfLocalTateDualityStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOfLocalCohomologyShapeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatInvIsoOfLocalTateDualityCyclotomicTwistStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CohomologyShapeOfTateDualityEulerStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHomModuloUnramifiedShapeOfLocalDualityStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedPadicDecompositionHomExistsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRecStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrFiniteOverPadicTopologiesExistStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCohomologySevenElementaryFactsStatement

@[expose] public section

namespace GlobalTheory

theorem langRecCore_of_artinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hT : Formalism.GaloisCohomology.LocalTateDualityK)
    (hE : Formalism.GaloisCohomology.LocalEulerCharK) : ReciprocityTheory.ChartRestriction.T2.Core :=
  { dec := GlobalTheory.T.decomposition_group_equiv_local_galois_group,
    inv := GlobalTheory.T.invIso_of_localTateDuality hT,
    fin := GlobalTheory.T.finIso_dualLattice_of_localTateDuality hT,
    rat := GlobalTheory.T.rationalLocalDuality_of_localTateDuality hT,
    int := GlobalTheory.T.integral_localDuality_of_localTateDuality hT,
    jspan := GlobalTheory.T.span_of_local_cohomology_shape,
    nat := GlobalTheory.T.natInvIso_of_localTateDuality_cyclotomicTwist hT,
    shape := GlobalTheory.T.cohomology_shape_of_tate_duality_euler hT hE,
    shapeUnr := GlobalTheory.T.galoisHom_modulo_unramified_shape_of_localDuality hT hE,
    unr := GlobalTheory.T.unramified_padic_decomposition_hom_exists,
    vhE := GlobalTheory.T.unramifiedGaloisHoms_bounded_classNumber_of_artinReciprocity hA,
    top := GlobalTheory.T.dvr_finite_over_padic_topologies_exist,
    elem := GlobalTheory.T.local_cohomology_seven_elementary_facts }

end GlobalTheory
