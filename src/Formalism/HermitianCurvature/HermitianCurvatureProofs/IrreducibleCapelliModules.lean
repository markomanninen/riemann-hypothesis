module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CommonEigenvectors
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HighestWeightPolynomials
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliAbstractCharacter
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StarSumLemmas
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BorderedDeterminants
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BranchingSystems
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ClosureOperators
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightMonotonicity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StrictBoxOrder

@[expose] public section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt

theorem capelli_singular : Qr.CapSing := qr_capSing_of singular_dominant exists_singular_maximal_vector

theorem top_weight_singular : Qr.TopWeightSing := qr_topWeightSing_of exists_singular_maximal_vector capelli_singular

theorem vector_descent : Qr.VecDown := qr_vecDown_of quantum_minor_polynomial polynomial_vanishing

theorem raising_nonzero : Qr.RaiseNZ := qr_raiseNZ_of covariant_raising

theorem lowering_nonzero : Qr.LowerNZ := qr_lowerNZ_of vector_descent

theorem branching_decomposition : Qr.Decomp :=
  qr_decomp_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations covariant_raising vector_descent
    raising_nonzero lowering_nonzero

theorem multiplicity_one : Qr.MultOne := qr_multOne_of exists_singular_maximal_vector dual_minor span_singular_vectors

theorem irreducible_capelli_modules : Qr.IrredCap :=
  qr_irredCap_of exists_singular_maximal_vector capelli_singular capelli_stabilizer submodule_relations top_weight_singular
    dual_minor span_top_vectors multiplicity_one branching_decomposition capelli_independence

theorem branching_algebraic : Qr.BranchingAlg := qr_branchingAlg_of branching_decomposition capelli_independence irreducible_capelli_modules

end Formalism.FourierDecayAlt.P
