module

public import Formalism.LogFactorialIndices.SignedSubspaceIndex.SumInterlacedBoundFails
public import Mathlib
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.LogProductFormula
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxDet
public import Formalism.LogFactorialIndices.SignedSubspaceIndex.SubspaceLatticeIndex

@[expose] public section

namespace Formalism.LatticeIndexTer

theorem latFinite : LatFinite := lattice_quotient_finite
theorem latBasis : LatBasis := lattice_has_basis
theorem idxDet : IdxDet := lattice_index_eq_det_valuation

end Formalism.LatticeIndexTer
