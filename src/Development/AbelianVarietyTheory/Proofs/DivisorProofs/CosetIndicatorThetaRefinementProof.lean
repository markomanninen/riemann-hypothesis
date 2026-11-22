module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TopPlaceLogTheta
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst

@[expose] public section

namespace GlobalTheory.ColNorms

open NumberField IsDedekindDomain Formalism.L2.Ker

theorem coset_refinement : CosetRefinement := by
  intro X A a b S Md _ _ hOdd hLa
  exact indAdd_of A a b S Md hOdd.pos (lattice_classes_finite_refinement X a b S) (indTieD_of_la A a b S Md hOdd.pos hLa)

end GlobalTheory.ColNorms
