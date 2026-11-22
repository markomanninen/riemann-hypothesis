module

public import Mathlib
public import GroundTheory.AutomorphicForms.AdelicUnitaryGroups.Lattice

@[expose] public section

set_option linter.unusedSectionVars false

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct Topology Filter IsDedekindDomain NumberField
open scoped RestrictedProduct

noncomputable section

variable {K E : Type*} [Field K] [NumberField K] [CommRing E] [Algebra K E]
  [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι E)
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)


variable (K) in
def finiteAdeleEval (v : HeightOneSpectrum (𝓞 K)) :
    FiniteAdeleRing (𝓞 K) K →ₐ[K] v.adicCompletion K where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end

end GroundTheory.Automorphic
