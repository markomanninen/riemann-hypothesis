module

public import Mathlib
public import GroundTheory.AutomorphicForms.UnitaryGroupScheme

@[expose] public section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

variable (F : Type*) [Field F]

variable {F}

section Split

variable (F) (R : Type*) [CommRing R] [Algebra F R]

noncomputable def splitEquiv : R ⊗[F] (F × F) ≃ₐ[R] R × R :=
  (Algebra.TensorProduct.prodRight F R R F F).trans
    (AlgEquiv.prodCongr (Algebra.TensorProduct.rid F R R) (Algebra.TensorProduct.rid F R R))

variable {F R}



variable {ι : Type*} [Fintype ι] [DecidableEq ι]



variable (H : Matrix ι ι (F × F))






end Split

section SplitFunctor

open CategoryTheory

universe u

variable (F : Type u) [Field F] (ι : Type u) [Fintype ι] [DecidableEq ι]

variable {F ι}

end SplitFunctor

end GroundTheory.Automorphic
