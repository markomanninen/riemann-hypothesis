module

public import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped TensorProduct

section Ext

variable {K L : Type} [Field K] [Field L] [Algebra K L] {M : Type} [AddCommGroup M] [Module K M]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def incl : M →ₗ[K] L ⊗[K] M := TensorProduct.mk K L M 1

end Ext

section Forms

variable {K : Type} [Field K] {LL : Type} [Field LL] [NumberField LL] [Algebra K LL]
variable {C : Type} [AddCommGroup C] [Module K C] {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {D : D7}

def rhoOf (LL : Type) [Field LL] [Algebra K LL] {G0 : Type} [Group G0] (ρC : G0 →* (C →ₗ[K] C)) :
    G0 →* (LL ⊗[K] C →ₗ[LL] LL ⊗[K] C) where
  toFun g := (ρC g).baseChange LL
  map_one' := by rw [map_one]; exact LinearMap.baseChange_one _ _
  map_mul' g g' := by rw [map_mul]; exact LinearMap.baseChange_mul _ _

end Forms

end Formalism.L2.Pj
