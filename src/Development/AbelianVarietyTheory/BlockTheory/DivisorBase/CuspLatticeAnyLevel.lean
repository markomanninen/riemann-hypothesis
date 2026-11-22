module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
public import Formalism.LocalToGlobal.ProjectiveLattices.BaseEmbeddingInclusion
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.KaSmallNonpos

@[expose] public section

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith
open scoped TensorProduct

section Abstract

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G] [Fintype G]


omit [NumberField LL] in
def IsCentralIdem (eC : G → LL) : Prop :=
  (∀ g h, eC (h * g * h⁻¹) = eC g) ∧ ∀ g, ∑ h, eC h * eC (h⁻¹ * g) = eC g

end Abstract

variable {D : D7}

section Comparison₂

variable (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G]

end Comparison₂

section Level

variable {E : Type} [Field E] [NumberField E] {Pg : Finset (Formalism.L2.DIV.Pl E)} {r : ℕ} {LL : Type} [Field LL]
  {G : Type} [Group G]

end Level

end GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents
