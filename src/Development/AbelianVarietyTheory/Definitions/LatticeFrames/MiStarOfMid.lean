module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
public import Formalism.LocalToGlobal.IndefiniteReal.EvTieP
public import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily

@[expose] public section

noncomputable section

open scoped InnerProductSpace
open Formalism.BasicNotions Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links

namespace GlobalTheory.MiS
open Formalism Formalism.IndefR

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section FreeSingleHomotopyEquivDiscreteChains

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


end FreeSingleHomotopyEquivDiscreteChains

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {Bs : DefBase K} {A : DefAmb Bs} (X : CxData A)
  {fc : DefSub A → DefFace Bs} (cr : Crd A fc) (cv : CrdV A)

def OpsUnit (V : X.EE →ₗ[ℂ] X.EE) (U : ∀ u, Matrix (Fin ((fc X.zs).Dc.a u)) (Fin ((fc X.zs).Dc.a u)) ℂ) : Prop :=
  (∀ e ∈ X.EEl true, V e ∈ X.EEl true ∧ ‖V e‖ = ‖e‖) ∧
    ∀ u x, fnorm ((fc X.zs).Dc.Xc u Bs.v0) ((U u).mulVec x) = fnorm ((fc X.zs).Dc.Xc u Bs.v0) x

variable {X cr cv}

end Gen

end GlobalTheory.MiS

end
