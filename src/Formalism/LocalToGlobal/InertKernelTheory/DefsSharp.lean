module

public import Formalism.LocalToGlobal.InertKernelTheory.SecondKernelEntrywiseLastLevel

@[expose] public section

noncomputable section

open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset

namespace Formalism.L2.KerInert.SecondKernelSharpWeights

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.KerInert.K2 Formalism.L2.KerInert.SecondKernelInstances

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

end Gen

def SharpWtIs : Prop :=
  ∀ (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ), j < D.R.m →
    ∀ (τ : D.what₂.Tau) (r : Fin (D.R.N j)),
      ((((nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ : ℤ)) : ℚ) =
        ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) - (j : ℚ) * ((D.R.t : ℚ) + 1) / 2

end Formalism.L2.KerInert.SecondKernelSharpWeights
