module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

@[expose] public section

noncomputable section

namespace PI.LatSizeCont

open MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct ENNReal Matrix

namespace Size

variable (I : Formalism.MainNotions.S.AutInst)

def latSet (x : I.GA) : Set (Fin I.n → I.E) :=
  {u | (I.fmat x.2⁻¹) *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (u i)) ∈ I.Lf}

end Size

end PI.LatSizeCont
