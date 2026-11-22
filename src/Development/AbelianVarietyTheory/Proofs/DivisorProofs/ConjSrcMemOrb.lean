module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommuteOfCommuteSeparableCharpoly
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

@[expose] public section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw.Comm

open GlobalTheory.EulerTw

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem thF_thF (g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : thF E n (thF E n g) = g :=
  GlobalTheory.ThetaPull.thetaGL_thetaGL _ GlobalTheory.ThetaPull.cFin_cFin g

theorem thF_ratF (g : GL (Fin n) E) : ratF E n (thE E n g) = thF E n (ratF E n g) :=
  GlobalTheory.ThetaPull.map_thetaGL _ _ _ (fun x => (conjFin_algebraMap (IsCMField.complexConj E).toRingEquiv x).symm) g

end GlobalTheory.EulerTw.Comm

namespace GlobalTheory.EulerTw

end GlobalTheory.EulerTw
