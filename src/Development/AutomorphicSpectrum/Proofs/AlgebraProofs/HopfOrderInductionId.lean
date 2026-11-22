module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExtTensor

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem indOrder_id_eq_of_isHopfOrder : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)), IsHopfOrder A → indOrder (MonoidHom.id T) A = A :=
  PositivityTheory.HtPt.Mh.ind_id

end GlobalTheory.CompanionTheory.Ar.BT
