module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDatumRealDerivativeFockVectorsAll
public import Formalism.LocalToGlobal.IndefiniteReal.WeilFull

@[expose] public section

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_realDerivative_fockVectors_all : ∀ D : D7, Formalism.IndefR.WeilFull.RealAllO D := by
  first | exact @GlobalTheory.WeilReal.realAllO | exact GlobalTheory.WeilReal.realAllO | (intros; apply GlobalTheory.WeilReal.realAllO <;> assumption)
