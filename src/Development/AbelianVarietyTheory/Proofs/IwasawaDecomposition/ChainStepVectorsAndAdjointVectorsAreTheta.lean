module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StepVecThetaLem
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsThetaFunOOfThetaAt

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory.VecTheta

theorem vecThetaSD : ∀ D : D7, Formalism.IndefR.Fin.VecThetaSD D := fun _ =>
  ⟨fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => isThetaFunO_stepVec h,
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h => isThetaFunO_thPVec h⟩

end GlobalTheory.VecTheta
