module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Retie
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScale
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolumeStatement

@[expose] public section

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Vol GlobalTheory.Mem.Per

namespace GlobalTheory.Mem

theorem retie_volTieG_and_cdScaleTie :
    ∀ D : D7, Formalism.L2.Theta.VolTieG (retie D) ∧ cdScaleTie (retie D) := by
  intro D
  refine ⟨GlobalTheory.T.volumesAgreeAdelic_of_trueVolume (retie D) (fun _ => rfl), ?_⟩
  rw [cdScaleTie_iff]
  exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale D.cd

end GlobalTheory.Mem
