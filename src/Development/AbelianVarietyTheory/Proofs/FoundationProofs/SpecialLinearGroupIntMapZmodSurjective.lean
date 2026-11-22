module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd

@[expose] public section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem specialLinearGroup_map_intCast_zmod_surjective :
    ∀ (M : ℕ), Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) :
      SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod M)) :=
  fun M => GlobalTheory.specialLinearGroup_map_zmod_surjective (Fin 2) M

end GlobalTheory
