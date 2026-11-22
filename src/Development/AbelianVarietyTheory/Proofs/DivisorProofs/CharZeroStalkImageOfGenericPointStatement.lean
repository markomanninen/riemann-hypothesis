module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharZeroStalkImageOfGenericPoint
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamIdeal

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charZero_stalk_imageOfGenericPoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsIntegral Y], CharZero Γ(Y, ⊤) →
    ∀ (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π))),
    letI := GlobalTheory.NormSheafDescent.fieldK π hK;
    CharZero (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) := by
  intro Y Z π _ hY hK
  have : Nonempty (⊤ : Y.Opens) := ⟨⟨genericPoint Y, trivial⟩⟩
  have hL : CharZero Y.functionField :=
    charZero_of_injective_ringHom (f := (Y.germToFunctionField ⊤).hom)
      (Y.germToFunctionField_injective ⊤)
  exact (π.stalkMap (genericPoint Y)).hom.charZero
