module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenKerOfInfConn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalIdealSt

@[expose] public section

namespace GlobalTheory.Published

theorem GlobalArtinReciprocity.heckeLAdicCharacter_and_principalIdealSt :
    GlobalArtinReciprocity → HeckeLAdicCharacter ∧ PrincipalIdealSt :=
  fun h => ⟨h.heckeLAdicCharacter, h.principalIdealSt⟩

end GlobalTheory.Published
