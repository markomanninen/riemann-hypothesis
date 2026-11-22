module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LandherrHasse
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdOfLandherrHasse

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem genusMassStd_all : ∀ D : D7, GenusMassStd D :=
  genusMassStd_of_landherrHasse DefiniteOrthonormal.landherrHasse

end GlobalTheory
