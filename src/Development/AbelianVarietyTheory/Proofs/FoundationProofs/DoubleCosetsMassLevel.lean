module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefClassDecompIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteAndMass

@[expose] public section

namespace GlobalTheory.DefiniteDecompObj

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

theorem doubleCosets_mass : ∀ D : D7, DefClassDecomp D :=
  GlobalTheory.DefiniteDecomp.defClassDecomp

end GlobalTheory.DefiniteDecompObj
