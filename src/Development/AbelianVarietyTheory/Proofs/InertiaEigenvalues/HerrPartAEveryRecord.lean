module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.ClassMapInjectiveBijectiveNorms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrAAndNatural

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory.HerrFull

theorem herr_part_a_every_record :
    ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
      Formalism.MainNotions.LocalSituation.ClassMapInjectiveBijectiveNorms D HW F :=
  fun D HW F => herr_a_and_natural D HW F

end GlobalTheory.HerrFull
