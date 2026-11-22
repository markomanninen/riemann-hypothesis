module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeNhds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompletionPhiSubOneBijective

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.Decompl

theorem fontaine_and_decompletion :
    ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm9 D HW F :=
  fun D HW F l _ K s LL h =>
    ⟨GlobalTheory.Cyc.FontW.main D HW F l K s LL h, GlobalTheory.Decompl.decompletion D HW F l K s LL h⟩

end GlobalTheory.Decompl
