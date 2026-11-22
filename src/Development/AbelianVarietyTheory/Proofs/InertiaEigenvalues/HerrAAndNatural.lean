module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeNhds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompletionPhiSubOneBijective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HausdorffOfModuleTopologyFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocalLatticeRepresentationSpace

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation TensorProduct

namespace GlobalTheory.HerrFull

theorem fontaine_decompletion (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    adm9 D HW F := fun l _ K s LL h =>
  ⟨GlobalTheory.Cyc.FontW.main D HW F l K s LL h, GlobalTheory.Decompl.decompletion D HW F l K s LL h⟩

theorem herr_a_and_natural :
    ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), ∀ (l : ℕ) [Fact l.Prime]
      (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      HerrAat (sit D.loc HW l (D.locA l) K s LL h) ∧
        HerrAsat (sit D.loc HW l (D.locA l) K s LL h) ∧ ((HW l).W K s LL h).ClNat := by
  intro D HW F l _ K s LL h
  have h9 := fontaine_decompletion D HW F
  have h1 := GlobalTheory.HerrClass.herr_a D HW F h9 l K s LL h
  exact ⟨h1.1, h1.2, GlobalTheory.HerrNatural.clNat D HW F h9 l K s LL h⟩

end GlobalTheory.HerrFull
