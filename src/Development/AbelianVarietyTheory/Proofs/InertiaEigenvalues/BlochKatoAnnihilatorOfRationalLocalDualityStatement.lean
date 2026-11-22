module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfRationalLocalDuality
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoAnnihilator_of_rationalLocalDuality : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), GlobalTheory.Published.BlochKato.RationalDuality (P.PD K) → bkACore (P.PD K) := by
  first | exact @GlobalTheory.bkACore_of_rationalDuality | exact GlobalTheory.bkACore_of_rationalDuality | (intros; apply GlobalTheory.bkACore_of_rationalDuality <;> assumption)
