module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBoundsCrystallineDeRhamConcreteRings
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fontaine_bounds_crystalline_deRham_concrete_rings : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.fontCore (P.PD K) := by
  first | exact @GlobalTheory.Per.FontaineTied.fontCore_all_of_tied | exact GlobalTheory.Per.FontaineTied.fontCore_all_of_tied | (intros; apply GlobalTheory.Per.FontaineTied.fontCore_all_of_tied <;> assumption)
