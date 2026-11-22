module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPartCOfPartAPartBFiniteLevel
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_partC_of_partA_partB_finite_level : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ K : FinExt l, bkACore (P.PD K) → bkBCore (P.PD K) → Formalism.MainNotions.LocalSituation.bkC (P.PD K) := by
  first | exact @GlobalTheory.BKFinLevel.bkC_of_bkA_bkB | exact GlobalTheory.BKFinLevel.bkC_of_bkA_bkB | (intros; apply GlobalTheory.BKFinLevel.bkC_of_bkA_bkB <;> assumption)
