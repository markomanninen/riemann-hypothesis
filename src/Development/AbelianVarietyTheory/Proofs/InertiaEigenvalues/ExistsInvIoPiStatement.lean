module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInvIoPi
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_inv_io_pi_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∃ u ∈ FilB P 0, io AI AI.π₁ * u = 1 := by
  first | exact @GlobalTheory.ExpImage.exists_inv_io_pi | exact GlobalTheory.ExpImage.exists_inv_io_pi | (intros; apply GlobalTheory.ExpImage.exists_inv_io_pi <;> assumption)
