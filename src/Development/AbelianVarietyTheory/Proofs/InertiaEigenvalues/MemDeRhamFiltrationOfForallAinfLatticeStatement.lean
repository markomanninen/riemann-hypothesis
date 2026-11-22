module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemDeRhamFiltrationOfForallAinfLattice
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_deRhamFiltration_of_forall_ainfLattice : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (M : ℕ) (b : P.R.BdR), (∀ n : ℕ, b ∈ Lat AI M n) → b ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.mem_FilB_of_forall_Lat | exact GlobalTheory.ExpImage.mem_FilB_of_forall_Lat | (intros; apply GlobalTheory.ExpImage.mem_FilB_of_forall_Lat <;> assumption)
