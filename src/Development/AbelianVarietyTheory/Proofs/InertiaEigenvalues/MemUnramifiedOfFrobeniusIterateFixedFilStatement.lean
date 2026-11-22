module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemUnramifiedOfFrobeniusIterateFixedFil
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unramified_of_frobenius_iterate_fixed_fil : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (c : P.R.B), (⇑P.φB)^[finrank ℚ_[l] ↥(K0 K)] c = c → (∀ j : ℕ, P.ιB ((⇑P.φB)^[j] c) ∈ (P.PD K).Fil 0) → ∃ a : ↥(K0 K), c = algebraMap ↥(K0 K) P.R.B a := by
  first | exact @GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt | exact GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt | (intros; apply GlobalTheory.CrisPerFix.mem_unramified_of_frobenius_iterate_fixed_fil_alt <;> assumption)
