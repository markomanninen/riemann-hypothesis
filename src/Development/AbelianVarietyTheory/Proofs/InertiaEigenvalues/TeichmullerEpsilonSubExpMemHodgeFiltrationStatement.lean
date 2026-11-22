module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerEpsilonSubExpMemHodgeFiltration
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff

@[expose] public section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmullerEpsilon_sub_exp_mem_hodgeFiltration : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ M : ℕ, io AI (WittVector.teichmuller l AI.ε) - ∑ j ∈ Finset.range M, qB P ((j.factorial : ℚ_[l])⁻¹) * tD P ^ j ∈ FilB P (M : ℤ) := by
  first | exact @GlobalTheory.ExpImage.TaylorEps.eps_sub_exp | exact GlobalTheory.ExpImage.TaylorEps.eps_sub_exp | (intros; apply GlobalTheory.ExpImage.TaylorEps.eps_sub_exp <;> assumption)
