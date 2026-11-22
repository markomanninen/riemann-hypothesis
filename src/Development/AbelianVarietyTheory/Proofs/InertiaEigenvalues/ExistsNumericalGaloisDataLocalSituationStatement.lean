module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumericalGaloisDataLocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleQuotientKerIffFullLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopDataOfSlotHyps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleClassesPropsOfFlatCoefficient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleStd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDcrisLetterDeRhamComponentEqDim
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousCycOInvPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInvMultOfIsGenWith

@[expose] public section

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions
set_option synthInstance.maxHeartbeats 400000
open ReciprocityTheory.Def (Z1 B1 H1)
open TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numerical_galoisData_localSituation : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K LL : FinExt l)
    (hA : CaseA K LL) (lam : ↥(OL LL)), Irreducible lam → 5 ≤ (P.PD K).p →
    ∀ (t : ℕ) (h w η : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ℕ) (typ : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Bool)
      (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL))
      (χ : ℕ → ↥(GK K) →* (↥(OL LL))ˣ), tableLineDegreeTwo.TopHyp (P.PD K) (H.W K 1 LL hA.2.2).emb t h w η typ U T.ρ χ →
      (∀ i, Multiset.card (U i) = Module.finrank ↥LL.1 T.V) →
      ∃ (r : ℕ) (D : TopData (Module.finrank ℚ_[l] ↥(K0 K)) r) (ε : ↥(GK K) →* (↥(OL LL))ˣ),
        GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleTwistedCharClasses.Hyp P K LL (H.W K 1 LL hA.2.2).emb D
          (GalData.mk lam T (χ 1) ε) ∧ D.t = t ∧
        (∀ i a, ((D.Ut i).count a : ℤ) = tableLineDegreeTwo.jTil U w t i a) ∧
        ∀ c ∈ Finset.Icc 1 t,
          (GalData.mk lam T (χ 1) ε : GalData ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)).chi c = χ c := by
  first | exact @GlobalTheory.TopWindow.exists_topData_galData | exact GlobalTheory.TopWindow.exists_topData_galData | (intros; apply GlobalTheory.TopWindow.exists_topData_galData <;> assumption)
