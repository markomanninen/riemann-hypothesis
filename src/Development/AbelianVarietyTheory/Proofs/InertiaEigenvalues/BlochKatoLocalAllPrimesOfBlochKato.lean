module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoRightExact
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimOfQlDimensionFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfRationalLocalDualityStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoAnnihilatorOfIntegralLocalDualityStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPartCOfPartAPartBFiniteLevelStatement

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoLocalOfHyp

theorem bkAll_of_blochKatoLocal (hBK : GlobalTheory.Published.BlochKatoLocal) (hTD : Formalism.GaloisCohomology.LocalTateDualityK)
    (hEC : Formalism.GaloisCohomology.LocalEulerCharK) (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : LocTied l P AI) (K : FinExt l) : Formalism.MainNotions.LocalSituation.bkAll (P.PD K) := by
  obtain ⟨hDim, hRat, hInt⟩ := hBK l P AI hT K
  have hA : bkACore (P.PD K) := GlobalTheory.T.blochKatoAnnihilator_of_rationalLocalDuality l P K hRat
  have hB : bkBCore (P.PD K) := GlobalTheory.T.blochKato_annihilator_of_integralLocalDuality l P K hInt
  exact ⟨hA, GlobalTheory.T.blochKatoDim_of_Ql_dimensionFormula l P K hDim, GlobalTheory.BKRightExact.bkARightExact_of_tied l P AI hT K, hB,
    GlobalTheory.T.breuilKisin_partC_of_partA_partB_finite_level hTD hEC l P AI hT K hA hB⟩

theorem blochKatoLocal_allPrimes_of_blochKato : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.LocalSituation.Conclusion5 D := by
  intro hBK hTD hEC D l _ K
  exact bkAll_of_blochKatoLocal hBK hTD hEC l (D.loc l) (D.locA l) (D.locT l) K

end GlobalTheory.BlochKatoLocalOfHyp
