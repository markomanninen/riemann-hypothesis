module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfLiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAHypothesesAdmittedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingOfEtaleExactDeRhamCrystallineConstStatement

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory

theorem theoremA_closing : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, 160 ≤ C → ElementDenominator.Conclusion1 D C := by
  intro hBK hTD hEC D HW F Cm C hC
  exact GlobalTheory.T.integralityFromMetric_of_160_le D HW F Cm 23 32 32 C hC (GlobalTheory.T.localLifting_theoremA_hypotheses_admitted hBK hTD hEC D HW F Cm)

end GlobalTheory
