module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingOfEtaleExactDeRhamCrystallineConst
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfLiftingTheory
public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralityFromMetric_of_160_le : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ CA CB CK C : ℝ, 160 ≤ C → ElementDenominator.IntegralityFromMetric D HW F Cm CA CB CK C := by
  first | exact @GlobalTheory.TheoremAFinal.integralityFromMetric_of_le | exact GlobalTheory.TheoremAFinal.integralityFromMetric_of_le | (intros; apply GlobalTheory.TheoremAFinal.integralityFromMetric_of_le <;> assumption)
