module

public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfLocalFilteredHypothesesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremBHypothesesAdmittedStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OnePlaceAdmissibleOfGapConstantLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenvalueProductMapsLetterLatticeOfConclusionsAStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHoldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory

theorem theoremB_closing : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK →
    Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, (320 : ℝ) ≤ C → ArcLiftingSetup.aux₃ D HW F C := by
  intro hBK hTD hEC D HW F Cm C hC
  have h22 : CrystallineLiftingBounds.adm22 D HW F := GlobalTheory.FontaineIneq.one_place_admissible_of_gap_constant_le D HW F
  have h23 : CrystallineLiftingBounds.adm23 D HW F := (GlobalTheory.jumps_exact_adm D HW F).1
  have hN1 : Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm := GlobalTheory.T.wachLattice_laterClauses_hold D HW F Cm
  have hC4 : Formalism.MainNotions.N.LetterConditionGlobal D HW F := GlobalTheory.T.letterConditionGlobal_of_N1used D HW F Cm hN1
  exact GlobalTheory.T.theoremB_of_localFilteredHypotheses D HW F Cm C 10 23 32 32 8 hC h22 h23 hC4 (GlobalTheory.T.localLifting_theoremB_hypotheses_admitted hBK hTD hEC D HW F Cm)

end GlobalTheory
