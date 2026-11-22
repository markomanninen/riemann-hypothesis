module

public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.MomentRecursion.MomStep
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.PhiMul
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.DzSubMuNextNonneg
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.PhiCont
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.PositiveConjugation.HsOpOpMul
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.SignDefiniteness.NormDef
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.SignDefiniteness.ExplicitFunctionSquareIntegrable
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.DegreeNormalization.DegPsi
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.DegreeNormalization.GapNorm
public import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.CKContinuous
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.CoverExistsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.HcFormalDegreeOfDiscreteSeriesFormalDegree
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HsOpIntegralRankOne
public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CKContinuous
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.FormalDegreeCompactDualIff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraFormalDegreeCompactDualLargeGaps

@[expose] public section

noncomputable section

namespace CompanionTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS CompanionTheory.RgDs

theorem hsInt : HsInt := GlobalTheory.CompanionTheory.RgFd.hsInt GlobalTheory.CompanionTheory.HsPsProof.hsPs hsPol phiMul phiCont

theorem psiNorm_of (hI : NormInd) : PsiNorm := by
  intro n ε lam hl
  by_cases h : S7.q0 ε = 0
  · exact normDef n ε h lam hl
  · have h1 : 1 ≤ min (pOf ε) (qOf ε) := Nat.one_le_iff_ne_zero.2 h
    exact hI n ε (h1.trans (min_le_left _ _)) (h1.trans (min_le_right _ _)) lam hl

theorem normInd_of_steps (hP : CoefPow)
    (h : MomW → CoefPow → KNull → HsPol → PhiMul → PhiLe → PhiCont → HsInt → GapNorm → NormInd) : NormInd :=
  h momW hP (kNull_of momW hP) hsPol phiMul phiLe phiCont hsInt (gapNorm_of degPsi)

end CompanionTheory.RgFd
