module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsSt
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.MaxCuspsPfA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SublatticeCoefficients
public import Formalism.LocalToGlobal.ProjectiveLattices.RdOrbIntOfLatZ
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspKilledCoefficientEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.MaxCuspMemCuspFormsOfKilledCoefZeroStatement

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD NumberField Formalism.L2.Pj.FJ Formalism.L2.Pj.QAt

namespace GlobalTheory

theorem maxCusps_iff_killed_coeff_vanish : MaxCuspsStatement := by
  intro E _ _ _ r ρ X hspan hbas la hχ c P hP
  exact ⟨fun h => GlobalTheory.T.maxCusp_killedCoefficient_eq_zero E r ρ X hbas la hχ c P h,
    fun h => GlobalTheory.T.maxCusp_mem_cuspForms_of_killedCoef_zero E r ρ X hspan hbas la hχ c P hP h⟩

end GlobalTheory
