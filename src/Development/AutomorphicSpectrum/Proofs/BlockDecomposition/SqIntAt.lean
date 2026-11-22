module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.SquareIntegrableAtPlace.SqIntAt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.AutomorphicL2Unitary PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.SpectralAccumulation.FD
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.SqIntFD

theorem sqIntAt : PositivityTheory.Rg.BcB.SpectralAccumulation.FD.SqIntAt := by
  intro E _ _ _ N mG bG μ _ 𝓕 h𝓕 φ h h'
  obtain rfl : mG = borel _ := bG.measurable_eq
  have hm := GlobalTheory.CuspRep.CuspidalL2GL.memL2_of_isAutForm (μ := μ) h h'
  have hc := ((memL2_iff_fundamental_domain h𝓕).1 hm).2
  simpa using lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
    two_ne_zero ENNReal.ofNat_ne_top hc.eLpNorm_lt_top

end GlobalTheory.CompanionTheory.SqIntFD
