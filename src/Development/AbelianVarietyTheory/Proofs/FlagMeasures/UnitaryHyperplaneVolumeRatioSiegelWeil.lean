module

public import Mathlib
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.VolumeRatio
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelOneVectorMeasurableOfCompactSupportStatement

@[expose] public section

namespace GlobalTheory.VolRatioFromSiegelWeil

theorem volumeRatio :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → ∀ D : Formalism.BasicNotions.D7, Formalism.MainNotions.RT.MassRatioUnderVolume D :=
  fun hP =>
    GlobalTheory.VolRatioFromSecondClause.volumeRatio
      (GlobalTheory.T.siegel_one_vector_measurable_of_compactSupport (GlobalTheory.GaussMean.oneVectorCc_of_siegelWeil hP))

end GlobalTheory.VolRatioFromSiegelWeil
