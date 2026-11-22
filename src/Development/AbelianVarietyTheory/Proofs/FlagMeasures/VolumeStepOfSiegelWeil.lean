module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SiegelMeanCc
public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EnnrealVolumeRatioStepCancel
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoTsumOfMonotone
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMeanCcOfOneVectorCc
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneVectorCcOfSiegelWeil

@[expose] public section

open GlobalTheory.FlagMeas GlobalTheory.GaussMean

namespace GlobalTheory.GaussMean

theorem volumeStep_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → VolumeStep := fun h =>
  GlobalTheory.GaussMean.Step.volumeStep_of_siegelMean
    (GlobalTheory.GaussMean.Limit.siegelMean_of_cc
      (GlobalTheory.OneVectorMean.siegelMeanCc_of_oneVectorCc
        (GlobalTheory.GaussMean.oneVectorCc_of_siegelWeil h)))

end GlobalTheory.GaussMean
