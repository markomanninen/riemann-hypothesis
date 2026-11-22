module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsResVolume
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SmoothChartVolume
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.GenericComplexPoint

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem ResVolume.proof : ResVolume.Statement := by
  intro K _ ι _ P J e R _ _ hP
  obtain ⟨z, hzP, hzJ⟩ := exists_mcPts_not_mem_mcPts hP R.nondeg
  obtain ⟨x, -⟩ := R.surj z hzP hzJ
  have : Nonempty R.X := ⟨x⟩
  exact ChartVolume.exists_isSmoothVolume R.A

end GroundTheory.Heights₂.Heights.HilbertSamuel
