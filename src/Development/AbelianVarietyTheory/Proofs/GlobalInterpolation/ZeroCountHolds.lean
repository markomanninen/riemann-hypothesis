module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinsumMemLeOfSubset

@[expose] public section

namespace GlobalTheory.Mem.An

theorem zeroCount_holds : GlobalTheory.Mem.An.ZeroCount := by
  obtain ⟨C, -, H⟩ := GlobalTheory.ZeroWindow.count_zeros_window
  refine ⟨C, fun q _ χ hχ t => ?_⟩
  have h := (H q χ hχ t).2
  simpa only [zsumR, zerosIn, zmult, mul_one] using h

end GlobalTheory.Mem.An
