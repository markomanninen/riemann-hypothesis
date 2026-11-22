module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModels
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_doubleStep_kernel_localModels : ∀ (D : D7), LastLoc D := by
  first | exact @GlobalTheory.LastKerLoc.lastLoc | exact GlobalTheory.LastKerLoc.lastLoc | (intros; apply GlobalTheory.LastKerLoc.lastLoc <;> assumption)
