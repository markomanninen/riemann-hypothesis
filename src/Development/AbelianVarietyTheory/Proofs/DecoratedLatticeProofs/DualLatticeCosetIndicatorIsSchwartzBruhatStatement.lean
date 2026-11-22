module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualLatticeCosetIndicatorIsSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.T2SpaceMatrixOfIsNonarchimedeanLocalField

@[expose] public section

open MeasureTheory ValuativeRel Matrix IsLocalRing GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (cosetInd mainDatum)
open GlobalTheory.FinPl.Comm (fpair)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualLatticeCoset_indicator_isSchwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (q : Unif k) (L : Submodule 𝒪[k] (n → k)) [L.IsFullLattice k] (f : Module.Dual 𝓀[k] (Red L)), cosetInd q L f ∈ SB (n → k) := by
  first | exact @GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB | exact GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB | (intros; apply GlobalTheory.FinPl.CosetSB.cosetInd_mem_SB <;> assumption)
