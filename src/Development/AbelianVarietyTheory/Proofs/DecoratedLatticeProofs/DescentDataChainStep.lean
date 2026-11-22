module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinationsStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepVector
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepSelfDual
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalCombinationsComposeFinitelyManyPlacesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationsDistinctSplitPlacesCollectStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FoldrSplitPlaceSecondCombinationsVacuumNeZeroStatement

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

namespace GlobalTheory.MidDatum

theorem vac_true_mono {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T}
    (P : GlobalTheory.FinPl.Pl D → Prop) {F : WO S T → ℂ} (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) F) :
    GlobalTheory.FinPl.Vac ψ S T LS LT P F := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) (fun _ => True) := by
    apply AddSubgroup.closure_mono
    rintro w ⟨α, hα, -, rest⟩
    exact ⟨α, hα, fun _ hv => (hv trivial).elim, rest⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

end GlobalTheory.MidDatum
