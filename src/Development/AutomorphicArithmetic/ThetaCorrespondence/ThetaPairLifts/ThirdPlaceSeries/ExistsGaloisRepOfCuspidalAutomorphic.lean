module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisRepsCuspidalAll
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BuiltEx
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SameGaloisLevelExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RootsOfUnityRingLeWittIntegers
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GalEx
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AlCGTruegalEx
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem galoisRep_attached_to_cuspidal_all_levels_alt : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x,
    _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => GlobalTheory.BlockComplement.GaloisRepsCusp D' := by
  intro hP hL
  refine StepW.of_all fun K B f T w _ _ _ P x l => ?_
  refine ⟨fun _ => ∅, fun L _ => ?_⟩
  let T' : GlobalTheory.RowTie.WDTie (withLoc L).nd (withLoc L).naut := { l.a.A.wdT with }
  have cg : _root_.GlobalTheory.HeightCounting.CGTrueT hL (withLoc L) T' := { l.a.cg with }
  exact galoisRepsCusp_of_galEx (cg.galEx hL hP.what₂.fin hP.what₂.gal)
end GlobalTheory.HeightCounting.Up
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_galoisRepsCusp_of_level_c : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, AllSt fun _ _ _ _ _ _ x => ∀ l : _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevel hL x, _root_.GlobalTheory.CoefDuty.ForcedByAutomorphicSemisimpleData l.a.A l.mt.M l.c.ch l.c.tp.tup fun D' => GlobalTheory.BlockComplement.GaloisRepsCusp D' := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.galoisRep_attached_to_cuspidal_all_levels_alt | exact _root_.GlobalTheory.HeightCounting.Up.galoisRep_attached_to_cuspidal_all_levels_alt | (intros; apply _root_.GlobalTheory.HeightCounting.Up.galoisRep_attached_to_cuspidal_all_levels_alt <;> assumption)
end
end
