module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TuplesHaveLocalModelsAtConstructedPointOverTrueC
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tuplesHaveLocalModels_at_constructedPoint_over_trueColumns : GlobalTheory.TwV.Lt.AdmAtEnt2 → GlobalTheory.TwV.Lt.CurveEx → ∀ (K : Ctx) (β : BPt K), β.Is (positionOf HasPart) → ModelsAt β.D β.O := by
  first | exact @GlobalTheory.Svd.modelsAt_bpt | exact GlobalTheory.Svd.modelsAt_bpt | (intros; apply GlobalTheory.Svd.modelsAt_bpt <;> assumption)
