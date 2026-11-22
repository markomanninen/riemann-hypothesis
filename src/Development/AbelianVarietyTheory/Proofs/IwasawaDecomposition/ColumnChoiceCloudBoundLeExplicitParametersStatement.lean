module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnChoiceCloudBoundLeExplicit
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Formalism.LocalRingCardinality.DataTies
public import Formalism.LocalRingCardinality.SpanPowerMembership.RankRecordRowDimensionZero
public import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.KerEntHyp
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MtOfFactors
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Formalism.LocalRingCardinality.SpanPowerMembership.EntPlNonempty
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TrueColumnChoicesKernelDatumAdaptedBasesStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeLayerTrueColumnsParametersFreeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsKernelDataAtServedPlaceStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnChoice_cloudBound_le_cG : StepW Pinned fun K B f T w => ∀ Z : w.Lt, ∃ c : ℕ, (∀ u, Formalism.L2.G.CloudBound (w.D Z) u c) ∧ ∀ L : SizeData₂ (w.D Z), L.sc = K.s → Val K.C K.cD K.ch L → (c : ℝ) ≤ G.cG L := by
  first | exact @GlobalTheory.Mem.Top.Bl.cloudBound_step | exact GlobalTheory.Mem.Top.Bl.cloudBound_step | (intros; apply GlobalTheory.Mem.Top.Bl.cloudBound_step <;> assumption)
