module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicRowsDivisionTransportSpectralStageLattices
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OmPinsTr
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsBIffCoreB
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicRowsDivision_transport_spectralStage_lattices : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (Wt : Set B.places.Pl) (p0 : BaseLevelRowSide (w.D Z)) (t : RowsT K w Z Wt p0) (S' : SStage B w.C Z.W) (N : ∀ u, Submodule (𝓞 B.LL) (Z.V.div.Nu u).V) (h : B.Word → ℝ), ∃ (p0' : BaseLevelRowSide (w.D (SRe.upL Z S' N h))) (t' : RowsT K w (SRe.upL Z S' N h) Wt p0'), RowsSame t t' ∧ HEq t'.r.z.geo (geoHalf (a := ⟨Z.W, Z.V, Z.S, Z.N, Z.G⟩) (SRe.upL Z S' N h) (iK := t.r.z.alg) t.r.z.geo) ∧ SRe.pkOf t' = (SRe.pkOf t).up Z S' N h ∧ (Nonempty (RXs t) → Nonempty (RXs t')) := by
  intro K B f T w Z Wt p0 t S' N h
  exact GlobalTheory.Mem.R3.Rw.Up.rows_up K B f T w Z Wt p0 t S' N h
