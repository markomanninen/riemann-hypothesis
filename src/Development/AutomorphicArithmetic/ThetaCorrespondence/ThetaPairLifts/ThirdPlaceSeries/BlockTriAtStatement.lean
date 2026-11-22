module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsXdAllIff
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JumpsCardOfBuilt
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CenterEqSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCompOfOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateBlockUpperOfEigenfunctionUnipotentTypeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralFrameSplitNontrivialAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueNeZeroOne
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BlockTriAt
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_frame_split_place_nontrivial_alt : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c =>
  ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s (k : Fin (w.st Z).toD7.R.m), t.r.Y.tup s = (w.st Z).toD7.nd.mu i →
    Nontrivial ((w.st Z).toD7.what₂.Mt (t.r.Y.tup s) ((k : ℕ) + 1)) →
    ∀ (s' : ReciprocityTheory.Aut.SplitPlace (w.st Z).toD7.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin (w.st Z).toD7.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w ∈ t.r.z.R.Pg → GlobalTheory.CenFrame.IsResidue s' φ →
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV (w.st Z).toD7 k) (ad.PV k) (t.r.z.R.βV k) s' φ b →
        b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 (w.st Z).toD7.R.r) := by
  first | exact @_root_.GlobalTheory.FrameBlockTriangular.blockTri_at_alt | exact _root_.GlobalTheory.FrameBlockTriangular.blockTri_at_alt | (intros; apply _root_.GlobalTheory.FrameBlockTriangular.blockTri_at_alt <;> assumption)
end
