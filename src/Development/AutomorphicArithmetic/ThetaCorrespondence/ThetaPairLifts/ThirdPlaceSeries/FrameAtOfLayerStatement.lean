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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFinEMemDivisorStandard
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateBlockUpperOfEigenfunctionUnipotentTypeStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralFrameSplitNontrivialAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsResidueNeZeroOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.G0LiftUnitaryCentralFrame
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjParahoricBlockLiftStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NormChoiceOfExtension
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NGalTied
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RingSpecNormalisedCharacterEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FrameAtOfLayer
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameAt_of_tup_eq_mu_at_members : ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t _ _ c => ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s k, t.r.Y.tup s = (w.st Z).toD7.nd.mu i → GlobalTheory.CenLocAt.FrameAt t.r.Y t.r.z.cG k (ad.PV k) s := by
  first | exact @_root_.GlobalTheory.CenLocAt.frameAt_of_layer_alt | exact _root_.GlobalTheory.CenLocAt.frameAt_of_layer_alt | (intros; apply _root_.GlobalTheory.CenLocAt.frameAt_of_layer_alt <;> assumption)
end
