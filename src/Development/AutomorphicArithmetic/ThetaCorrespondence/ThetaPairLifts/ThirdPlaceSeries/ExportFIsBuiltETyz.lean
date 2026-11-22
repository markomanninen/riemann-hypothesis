module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnramifiedNoJump
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistAllPowersOfGaloisCohomologyClassField
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaChr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmbientBaseHeq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRationalRows
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAveragedSeriesOfClassSumsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullRankThetaSeriesFormsOfRationalScalarsStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedPlaceIndexMemFirstPairOfCompatibleChoice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorPreservesSupLatticeRealSideStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaSeriesRationalityAndCoefficientBoundStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.WeightsConj
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CoreAltAltBis
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwJoin
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec

@[expose] public section

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TwSys GlobalTheory.LiftLeaf GlobalTheory.TwAll GlobalTheory.SupLaw
namespace GlobalTheory.ExportFirst
abbrev _root_.GlobalTheory.ExportFirst.exportF_isBuiltE_tyz : Prop :=  GlobalTheory.TwSys.Cheb → GlobalTheory.Published.PoitouTateTotallyComplex → GlobalTheory.Published.CohDimTwo → GlobalTheory.Published.TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → GlobalTheory.Published.RayCharacterArtin → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt → GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt → GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → GlobalTheory.HeckeSupSt.HeckeReadTie → GlobalTheory.Published.AutomorphicFormsFiniteGL → _root_.UpperTheory.GalS.CuspUAlt → GlobalTheory.Published.DeRhamPotSemistable → _root_.UpperTheory.GalS.CarUAlt → (∀ D : D7, LocalSituation.Conclusion5 D) → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (p : _root_.GlobalTheory.Mem.Top.Bl.Parameters hL), (GlobalTheory.Mem.Top.EvLgG fun K B f T => GlobalTheory.Mem.Top.Bl.KPx B f → T = GlobalTheory.Mem.Top.TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (p.N K B f T w Z Wt p0 t nch n xd c) → Nonempty (p.R K B f T w Z Wt p0 t) → GlobalTheory.Mem.Top.Bl.ColPin w → Nonempty (_root_.GlobalTheory.TwInputs.TwistNormChoice hL K B f T w Z Wt p0 t nch n xd c)) → GlobalTheory.Mem.Top.GroupRetwisting.ExportF GlobalTheory.Mem.Top.Bl.KPx (GlobalTheory.Mem.Top.Bl.IsBuiltE p.s)
end GlobalTheory.ExportFirst
end
