module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftThroughCompletionIso
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValLeOneOfMemKO
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceUnitsCharacterEqOfAgreeOnField
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoric
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharacterEqInvAtTransposeInvLowerBlockDet
public import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTameInflationCharacterOfPadicIsoStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleSmoothPullbackPadicRingIsoStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfBlockTypeVectorPadicIsoStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectorsStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicLocalComponentFixedStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLanglandsSplitQp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.L2.Host

namespace GlobalTheory.LocCompTy

open GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

theorem rt_mem_isoTyp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
    (S : Submodule ℂ (GAf L n → a.W)) (h : GAf L n) {f : GAf L n → a.W}
    (hf : f ∈ NG.isoTyp a.ρ S) : NG.rt L n h f ∈ NG.isoTyp a.ρ S := by
  have : NG.isoTyp a.ρ S ≤ (NG.isoTyp a.ρ S).comap (NG.rt L n h) := by
    refine sSup_le fun S' hS' => ?_
    intro y hy
    exact le_sSup hS' (hS'.1.1.stable h y hy)
  exact this hf



end GlobalTheory.LocCompTy
