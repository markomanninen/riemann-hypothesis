module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermMMulTranspose
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFramesStrongApproximationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeRealCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataPrincipalCongruenceLevel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaTermTsumLeTwo
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogClassNumberLeLogAbsDiscrDiv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndexBoundOfPublished
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyCompactSecondCountableBorelCountable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsInertPlOfInertOff
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousEquivariantDetOneFactorProjectioStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupMeasureDecomposition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainOrthonormalFrameIdentificationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousRealComponentHomUnitaryAdelicStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateLevelRealBoxLeIndexMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentRepresentativesInjectiveDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicSplit
public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartMemFullLevelOfKeepsSelfDualLatticeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceConjMemArithmeticGroup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCongruenceIffCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitaryPartIsInvertibleUnitaryAdelic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SignatureUnitaryLatticeFamily
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

@[expose] public section

section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
abbrev _root_.GlobalTheory.T.CovolumeRatioIdentity : Prop :=  ∀ (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (D : D7) (Tu : Type) (C : LevCh D Tu) (t0 : Tu) (hC : C.Is t0) (i : Fin D.R.m) (P : LevelP C.Pg D.R.r ℂ) (μ : MeasureTheory.Measure (GA D (Wc D i))) (𝓕 : Set (GA D (Wc D i))) (hF : IsMeasFD (Wc D i) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW C i P) μ 𝓕) (L : ℝ) (hL : GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.Sizes D L), Real.log (μ 𝓕).toReal ≤ D.R.f * (D.R.r : ℝ) ^ 2 * Real.log ((D.R.r : ℝ) + 3) + (38 + 81) * (D.R.f * (D.R.r : ℝ) ^ 2 * L)
end
