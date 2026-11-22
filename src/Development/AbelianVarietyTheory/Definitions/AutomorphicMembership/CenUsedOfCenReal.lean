module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OExt
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsNormalisedOfIsDiscrete
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RationalRayLevels
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsValueTiedOfIsToricElt
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight

@[expose] public section

noncomputable section

namespace GlobalTheory.HeightCounting.Up

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting
  GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure PrN : Prop where
  what₂ : GlobalTheory.NRows.Hypotheses₂
  decay : GlobalTheory.Published.CuspRapidDecay
  hc : GlobalTheory.Published.HarishChandraFinite
  greenC : GlobalTheory.Published.GreenCuspidal
  green : GlobalTheory.GLq.Green
  zel : GlobalTheory.Published.ZelevinskyPolynomialRing
  dz : GlobalTheory.Published.DepthZeroInertia
  ray : GlobalTheory.Published.RayClassFieldSt
  rayF : GlobalTheory.NT.RayField
  rayA : GlobalTheory.Published.RayCharacterArtin
  bc : GlobalTheory.Published.BaseChangeDefiniteUnitary
  ds : GlobalTheory.Published.DiscreteSpectrumGL
  gen : GlobalTheory.Published.GenericUnitaryDualGL
  std : GlobalTheory.Published.StandardCosocleGL
  cheb : GlobalTheory.TwSys.Cheb
  howe : GlobalTheory.Hk3.HoweUnram

structure SerN : Prop where
  rat : GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat
  int : GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt
  hkInt : GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39.HeckeInt
  hkTr : GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform
  hkRead : GlobalTheory.HeckeSupSt.HeckeReadTie
  ratio : GlobalTheory.ToricRational.RatioConj

def RootsLL (D : D7) : Prop := ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ D.what₂.restRowsFiniteGroupCard

end GlobalTheory.HeightCounting.Up

end
