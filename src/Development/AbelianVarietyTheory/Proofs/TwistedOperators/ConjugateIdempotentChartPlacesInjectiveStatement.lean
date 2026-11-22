module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIdempotentChartPlacesInjective
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOrEqOfPlaceIdem
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinprodLocalDifferentIdealNormEqDiscr
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ProductLocalDensitiesAdeleCharacter

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_idempotent_chart_places_injective : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), (∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) → e = ∑ Q ∈ P, es Q → e * cA D e = 0 → ∀ v : ↥P → HeightOneSpectrum (𝓞 D.host.F), (∀ Q : ↥P, ∃ π : AE D →+* Fv D.host.F (v Q), GlobalTheory.SplitHecke.Chart (cA D (es Q)) (v Q) π) → Function.Injective v := by
  first | exact @GlobalTheory.ChartPlaces.chart_places_injective | exact GlobalTheory.ChartPlaces.chart_places_injective | (intros; apply GlobalTheory.ChartPlaces.chart_places_injective <;> assumption)
