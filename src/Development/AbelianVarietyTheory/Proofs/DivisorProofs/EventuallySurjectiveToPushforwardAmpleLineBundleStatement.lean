module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySurjectiveToPushforwardAmpleLineBundle
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_surjective_toPushforward_ampleLineBundle_pow : ∀ (k : Type) [CommRing k] [IsNoetherianRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsProjOver p → ∀ (L : LB X), IsAmpleLB L → ∀ (T : Scheme.{0}) (i : T ⟶ X) [IsClosedImmersion i], ∀ᶠ N in atTop, Function.Surjective ((GlobalTheory.LB.toPushforward (lbPow L N) i).app ⊤) := by
  exact @GlobalTheory.surjective_toPushforward_app_top_lbPow
