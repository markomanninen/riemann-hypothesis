module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExpFactorAllOrbitsEqProdOrbits
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.KappaIntegralOfCalculation
public import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.OfClosedInt
public import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne
public import Formalism.GaussJetBounds.GaussJetProofs.LogarithmWeightComparison
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitPowerSeriesCoefficients.OrbEmb
public import Formalism.GaussJetBounds.GaussJetProofs.OrbMul
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OrbitJetDegreeBound.JetTdegEqDegree
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralOrbitSeries
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesBConditionsLargePrime

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open MvPowerSeries
open Formalism.DworkPowerSeriesWeights (Integral mvExp entLog ZV)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expFactor_allOrbits_eq_prod_orbits : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (R : Finset (OrbitPlaces.Pl D)) {M N N' : ℕ} (eA : Fin M ≃ R × Fin N)
    (be : MvPowerSeries (ZMod (nP D p)) ℂ_[p]) (hbe : constantCoeff be = 0), subst (fun y : ZV (nP D p) M N' =>
        (X (OrbitPlaces.orbMap D p (eA y.2.1).1 y.1, (eA y.2.1).2, y.2.2) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]))
      (mvExp ((-1 : ℂ_[p]) • Formalism.DworkPowerSeriesWeights.bSum (Formalism.DworkPowerSeriesWeights.idM : ZV (nP D p) M N' → ZV (nP D p) M N' → ℂ_[p]) be)) =
      product_zeroth_first_parts.expS ℂ_[p] (OrbitPlaces.beAll D p (N0 := N) (N1 := N') R (fun _ => -1) (fun _ => be)) := by
  first | exact @GlobalTheory.ExpFacOrbits.expFactor_allOrbits | exact GlobalTheory.ExpFacOrbits.expFactor_allOrbits | (intros; apply GlobalTheory.ExpFacOrbits.expFactor_allOrbits <;> assumption)
