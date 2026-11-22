module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.GeometricRealizationOfWeightOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LefschetzFixedPointFiniteEtaleCorrespondence

@[expose] public section

namespace UpperTheory.Gal.Int.Geo

theorem weight_one_geometric_realization : LocalSmoothExtension.HolomorphicLefschetzFormula := by
  unfold LocalSmoothExtension.HolomorphicLefschetzFormula
  exact GlobalTheory.T.lefschetz_fixedPoint_finite_etale_correspondence

theorem geoOne_holds : GeoOne := geometric_realization_of_weight_one weight_one_geometric_realization

end UpperTheory.Gal.Int.Geo
