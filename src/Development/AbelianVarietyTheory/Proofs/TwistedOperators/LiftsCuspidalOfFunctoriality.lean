module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealDiscreteSeriesDataThetaPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeriesStatement

@[expose] public section

namespace GlobalTheory.PairLift

theorem liftsCuspidal_of_functoriality (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules)
    (hC : GlobalTheory.Published.CuspRapidDecay) (hW : GlobalTheory.Published.CasselmanWallach) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal := by
  obtain ⟨X, hX, -, -, h3, h4, h5⟩ := GlobalTheory.T.exists_real_discreteSeries_data_theta_properties hD hH
  have I := fun D => GlobalTheory.T.thetaPairAnalyticHypotheses_of_discreteSeries hD hH hC hW D X hX
  exact liftsCuspidal X hX h3 h4 h5 hH hC (fun D => (I D).bridge) (fun D => (I D).vacChar) (fun D => (I D).lie)
    (fun D => (I D).cpt) (fun D => (I D).dense) (fun D => (I D).laws) (fun D => (I D).const) (fun D => (I D).ext)

end GlobalTheory.PairLift
