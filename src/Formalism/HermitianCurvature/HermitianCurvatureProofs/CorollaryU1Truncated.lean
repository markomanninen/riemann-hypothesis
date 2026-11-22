module

public import Formalism.HermitianCurvature.StatementU
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCost
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DirectionsInParabolic
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses

@[expose] public section

theorem Formalism.FourierDecayAlt.P.derivative_cost_bound : Formalism.FourierDecayAlt.U.DerivativeCost := by
  have hS : Formalism.FourierDecayAlt.U.SliceMem := Formalism.FourierDecayAlt.P.slice_membership
  have h21 : Formalism.FourierDecayAlt.U.SliceCoordinateSizes :=
    Formalism.FourierDecayAlt.P.Ux6.coordinate_sizes_of_hypotheses hS Formalism.FourierDecayAlt.P.block3_apply_embedding Formalism.FourierDecayAlt.P.aux_statement_17
      Formalism.FourierDecayAlt.P.hat_z_on_slice
  exact operator_word_cost hS Formalism.FourierDecayAlt.P.radical_parametrisation Formalism.FourierDecayAlt.P.slice_right_coordinates
    Formalism.FourierDecayAlt.P.slice_left_coordinates Formalism.FourierDecayAlt.P.slice_z_coordinates Formalism.FourierDecayAlt.P.directions_in_parabolic h21
