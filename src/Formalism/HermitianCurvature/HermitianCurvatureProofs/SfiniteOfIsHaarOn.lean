module

public import Formalism.HermitianCurvature.CompositeFormulaOfDensities
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSplitAssocMeasurePreserving
public import Formalism.HermitianCurvature.TopDensNonnegOfKappa
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HerClassesOfParts
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopDensNonnegOfKappa
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignedCoordinateEqSignSmul
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfWaveQQ
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvSelf
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RadJFExists
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopTwistDensOfZeta
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm

@[expose] public section

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd

theorem sfinite_of_isHaarOn {k r : ℕ} (U : Set (B.Mat k r)) (μ : Measure (Mt k r)) (h : B.IsHaarOn U μ) :
    SFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  infer_instance

end Formalism.FourierDecayAlt.P5
