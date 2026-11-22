module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaZeroMeanLogNormConjugatesOfWeberStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticePeriodEtaObj
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaWeberStatement

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory.Theta0MeanLeC

theorem theta0MeanLeC : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D :=
  (GlobalTheory.T.thetaZero_mean_log_norm_conjugates_of_weber GlobalTheory.LatticePeriodEtaObj.latticePeriodEta_obj GlobalTheory.ThetaWeberObj.thetaWeberStatement).1.2.2

end GlobalTheory.Theta0MeanLeC
