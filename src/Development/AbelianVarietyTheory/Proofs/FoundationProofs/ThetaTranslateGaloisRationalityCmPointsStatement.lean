module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTranslate_galoisRationality_cmPoints : ∀ D : D7, gal D := by
  first | exact @GlobalTheory.GalTheta.gal_all | exact GlobalTheory.GalTheta.gal_all | (intros; apply GlobalTheory.GalTheta.gal_all <;> assumption)
