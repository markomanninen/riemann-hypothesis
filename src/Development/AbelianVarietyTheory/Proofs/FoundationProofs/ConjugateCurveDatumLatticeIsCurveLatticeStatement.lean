module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice : ∀ D : D7, galCurve D := by
  first | exact @GlobalTheory.ConjCurve.galCurve_holds | exact GlobalTheory.ConjCurve.galCurve_holds | (intros; apply GlobalTheory.ConjCurve.galCurve_holds <;> assumption)
