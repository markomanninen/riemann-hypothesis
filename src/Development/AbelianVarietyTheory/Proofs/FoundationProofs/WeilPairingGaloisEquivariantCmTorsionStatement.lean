module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilPairingGaloisEquivariantCmTorsion
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_galois_equivariant_cm_torsion : ∀ D : D7, WeilPairingGaloisAlt D := by
  first | exact @GlobalTheory.WeilPairingGalois.weilPairingGalois_all | exact GlobalTheory.WeilPairingGalois.weilPairingGalois_all | (intros; apply GlobalTheory.WeilPairingGalois.weilPairingGalois_all <;> assumption)
