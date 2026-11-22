module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroPotentiallySemistableOfSenTheorem
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightZero_potentiallySemistable_of_sen_theorem : SenStep := by
  first | exact @GlobalTheory.PMon.senStep | exact GlobalTheory.PMon.senStep | (intros; apply GlobalTheory.PMon.senStep <;> assumption)
