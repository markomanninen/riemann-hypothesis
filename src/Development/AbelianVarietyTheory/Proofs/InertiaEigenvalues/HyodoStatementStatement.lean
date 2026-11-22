module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HyodoStatement
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyodo_statement : Hyodo := by
  first | exact @GlobalTheory.PMon.hyodo | exact GlobalTheory.PMon.hyodo | (intros; apply GlobalTheory.PMon.hyodo <;> assumption)
