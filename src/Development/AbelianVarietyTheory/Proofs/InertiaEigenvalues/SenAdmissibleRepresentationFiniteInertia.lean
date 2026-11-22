module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenFiniteOfNoTower
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfMemInertia

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem senFinite : SenFinite := GlobalTheory.PMon.Ram.senFinite_of_noTower GlobalTheory.PMon.Ram.noTower

end GlobalTheory.PMon
