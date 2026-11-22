module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesPureInnerProductsTensorProduct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChosenSeries

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Matrix GlobalTheory.Chain GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discreteSeries_pureInnerProducts_tensorProduct : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), TensorLaw M := by
  first | exact @GlobalTheory.Chain.RealIt.tensorLaw | exact GlobalTheory.Chain.RealIt.tensorLaw | (intros; apply GlobalTheory.Chain.RealIt.tensorLaw <;> assumption)
