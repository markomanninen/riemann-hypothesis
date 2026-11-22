module

public import Mathlib
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.InertKernelTheory.GenusOneModelExistsLattice
public import Formalism.LocalToGlobal.InertKernelTheory.StatementJets
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlgT
public import Formalism.LocalToGlobal.InertKernelTheory.KernelsIntegralInert

@[expose] public section

namespace GlobalTheory

theorem intInert_of_complexMultiplication_condition : Formalism.L2.Th1.CM.CM2 → Formalism.L2.KerInert.IntInert :=
  fun h => by
    haveI : Fact Formalism.L2.Th1.CM.CM2 := ⟨h⟩
    exact Formalism.L2.KerInert.kernels_integral_inert

end GlobalTheory
