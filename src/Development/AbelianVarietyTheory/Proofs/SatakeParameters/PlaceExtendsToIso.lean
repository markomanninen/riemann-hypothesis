module

public import Mathlib
public import Formalism.LocalToGlobal.InertKernelTheory.StatementIota
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MkLeContinuumOfDenseRange

@[expose] public section

namespace GlobalTheory.ThLoc

theorem place_extends_to_iso : Formalism.L2.KerInert.LamExt :=
  fun p _ lam => GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p lam

end GlobalTheory.ThLoc
