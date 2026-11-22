module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHolds
public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.LeibnizOrders.LeibnizOrd

@[expose] public section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_gp_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PsiGP k := by
  first | exact @GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP | exact GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP | (intros; apply GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP <;> assumption)
