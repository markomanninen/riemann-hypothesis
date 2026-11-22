module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaProductPowAlgebraicModulusOneAll
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkLat
public import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg

@[expose] public section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kappaProduct_pow_algebraicModulusOneAll : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (m : ℕ), StandardLatticesGL3.Mod1All (B.kappa ^ m) := by
  first | exact @GlobalTheory.KappaPowMod.kappa_pow_mod1All | exact GlobalTheory.KappaPowMod.kappa_pow_mod1All | (intros; apply GlobalTheory.KappaPowMod.kappa_pow_mod1All <;> assumption)
