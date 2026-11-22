module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveKernelCoindIntertwiningMap
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BlockProductIsomorphism
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions

@[expose] public section

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_kernel_coind_intertwiningMap : ∀ (G : Type) [Group G] [Finite G] (P P' : Subgroup G) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ P V) (σ' : Representation ℂ P' V'), ∃ K : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ') →ₗ[ℂ] (G → V →ₗ[ℂ] V'), Function.Injective K ∧ ∀ (Φ : Representation.IntertwiningMap (Representation.coind P.subtype σ) (Representation.coind P'.subtype σ')) (p' : P') (g : G) (p : P), K Φ ((p' : G) * g * (p : G)) = σ' p' ∘ₗ K Φ g ∘ₗ σ p := by
  first | exact @GlobalTheory.CoindKernel.exists_kernel | exact GlobalTheory.CoindKernel.exists_kernel | (intros; apply GlobalTheory.CoindKernel.exists_kernel <;> assumption)
