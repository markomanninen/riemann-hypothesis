module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdmissibleRepresentationFactorisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
public import Formalism.SharpRestriction.Divisibility.LatticeTransfer
public import Development.AbelianVarietyTheory.Definitions.Divisors.PrismaticDieudonnePerfdIff
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsWeilChar
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
public import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationPrimitiveRootPrimePowSubOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimsLeHeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuoti
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIdeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopfStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulPMemFrobeniusKernelOfVerschiebungEqZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebungStatement

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.PDivGroup.CotDim in
theorem GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] (hp : (p : k) = 0) (Γ : PDivGroup p k) :
    Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Γ.height := by
  letI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hp
  have hdimD := finrank_level_one Γ.dual
  have hmulP : Function.Injective (Γ.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := Γ.dual_mulP_surjective 1 φ
    change ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)
    rw [e]

  have hord := finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((PDivGroup.relFrob hp Γ.dual).app 1)
  have hcot (G : PDivGroup p k) :
      p ^ Module.finrank k (Cot k (G.A 1)) ≤
        Module.finrank k (G.A 1 ⧸ kerIdeal ((PDivGroup.relFrob hp G).app 1)) :=
    (FrobKerOrder.pow_finrank_cot_le (p := p) (k := k) (H := G.A 1)).trans
      (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp G 1))

  have hker : LinearMap.ker ((PDivGroup.verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (PDivGroup.frobTwist hp Γ).A 1).toLinearMap ≤
      (kerIdeal ((PDivGroup.relFrob hp Γ).app 1)).restrictScalars k := by
    intro a ha
    have h := GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero p k hp Γ a ha
    rw [kerIdeal_comp] at h
    change a ∈ kerIdeal ((PDivGroup.relFrob hp Γ).app 1)
    rw [← GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf k _ _ (Γ.mulP 1) hmulP
      (kerIdeal ((PDivGroup.relFrob hp Γ).app 1))]
    exact h
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p k hp Γ
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((PDivGroup.relFrob hp Γ).app 1)).restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((PDivGroup.relFrob hp Γ).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((PDivGroup.relFrob hp Γ).app 1)) ≤
      Module.finrank k (LinearMap.range ((PDivGroup.relFrob hp Γ.dual).app 1 :
        (PDivGroup.frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) := by omega
  apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1
  change _ ≤ p ^ Γ.dual.height
  rw [pow_add, mul_comm, ← hdimD, hord]
  exact Nat.mul_le_mul (hcot Γ.dual) ((hcot Γ).trans hrD)
