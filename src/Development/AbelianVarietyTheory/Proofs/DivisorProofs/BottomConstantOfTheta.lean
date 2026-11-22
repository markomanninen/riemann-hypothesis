module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantNormalized
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationProportionalityRatioLeBottomPairsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraRest

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTop.BotConstPf

theorem gBig_imp {P R : GP} (hP : GBig P)
    (h : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Lc.Is μ₀ → P G μ₀ C x b → R G μ₀ C x b) : GBig R := by
  obtain ⟨CF0, h1⟩ := hP
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h2⟩ := h1 ε CF hCF
  exact ⟨C0, x0, fun C hC D large₂ he hx hr T Lc μ₀ hμ G => h G μ₀ _ _ _ hμ (h2 C hC D large₂ he hx hr T Lc μ₀ hμ G)⟩

theorem exists_prime_under {K : Type} [Field K] [NumberField K] (w : Formalism.PairingDivisionLocalBalance.Pl K) :
    ∃ p : ℕ, p.Prime ∧ (p : 𝓞 K) ∈ w.asIdeal := by
  first
  | exact @_root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem
  | exact _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem
  | (apply _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeMembershipExistence.exists_prime_mem ..)

theorem lamC_div_norm {p : ℕ} [Fact p.Prime] {u₁ u₂ : ℂ} (h₁ : u₁ ∈ Qbar) (h₂ : u₂ ∈ Qbar)
    (n₁ : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u₁‖ = 1) (n₂ : ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u₂‖ = 1) :
    u₁ / u₂ ∈ Qbar ∧ ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam (u₁ / u₂)‖ = 1 := by
  have h3 : u₁ / u₂ ∈ Qbar := div_mem h₁ h₂
  refine ⟨h3, fun lam => ?_⟩
  have e : (⟨u₁ / u₂, h3⟩ : Qbar) = ⟨u₁, h₁⟩ / ⟨u₂, h₂⟩ := rfl
  have a := n₁ lam
  have b := n₂ lam
  rw [lamC, dite_eq_left h₁] at a
  rw [lamC, dite_eq_left h₂] at b
  rw [lamC, dite_eq_left h3, e, map_div₀, norm_div, a, b, div_one]

end GlobalTheory.SqTop.BotConstPf

namespace GlobalTheory.SqTop

open BotConstPf

end GlobalTheory.SqTop

end
