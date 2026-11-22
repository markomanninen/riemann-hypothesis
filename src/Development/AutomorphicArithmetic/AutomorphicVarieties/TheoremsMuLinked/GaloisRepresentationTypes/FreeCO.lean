module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.AlgPowConst
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.PurityTempered.Temper
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.CompatCsd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMonoOdd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistenceOfGaloisRepresentationsOfHyp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.SignFix
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Formalism.PrimeAboveExistence.LenEqPlaces
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsCrysAtCyclotomicZpowRestrictDecompositionGroup

@[expose] public section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Th
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cont_units {Γ R : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Monoid R]
    [TopologicalSpace R] (f : Γ →* Rˣ) (h : Continuous fun s => (f s : R)) : Continuous f := by
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  exact h.comp continuous_inv

private theorem conj_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (g : GL (Fin n) k) (s : Γ) :
    ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (χ s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  simp only [Units.val_mul, tw_val, Matrix.mul_smul, Matrix.smul_mul]

private theorem flag_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ) (H : Subgroup Γ)
    (κ : Fin n → ↥H →* kˣ) (g : GL (Fin n) k)
    (hg : ∀ s : ↥H, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) k) i j = 0) ∧
      ∀ i, (g * r s * g⁻¹ : GL (Fin n) k) i i = (κ i s : k)) :
    W.HasFlag ((tw r χ).comp H.subtype) fun i => κ i * χ.comp H.subtype := by
  refine ⟨g, fun s => ⟨fun i j hij => ?_, fun i => ?_⟩⟩
  · have := (hg s).1 i j hij
    show ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0
    rw [conj_tw, Matrix.smul_apply]
    exact smul_eq_zero_of_right _ this
  · have := (hg s).2 i
    show ((g * tw r χ s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = _
    rw [conj_tw, Matrix.smul_apply, smul_eq_mul, this]
    exact mul_comm _ _

private theorem pow_fixes (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] {M : ℕ} (hM : 1 ≤ M) :
    ∃ k : ℕ, 0 < k ∧ ∀ (s : G F Ω) (ζ : Ω), ζ ^ M = 1 → (s ^ k) ζ = ζ := by
  classical
  have hfin : {ζ : Ω | ζ ^ M = 1}.Finite := by
    refine ((Polynomial.nthRoots M (1 : Ω)).toFinset.finite_toSet).subset fun ζ hζ => ?_
    simpa [Polynomial.mem_nthRoots (show 0 < M by omega)] using hζ
  haveI : Finite {ζ : Ω // ζ ^ M = 1} := hfin
  let f : G F Ω →* Equiv.Perm {ζ : Ω // ζ ^ M = 1} :=
    { toFun := fun s => Equiv.Perm.subtypePerm (s : Ω ≃ₐ[F] Ω).toEquiv fun x => by
        change s x ^ M = 1 ↔ x ^ M = 1
        rw [← map_pow, map_eq_one_iff _ (s : Ω ≃ₐ[F] Ω).injective]
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  refine ⟨Nat.card (Equiv.Perm {ζ : Ω // ζ ^ M = 1}), Nat.card_pos, fun s ζ hζ => ?_⟩
  have h1 : f (s ^ Nat.card (Equiv.Perm {ζ : Ω // ζ ^ M = 1})) = 1 := by
    rw [map_pow, pow_card_eq_one']
  exact congrArg (fun p : Equiv.Perm {ζ : Ω // ζ ^ M = 1} => (p ⟨ζ, hζ⟩ : Ω)) h1
