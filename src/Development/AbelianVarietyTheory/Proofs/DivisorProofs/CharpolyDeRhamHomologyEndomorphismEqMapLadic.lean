module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.SplitTori.SplitTorusAff
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFieldSmoothOfRelativeDimensionExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LPowerTorsionEndomorphismEvaluation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharPStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyDeRhamHomologyAbelianVarietyCharZeroStatement

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Cris GlobalTheory.DeRham

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

theorem charpoly_push_eq_map_charpoly (k : Type) [Field k] [IsAlgClosed k]
    (B : GlobalTheory.AV.AbVar k) (f : B ⟶ B) [Module.Finite k (HdR B.X)] :
    LinearMap.charpoly (push (dp0 k) (𝟙 _) f.hom) =
      (GlobalTheory.AV.AbVar.charpoly (End.of f)).map (Int.castRingHom k) := by
  obtain ⟨p, hp⟩ := CharP.exists k
  rcases CharP.char_is_prime_or_zero k p with h | h
  · haveI : Fact p.Prime := ⟨h⟩
    exact GlobalTheory.T.charpoly_deRhamHomology_abelianVariety_charP p k B f
  · subst h
    have : CharZero k := CharP.charP_to_charZero k
    have hcharpoly := GlobalTheory.DeRhamCharpolyZero.charpoly_push k B f
    exact hcharpoly

theorem charpoly_push_eq : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (f : A ⟶ A) [IsMonHom f] (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
      (φ : L →ₗ[ℤ] L) (l : ℕ), l.Prime → (l : k) ≠ 0 →
      ∀ ev : ℕ → L → (Over.mk (𝟙 (Sp k)) ⟶ A),
      (∀ j x y, ev j (x + y) = ev j x * ev j y) →
      (∀ j x, ev j (φ x) = ev j x ≫ f) →
      (∀ j x, ev j x = 1 ↔ ∃ y, x = l ^ j • y) →
      (∀ j (q : Over.mk (𝟙 (Sp k)) ⟶ A), q ^ (l ^ j) = 1 ↔ ∃ x, ev j x = q) →
      ∀ [Module.Finite k (HdR A)],
        LinearMap.charpoly (push (dp0 k) (𝟙 _) f) = (LinearMap.charpoly φ).map (Int.castRingHom k) := by
  intro k _ _ A _ _ hA f _ L _ _ _ φ l hl hlk ev hadd hφ hker him _
  obtain ⟨g, hg⟩ := GlobalTheory.AV.exists_smoothOfRelativeDimension_of_isAbelianScheme k A hA
  let B : GlobalTheory.AV.AbVar k := ⟨A, hA, g, hg⟩
  let f' : B ⟶ B := GlobalTheory.AV.AbVar.Hom.mk (A := B) (B := B) f
  rw [GlobalTheory.T.l_power_torsion_endomorphism_evaluation k B f' L φ l hl hlk ev hadd hφ hker him]
  exact charpoly_push_eq_map_charpoly k B f'

end GlobalTheory.DeRham
