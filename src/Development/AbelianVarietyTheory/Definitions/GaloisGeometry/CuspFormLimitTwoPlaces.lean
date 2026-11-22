module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong

namespace GlobalTheory.CongL

def SeedWtU : Type 1 :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (l : ℕ) [Fact l.Prime] (a : ℕ), (Qbar l ≃+* ℂ) →
    HeightOneSpectrum (𝓞 E) → HeightOneSpectrum (𝓞 E) → Submodule ℂ (UA E a → ℂ) → Submodule ℂ (UA E a → ℂ) → Prop

def SeedWtU.noCondition : SeedWtU := fun _ _ _ _ _ _ _ _ _ _ _ _ => True

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

def OverPl (ι : Qbar l ≃+* ℂ) (τ : E →+* ℂ) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x ∈ w.asIdeal, ‖ι.symm (τ (x : E))‖ < 1

def SameWtAt (ι : Qbar l ≃+* ℂ) (w : HeightOneSpectrum (𝓞 E)) (U U' : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, OverPl ι τ w → ∀ lam, HasWeightAt U τ lam ↔ HasWeightAt U' τ lam

def SameWtOff (ι : Qbar l ≃+* ℂ) (w₀ v' : HeightOneSpectrum (𝓞 E)) (U U' : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, (∀ u : HeightOneSpectrum (𝓞 E), OverPl ι τ u → Apart u w₀ ∧ Apart u v') →
    ∀ lam, HasWeightAt U τ lam ↔ HasWeightAt U' τ lam

def SeedWU2 (Ty : UnitaryAutomorphicTypeClass) (Gen : ℕ → ℕ → Multiset ℂˣ → Prop) (Wt : SeedWtU := SeedWtU.noCondition) : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ d : ℕ, FieldOK E l d →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), NonSplitSet T → ∀ U : Submodule ℂ (UA E a → ℂ), AutOffT T U →
    ∀ w₀ v' : HeightOneSpectrum (𝓞 E), ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal → IsSplitAt w₀ → ((l : ℕ) : 𝓞 E) ∈ v'.asIdeal →
    Apart v' w₀ → ∀ S Y : Finset (HeightOneSpectrum (𝓞 E)),
    ∃ Z₀ : Finset (HeightOneSpectrum (𝓞 E)),
      (∀ z ∈ Z₀, UsPl d z ∧ ((l : ℕ) : 𝓞 E) ∉ z.asIdeal ∧ Apart z w₀ ∧ ApartAll S z) ∧
      ∀ U' : Submodule ℂ (UA E a → ℂ), AutOffT T U' → SameWtOff ι w₀ v' U U' → Wt E l a ι w₀ v' U U' →
      Ty E l a w₀ U' → SphOffU w₀ S U' → (∀ z ∈ Z₀, GenAtU Gen U' z) →
      ∃ r : G E Ω →* GL (Fin a) (Qbar l), Continuous r ∧ IsSSRep r ∧
        (∃ (V : Set (G E Ω)) (X : Finset (HeightOneSpectrum (𝓞 E))), IsOpen V ∧ Dense V ∧
          ∀ w, w ∉ X → UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
            ∀ B, SatU U' w B → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
              (∀ s ∈ Ine (F := E) A, r s = 1) ∧ ∀ s : G E Ω, IsFrob A (normV w) s → s ∈ V →
                ((r s⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
                  ((UpperTheory.V.Af.algSat a (normV w) B).map fun b => Polynomial.X - Polynomial.C b).prod) ∧
        (∀ w ∈ Y, UsPl d w → ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ApartAll S w →
          ∀ B, SatU U' w B → Gen a (normV w) B → UpperTheory.V.Af.FrobEig ι r w (UpperTheory.V.Af.algSat a (normV w) B)) ∧
        (∀ w ∈ Y, ((l : ℕ) : 𝓞 E) ∈ w.asIdeal → Apart w w₀ → Apart w v' → ApartAll S w → CrysDRU U' ι r w)

theorem sameWtAt_of_off (ι : Qbar l ≃+* ℂ) {w₀ v' w : HeightOneSpectrum (𝓞 E)} {U U' : Submodule ℂ (UA E a → ℂ)}
    (h : SameWtOff ι w₀ v' U U') (hw : ∀ τ : E →+* ℂ, OverPl ι τ w → ∀ u, OverPl ι τ u → u = w)
    (h₀ : Apart w w₀) (h' : Apart w v') : SameWtAt ι w U U' :=
  by
    unfold SameWtAt SameWtOff at *
    exact fun τ hτ lam => h τ (fun u hu => by rw [hw τ hτ u hu]; exact ⟨h₀, h'⟩) lam

end GlobalTheory.CongL

end
