module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.X0OfStarCondition
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.ClosedAtLConclusionOfMem
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotHasParamOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLocalComponentEigenvectorSplitPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.RoadW GlobalTheory.CongL Polynomial

namespace GlobalTheory.RoadWGeo

def Lacunary (J : Finset ℤ) : Prop :=
  ∀ A B : Finset ℤ, A ⊆ J → B ⊆ J → Disjoint A B → A.Nonempty → B.Nonempty →
    (B.card : ℤ) * A.sum id ≠ (A.card : ℤ) * B.sum id

theorem lacunary_of_growth {J : Finset ℤ} (hpos : ∀ x ∈ J, 0 < x) (hg : ∀ x ∈ J, ∀ y ∈ J, x < y → (J.card : ℤ) * x < y) :
    Lacunary J := by
  classical
  have key : ∀ A B : Finset ℤ, A ⊆ J → B ⊆ J → B.Nonempty → ∀ m ∈ A, (∀ b ∈ B, b < m) →
      (A.card : ℤ) * B.sum id < (B.card : ℤ) * A.sum id := by
    intro A B hA hB hBn m hm hlt
    have h1 : m ≤ A.sum id := Finset.single_le_sum (f := id) (fun x hx => (hpos x (hA hx)).le) hm
    have hc : (A.card : ℤ) ≤ J.card := by exact_mod_cast Finset.card_le_card hA
    have h2 : ∑ b ∈ B, (A.card : ℤ) * b < ∑ _b ∈ B, m := by
      refine Finset.sum_lt_sum_of_nonempty hBn fun b hb => ?_
      have := hg b (hB hb) m (hA hm) (hlt b hb)
      have := mul_le_mul_of_nonneg_right hc (hpos b (hB hb)).le
      linarith
    rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at h2
    have h3 : (B.card : ℤ) * m ≤ B.card * A.sum id := mul_le_mul_of_nonneg_left h1 (by positivity)
    exact lt_of_lt_of_le h2 h3
  intro A B hA hB hd hAn hBn
  have hne : (A ∪ B).Nonempty := hAn.mono Finset.subset_union_left
  have hmax : ∀ x ∈ A ∪ B, x ≤ (A ∪ B).max' hne := fun x hx => Finset.le_max' _ _ hx
  rcases Finset.mem_union.1 (Finset.max'_mem _ hne) with hm | hm
  · refine (key A B hA hB hBn _ hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_right _ hb)) ?_).ne'
    intro e
    exact Finset.disjoint_left.1 hd hm (e ▸ hb)
  · refine (key B A hB hA hAn _ hm fun b hb => lt_of_le_of_ne (hmax b (Finset.mem_union_left _ hb)) ?_).ne
    intro e
    exact Finset.disjoint_left.1 hd hb (e ▸ hm)

theorem not_lacunary_three (k : ℤ) : ¬ Lacunary ({k, k + 1, k + 2} : Finset ℤ) := by
  intro h
  have h02 : k ≠ k + 2 := by omega
  refine h {k, k + 2} {k + 1} ?_ ?_ ?_ (by simp) (by simp) ?_
  · intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · intro x; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  · simp only [Finset.disjoint_singleton_right, Finset.mem_insert, Finset.mem_singleton]; omega
  · rw [Finset.sum_pair h02, Finset.card_pair h02]; simp; ring

def wtJumps {a : ℕ} (lam : DomWeight a) : Finset ℤ :=
  Finset.univ.image fun k : Fin a => ((k : ℕ) : ℤ) - lam.w k

theorem strictMono_jump {a : ℕ} (lam : DomWeight a) : StrictMono fun k : Fin a => ((k : ℕ) : ℤ) - lam.w k := by
  intro i j hij
  have h1 := lam.anti hij.le
  have h2 : (i : ℕ) < j := hij
  simp only
  omega

theorem card_wtJumps {a : ℕ} (lam : DomWeight a) : (wtJumps lam).card = a := by
  rw [wtJumps, Finset.card_image_of_injective _ (strictMono_jump lam).injective]; simp

theorem wtJumps_val {a : ℕ} (lam : DomWeight a) :
    (wtJumps lam).val.map (fun n : ℤ => (n : ℂ)) = (infOfWeight lam).map (fun z => ((a : ℂ) - 1) / 2 - z) := by
  rw [wtJumps, Finset.image_val_of_injOn (strictMono_jump lam).injective.injOn, infOfWeight, Multiset.map_map, Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  simp only [Function.comp]
  push_cast
  ring

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsCMField E] {l : ℕ} [Fact l.Prime]

def ESAt {d : ℕ} (ι : Qbar l ≃+* ℂ) (ρ : G E Ω →* GL (Fin d) (Qbar l)) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂ) :
    Prop :=
  ∀ A : ValuationSubring Ω, IsPlaceOver A w → (∀ s ∈ Ine (F := E) A, ρ s = 1) ∧
    ∀ σ : G E Ω, IsFrob A (normV w) σ →
      aeval (ρ σ⁻¹ : Matrix (Fin d) (Fin d) (Qbar l)) (((B.map fun b => X - C b).prod).map ι.symm.toRingHom) = 0

def LacWtAt {a : ℕ} (ι : Qbar l ≃+* ℂ) (v' : HeightOneSpectrum (𝓞 E)) (U : Submodule ℂ (UA E a → ℂ)) : Prop :=
  ∃ τ : E →+* ℂ, OverPl ι τ v' ∧ ∃ lam : DomWeight a, HasWeightAt U τ lam ∧ Lacunary (wtJumps lam)

end GlobalTheory.RoadWGeo

namespace GlobalTheory.Published

open GlobalTheory.RoadWGeo

end GlobalTheory.Published

end
