module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.BasisExtend

@[expose] public section

namespace GlobalTheory.CompanionTheory.FieldDeg

open ReciprocityTheory.ChartRestriction.G.T0.VariableBasisExtension

theorem finrank_fraction_over_adjoin_X_eq (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [Algebra Ω₀ Ω]
    [FiniteDimensional Ω₀ Ω] (I : Type)
    [Algebra Ω₀ (FractionRing (MvPolynomial I Ω))]
    (hF : algebraMap Ω₀ (FractionRing (MvPolynomial I Ω)) =
      (algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp (algebraMap Ω₀ Ω)) :
    Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
        algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)))
      (FractionRing (MvPolynomial I Ω)) = Module.finrank Ω₀ Ω := by
  classical
  let φ : FractionRing (MvPolynomial I Ω₀) →+* FractionRing (MvPolynomial I Ω) :=
    liftY (L := Ω₀) (E := Ω) (σ := I)
  let : Algebra (FractionRing (MvPolynomial I Ω₀)) (FractionRing (MvPolynomial I Ω)) :=
    φ.toAlgebra
  have hφ : ∀ a : MvPolynomial I Ω₀, φ (algebraMap _ _ a) =
      algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))
        (MvPolynomial.map (algebraMap Ω₀ Ω) a) := fun a => by
    simp only [φ, liftY, IsFractionRing.lift_algebraMap, RingHom.comp_apply]
  have h1 : Module.finrank (FractionRing (MvPolynomial I Ω₀)) (FractionRing (MvPolynomial I Ω)) =
      Module.finrank Ω₀ Ω := by
    let : Algebra (MvPolynomial I Ω₀) (MvPolynomial I Ω) := MvPolynomial.algebraMvPolynomial
    let b := Module.finBasis Ω₀ Ω
    let j := algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))
    let v := fun i => j (MvPolynomial.C (b i))
    let S := Submodule.span (FractionRing (MvPolynomial I Ω₀)) (Set.range v)
    have hsmul (q : MvPolynomial I Ω₀) (p : MvPolynomial I Ω) :
        j (q • p) =
          (algebraMap (MvPolynomial I Ω₀) (FractionRing (MvPolynomial I Ω₀)) q) • j p := by
      rw [Algebra.smul_def, Algebra.smul_def]
      change j (_ * p) = φ (algebraMap _ _ q) * j p
      rw [map_mul, hφ]
      rfl
    have hj (p : MvPolynomial I Ω) : j p ∈ S := by
      rw [ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis.eq_sum_crd b p, map_sum]
      simp only [hsmul]
      exact Submodule.sum_mem S fun i _ => S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
    have hli : LinearIndependent (FractionRing (MvPolynomial I Ω₀)) v := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples
        (nonZeroDivisors (MvPolynomial I Ω₀)) Finset.univ g
      choose q hq using fun k => ha k (Finset.mem_univ k)
      have hsum : ∑ k, q k • (MvPolynomial.C (b k) : MvPolynomial I Ω) = 0 := by
        apply IsFractionRing.injective (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))
        change j (∑ k, q k • MvPolynomial.C (b k)) = j 0
        rw [map_sum, map_zero]
        simp only [hsmul]
        change ∑ k, (algebraMap (MvPolynomial I Ω₀) (FractionRing (MvPolynomial I Ω₀)) (q k)) •
          v k = 0
        simp_rw [hq, Algebra.smul_def (a : MvPolynomial I Ω₀), mul_smul, ← Finset.smul_sum,
          hg, smul_zero]
      have hqi := (Fintype.linearIndependent_iff.mp
        (ReciprocityTheory.ChartRestriction.G.T0.PolynomialCoordinateBasis.linearIndependent_C
          (σ := I) b)) q hsum i
      have hzero : (a : MvPolynomial I Ω₀) • g i = 0 := by
        rw [← hq i, hqi, map_zero]
      rw [Algebra.smul_def] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors a.2)
    have hmul : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := by
      intro x hx y hy
      have hxy := Submodule.mul_mem_mul hx hy
      change x * y ∈ Submodule.span _ (Set.range v) * Submodule.span _ (Set.range v) at hxy
      rw [Submodule.span_mul_span] at hxy
      refine (Submodule.span_le.mpr ?_) hxy
      rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨k, rfl⟩, rfl⟩
      change j _ * j _ ∈ S
      rw [← map_mul]
      exact hj _
    have hone : 1 ∈ S := by simpa using hj 1
    let A := S.toSubalgebra hone fun x y hx hy => hmul x hx y hy
    have hfg : A.toSubmodule.FG := by
      rw [Submodule.toSubalgebra_toSubmodule]
      exact Submodule.fg_span (Set.finite_range v)
    have htop : ⊤ ≤ S := by
      intro x _
      obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (MvPolynomial I Ω) x
      have hint := IsIntegral.of_mem_of_fg _ hfg (j q) (hj q)
      have hinv := A.inv_mem_of_algebraic (x := ⟨j q, hj q⟩) hint.isAlgebraic
      rw [div_eq_mul_inv]
      exact hmul _ (hj p) _ hinv
    rw [Module.finrank_eq_card_basis (Module.Basis.mk hli htop)]
    simp
  let K := IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
    algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q))
  have hpoly : ∀ a : MvPolynomial I Ω₀, algebraMap (MvPolynomial I Ω)
      (FractionRing (MvPolynomial I Ω)) (MvPolynomial.map (algebraMap Ω₀ Ω) a) ∈ K := fun a => by
    induction a using MvPolynomial.induction_on with
    | C r =>
      have := K.algebraMap_mem r
      rw [hF] at this
      simpa [MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))] using this
    | add p q hp hq => simpa using K.add_mem hp hq
    | mul_X p i hp =>
      have hX : algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X i) ∈ K :=
        IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩
      simpa using K.mul_mem hp hX
  have hmem : ∀ x, φ x ∈ K := fun x => by
    obtain ⟨a, c, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial I Ω₀) x
    rw [map_div₀, hφ, hφ]
    exact K.div_mem (hpoly a) (hpoly c)
  have hle : K ≤ Subfield.toIntermediateField φ.fieldRange (fun r => by
      refine ⟨algebraMap (MvPolynomial I Ω₀) _ (MvPolynomial.C r), ?_⟩
      rw [hφ, hF]
      simp [MvPolynomial.map_C, MvPolynomial.algebraMap_eq, IsScalarTower.algebraMap_apply Ω (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω))]) := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    refine ⟨algebraMap (MvPolynomial I Ω₀) _ (MvPolynomial.X q), ?_⟩
    rw [hφ]; simp
  let ψ : FractionRing (MvPolynomial I Ω₀) →+* K := φ.codRestrict K hmem
  have hψ : Function.Bijective ψ := by
    refine ⟨fun x y h => φ.injective (congrArg Subtype.val h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := hle y.2
    exact ⟨x, Subtype.ext hx⟩
  rw [← h1]
  exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.ofBijective ψ hψ) (RingEquiv.refl _)
    (by ext x; rfl)).symm

theorem finrank_adjoin_vars :
    ∀ (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] (fn : Ω₀ →+* Ω) (I : Type) (d : ℕ),
      0 < d →
      (letI : Algebra Ω₀ Ω := fn.toAlgebra;
       Module.finrank Ω₀ Ω = d) →
      letI : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
        ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra;
      Module.finrank (IntermediateField.adjoin Ω₀ (Set.range fun q : I =>
        algebraMap (MvPolynomial I Ω) (FractionRing (MvPolynomial I Ω)) (MvPolynomial.X q)))
        (FractionRing (MvPolynomial I Ω)) = d := by
  intro Ω₀ Ω _ _ fn I d hd hfin
  let : Algebra Ω₀ Ω := fn.toAlgebra
  have : FiniteDimensional Ω₀ Ω := Module.finite_of_finrank_pos (hfin ▸ hd)
  let : Algebra Ω₀ (FractionRing (MvPolynomial I Ω)) :=
    ((algebraMap Ω (FractionRing (MvPolynomial I Ω))).comp fn).toAlgebra
  exact (finrank_fraction_over_adjoin_X_eq Ω₀ Ω I rfl).trans hfin

end GlobalTheory.CompanionTheory.FieldDeg
