module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomLiftBasis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensitySixth
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsAddConjTransposeEq
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.VdEqZeroOfNotLe

@[expose] public section

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.HU

open LocalSpans idealPowerSpanBounds localizedQuotients integralBasisSpans

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem exists_arch {S : Subring K} {ϖ : K} (hS : IsLocUnif S ϖ) {α : Type*} [Fintype α] (f : α → K) :
    ∃ l : ℕ, ∀ a, ϖ ^ l * f a ∈ S := by
  classical
  choose l hl using fun a => hS.arch (f a)
  refine ⟨∑ a, l a, fun a => ?_⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), add_comm, pow_add, mul_assoc]
  exact S.mul_mem (pow_mem hS _) (hl a)

theorem exists_isE (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    ∃ e, IsE h (locF 𝔭 (spanO b)) 𝔭 e := by
  classical
  have : 𝔭.IsPrime := h𝔭.isPrime
  let f := algebraMap (𝓞 F) (𝓞 K)
  let g := algebraMap (𝓞 K) K
  let a := (gramK h b)⁻¹
  have hdet : IsUnit (gramK h b).det := isUnit_iff_ne_zero.2 (gramK_det_ne_zero hd b)
  -- Clear the denominators of all entries of the inverse Gram matrix at once.
  obtain ⟨n, hn, ha⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun p : κ × κ => a p.1 p.2))
  have hentry (i j : κ) : ∃ z : 𝓞 K, g z = (n : K) * a i j := by
    have hi := ha (a i j) (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩)
    exact ⟨⟨n • a i j, hi⟩, by simp [g, zsmul_eq_mul]⟩
  have hnspan : Ideal.span {(n : 𝓞 F)} ≠ 0 := by
    simpa using (Int.cast_ne_zero.mpr hn : (n : 𝓞 F) ≠ 0)
  have hpunit : ¬ IsUnit 𝔭 := fun hunit => h𝔭.ne_top (Ideal.isUnit_iff.mp hunit)
  -- Factor out the power of 𝔭 in the denominator ideal.
  obtain ⟨J, hJ, hJp⟩ :=
    (FiniteMultiplicity.of_not_isUnit hpunit hnspan).exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hJp
  obtain ⟨u, huJ, hu⟩ := IsConcreteLE.not_le_iff_exists.mp hJp
  generalize multiplicity 𝔭 (Ideal.span {(n : 𝓞 F)}) = l at hJ
  refine ⟨l, fun x hx t ht => ?_⟩
  have htu : t * u ∈ Ideal.span {(n : 𝓞 F)} := by
    rw [hJ]
    exact Ideal.mul_mem_mul ht huJ
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp htu
  let v := gramK h b *ᵥ b.equivFun x
  have hv : ∀ j, v j ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
    intro j
    have h1 := hx (b j) (le_locF 𝔭 _ (Submodule.subset_span ⟨j, rfl⟩))
    rw [form_repr h b] at h1
    have hb1 : b.equivFun (b j) = Pi.single j 1 := by
      funext j'
      rw [Basis.equivFun_self, Pi.single_apply]
      simp only [eq_comm]
    have hb2 : star (Pi.single j (1 : K) : κ → K) = Pi.single j 1 := by
      funext l
      by_cases hl : l = j
      · subst hl; simp
      · simp [hl]
    rwa [hb1, hb2, single_one_dotProduct] at h1
  have hx' : b.equivFun x = a *ᵥ v := by
    change b.equivFun x = (gramK h b)⁻¹ *ᵥ (gramK h b *ᵥ b.equivFun x)
    rw [mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, one_mulVec]
  change f t • x ∈ locF 𝔭 (spanO b)
  rw [← b.sum_equivFun x, hx', Finset.smul_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [mulVec, dotProduct, Finset.sum_smul, Finset.smul_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  obtain ⟨s, hs, hsj⟩ := (mem_locF 𝔭 _ _).mp (hv j)
  obtain ⟨y, hy⟩ := Submodule.mem_one.mp hsj
  obtain ⟨z, hz⟩ := hentry i j
  refine (mem_locF 𝔭 _ _).mpr ⟨u * s, fun hm => (h𝔭.isPrime.mem_or_mem hm).elim hu hs, ?_⟩
  have hprod : g (f (u * s)) * g (f t) * (a i j * v j) = g (f w * z * y) := by
    have hw' : g (f w) * (n : K) = g (f t) * g (f u) := by
      simpa [map_mul, f, g] using congrArg (fun r => g (f r)) hw
    have hy' : g y = g (f s) * v j := hy
    calc
      _ = (g (f t) * g (f u)) * (a i j * (g (f s) * v j)) := by
        simp only [map_mul]
        ring
      _ = _ := by
        rw [map_mul, map_mul, hz, hy', ← hw']
        ring
  change f (u * s) • f t • (a i j * v j) • b i ∈ spanO b
  rw [← algebraMap_smul K (f (u * s)), ← algebraMap_smul K (f t), smul_smul, smul_smul]
  change (g (f (u * s)) * g (f t) * (a i j * v j)) • b i ∈ spanO b
  rw [hprod, show g (f w * z * y) • b i = (f w * z * y) • b i from algebraMap_smul K _ _]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem isE_eA (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hd : ∀ x, h x x = 0 → x = 0) (b : Basis κ K V) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    IsE h (locF 𝔭 (spanO b)) 𝔭 (eA h (locF 𝔭 (spanO b)) 𝔭) :=
  Nat.sInf_mem (s := {e | IsE h (locF 𝔭 (spanO b)) 𝔭 e}) (exists_isE hK hF hd b h𝔭)

end Formalism.HermitianLattices.Ext.L3.HU
