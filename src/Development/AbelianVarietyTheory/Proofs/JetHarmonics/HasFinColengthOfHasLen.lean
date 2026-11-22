module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import ReciprocityTheory.DualLattices.ProdDvdOfIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegOUnif
public import ReciprocityTheory.DualLattices.CotangentSurjective
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NotIsUnitNatCastOfIsLocalHom
public import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SplitUnramifiedPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueMaximalAbovePlace
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DifferentPowerUnramifiedIff
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.PGsh.Up
open GlobalTheory.TorsionCompare NumberField
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AvChartCompare

section Charts

variable {R : Type} [CommRing R]

variable {G : Over (Sp R)} {d : ℕ}

end Charts

section Series

variable {O : Type} [CommRing O] {d : ℕ}

variable {C : Type} [Field C] (v : Valuation C NNReal) [Algebra O C]

variable {v}

theorem hasLen_le_of_surjective (hv : v.Integers O) {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (π : M →ₗ[O] N) (hπ : Function.Surjective π) {x y : NNReal}
    (hx : HasLen v O M x) (hy : HasLen v O N y) : x ≤ y := by
  have := isLocal_of_integers hv
  obtain ⟨m, c, ⟨e⟩, rfl⟩ := hx
  obtain ⟨n, b, ⟨e'⟩, rfl⟩ := hy
  let f := e'.toLinearMap ∘ₗ π ∘ₗ e.symm.toLinearMap
  have hf : Function.Surjective f := e'.surjective.comp (hπ.comp e.symm.surjective)
  let q : Fin m → ((j : Fin n) → O ⧸ Ideal.span {b j}) :=
    fun i => f (Pi.single i (1 : O ⧸ Ideal.span {c i}))
  have hq : Submodule.span O (Set.range q) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨z, rfl⟩ := hf z
    have hz : z = ∑ i, (Quotient.out (z i) : O) • Pi.single i (1 : O ⧸ Ideal.span {c i}) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · simp only [Pi.smul_apply, Pi.single_eq_same, Algebra.smul_def, _root_.mul_one,
          Ideal.Quotient.algebraMap_eq]
        exact (Ideal.Quotient.mk_out (z k)).symm
      · intro b _ hb
        simp [Pi.single_eq_of_ne' hb]
      · intro h; exact absurd (Finset.mem_univ k) h
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz, map_sum]
    exact Submodule.sum_mem _ fun i _ => by
      rw [map_smul]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hT : ∀ k, ∑ i, (Matrix.diagonal c) k i • q i = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · simp only [Matrix.diagonal_apply_eq, q, ← map_smul]
      have : c k • (Pi.single k (1 : O ⧸ Ideal.span {c k}) : (i : Fin m) → O ⧸ Ideal.span {c i}) =
          0 := by
        funext j
        by_cases hj : j = k
        · subst hj
          simp only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply, Algebra.smul_def, _root_.mul_one,
            Ideal.Quotient.algebraMap_eq]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
        · simp [Pi.single_eq_of_ne hj]
      rw [this, map_zero]
    · intro b _ hb; simp [Matrix.diagonal_apply_ne _ (Ne.symm hb)]
    · intro h; exact absurd (Finset.mem_univ k) h
  have h := det_mem_span_prod n b m q hq (Matrix.diagonal c) hT
  rw [Matrix.det_diagonal] at h
  simpa only [map_prod] using hv.le_of_dvd (Ideal.mem_span_singleton.1 h)

end Series

section Emb

variable {E : Type} [Field E] [NumberField E] {C : Type} [Field C] [CharZero C]
  {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

end Emb

section Places

variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)]
  {C : Type} [Field C] [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O]

variable {w : AvDefs.Place p (𝓞 E)} {P : Ideal (𝓞 E)}

end Places



end GlobalTheory.AvChartCompare
