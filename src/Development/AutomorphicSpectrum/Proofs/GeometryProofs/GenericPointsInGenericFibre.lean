module

public import Mathlib
public import Development.WeilBound.CoreStatements.HodgeTatePoints.MlLift
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open PositivityTheory.HtPt.Ml (generic_max mem_of_dense_of_max)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CompanionTheory.Ar.M0

theorem genericPoints_subset_range_j :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
      (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O]
      (β : O →+* c.F) (Y : Model Xo c β),
      IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) →
        genericPoints Y.X ⊆ Set.range Y.j := by
  intro E _ _ _ H D l Xo c O _ β Y hO hFraction v hv
  let := β.toAlgebra
  have : IsFractionRing O c.F := hFraction
  have : IsPreimmersion (spMap β) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have := Y.flat
  have := Y.jQ_open
  have : IsProper Y.s := by
    obtain ⟨N, i, hi, hs⟩ := Y.proj
    have := hi
    have := isProper_str O N
    rw [← hs]
    infer_instance
  have : IsNoetherian (pullback Y.s (spMap β)) := {}

  -- Flatness lifts the generic point of the base to a generalization of v.
  let z : Sp c.F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum c.F)
  have hz : (spMap β z).asIdeal = ⊥ := by
    change RingHom.ker β = ⊥
    exact (RingHom.injective_iff_ker_eq_bot β).mp (IsFractionRing.injective O c.F)
  have hspec : spMap β z ⤳ Y.s v := by
    apply (PrimeSpectrum.le_iff_specializes _ _).mp
    change (spMap β z).asIdeal ≤ (Y.s v).asIdeal
    rw [hz]
    exact bot_le
  obtain ⟨v', hv'v, hv'⟩ := Flat.generalizingMap Y.s hspec
  rw [generic_max hv hv'v] at hv'
  obtain ⟨q, hq, _⟩ := Scheme.Pullback.exists_preimage_pullback v z hv'
  -- Every generalization of q has the same image, and the projection is injective.
  have hqmax : ∀ q', q' ⤳ q → q' = q := by
    intro q' hq'
    apply (pullback.fst Y.s (spMap β)).isEmbedding.injective
    rw [hq]
    exact generic_max hv (hq ▸ hq'.map (pullback.fst Y.s (spMap β)).continuous)
  obtain ⟨w, hw⟩ := mem_of_dense_of_max Y.jQ.isOpenEmbedding.isOpen_range Y.jQ_dense hqmax
  exact ⟨w, by rw [Model.j, Scheme.Hom.comp_apply, hw, hq]⟩

end GlobalTheory.CompanionTheory.Ar.M0
