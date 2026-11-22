module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergWordL2Bound

@[expose] public section

open NumberField MeasureTheory

namespace GlobalTheory.WeilM

theorem schA_memLp_two : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ],
    letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
    ∀ μ : MeasureTheory.Measure (κ → AdeleRing (𝓞 F) F), μ.IsAddHaarMeasure →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, MeasureTheory.MemLp Φ 2 μ := by
  intro F _ _ κ _
  letI : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  intro μ hμ Φ hΦ
  obtain ⟨n, g, f, hg, rfl⟩ := GlobalTheory.ThetaSobolevBase.exists_sumPure hΦ
  classical
  unfold GlobalTheory.ThetaSobolevBase.sumPure
  have hs : ∀ s : Finset (Fin n), MemLp (∑ i ∈ s, GlobalTheory.WeilM.pureA F (f i) (g i)) 2 μ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simpa [Finset.sum_insert, hi] using
        (GlobalTheory.ThetaSobolevBase.memLp_pureA μ hμ (f i) (hg i)).add ih
  simpa using hs Finset.univ

end GlobalTheory.WeilM
