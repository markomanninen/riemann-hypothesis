module

public import Mathlib
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.ParConsts
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.InstLocalRingSymplecticCoefficients
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.UnitaryThreeIrreduciblePoints
public import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.GradedCompletionLemmas
public import ReciprocityTheory.GaloisValuations.ArithOfA

@[expose] public section

open NumberField IsDedekindDomain Pointwise

namespace GlobalTheory.PlaceConjQ

theorem eq_of_prime_mem {q : ℕ} (hq : q.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : v = w := by
  have : Fact q.Prime := ⟨hq⟩
  have := v.isPrime
  have := w.isPrime
  have h1 := ((ReciprocityTheory.Gal.liesOver_span_iff q v.asIdeal).2 hv).over
  have h2 := ((ReciprocityTheory.Gal.liesOver_span_iff q w.asIdeal).2 hw).over
  apply HeightOneSpectrum.ext
  ext x
  obtain ⟨n, rfl⟩ := Rat.ringOfIntegersEquiv.symm.surjective x
  have e : Rat.ringOfIntegersEquiv.symm n = algebraMap ℤ (𝓞 ℚ) n :=
    (eq_intCast Rat.ringOfIntegersEquiv.symm.toRingHom n).trans (eq_intCast (algebraMap ℤ (𝓞 ℚ)) n).symm
  rw [e, ← Ideal.mem_comap, ← Ideal.mem_comap]
  change n ∈ v.asIdeal.under ℤ ↔ n ∈ w.asIdeal.under ℤ
  rw [← h1, ← h2]

end GlobalTheory.PlaceConjQ
