module

public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.EtaleCohomology.TateTwists.EtaleTwistedCupAssocOfTwistedPairingExistsAssoc

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleTateTwistCupPairingExistsAndCupUnique : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), IsTwPair (twPair q i j) ∧ ∀ (k : ℤ), i + j = k →
    ∀ μ ν : Pair (res _ (tw q i)) (res _ (tw q j)) (res _ (tw q k)), IsTwPair μ → IsTwPair ν →
      ∀ (E : Spc) {n m w : ℤ} (h : n + m = w), μ.cup E h = ν.cup E h

theorem t_twpair_ex_of (htw : EtaleTateTwistCupPairingExistsAndCupUnique) : t_twpair_ex := by
  intro q _ i j
  exact ⟨twPair q i j, (htw q i j).1⟩

end LateralTheory.EtaleFoundations
