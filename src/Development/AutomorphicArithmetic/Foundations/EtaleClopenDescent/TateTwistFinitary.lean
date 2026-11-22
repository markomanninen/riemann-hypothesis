module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorIsFinitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistRingFunctorPreservesFilteredColimitsStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

theorem UpperTheory.Cb.tateTwist_finitary :
    ∀ (q : ℕ) (i : ℤ), Finitary (R := ZMod q) (tw q i) := by
  intro q i
  exact GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary (ZMod q) (twF q i) (GlobalTheory.T.tateTwistRingFunctor_preservesFilteredColimits q i)
