module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFilteredColimitRingsFinitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorIsFinitaryStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistRingFunctorPreservesFilteredColimitsStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

theorem UpperTheory.twistCohomology_commutes_with_filtered_colimits :
    GlobalTheory.EtC.B1 := by
  intro q J _ _ D c hc n i
  have hF : GlobalTheory.EtC.Finitary (tw q i) := GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary (ZMod q) (twF q i) (GlobalTheory.T.tateTwistRingFunctor_preservesFilteredColimits q i)
  obtain ⟨h1, h2⟩ := GlobalTheory.T.etaleCohomology_filteredColimit_rings_finitary (ZMod q) (tw q i) hF J D c hc n
  exact ⟨fun x _ => h1 x, fun j y _ hy => h2 j y hy⟩
