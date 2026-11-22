module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.IsDualPair
public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.DecZhat
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryCriterion
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RootEquality

@[expose] public section

noncomputable section

namespace UpperTheory.V.Pa

section Abstract

variable {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M] (ρ : Representation R G M)

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [Finite M]

end Abstract

theorem unrBare : ∀ (l : ℕ) [Fact l.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
    (C : Type) [CommGroup C] [Finite C] (χ : ReciprocityTheory.Gal.Dec (F := F) A →* C), Formalism.ConjugateSelfDual.IsPlaceOver A v →
    IsOpen (χ.ker : Set (ReciprocityTheory.Gal.Dec (F := F) A)) → (Nat.card C).Coprime l →
    UnrCount l (ReciprocityTheory.Gal.Dec (F := F) A) ((ReciprocityTheory.Gal.Ine A).subgroupOf (ReciprocityTheory.Gal.Dec A) ⊓ χ.ker) :=
  _root_.UpperTheory.Reformulated.B.RootEquality.unrBare

end UpperTheory.V.Pa
