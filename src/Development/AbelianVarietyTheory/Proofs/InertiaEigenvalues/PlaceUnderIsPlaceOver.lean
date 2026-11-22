module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
public import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GroundTheory.Global (HeckeCharacter localAdelicChar)
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped Pointwise
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.DelGlob.placeUnder_isPlaceOver {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {K : Type} [Field K] [NumberField K]
    [Algebra K Ω] (L : Type) [Field L] [NumberField L] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω]
    {u : HeightOneSpectrum (𝓞 L)} (hu : IsPlaceOver A u) : IsPlaceOver A (u.under (𝓞 K)) := fun x => by
  have e : algebraMap L Ω ((algebraMap (𝓞 K) (𝓞 L) x : 𝓞 L) : L) = algebraMap K Ω (x : K) := by
    rw [IsScalarTower.algebraMap_apply K L Ω]
    rfl
  rw [← e, hu]
  rfl
