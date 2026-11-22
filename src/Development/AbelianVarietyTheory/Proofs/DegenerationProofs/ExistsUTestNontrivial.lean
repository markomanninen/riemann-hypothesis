module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevelStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatementsStatement
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBigThetaSysWithAction
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsWeilIsRoot
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsPrimitiveRootArcRoot
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDiscreteValuationRingAndFiniteResidueFieldValu
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsFunctional
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcDataSpecialiseAtUniformiserStatement
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedModelTorsionLabelsExist
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFractionRingOfForallDiv
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemOfPolarisedLevel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HypSEisensteinCurve
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelHasConstantThetaPt
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTorsionGeneratorsRational
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosurePadicInt

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.DegenerateTest

section Pull

variable {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} [GrpObj G] [GrpObj G'] [GrpObj G'']
  {L : LB G.left} {L' : LB G'.left} {L'' : LB G''.left}

end Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}


open IsLocalRing in
theorem exists_padic_embedding (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (h : Finite (ResidueField V)) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (c : FractionRing V →+* PadicAlgCl p),
      ∀ x, ‖c x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)) := by
  obtain ⟨p, _, K₀, e, e₀, -, he⟩ := completeDVR_eq_integralClosure_padicInt.1 V (FractionRing V) h
  refine ⟨p, inferInstance, (algebraMap K₀ (PadicAlgCl p)).comp e.toRingHom, fun x => ?_⟩
  refine (mem_integralClosure_padicInt_iff K₀ (e x)).symm.trans ⟨fun hx => ⟨e₀.symm ⟨e x, hx⟩, ?_⟩, ?_⟩
  · apply e.injective
    rw [he, e₀.apply_symm_apply]
  · rintro ⟨v, rfl⟩
    rw [he]
    exact (e₀ v).2

end GlobalTheory.DegenerateTest

end
