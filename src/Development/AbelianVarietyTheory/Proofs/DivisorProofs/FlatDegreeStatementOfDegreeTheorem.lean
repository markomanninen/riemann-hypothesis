module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldAbelianTameIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticSubfieldRootDiscriminant
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.NormalFormsEqOfKeyDataIsoComplex
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsRigTransport
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleIffOfIsReduced
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModuliSchemePolarizedAbelianLevel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.FieldSizeMonotone
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LevelOfSplitAndLevelCoeffExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelExistsAfterBaseChange
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGlobalModelGoodLevelAllPrimes
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValuationExtension
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationWeightedLogNormSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSumDegreeFormula
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LieMultIffFinrank
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanNormSquareExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationIndexValuationCompat

@[expose] public section

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM Matrix

namespace GlobalTheory.FlatDegreeCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Degree

variable {k : Type} [Field k] [NumberField k]

end Degree

section Lie

variable {k : Type} [Field k] [NumberField k] {t : SAB H (Sp k)} {m : ℕ} {x : Fin m → (epsR k ⟶ t.G)}

theorem isEigBasis_iff (τ : E →+* k) : EigenvectorLieDegree.IsEigBasis t.act (τ.comp (algebraMap (𝓞 E) E)) x ↔
    AdelicDegreeTameRamification.IsEigenBasis t (fun a => τ (a : E)) x := Iff.rfl


end Lie

section Point

variable {k : Type} [Field k] [NumberField k]

variable {t : SAB H (Sp k)} {τ τ' : E →+* k} {p q : ℕ}

end Point

section Extension

variable {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] {i : k →+* k'}

variable {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)} {ε : HeightOneSpectrum (𝓞 k') → ℕ}

variable {t : SAB H (Sp k)} {t' : SAB H (Sp k')}

end Extension

end GlobalTheory.FlatDegreeCompare
