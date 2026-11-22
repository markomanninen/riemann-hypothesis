module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPlaceGood
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceHeckeSatake
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceHeckeOperatorScalarOnSpherical
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClass
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedVectorsNeBotOfMemSumIntertwiningRanges
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceCompletionEquivUnique
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BiInvariantHeckeOpScalarOnSphericalIrreducibleStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RightTranslationSumScalarOnIsotypicPartStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitLocalComponentHasFixedVectorOfIsotypicStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.EigAgree

end GlobalTheory.EigAgree

theorem GlobalTheory.EigAgree.cast_ne_zero {D : D7} {μ : D.what₂.Tup} {a b : ℕ} (h : a = b) (f : D.what₂.Mt μ a) (hf : f ≠ 0) :
    (h ▸ f : D.what₂.Mt μ b) ≠ 0 := by
  subst h
  exact hf
