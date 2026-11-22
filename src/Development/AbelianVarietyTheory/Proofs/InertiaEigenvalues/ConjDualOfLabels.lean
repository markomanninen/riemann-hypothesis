module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceGoodSignature
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSplitPlaceEqFixedTypePrimePlace
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjugateSplitPlaceEqConjugatePlaceAndEmbedding
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelCharacterAtConjugateSplitPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivContra
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLocalComponentConjEqInverseTransposeStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneDualTransportMonodromyDimWildStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneLabelTransportDualInverseRootsStatement

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ConjPlaceDual

theorem conjPl_symm (D : D7) {w w' : PlE D.host} (h : IsConjPl D.host w w') : IsConjPl D.host w' w := by
  intro x y hy
  have hx : (x : D.host.E) = D.host.conj (y : D.host.E) := by
    rw [hy, GlobalTheory.SplitPlaceOver.host_conj_eq', GlobalTheory.SplitPlaceOver.host_conj_eq', IsCMField.complexConj_apply_apply]
  exact (h y x hx).symm

end GlobalTheory.ConjPlaceDual
