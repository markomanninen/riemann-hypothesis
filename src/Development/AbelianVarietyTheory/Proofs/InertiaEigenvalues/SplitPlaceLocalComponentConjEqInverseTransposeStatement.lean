module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceLocalComponentConjEqInverseTranspose
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

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceLocalComponent_conj_eq_inverseTranspose : ∀ (D : D7) (n : ℕ) (π : NG.AutRep D.host.E n) (s : SplitPlace D.host.E)
    (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (s.w.adicCompletion D.host.E))), IsLocS π.S s σ →
    ∃ (κ : s.w.adicCompletion D.host.E ≃+* (GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E)
      (σ' : GlobalTheory.SmGL.IrrRep (GL (Fin n) ((GlobalTheory.TypeTame.conjSP s).w.adicCompletion D.host.E))) (e : σ.V ≃ₗ[ℂ] σ'.V),
      Continuous κ ∧ (∀ x : D.host.E, κ (algebraMap D.host.E _ x) = algebraMap D.host.E _ (D.host.conj x)) ∧
      IsLocS π.S (GlobalTheory.TypeTame.conjSP s) σ' ∧
      ∀ g a, e (σ.ρ (GlobalTheory.TypeTame.invTranspose n g) a) = σ'.ρ (Matrix.GeneralLinearGroup.map κ.toRingHom g) (e a) := by
  first | exact @GlobalTheory.ConjLocComp.exists_isLocS_conjSP | exact GlobalTheory.ConjLocComp.exists_isLocS_conjSP | (intros; apply GlobalTheory.ConjLocComp.exists_isLocS_conjSP <;> assumption)
